(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for natural transformations of semifunctors\<close>
theory CZH_SMC_Small_NTSMCF
  imports 
    CZH_DG_Small_TDGHM
    CZH_SMC_Small_Semifunctor
    CZH_SMC_NTSMCF
begin



subsection\<open>Natural transformation of semifunctors with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tm_ntsmcf = is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> +
  assumes tm_ntsmcf_is_tm_tdghm[slicing_intros]: "ntsmcf_tdghm \<NN> :
    smcf_dghm \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m smcf_dghm \<GG> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"

syntax "_is_tm_ntsmcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tm_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_tm_ntsmcfs :: "V \<Rightarrow> V"
  where "all_tm_ntsmcfs \<alpha> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tm_ntsmcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tm_ntsmcfs \<alpha> \<AA> \<BB> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_tm_ntsmcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_tm_ntsmcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv>
    set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma (in is_tm_ntsmcf) tm_ntsmcf_is_tm_tdghm':
  assumes "\<alpha>' = \<alpha>"
    and "\<FF>' = smcf_dghm \<FF>"
    and "\<GG>' = smcf_dghm \<GG>"
    and "\<AA>' = smc_dg \<AA>"
    and "\<BB>' = smc_dg \<BB>"
  shows "ntsmcf_tdghm \<NN> :
    \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule tm_ntsmcf_is_tm_tdghm)

lemmas [slicing_intros] = is_tm_ntsmcf.tm_ntsmcf_is_tm_tdghm'


text\<open>Rules.\<close>

lemma (in is_tm_ntsmcf) is_tm_ntsmcf_axioms'[smc_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_ntsmcf_axioms)

mk_ide rf is_tm_ntsmcf_def[unfolded is_tm_ntsmcf_axioms_def]
  |intro is_tm_ntsmcfI|
  |dest is_tm_ntsmcfD[dest]|
  |elim is_tm_ntsmcfE[elim]|

lemmas [smc_small_cs_intros] = is_tm_ntsmcfD(1)


text\<open>Slicing.\<close>

context is_tm_ntsmcf
begin

interpretation tdghm: is_tm_tdghm
  \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close> \<open>smcf_dghm \<GG>\<close> \<open>ntsmcf_tdghm \<NN>\<close>
  by (rule tm_ntsmcf_is_tm_tdghm)

lemmas_with [unfolded slicing_simps]:
  tm_ntsmcf_NTMap_in_Vset = tdghm.tm_tdghm_NTMap_in_Vset

end


text\<open>Elementary properties.\<close>

sublocale is_tm_ntsmcf \<subseteq> NTDom: is_tm_semifunctor \<alpha> \<AA> \<BB> \<FF> 
  using tm_ntsmcf_is_tm_tdghm 
  by (intro is_tm_semifunctorI) (auto simp: smc_cs_intros)

sublocale is_tm_ntsmcf \<subseteq> NTCod: is_tm_semifunctor \<alpha> \<AA> \<BB> \<GG>
  using tm_ntsmcf_is_tm_tdghm 
  by (intro is_tm_semifunctorI) (auto simp: smc_cs_intros)


text\<open>Further rules.\<close>

lemma is_tm_ntsmcfI':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<FF>: is_tm_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tm_semifunctor \<alpha> \<AA> \<BB> \<GG> by (rule assms(3))
  show ?thesis
  proof(intro is_tm_ntsmcfI)
    show "ntsmcf_tdghm \<NN> :
      smcf_dghm \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>m smcf_dghm \<GG> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
      by (intro is_tm_tdghmI) (auto simp: slicing_intros)
  qed (auto simp: assms(2,3) vfsequence_axioms smc_cs_intros)
qed

lemma is_tm_ntsmcfD':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret is_tm_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by (auto simp: smc_small_cs_intros)
qed

lemmas [smc_small_cs_intros] = is_tm_ntsmcfD'(2,3)


text\<open>Size.\<close>

lemma small_all_tm_ntsmcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> 
    elts (set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_ntsmcfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<NN> assume "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<FF> \<GG> \<AA> \<BB> where "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    then interpret is_tm_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> .
    have "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (auto simp: smc_cs_intros)
    then show "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  qed
qed

lemma small_tm_ntsmcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    )
    auto

lemma small_these_tm_ntsmcfs[simp]: 
  "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    ) 
    auto


text\<open>Further elementary results.\<close>

lemma these_tm_ntsmcfs_iff(*not simp*): 
  "\<NN> \<in>\<^sub>\<circ> these_tm_ntsmcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow>
    \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto


subsubsection\<open>
Opposite natural transformation of semifunctors with tiny maps
\<close>

lemma (in is_tm_ntsmcf) is_tm_ntsmcf_op: "op_ntsmcf \<NN> : 
  op_smcf \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_smc \<BB>"
  by (intro is_tm_ntsmcfI') 
    (cs_concl cs_intro: smc_cs_intros smc_op_intros)+

lemma (in is_tm_ntsmcf) is_tm_ntsmcf_op'[smc_op_intros]: 
  assumes "\<GG>' = op_smcf \<GG>"
    and "\<FF>' = op_smcf \<FF>"
    and "\<AA>' = op_smc \<AA>"
    and "\<BB>' = op_smc \<BB>"
  shows "op_ntsmcf \<NN> : \<GG>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_ntsmcf_op)

lemmas is_tm_ntsmcf_op[smc_op_intros] = is_tm_ntsmcf.is_tm_ntsmcf_op'


subsubsection\<open>
Vertical composition of natural transformations of 
semifunctors with tiny maps
\<close>

lemma ntsmcf_vcomp_is_tm_ntsmcf[smc_small_cs_intros]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<MM>: is_tm_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_tm_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis 
    by (rule is_tm_ntsmcfI') (auto intro: smc_cs_intros smc_small_cs_intros)
qed 


subsubsection\<open>
Composition of a natural transformation of semifunctors and a semifunctor
\<close>

lemma ntsmcf_smcf_comp_is_tm_ntsmcf:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_tm_ntsmcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_tm_semifunctor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  from assms show ?thesis
    by (intro is_tm_ntsmcfI)
      (
        cs_concl 
          cs_simp: slicing_commute[symmetric] 
          cs_intro: smc_cs_intros dg_small_cs_intros slicing_intros
      )+
qed

lemma ntsmcf_smcf_comp_is_tm_ntsmcf'[smc_small_cs_intros]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<FF> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>"
    and "\<GG>' = \<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<HH> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule ntsmcf_smcf_comp_is_tm_ntsmcf)


subsubsection\<open>
Composition of a semifunctor and a natural transformation of semifunctors
\<close>

lemma smcf_ntsmcf_comp_is_tm_ntsmcf:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<HH>: is_tm_semifunctor \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_tm_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  from assms show ?thesis
    by (intro is_tm_ntsmcfI)
      (
        cs_concl 
          cs_simp: slicing_commute[symmetric] 
          cs_intro: smc_cs_intros dg_small_cs_intros slicing_intros
      )+
qed

lemma smcf_ntsmcf_comp_is_tm_ntsmcf'[smc_small_cs_intros]:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>"
    and "\<GG>' = \<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG>"
  shows "\<HH> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule smcf_ntsmcf_comp_is_tm_ntsmcf)



subsection\<open>Tiny natural transformation of semifunctors\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tiny_ntsmcf = is_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> +
  assumes tiny_ntsmcf_is_tdghm[slicing_intros]: "ntsmcf_tdghm \<NN> :
    smcf_dghm \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y smcf_dghm \<GG> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> smc_dg \<BB>" 

syntax "_is_tiny_ntsmcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y _ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tiny_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_tiny_ntsmcfs :: "V \<Rightarrow> V"
  where "all_tiny_ntsmcfs \<alpha> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tiny_ntsmcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tiny_ntsmcfs \<alpha> \<AA> \<BB> \<equiv> 
    set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_tiny_ntsmcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_tiny_ntsmcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv> 
    set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma (in is_tiny_ntsmcf) tiny_ntsmcf_is_tdghm':
  assumes "\<alpha>' = \<alpha>"
    and "\<FF>' = smcf_dghm \<FF>"
    and "\<GG>' = smcf_dghm \<GG>"
    and "\<AA>' = smc_dg \<AA>"
    and "\<BB>' = smc_dg \<BB>"
  shows "ntsmcf_tdghm \<NN> : \<FF>' \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule tiny_ntsmcf_is_tdghm)

lemmas [slicing_intros] = is_tiny_ntsmcf.tiny_ntsmcf_is_tdghm'


text\<open>Rules.\<close>

lemma (in is_tiny_ntsmcf) is_tiny_ntsmcf_axioms'[smc_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule is_tiny_ntsmcf_axioms)

mk_ide rf is_tiny_ntsmcf_def[unfolded is_tiny_ntsmcf_axioms_def]
  |intro is_tiny_ntsmcfI|
  |dest is_tiny_ntsmcfD[dest]|
  |elim is_tiny_ntsmcfE[elim]|


text\<open>Elementary properties.\<close>

sublocale is_tiny_ntsmcf \<subseteq> NTDom: is_tiny_semifunctor \<alpha> \<AA> \<BB> \<FF> 
  using tiny_ntsmcf_is_tdghm 
  by (intro is_tiny_semifunctorI) (auto simp: smc_cs_intros)

sublocale is_tiny_ntsmcf \<subseteq> NTCod: is_tiny_semifunctor \<alpha> \<AA> \<BB> \<GG>
  using tiny_ntsmcf_is_tdghm 
  by (intro is_tiny_semifunctorI) (auto simp: smc_cs_intros)

sublocale is_tiny_ntsmcf \<subseteq> is_tm_ntsmcf
  by (rule is_tm_ntsmcfI')
    (auto simp: tiny_ntsmcf_is_tdghm smc_small_cs_intros smc_cs_intros)


text\<open>Further rules.\<close>

lemma is_tiny_ntsmcfI':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto intro: is_tiny_ntsmcfI)

lemma is_tiny_ntsmcfD':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret is_tiny_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    by 
      (
        auto 
          simp: is_ntsmcf_axioms 
          intro:  
            NTDom.is_tiny_semifunctor_axioms 
            NTCod.is_tiny_semifunctor_axioms
      )
qed

lemmas [smc_small_cs_intros] = is_tiny_ntsmcfD'(2,3)

lemma is_tiny_ntsmcfE':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto dest: is_tiny_ntsmcfD'(2,3))

lemma is_tiny_ntsmcf_iff:
  "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<longleftrightarrow>
    (
      \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<and>
      \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<and>
      \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>
    )"
  using is_tiny_ntsmcfI' is_tiny_ntsmcfD' by (intro iffI) auto


text\<open>Size.\<close>

lemma (in is_tiny_ntsmcf) tiny_ntsmcf_in_Vset: "\<NN> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [smc_cs_intros] =
    tm_ntsmcf_NTMap_in_Vset
    NTDom.tiny_smcf_in_Vset
    NTCod.tiny_smcf_in_Vset
    NTDom.HomDom.tiny_smc_in_Vset
    NTDom.HomCod.tiny_smc_in_Vset
  show ?thesis
    by (subst ntsmcf_def) 
      (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros V_cs_intros)
qed

lemma small_all_tiny_ntsmcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> 
    elts (set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_ntsmcfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<NN> assume "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<FF> \<GG> \<AA> \<BB> where "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    then interpret is_tiny_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> .
    have "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
      by (auto intro: smc_cs_intros)
    then show "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  qed
qed

lemma small_tiny_ntsmcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of 
            _ 
            \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    )
    auto

lemma small_these_tiny_ntcfs[simp]: 
  "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule down[
        of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
        ]
    ) 
    auto

lemma tiny_ntsmcfs_vsubset_Vset[simp]: 
  "set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  (is \<open>set ?ntsmcfs \<subseteq>\<^sub>\<circ> _\<close>)
proof(cases \<open>tiny_semicategory \<alpha> \<AA> \<and> tiny_semicategory \<alpha> \<BB>\<close>)
  case True
  then have "tiny_semicategory \<alpha> \<AA>" and "tiny_semicategory \<alpha> \<BB>" by auto
  show ?thesis 
  proof(rule vsubsetI)
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> set ?ntsmcfs"
    then obtain \<FF> \<GG> where "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by auto
    then interpret is_tiny_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> .
    from tiny_ntsmcf_in_Vset show "\<NN> \<in>\<^sub>\<circ> Vset \<alpha>" by simp
  qed
next
  case False
  then have "set ?ntsmcfs = 0" 
    unfolding is_tiny_ntsmcf_iff is_tiny_semifunctor_iff by auto
  then show ?thesis by simp
qed

lemma (in is_ntsmcf) ntsmcf_is_tiny_ntsmcf_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>" 
proof(intro is_tiny_ntsmcfI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>"
    by (intro ntsmcf_is_ntsmcf_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: dg_cs_intros\<close>)+
  show "ntsmcf_tdghm \<NN> :
    smcf_dghm \<FF> \<mapsto>\<^sub>D\<^sub>G\<^sub>H\<^sub>M\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y smcf_dghm \<GG> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> smc_dg \<BB>"
    by 
      ( 
        rule is_tdghm.tdghm_is_tiny_tdghm_if_ge_Limit, 
        rule ntsmcf_is_tdghm;
        intro assms
     )
qed


text\<open>Further elementary results.\<close>

lemma these_tiny_ntsmcfs_iff(*not simp*):
  "\<NN> \<in>\<^sub>\<circ> these_tiny_ntsmcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow>
    \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto


subsubsection\<open>Opposite natural transformation of tiny semifunctors\<close>

lemma (in is_tiny_ntsmcf) is_tm_ntsmcf_op: "op_ntsmcf \<NN> :
  op_smcf \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> op_smc \<BB>"
  by (intro is_tiny_ntsmcfI')
    (cs_concl cs_intro: smc_cs_intros smc_op_intros)+

lemma (in is_tiny_ntsmcf) is_tiny_ntsmcf_op'[smc_op_intros]: 
  assumes "\<GG>' = op_smcf \<GG>"
    and "\<FF>' = op_smcf \<FF>"
    and "\<AA>' = op_smc \<AA>"
    and "\<BB>' = op_smc \<BB>"
  shows "op_ntsmcf \<NN> : \<GG>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_ntsmcf_op)

lemmas is_tiny_ntsmcf_op[smc_op_intros] = is_tiny_ntsmcf.is_tiny_ntsmcf_op'


subsubsection\<open>
Vertical composition of tiny natural transformations of 
semifunctors
\<close>

lemma ntsmcf_vcomp_is_tiny_ntsmcf[smc_small_cs_intros]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<MM>: is_tiny_ntsmcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_tiny_ntsmcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis by (rule is_tiny_ntsmcfI') (auto intro: smc_small_cs_intros)
qed

text\<open>\newpage\<close>

end