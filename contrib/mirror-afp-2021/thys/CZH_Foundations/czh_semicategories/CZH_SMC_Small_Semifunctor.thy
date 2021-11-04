(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for semifunctors\<close>
theory CZH_SMC_Small_Semifunctor
  imports 
    CZH_DG_Small_DGHM
    CZH_SMC_Semifunctor
    CZH_SMC_Small_Semicategory
begin



subsection\<open>Semifunctor with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tm_semifunctor = is_semifunctor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> +
  assumes tm_smcf_is_tm_dghm[slicing_intros]: 
    "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> smc_dg \<BB>" 

syntax "_is_tm_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_tm_semifunctor \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_tm_semifunctor :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_tm_semifunctor \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_tm_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_tm_semifunctor \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_tm_smcfs :: "V \<Rightarrow> V"
  where "all_tm_smcfs \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation small_tm_smcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "small_tm_smcfs \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma (in is_tm_semifunctor) tm_smcf_is_tm_dghm':
  assumes "\<alpha>' = \<alpha>"
    and "\<AA>' = smc_dg \<AA>"
    and "\<BB>' = smc_dg \<BB>"
  shows "smcf_dghm \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule tm_smcf_is_tm_dghm)

lemmas [slicing_intros] = is_tm_semifunctor.tm_smcf_is_tm_dghm'


text\<open>Rules.\<close>

lemma (in is_tm_semifunctor) is_tm_semifunctor_axioms'[smc_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_semifunctor_axioms)

mk_ide rf is_tm_semifunctor_def[unfolded is_tm_semifunctor_axioms_def]
  |intro is_tm_semifunctorI|
  |dest is_tm_semifunctorD[dest]|
  |elim is_tm_semifunctorE[elim]|

lemmas [smc_small_cs_intros] = is_tm_semifunctorD(1)


text\<open>Slicing.\<close>

context is_tm_semifunctor
begin

interpretation dghm: is_tm_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
  by (rule tm_smcf_is_tm_dghm)

lemmas_with [unfolded slicing_simps]:
  tm_smcf_ObjMap_in_Vset[smc_small_cs_intros] = dghm.tm_dghm_ObjMap_in_Vset
  and tm_smcf_ArrMap_in_Vset[smc_small_cs_intros] = dghm.tm_dghm_ArrMap_in_Vset

end


text\<open>Elementary properties.\<close>

sublocale is_tm_semifunctor \<subseteq> HomDom: tiny_semicategory \<alpha> \<AA> 
proof(rule tiny_semicategoryI')
  show "\<AA>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule vdomain_in_VsetI[OF tm_smcf_ObjMap_in_Vset, unfolded smc_cs_simps])
  show "\<AA>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule vdomain_in_VsetI[OF tm_smcf_ArrMap_in_Vset, unfolded smc_cs_simps])
qed (simp add: smc_cs_intros)


text\<open>Further rules.\<close>

lemma is_tm_semifunctorI':
  assumes [simp]: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and [simp]: "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and [simp]: "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and [simp]: "semicategory \<alpha> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_tm_semifunctorI)
  interpret is_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  show "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
    by (intro is_tm_dghmI', unfold slicing_simps) (auto simp: slicing_intros)
qed simp_all

lemma is_tm_semifunctorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "semicategory \<alpha> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  interpret is_tm_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))    
  show "semicategory \<alpha> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (auto intro: smc_cs_intros smc_small_cs_intros)
qed

lemmas [smc_small_cs_intros] = is_tm_semifunctorD'(1)

lemma is_tm_semifunctorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "semicategory \<alpha> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  using is_tm_semifunctorD'[OF assms] by simp


text\<open>Size.\<close>

lemma small_all_tm_smcfs[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show 
    "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
      elts (set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_smcfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<FF> assume "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<AA> \<BB> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    then interpret is_tm_semifunctor \<alpha> \<AA> \<BB> \<FF> by simp
    show "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (auto intro: is_semifunctor_axioms)
  qed
qed


subsubsection\<open>Opposite semifunctor with tiny maps\<close>

lemma (in is_tm_semifunctor) is_tm_semifunctor_op: 
  "op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_smc \<BB>"
  by (intro is_tm_semifunctorI', unfold smc_op_simps)
    (cs_concl cs_intro: smc_cs_intros smc_op_intros smc_small_cs_intros)

lemma (in is_tm_semifunctor) is_tm_semifunctor_op'[smc_op_intros]:  
  assumes "\<AA>' = op_smc \<AA>" and "\<BB>' = op_smc \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_semifunctor_op)

lemmas is_tm_semifunctor_op[smc_op_intros] = is_tm_semifunctor.is_tm_semifunctor_op'


subsubsection\<open>Composition of semifunctors with tiny maps\<close>

lemma smcf_comp_is_tm_semifunctor[smc_small_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(rule is_tm_semifunctorI)
  interpret \<FF>: is_tm_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tm_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  show "smcf_dghm (\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF>) : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"
    unfolding slicing_commute[symmetric] 
    using \<FF>.tm_smcf_is_tm_dghm \<GG>.tm_smcf_is_tm_dghm  
    by (auto simp: dg_small_cs_intros)
  show "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (auto intro: smc_cs_intros)
qed


subsubsection\<open>Finite semicategories and semifunctors with tiny maps\<close>

lemma (in is_semifunctor) smcf_is_tm_semifunctor_if_HomDom_finite_semicategory:
  assumes "finite_semicategory \<alpha> \<AA>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_tm_semifunctorI)
  interpret \<AA>: finite_semicategory \<alpha> \<AA> by (rule assms(1))
  show "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"
    by 
      (
        rule is_dghm.dghm_is_tm_dghm_if_HomDom_finite_digraph[
          OF smcf_is_dghm \<AA>.fin_smc_finite_digraph
          ]
      )
qed (auto intro: smc_cs_intros)


subsubsection\<open>Constant semifunctor with tiny maps\<close>

lemma smcf_const_is_tm_semifunctor: 
  assumes "tiny_semicategory \<alpha> \<CC>"
    and "semicategory \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f = f"
  shows "smcf_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<DD>"
proof(intro is_tm_semifunctorI)
  interpret \<CC>: tiny_semicategory \<alpha> \<CC> by (rule assms(1))
  interpret \<DD>: semicategory \<alpha> \<DD> by (rule assms(2))
  show "smcf_dghm (smcf_const \<CC> \<DD> a f) : smc_dg \<CC> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> smc_dg \<DD>"
    unfolding slicing_commute[symmetric]
    by (rule dghm_const_is_tm_dghm) 
      (auto simp: slicing_simps \<CC>.tiny_smc_tiny_digraph assms(3) \<DD>.smc_digraph)
  from assms show "smcf_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros)
qed

lemma smcf_const_is_tm_semifunctor':
  assumes "tiny_semicategory \<alpha> \<CC>"
    and "semicategory \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f = f"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "smcf_const \<CC> \<DD> a f : \<CC>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<DD>'"
  using assms(1-4) unfolding assms(5,6) by (rule smcf_const_is_tm_semifunctor)

lemmas [smc_small_cs_intros] = smcf_const_is_tm_semifunctor'



subsection\<open>Tiny semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tiny_semifunctor = is_semifunctor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> + 
  assumes tiny_smcf_is_tiny_dghm[slicing_intros]: 
    "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> smc_dg \<BB>"

syntax "_is_tiny_semifunctor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_tiny_semifunctor \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_tiny_smcf :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_tiny_smcf \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_tiny_smcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_tiny_smcf \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_tiny_smcfs :: "V \<Rightarrow> V"
  where "all_tiny_smcfs \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tiny_smcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tiny_smcfs \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

lemmas [slicing_intros] = is_tiny_semifunctor.tiny_smcf_is_tiny_dghm


text\<open>Rules.\<close>

lemma (in is_tiny_semifunctor) is_tiny_semifunctor_axioms'[smc_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tiny_semifunctor_axioms)

mk_ide rf is_tiny_semifunctor_def[unfolded is_tiny_semifunctor_axioms_def]
  |intro is_tiny_semifunctorI|
  |dest is_tiny_semifunctorD[dest]|
  |elim is_tiny_semifunctorE[elim]|

lemmas [smc_small_cs_intros] = is_tiny_semifunctorD(1)


text\<open>Elementary properties.\<close>

sublocale is_tiny_semifunctor \<subseteq> HomDom: tiny_semicategory \<alpha> \<AA>
proof(intro tiny_semicategoryI')
  interpret dghm: is_tiny_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
    by (rule tiny_smcf_is_tiny_dghm)
  show "\<AA>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule dghm.HomDom.tiny_dg_Obj_in_Vset[unfolded slicing_simps])    
  show "\<AA>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule dghm.HomDom.tiny_dg_Arr_in_Vset[unfolded slicing_simps])    
qed (auto simp: smc_cs_intros)

sublocale is_tiny_semifunctor \<subseteq> HomCod: tiny_semicategory \<alpha> \<BB>
proof(intro tiny_semicategoryI')
  interpret dghm: is_tiny_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
    by (rule tiny_smcf_is_tiny_dghm)
  show "\<BB>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule dghm.HomCod.tiny_dg_Obj_in_Vset[unfolded slicing_simps])    
  show "\<BB>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule dghm.HomCod.tiny_dg_Arr_in_Vset[unfolded slicing_simps])    
qed (auto simp: smc_cs_intros)

sublocale is_tiny_semifunctor \<subseteq> is_tm_semifunctor
proof(intro is_tm_semifunctorI')
  interpret dghm: is_tiny_dghm \<alpha> \<open>smc_dg \<AA>\<close> \<open>smc_dg \<BB>\<close> \<open>smcf_dghm \<FF>\<close>
    by (rule tiny_smcf_is_tiny_dghm)
  note Vset[unfolded slicing_simps] = 
    dghm.tiny_dghm_ObjMap_in_Vset
    dghm.tiny_dghm_ArrMap_in_Vset
  show "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (intro Vset)+
qed (auto simp: smc_cs_intros)


text\<open>Further rules.\<close>

lemma is_tiny_semifunctorI':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "tiny_semicategory \<alpha> \<AA>"
    and "tiny_semicategory \<alpha> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms 
  by 
    (
      auto simp: 
        smc_cs_simps 
        smc_cs_intros 
        is_semifunctor.smcf_is_dghm 
        is_tiny_dghm.intro 
        is_tiny_semifunctorI 
        tiny_semicategory.tiny_smc_tiny_digraph
    )

lemma is_tiny_semifunctorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "tiny_semicategory \<alpha> \<AA>"
    and "tiny_semicategory \<alpha> \<BB>"
proof-
  interpret is_tiny_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "tiny_semicategory \<alpha> \<AA>" 
    and "tiny_semicategory \<alpha> \<BB>"
    by (auto intro: smc_small_cs_intros)
qed

lemmas [smc_small_cs_intros] = is_tiny_semifunctorD'(2,3)

lemma is_tiny_semifunctorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "tiny_semicategory \<alpha> \<AA>"
    and "tiny_semicategory \<alpha> \<BB>"
  using is_tiny_semifunctorD'[OF assms] by auto

lemma is_tiny_semifunctor_iff:
  "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<longleftrightarrow>
    (\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<and> tiny_semicategory \<alpha> \<AA> \<and> tiny_semicategory \<alpha> \<BB>)"
  by (auto intro: is_tiny_semifunctorI' dest: is_tiny_semifunctorD'(2,3))


text\<open>Size.\<close>

lemma (in is_tiny_semifunctor) tiny_smcf_in_Vset: "\<FF> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [smc_cs_intros] = 
    tm_smcf_ObjMap_in_Vset 
    tm_smcf_ArrMap_in_Vset
    HomDom.tiny_smc_in_Vset 
    HomCod.tiny_smc_in_Vset 
  show ?thesis
    by (subst smcf_def) 
      (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros V_cs_intros)
qed

lemma small_all_tiny_smcfs[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show 
    "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> 
      elts (set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_smcfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<FF> assume "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<AA> \<BB> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    then interpret is_tiny_semifunctor \<alpha> \<AA> \<BB> \<FF> by simp
    show "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" using is_semifunctor_axioms by auto
  qed
qed

lemma tiny_smcfs_vsubset_Vset[simp]: 
  "set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(rule vsubsetI)
  fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> all_tiny_smcfs \<alpha>"
  then obtain \<AA> \<BB> where \<FF>: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
  then show "\<FF> \<in>\<^sub>\<circ> Vset \<alpha>" by (auto simp: is_tiny_semifunctor.tiny_smcf_in_Vset)
qed

lemma (in is_semifunctor) smcf_is_tiny_semifunctor_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>"
proof(intro is_tiny_semifunctorI)
  show "smcf_dghm \<FF> : smc_dg \<AA> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> smc_dg \<BB>"
    by 
      (
        rule is_dghm.dghm_is_tiny_dghm_if_ge_Limit, 
        rule smcf_is_dghm; 
        intro assms
      )
qed (simp add: smcf_is_semifunctor_if_ge_Limit assms)


subsubsection\<open>Opposite tiny semifunctor\<close>

lemma (in is_tiny_semifunctor) is_tiny_semifunctor_op: 
  "op_smcf \<FF> : op_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> op_smc \<BB>"
  by (intro is_tiny_semifunctorI') 
    (cs_concl cs_intro: smc_small_cs_intros smc_op_intros)+

lemma (in is_tiny_semifunctor) is_tiny_semifunctor_op'[smc_op_intros]:  
  assumes "\<AA>' = op_smc \<AA>" and "\<BB>' = op_smc \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tiny_semifunctor_op)

lemmas is_tiny_semifunctor_op[smc_op_intros] = 
  is_tiny_semifunctor.is_tiny_semifunctor_op'


subsubsection\<open>Composition of tiny semifunctors\<close>

lemma smcf_comp_is_tiny_semifunctor[smc_small_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>S\<^sub>M\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<FF>: is_tiny_semifunctor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tiny_semifunctor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  show ?thesis 
    by (rule is_tiny_semifunctorI') 
      (cs_concl cs_intro: smc_cs_intros smc_small_cs_intros)
qed


subsubsection\<open>Tiny constant semifunctor\<close>

lemma smcf_const_is_tiny_semifunctor:
  assumes "tiny_semicategory \<alpha> \<CC>" 
    and "tiny_semicategory \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f = f"
  shows "smcf_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<DD>"
proof(intro is_tiny_semifunctorI')
  from assms show "smcf_const \<CC> \<DD> a f : \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_small_cs_intros)
qed (auto simp: assms(1,2))

lemma smcf_const_is_tiny_semifunctor'[smc_small_cs_intros]:
  assumes "tiny_semicategory \<alpha> \<CC>"
    and "tiny_semicategory \<alpha> \<DD>" 
    and "f : a \<mapsto>\<^bsub>\<DD>\<^esub> a"
    and "f \<circ>\<^sub>A\<^bsub>\<DD>\<^esub> f = f"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "smcf_const \<CC> \<DD> a f : \<CC>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<DD>'"
  using assms(1-4) unfolding assms(5,6) by (rule smcf_const_is_tiny_semifunctor)

text\<open>\newpage\<close>

end