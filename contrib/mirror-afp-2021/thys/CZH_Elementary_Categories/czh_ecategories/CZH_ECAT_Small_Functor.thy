(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for functors\<close>
theory CZH_ECAT_Small_Functor
  imports 
    CZH_Foundations.CZH_SMC_Small_Semifunctor
    CZH_ECAT_Functor
    CZH_ECAT_Small_Category
begin



subsection\<open>Functor with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tm_functor = is_functor \<alpha> \<AA> \<BB> \<FF>  for \<alpha> \<AA> \<BB> \<FF> +
  assumes tm_cf_is_semifunctor[slicing_intros]: 
    "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> cat_smc \<BB>" 

syntax "_is_tm_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_tm_functor \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_tm_functor :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_tm_functor \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_dg \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_tm_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  (\<open>(_ :/ _ \<^sub>C\<^sub>.\<^sub>t\<^sub>m\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>C\<^sub>.\<^sub>t\<^sub>m\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_tm_functor \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_tm_cfs :: "V \<Rightarrow> V"
  where "all_tm_cfs \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation small_tm_cfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "small_tm_cfs \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma (in is_tm_functor) tm_cf_is_semifunctor':
  assumes "\<alpha>' = \<alpha>"
    and "\<AA>' = cat_smc \<AA>"
    and "\<BB>' = cat_smc \<BB>"
  shows "cf_smcf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule tm_cf_is_semifunctor)

lemmas [slicing_intros] = is_tm_functor.tm_cf_is_semifunctor'


text\<open>Rules.\<close>

lemma (in is_tm_functor) is_tm_functor_axioms'[cat_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_functor_axioms)

mk_ide rf is_tm_functor_def[unfolded is_tm_functor_axioms_def]
  |intro is_tm_functorI|
  |dest is_tm_functorD[dest]|
  |elim is_tm_functorE[elim]|

lemmas [cat_small_cs_intros] = is_tm_functorD(1)


text\<open>Slicing.\<close>

context is_tm_functor
begin

interpretation smcf: is_tm_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
  by (rule tm_cf_is_semifunctor)

lemmas_with [unfolded slicing_simps]:
  tm_cf_ObjMap_in_Vset[cat_cs_intros] = smcf.tm_smcf_ObjMap_in_Vset
  and tm_cf_ArrMap_in_Vset[cat_cs_intros] = smcf.tm_smcf_ArrMap_in_Vset

end

sublocale is_tm_functor \<subseteq> HomDom: tiny_category \<alpha> \<AA>
proof(rule tiny_categoryI')
  show "\<AA>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule vdomain_in_VsetI[OF tm_cf_ObjMap_in_Vset, unfolded cat_cs_simps])
  show "\<AA>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule vdomain_in_VsetI[OF tm_cf_ArrMap_in_Vset, unfolded cat_cs_simps])
qed (simp add: cat_cs_intros)


text\<open>Further rules.\<close>

lemma is_tm_functorI':
  assumes [simp]: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and [simp]: "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and [simp]: "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_tm_functorI)
  interpret is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  show "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
    by (intro is_tm_semifunctorI', unfold slicing_simps) 
      (auto simp: slicing_intros)
qed simp_all

lemma is_tm_functorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  interpret is_tm_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))    
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (auto intro: cat_cs_intros)
qed

lemmas [cat_small_cs_intros] = is_tm_functorD'(1)

lemma is_tm_functorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  using is_tm_functorD'[OF assms] by simp


text\<open>Size.\<close>

lemma small_all_tm_cfs[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show 
    "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
      elts (set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_cfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<FF> assume "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<AA> \<BB> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    then interpret is_tm_functor \<alpha> \<AA> \<BB> \<FF> .
    show "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (blast intro: is_functor_axioms')
  qed
qed


subsubsection\<open>Opposite functor with tiny maps\<close>

lemma (in is_tm_functor) is_tm_functor_op: 
  "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
  by (intro is_tm_functorI', unfold cat_op_simps)
    (cs_concl cs_intro: cat_cs_intros cat_op_intros)

lemma (in is_tm_functor) is_tm_functor_op'[cat_op_intros]:  
  assumes "\<AA>' = op_cat \<AA>" and "\<BB>' = op_cat \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_cf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_functor_op)

lemmas is_tm_functor_op[cat_op_intros] = is_tm_functor.is_tm_functor_op'


subsubsection\<open>Composition of functors with tiny maps\<close>

lemma cf_comp_is_tm_functor[cat_small_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof(rule is_tm_functorI)
  interpret \<FF>: is_tm_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tm_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  from \<FF>.tm_cf_is_semifunctor \<GG>.tm_cf_is_semifunctor show 
    "cf_smcf (\<GG> \<circ>\<^sub>C\<^sub>F \<FF>) : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> cat_smc \<CC>"   
    by (auto simp: smc_small_cs_intros slicing_commute[symmetric])
  show "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" by (auto intro: cat_cs_intros)
qed


subsubsection\<open>Finite categories and functors with tiny maps\<close>

lemma (in is_functor) cf_is_tm_functor_if_HomDom_finite_category:
  assumes "finite_category \<alpha> \<AA>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_tm_functorI)
  interpret \<AA>: finite_category \<alpha> \<AA> by (rule assms(1))
  show "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
    by 
      (
        rule 
          is_semifunctor.smcf_is_tm_semifunctor_if_HomDom_finite_semicategory[
            OF cf_is_semifunctor \<AA>.fin_cat_finite_semicategory
            ]
      )
qed (auto intro: cat_cs_intros)


subsubsection\<open>Constant functor with tiny maps\<close>

lemma cf_const_is_tm_functor: 
  assumes "tiny_category \<alpha> \<CC>" and "category \<alpha> \<DD>" and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  shows "cf_const \<CC> \<DD> a : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<DD>"
proof(intro is_tm_functorI)
  from assms show "cf_smcf (cf_const \<CC> \<DD> a) : cat_smc \<CC> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> cat_smc \<DD>"
    by 
      (
        cs_concl 
          cs_simp: slicing_commute[symmetric] slicing_simps cat_cs_simps 
          cs_intro: slicing_intros cat_cs_intros smc_small_cs_intros
      )+
  from assms show "cf_const \<CC> \<DD> a : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_intro: cat_cs_intros cat_small_cs_intros)
qed

lemma cf_const_is_tm_functor'[cat_small_cs_intros]:
  assumes "tiny_category \<alpha> \<CC>"
    and "category \<alpha> \<DD>" 
    and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "cf_const \<CC> \<DD> a : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<DD>'"
  using assms(1-3) unfolding assms(4,5) by (rule cf_const_is_tm_functor)



subsection\<open>Tiny functor\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tiny_functor = is_functor \<alpha> \<AA> \<BB> \<FF> for \<alpha> \<AA> \<BB> \<FF> +
  assumes tiny_cf_is_tiny_semifunctor[slicing_intros]: 
    "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> cat_smc \<BB>" 

syntax "_is_tiny_functor" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> "CONST is_tiny_functor \<alpha> \<AA> \<BB> \<FF>"

abbreviation (input) is_cn_tiny_cf :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_cn_tiny_cf \<alpha> \<AA> \<BB> \<FF> \<equiv> \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"

syntax "_is_cn_tiny_cf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<mapsto>\<mapsto>\<index> _)\<close> [51, 51, 51] 51)
translations "\<FF> : \<AA> \<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> \<BB>" \<rightharpoonup> "CONST is_cn_cf \<alpha> \<AA> \<BB> \<FF>"

abbreviation all_tiny_cfs :: "V \<Rightarrow> V"
  where "all_tiny_cfs \<alpha> \<equiv> set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tiny_cfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tiny_cfs \<alpha> \<AA> \<BB> \<equiv> set {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

lemmas [slicing_intros] = is_tiny_functor.tiny_cf_is_tiny_semifunctor


text\<open>Rules.\<close>

lemma (in is_tiny_functor) is_tiny_functor_axioms'[cat_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>"
  shows "\<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tiny_functor_axioms)

mk_ide rf is_tiny_functor_def[unfolded is_tiny_functor_axioms_def]
  |intro is_tiny_functorI|
  |dest is_tiny_functorD[dest]|
  |elim is_tiny_functorE[elim]|

lemmas [cat_small_cs_intros] = is_tiny_functorD(1)


text\<open>Elementary properties.\<close>

sublocale is_tiny_functor \<subseteq> HomDom: tiny_category \<alpha> \<AA>
proof(intro tiny_categoryI')
  interpret smcf: is_tiny_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
    by (rule tiny_cf_is_tiny_semifunctor)
  show "\<AA>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule smcf.HomDom.tiny_smc_Obj_in_Vset[unfolded slicing_simps])    
  show "\<AA>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule smcf.HomDom.tiny_smc_Arr_in_Vset[unfolded slicing_simps])    
qed (auto simp: cat_cs_intros)

sublocale is_tiny_functor \<subseteq> HomCod: tiny_category \<alpha> \<BB>
proof(intro tiny_categoryI')
  interpret smcf: is_tiny_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
    by (rule tiny_cf_is_tiny_semifunctor)
  show "\<BB>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule smcf.HomCod.tiny_smc_Obj_in_Vset[unfolded slicing_simps])    
  show "\<BB>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule smcf.HomCod.tiny_smc_Arr_in_Vset[unfolded slicing_simps])    
qed (auto simp: cat_cs_intros)

sublocale is_tiny_functor \<subseteq> is_tm_functor
proof(intro is_tm_functorI')
  interpret smcf: is_tiny_semifunctor \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close>
    by (rule tiny_cf_is_tiny_semifunctor)
  note Vset[unfolded slicing_simps] = 
    smcf.tm_smcf_ObjMap_in_Vset
    smcf.tm_smcf_ArrMap_in_Vset
  show "\<FF>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" "\<FF>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (intro Vset)+
qed (auto simp: cat_cs_intros)


text\<open>Further rules.\<close>

lemma is_tiny_functorI':
  assumes [simp]: "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "tiny_category \<alpha> \<AA>"
    and "tiny_category \<alpha> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_tiny_functorI)
  interpret \<FF>: is_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  interpret \<AA>: tiny_category \<alpha> \<AA> by (rule assms(2))
  interpret \<BB>: tiny_category \<alpha> \<BB> by (rule assms(3))
  show "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
    by (intro is_tiny_semifunctorI') (auto intro: slicing_intros)
qed (rule assms(1))

lemma is_tiny_functorD':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "tiny_category \<alpha> \<AA>"
    and "tiny_category \<alpha> \<BB>"
proof-
  interpret is_tiny_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(1))
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "tiny_category \<alpha> \<AA>" and "tiny_category \<alpha> \<BB>"
    by (auto intro: cat_small_cs_intros)
qed

lemmas [cat_small_cs_intros] = is_tiny_functorD'(2,3)

lemma is_tiny_functorE':
  assumes "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" 
    and "tiny_category \<alpha> \<AA>"
    and "tiny_category \<alpha> \<BB>"
  using is_tiny_functorD'[OF assms] by auto

lemma is_tiny_functor_iff:
  "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<longleftrightarrow> 
    (\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<and> tiny_category \<alpha> \<AA> \<and> tiny_category \<alpha> \<BB>)"
  by (auto intro: is_tiny_functorI' dest: is_tiny_functorD'(2,3))


text\<open>Size.\<close>

lemma (in is_tiny_functor) tiny_cf_in_Vset: "\<FF> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [cat_cs_intros] = 
    tm_cf_ObjMap_in_Vset 
    tm_cf_ArrMap_in_Vset
    HomDom.tiny_cat_in_Vset 
    HomCod.tiny_cat_in_Vset 
  show ?thesis
    by (subst cf_def) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros V_cs_intros)
qed

lemma small_all_tiny_cfs[simp]: "small {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show 
    "{\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> 
      elts (set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_cfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<FF> assume "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<AA> \<BB> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
    then interpret is_tiny_functor \<alpha> \<AA> \<BB> \<FF> by simp
    show "\<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (meson is_functor_axioms)
  qed
qed

lemma small_tiny_cfs[simp]: "small {\<FF>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) auto

lemma all_tiny_cfs_vsubset_Vset[simp]: 
  "set {\<FF>. \<exists>\<AA> \<BB>. \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(rule vsubsetI) 
  fix \<FF> assume "\<FF> \<in>\<^sub>\<circ> all_tiny_cfs \<alpha>"
  then obtain \<AA> \<BB> where "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by clarsimp
  then show "\<FF> \<in>\<^sub>\<circ> Vset \<alpha>" by (auto simp: is_tiny_functor.tiny_cf_in_Vset)
qed

lemma (in is_functor) cf_is_tiny_functor_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>"
proof(intro is_tiny_functorI)
  show "cf_smcf \<FF> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_smc \<BB>"
    by 
      (
        rule is_semifunctor.smcf_is_tiny_semifunctor_if_ge_Limit, 
        rule cf_is_semifunctor; 
        intro assms
      )
qed (simp add: cf_is_functor_if_ge_Limit assms)


subsubsection\<open>Opposite tiny semifunctor\<close>

lemma (in is_tiny_functor) is_tiny_functor_op: 
  "op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
  by (intro is_tiny_functorI') 
    (cs_concl cs_intro: cat_op_intros cat_small_cs_intros)+

lemma (in is_tiny_functor) is_tiny_functor_op'[cat_op_intros]:  
  assumes "\<AA>' = op_cat \<AA>" and "\<BB>' = op_cat \<BB>" and "\<alpha>' = \<alpha>"
  shows "op_cf \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule is_tiny_functor_op)

lemmas is_tiny_functor_op[cat_op_intros] = 
  is_tiny_functor.is_tiny_functor_op'


subsubsection\<open>Composition of tiny functors\<close>

lemma cf_comp_is_tiny_functor[cat_small_cs_intros]:
  assumes "\<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<CC>" and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<GG> \<circ>\<^sub>C\<^sub>F \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<FF>: is_tiny_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tiny_functor \<alpha> \<BB> \<CC> \<GG> by (rule assms(1))
  show ?thesis by (rule is_tiny_functorI') (auto intro: cat_small_cs_intros)
qed


subsubsection\<open>Tiny constant functor\<close>

lemma cf_const_is_tiny_functor:
  assumes "tiny_category \<alpha> \<CC>" and "tiny_category \<alpha> \<DD>" and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
  shows "cf_const \<CC> \<DD> a : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<DD>"
proof(intro is_tiny_functorI')
  from assms show "cf_const \<CC> \<DD> a : \<CC> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<DD>"
    by (cs_concl cs_intro: cat_small_cs_intros)
qed (auto simp: assms(1,2))

lemma cf_const_is_tiny_functor':
  assumes "tiny_category \<alpha> \<CC>"
    and "tiny_category \<alpha> \<DD>" 
    and "a \<in>\<^sub>\<circ> \<DD>\<lparr>Obj\<rparr>"
    and "\<CC>' = \<CC>"
    and "\<DD>' = \<DD>"
  shows "cf_const \<CC> \<DD> a : \<CC>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<DD>'"
  using assms(1-3) unfolding assms(4,5) by (rule cf_const_is_tiny_functor)

lemmas [cat_small_cs_intros] = cf_const_is_tiny_functor'

text\<open>\newpage\<close>

end