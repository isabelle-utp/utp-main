(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for natural transformations\<close>
theory CZH_ECAT_Small_NTCF
  imports 
    CZH_Foundations.CZH_SMC_Small_NTSMCF
    CZH_ECAT_Small_Functor
    CZH_ECAT_NTCF
begin



subsection\<open>Natural transformation of functors with tiny maps\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tm_ntcf = is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> +
  assumes tm_ntcf_is_tm_ntsmcf: "ntcf_ntsmcf \<NN> :
    cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m cf_smcf \<GG> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"

syntax "_is_tm_ntcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_tm_ntcfs :: "V \<Rightarrow> V"
  where "all_tm_ntcfs \<alpha> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tm_ntcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tm_ntcfs \<alpha> \<AA> \<BB> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_tm_ntcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_tm_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv>
    set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma (in is_tm_ntcf) tm_ntcf_is_tm_ntsmcf':
  assumes "\<FF>' = cf_smcf \<FF>"
    and "\<GG>' = cf_smcf \<GG>"
    and "\<AA>' = cat_smc \<AA>"
    and "\<BB>' = cat_smc \<BB>"
  shows "ntcf_ntsmcf \<NN> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule tm_ntcf_is_tm_ntsmcf)

lemmas [slicing_intros] = is_tm_ntcf.tm_ntcf_is_tm_ntsmcf'


text\<open>Rules.\<close>

lemma (in is_tm_ntcf) is_tm_ntcf_axioms'[cat_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_ntcf_axioms)

mk_ide rf is_tm_ntcf_def[unfolded is_tm_ntcf_axioms_def]
  |intro is_tm_ntcfI|
  |dest is_tm_ntcfD[dest]|
  |elim is_tm_ntcfE[elim]|

lemmas [cat_small_cs_intros] = is_tm_ntcfD(1)

context is_tm_ntcf
begin

interpretation ntsmcf: is_tm_ntsmcf
  \<alpha> \<open>cat_smc \<AA>\<close> \<open>cat_smc \<BB>\<close> \<open>cf_smcf \<FF>\<close> \<open>cf_smcf \<GG>\<close> \<open>ntcf_ntsmcf \<NN>\<close>
  by (rule tm_ntcf_is_tm_ntsmcf)

lemmas_with [unfolded slicing_simps]:
  tm_ntcf_NTMap_in_Vset = ntsmcf.tm_ntsmcf_NTMap_in_Vset

end

sublocale is_tm_ntcf \<subseteq> NTDom: is_tm_functor \<alpha> \<AA> \<BB> \<FF>
  using tm_ntcf_is_tm_ntsmcf 
  by (intro is_tm_functorI) (auto intro: cat_cs_intros is_tm_ntsmcfD')

sublocale is_tm_ntcf \<subseteq> NTCod: is_tm_functor \<alpha> \<AA> \<BB> \<GG>
  using tm_ntcf_is_tm_ntsmcf 
  by (intro is_tm_functorI) (auto intro: cat_cs_intros is_tm_ntsmcfD')


text\<open>Further rules.\<close>

lemma is_tm_ntcfI':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<FF>: is_tm_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tm_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(3))
  show ?thesis
  proof(intro is_tm_ntcfI)
    show "ntcf_ntsmcf \<NN> : 
      cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m cf_smcf \<GG> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"
      by (intro is_tm_ntsmcfI') (auto intro: slicing_intros)
  qed (auto intro: cat_cs_intros)
qed

lemma is_tm_ntcfD':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by (auto simp: cat_small_cs_intros)
qed

lemmas [cat_small_cs_intros] = is_tm_ntcfD'(2,3)

lemma is_tm_ntcfE':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  using is_tm_ntcfD'[OF assms] by auto


text\<open>The set of all natural transformations with tiny maps is small.\<close>

lemma small_all_tm_ntcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show 
    "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>
      elts (set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_ntcfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<NN> assume "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<FF> \<GG> \<AA> \<BB> where "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    then interpret is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by simp
    have "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (auto simp: cat_cs_intros)
    then show "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  qed
qed

lemma small_tm_ntcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}\<close>])
    auto

lemma small_these_tm_ntcfs[simp]: 
  "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}"
  by (rule down[of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>}\<close>]) 
    auto


text\<open>Further elementary results.\<close>

lemma these_tm_ntcfs_iff: (*not simp*)
  "\<NN> \<in>\<^sub>\<circ> these_tm_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow> \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto


subsubsection\<open>Opposite natural transformation of functors with tiny maps\<close>

lemma (in is_tm_ntcf) is_tm_ntcf_op: "op_ntcf \<NN> :
  op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
  by (intro is_tm_ntcfI')
    (cs_concl cs_intro: cat_cs_intros cat_op_intros)+

lemma (in is_tm_ntcf) is_tm_ntcf_op'[cat_op_intros]: 
  assumes "\<GG>' = op_cf \<GG>"
    and "\<FF>' = op_cf \<FF>"
    and "\<AA>' = op_cat \<AA>"
    and "\<BB>' = op_cat \<BB>"
  shows "op_ntcf \<NN> : \<GG>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_ntcf_op)

lemmas is_tm_ntcf_op[cat_op_intros] = is_tm_ntcf.is_tm_ntcf_op'


subsubsection\<open>
Vertical composition of natural transformations of 
functors with tiny maps
\<close>

lemma ntcf_vcomp_is_tm_ntcf[cat_small_cs_intros]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<MM>: is_tm_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis 
    by (rule is_tm_ntcfI') (auto intro: cat_cs_intros cat_small_cs_intros) 
qed


subsubsection\<open>Identity natural transformation of a functor with tiny maps\<close>

lemma (in is_tm_functor) tm_cf_ntcf_id_is_tm_ntcf:
  "ntcf_id \<FF> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  by (intro is_tm_ntcfI') (auto intro: cat_cs_intros cat_small_cs_intros)

lemma (in is_tm_functor) tm_cf_ntcf_id_is_tm_ntcf':
  assumes "\<FF>' = \<FF>" and "\<GG>' = \<FF>"
  shows "ntcf_id \<FF> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>': \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms(1,2) by (rule tm_cf_ntcf_id_is_tm_ntcf)

lemmas [cat_small_cs_intros] = is_tm_functor.tm_cf_ntcf_id_is_tm_ntcf'


subsubsection\<open>Constant natural transformation of functors with tiny maps\<close>

lemma ntcf_const_is_tm_ntcf:
  assumes "tiny_category \<alpha> \<JJ>" and "category \<alpha> \<CC>" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "ntcf_const \<JJ> \<CC> f : 
    cf_const \<JJ> \<CC> a \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m cf_const \<JJ> \<CC> b : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    (is \<open>?Cf : ?Ca \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m ?Cb : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>\<close>)
proof(intro is_tm_ntcfI')
  interpret \<JJ>: tiny_category \<alpha> \<JJ> by (rule assms(1))
  interpret \<CC>: category \<alpha> \<CC> by (rule assms(2))
  from assms show 
    "?Cf : ?Ca \<mapsto>\<^sub>C\<^sub>F ?Cb : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    "cf_const \<JJ> \<CC> a : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    "cf_const \<JJ> \<CC> b : \<JJ> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    by (cs_concl cs_intro: cat_small_cs_intros cat_cs_intros)+
qed

lemma ntcf_const_is_tm_ntcf'[cat_small_cs_intros]:
  assumes "tiny_category \<alpha> \<JJ>" 
    and "category \<alpha> \<CC>"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<AA> = cf_const \<JJ> \<CC> a"
    and "\<BB> = cf_const \<JJ> \<CC> b"
    and "\<JJ>' = \<JJ>"
    and "\<CC>' = \<CC>"
  shows "ntcf_const \<JJ> \<CC> f : \<AA> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<BB> : \<JJ>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>'"
  using assms(1-3) unfolding assms(4-7) by (rule ntcf_const_is_tm_ntcf)


subsubsection\<open>Natural isomorphisms of functors with tiny maps\<close>

locale is_tm_iso_ntcf = is_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> + is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> 
  for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>

syntax "_is_tm_iso_ntcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ : _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o _ : _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tm_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"


text\<open>Rules.\<close>

mk_ide rf is_tm_iso_ntcf_def
  |intro is_tm_iso_ntcfI|
  |dest is_tm_iso_ntcfD[dest]|
  |elim is_tm_iso_ntcfE[elim]|

lemmas [ntcf_cs_intros] = is_tm_iso_ntcfD

lemma iso_tm_ntcf_is_arr_isomorphism:
  assumes "category \<alpha> \<BB>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows [ntcf_cs_intros]: "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> = ntcf_id \<GG>"
    and "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>"
proof-
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(1))
  interpret \<NN>: is_tm_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms)
  note inv_\<NN> = iso_ntcf_is_arr_isomorphism[OF \<NN>.is_iso_ntcf_axioms]
  show "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  proof(intro is_tm_iso_ntcfI)
    show "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (intro inv_\<NN>(1))
    interpret inv_\<NN>: is_iso_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<open>inv_ntcf \<NN>\<close> by (rule inv_\<NN>(1))
    show "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
      by (intro is_tm_ntcfI') (auto intro: cat_cs_intros cat_small_cs_intros)
  qed
  show "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> = ntcf_id \<GG>" "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>" 
    by (intro inv_\<NN>(2,3))+
qed

lemma is_arr_isomorphism_is_tm_iso_ntcf:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and [simp]: "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> = ntcf_id \<GG>"
    and [simp]: "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<MM>: is_tm_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<MM> by (rule assms(2))
  show ?thesis
  proof(rule is_tm_iso_ntcfI)
    show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (rule is_arr_isomorphism_is_iso_ntcf) (auto intro: cat_small_cs_intros)
    show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
      by (rule is_tm_ntcfI')
        (auto simp: \<NN>.tm_ntcf_NTMap_in_Vset intro: cat_small_cs_intros)
  qed
qed


subsubsection\<open>
Composition of a natural transformation 
of functors with tiny maps and a functor with tiny maps
\<close>

lemma ntcf_cf_comp_is_tm_ntcf:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH> : \<FF> \<circ>\<^sub>C\<^sub>F \<HH> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> \<circ>\<^sub>C\<^sub>F \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<NN>: is_tm_ntcf \<alpha> \<BB> \<CC> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<HH>: is_tm_functor \<alpha> \<AA> \<BB> \<HH> by (rule assms(2))
  from assms show ?thesis
    by (intro is_tm_ntcfI)
      (
        cs_concl 
          cs_simp: slicing_commute[symmetric] 
          cs_intro: cat_cs_intros smc_small_cs_intros slicing_intros
      )+
qed

lemma ntcf_cf_comp_is_tm_ntcf'[cat_small_cs_intros]:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<FF> \<circ>\<^sub>C\<^sub>F \<HH>"
    and "\<GG>' = \<GG> \<circ>\<^sub>C\<^sub>F \<HH>"
  shows "\<NN> \<circ>\<^sub>N\<^sub>T\<^sub>C\<^sub>F\<^sub>-\<^sub>C\<^sub>F \<HH> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule ntcf_cf_comp_is_tm_ntcf)


subsubsection\<open>
Composition of a functor with tiny maps 
and a natural transformation of functors with tiny maps
\<close>

lemma cf_ntcf_comp_is_tm_ntcf:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<HH> \<circ>\<^sub>C\<^sub>F \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<HH> \<circ>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<HH>: is_tm_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(1))
  interpret \<NN>: is_tm_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  from assms show ?thesis
    by (intro is_tm_ntcfI)
      (
        cs_concl 
          cs_simp: slicing_commute[symmetric] 
          cs_intro: cat_cs_intros smc_small_cs_intros slicing_intros
      )+
qed

lemma cf_ntcf_comp_is_tm_ntcf'[cat_small_cs_intros]:
  assumes "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF>' = \<HH> \<circ>\<^sub>C\<^sub>F \<FF>"
    and "\<GG>' = \<HH> \<circ>\<^sub>C\<^sub>F \<GG>"
  shows "\<HH> \<circ>\<^sub>C\<^sub>F\<^sub>-\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>m \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  using assms(1,2) unfolding assms(3,4) by (rule cf_ntcf_comp_is_tm_ntcf)



subsection\<open>Tiny natural transformation of functors\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tiny_ntcf = is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> +
  assumes tiny_ntcf_is_tiny_ntsmcf: 
    "ntcf_ntsmcf \<NN> :
      cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y cf_smcf \<GG> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> cat_smc \<BB>"

syntax "_is_tiny_ntcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ :/ _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y _ :/ _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons> 
  "CONST is_tiny_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"

abbreviation all_tiny_ntcfs :: "V \<Rightarrow> V"
  where "all_tiny_ntcfs \<alpha> \<equiv>
    set {\<NN>. \<exists>\<AA> \<BB> \<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation tiny_ntcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "tiny_ntcfs \<alpha> \<AA> \<BB> \<equiv>
    set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

abbreviation these_tiny_ntcfs :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "these_tiny_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<equiv>
    set {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"

lemma (in is_tiny_ntcf) tiny_ntcf_is_tiny_ntsmcf':
  assumes "\<alpha>' = \<alpha>"
    and "\<FF>' = cf_smcf \<FF>"
    and "\<GG>' = cf_smcf \<GG>"
    and "\<AA>' = cat_smc \<AA>"
    and "\<BB>' = cat_smc \<BB>"
  shows "ntcf_ntsmcf \<NN> : \<FF>' \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule tiny_ntcf_is_tiny_ntsmcf)

lemmas [slicing_intros] = is_tiny_ntcf.tiny_ntcf_is_tiny_ntsmcf'


text\<open>Rules.\<close>

lemma (in is_tiny_ntcf) is_tiny_ntcf_axioms'[cat_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<AA>' = \<AA>" and "\<BB>' = \<BB>" and "\<FF>' = \<FF>" and "\<GG>' = \<GG>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule is_tiny_ntcf_axioms)

mk_ide rf is_tiny_ntcf_def[unfolded is_tiny_ntcf_axioms_def]
  |intro is_tiny_ntcfI|
  |dest is_tiny_ntcfD[dest]|
  |elim is_tiny_ntcfE[elim]|


text\<open>Elementary properties.\<close>

sublocale is_tiny_ntcf \<subseteq> NTDom: is_tiny_functor \<alpha> \<AA> \<BB> \<FF> 
  using tiny_ntcf_is_tiny_ntsmcf 
  by (intro is_tiny_functorI) 
    (auto intro: cat_cs_intros simp: is_tiny_ntsmcf_iff)

sublocale is_tiny_ntcf \<subseteq> NTCod: is_tiny_functor \<alpha> \<AA> \<BB> \<GG>
  using tiny_ntcf_is_tiny_ntsmcf 
  by (intro is_tiny_functorI) 
    (auto intro: cat_cs_intros simp: is_tiny_ntsmcf_iff)

sublocale is_tiny_ntcf \<subseteq> is_tm_ntcf 
  by (rule is_tm_ntcfI') (auto intro: cat_cs_intros cat_small_cs_intros)

lemmas (in is_tiny_ntcf) tiny_ntcf_is_tm_ntcf[cat_small_cs_intros] = 
  is_tm_ntcf_axioms

lemmas [cat_small_cs_intros] = is_tiny_ntcf.tiny_ntcf_is_tm_ntcf


text\<open>Further rules.\<close>

lemma is_tiny_ntcfI':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<FF>: is_tiny_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tiny_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(3))
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    by (intro is_tiny_ntcfI is_tiny_ntsmcfI') 
      (auto intro: cat_cs_intros slicing_intros)
qed

lemma is_tiny_ntcfD':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_tiny_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    by (auto intro: cat_small_cs_intros)
qed

lemmas [cat_small_cs_intros] = is_tiny_ntcfD'(2,3)

lemma is_tiny_ntcfE':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto dest: is_tiny_ntcfD'(2,3))

lemma is_tiny_ntcf_iff:
  "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<longleftrightarrow> 
    (
      \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<and> 
      \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<and> 
      \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>
    )"
   by (auto intro: is_tiny_ntcfI' dest: is_tiny_ntcfD'(2,3))

lemma (in is_tiny_ntcf) tiny_ntcf_in_Vset: "\<NN> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [cat_cs_intros] =
    tm_ntcf_NTMap_in_Vset
    NTDom.tiny_cf_in_Vset
    NTCod.tiny_cf_in_Vset
    NTDom.HomDom.tiny_cat_in_Vset
    NTDom.HomCod.tiny_cat_in_Vset
  show ?thesis
    by (subst ntcf_def) 
      (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros V_cs_intros)
qed

lemma small_all_tiny_ntcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
proof(rule down)
  show "{\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq> 
    elts (set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>})"
  proof
    (
      simp only: elts_of_set small_all_ntcfs if_True, 
      rule subsetI, 
      unfold mem_Collect_eq
    )
    fix \<NN> assume "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    then obtain \<FF> \<GG> \<AA> \<BB> where "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
      by clarsimp
    then interpret is_tiny_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> .
    have "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (auto intro: cat_cs_intros)
    then show "\<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by auto
  qed
qed

lemma small_tiny_ntcfs[simp]: 
  "small {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    )
    auto

lemma small_these_tiny_ntcfs[simp]: 
  "small {\<NN>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}"
  by 
    (
      rule 
        down[
          of _ \<open>set {\<NN>. \<exists>\<FF> \<GG> \<AA> \<BB>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>}\<close>
          ]
    ) 
    auto

lemma tiny_ntcfs_vsubset_Vset[simp]: 
  "set {\<NN>. \<exists>\<FF> \<GG>. \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>} \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  (is \<open>set ?ntcfs \<subseteq>\<^sub>\<circ> _\<close>)
proof(cases \<open>tiny_category \<alpha> \<AA> \<and> tiny_category \<alpha> \<BB>\<close>)
  case True
  then have "tiny_category \<alpha> \<AA>" and "tiny_category \<alpha> \<BB>" by auto
  show ?thesis 
  proof(rule vsubsetI)
    fix \<NN> assume "\<NN> \<in>\<^sub>\<circ> set ?ntcfs"
    then obtain \<FF> \<GG> where "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" by auto
    then interpret is_tiny_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by simp
    from tiny_ntcf_in_Vset show "\<NN> \<in>\<^sub>\<circ> Vset \<alpha>" by simp
  qed
next
  case False
  then have "set ?ntcfs = 0" 
    unfolding is_tiny_ntcf_iff is_tiny_functor_iff by auto
  then show ?thesis by simp
qed


text\<open>Further elementary results.\<close>

lemma these_tiny_ntcfs_iff: (*not simp*) 
  "\<NN> \<in>\<^sub>\<circ> these_tiny_ntcfs \<alpha> \<AA> \<BB> \<FF> \<GG> \<longleftrightarrow> \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  by auto


text\<open>Size.\<close>

lemma (in is_ntcf) ntcf_is_tiny_ntcf_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> \<BB>" 
proof(intro is_tiny_ntcfI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<beta>\<^esub> \<BB>"
    by (intro ntcf_is_ntcf_if_ge_Limit)
      (use assms(2) in \<open>cs_concl cs_intro: dg_cs_intros\<close>)+
  show "ntcf_ntsmcf \<NN> : 
    cf_smcf \<FF> \<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y cf_smcf \<GG> : cat_smc \<AA> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<beta>\<^esub> cat_smc \<BB>"
    by 
      ( 
        rule is_ntsmcf.ntsmcf_is_tiny_ntsmcf_if_ge_Limit, 
        rule ntcf_is_ntsmcf;
        intro assms
     )
qed


subsubsection\<open>Opposite natural transformation of tiny functors\<close>

lemma (in is_tiny_ntcf) is_tm_ntcf_op: "op_ntcf \<NN> :
  op_cf \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y op_cf \<FF> : op_cat \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> op_cat \<BB>"
  by (intro is_tiny_ntcfI')
   (cs_concl cs_intro: cat_cs_intros cat_op_intros)+

lemma (in is_tiny_ntcf) is_tiny_ntcf_op'[cat_op_intros]: 
  assumes "\<GG>' = op_cf \<GG>"
    and "\<FF>' = op_cf \<FF>"
    and "\<AA>' = op_cat \<AA>"
    and "\<BB>' = op_cat \<BB>"
  shows "op_ntcf \<NN> : \<GG>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<FF>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule is_tm_ntcf_op)

lemmas is_tiny_ntcf_op[cat_op_intros] = is_tiny_ntcf.is_tiny_ntcf_op'


subsubsection\<open>Vertical composition of tiny natural transformations\<close>

lemma ntsmcf_vcomp_is_tiny_ntsmcf[cat_small_cs_intros]:
  assumes "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<HH> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<MM>: is_tiny_ntcf \<alpha> \<AA> \<BB> \<GG> \<HH> \<MM> by (rule assms(1))
  interpret \<NN>: is_tiny_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(2))
  show ?thesis by (rule is_tiny_ntcfI') (auto intro: cat_small_cs_intros)
qed


subsubsection\<open>Tiny identity natural transformation\<close>

lemma (in is_tiny_functor) tiny_cf_ntcf_id_is_tiny_ntcf:
  "ntcf_id \<FF> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  by (intro is_tiny_ntcfI') (auto intro: cat_small_cs_intros)

lemma (in is_tiny_functor) tiny_cf_ntcf_id_is_tiny_ntcf'[cat_small_cs_intros]:
  assumes "\<FF>' = \<FF>" and "\<GG>' = \<FF>"
  shows "ntcf_id \<FF> : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG>' : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  unfolding assms by (rule tiny_cf_ntcf_id_is_tiny_ntcf)

lemmas [cat_small_cs_intros] = is_tiny_functor.tiny_cf_ntcf_id_is_tiny_ntcf'



subsection\<open>Tiny natural isomorphisms\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale is_tiny_iso_ntcf = is_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> + is_tiny_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> 
  for \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>

syntax "_is_tiny_iso_ntcf" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>(_ : _ \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o _ : _ \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<index> _)\<close> [51, 51, 51, 51, 51] 51)
translations "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>" \<rightleftharpoons>
  "CONST is_tiny_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN>"


text\<open>Rules.\<close>

mk_ide rf is_tiny_iso_ntcf_def
  |intro is_tiny_iso_ntcfI|
  |dest is_tiny_iso_ntcfD[dest]|
  |elim is_tiny_iso_ntcfE[elim]|

lemmas [ntcf_cs_intros] = is_tiny_iso_ntcfD(2)


text\<open>Elementary properties.\<close>

sublocale is_tiny_iso_ntcf \<subseteq> is_tm_iso_ntcf 
  by (rule is_tm_iso_ntcfI) (auto intro: cat_cs_intros cat_small_cs_intros)

lemmas (in is_tiny_iso_ntcf) is_tm_iso_ntcf_axioms' = is_tm_iso_ntcf_axioms

lemmas [ntcf_cs_intros] = is_tiny_iso_ntcf.is_tm_iso_ntcf_axioms'


text\<open>Further rules.\<close>

lemma is_tiny_iso_ntcfI':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<FF>: is_tiny_functor \<alpha> \<AA> \<BB> \<FF> by (rule assms(2))
  interpret \<GG>: is_tiny_functor \<alpha> \<AA> \<BB> \<GG> by (rule assms(3))
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    by (intro is_tiny_iso_ntcfI is_tiny_ntcfI') 
     (auto intro: cat_cs_intros cat_small_cs_intros)
qed

lemma is_tiny_iso_ntcfD':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_tiny_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    by (auto intro: cat_cs_intros cat_small_cs_intros)
qed

lemma is_tiny_iso_ntcfE':
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  obtains "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms by (auto dest: is_tiny_ntcfD'(2,3))

lemma is_tiny_iso_ntcf_iff:
  "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<longleftrightarrow> 
    (
      \<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB> \<and> 
      \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB> \<and> 
      \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>
    )"
  by (auto intro: is_tiny_iso_ntcfI' dest: is_tiny_ntcfD'(2,3))


subsubsection\<open>Further properties\<close>

lemma iso_tiny_ntcf_is_arr_isomorphism:
  assumes "category \<alpha> \<BB>" and "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  shows [ntcf_cs_intros]: "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> = ntcf_id \<GG>"
    and "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>"
proof-
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(1))
  interpret \<NN>: is_tiny_iso_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms)
  note inv_\<NN> = iso_ntcf_is_arr_isomorphism[OF \<NN>.is_iso_ntcf_axioms]
  show "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
  proof(intro is_tiny_iso_ntcfI)
    show "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (intro inv_\<NN>(1))
    interpret inv_\<NN>: is_iso_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<open>inv_ntcf \<NN>\<close> by (rule inv_\<NN>(1))
    show "inv_ntcf \<NN> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
      by (intro is_tiny_ntcfI') (auto intro: cat_small_cs_intros cat_cs_intros)
  qed
  show "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F inv_ntcf \<NN> = ntcf_id \<GG>" "inv_ntcf \<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>" 
    by (intro inv_\<NN>(2,3))+
qed

lemma is_arr_isomorphism_is_tiny_iso_ntcf:
  assumes "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and "\<MM> : \<GG> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
    and [simp]: "\<NN> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<MM> = ntcf_id \<GG>"
    and [simp]: "\<MM> \<bullet>\<^sub>N\<^sub>T\<^sub>C\<^sub>F \<NN> = ntcf_id \<FF>"
  shows "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<NN>: is_tiny_ntcf \<alpha> \<AA> \<BB> \<FF> \<GG> \<NN> by (rule assms(1))
  interpret \<MM>: is_tiny_ntcf \<alpha> \<AA> \<BB> \<GG> \<FF> \<MM> by (rule assms(2))
  show ?thesis
  proof(rule is_tiny_iso_ntcfI)
    show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
      by (rule is_arr_isomorphism_is_iso_ntcf) (auto intro: cat_small_cs_intros)
    show "\<NN> : \<FF> \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y \<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>i\<^sub>n\<^sub>y\<^bsub>\<alpha>\<^esub> \<BB>"
      by (rule is_tiny_ntcfI') (auto intro: cat_small_cs_intros)
  qed
qed

text\<open>\newpage\<close>

end