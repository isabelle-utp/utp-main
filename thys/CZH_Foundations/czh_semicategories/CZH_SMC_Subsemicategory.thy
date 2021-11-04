(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Subsemicategory\<close>
theory CZH_SMC_Subsemicategory
  imports 
    CZH_DG_Subdigraph
    CZH_SMC_Semifunctor
begin



subsection\<open>Background\<close>

named_theorems smc_sub_cs_intros
named_theorems smc_sub_bw_cs_intros
named_theorems smc_sub_fw_cs_intros
named_theorems smc_sub_bw_cs_simps



subsection\<open>Simple subsemicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale subsemicategory = 
  sdg: semicategory \<alpha> \<BB> + dg: semicategory \<alpha> \<CC> for \<alpha> \<BB> \<CC> + 
  assumes subsmc_subdigraph[slicing_intros]: "smc_dg \<BB> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>" 
    and subsmc_Comp[smc_sub_fw_cs_intros]: 
      "\<lbrakk> g : b \<mapsto>\<^bsub>\<BB>\<^esub> c; f : a \<mapsto>\<^bsub>\<BB>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"

abbreviation is_subsemicategory ("(_/ \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> subsemicategory \<alpha> \<BB> \<CC>"

lemmas [smc_sub_fw_cs_intros] = subsemicategory.subsmc_Comp


text\<open>Rules.\<close>

lemma (in subsemicategory) subsemicategory_axioms'[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<BB>' = \<BB>"
  shows "\<BB>' \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>"
  unfolding assms by (rule subsemicategory_axioms)

lemma (in subsemicategory) subsemicategory_axioms''[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule subsemicategory_axioms)

mk_ide rf subsemicategory_def[unfolded subsemicategory_axioms_def]
  |intro subsemicategoryI|
  |dest subsemicategoryD[dest]|
  |elim subsemicategoryE[elim!]|

lemmas [smc_sub_cs_intros] = subsemicategoryD(1,2)

lemma subsemicategoryI':
  assumes "semicategory \<alpha> \<BB>"
    and "semicategory \<alpha> \<CC>"
    and "\<And>a. a \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<BB>\<^esub> b \<Longrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<BB>\<^esub> c; f : a \<mapsto>\<^bsub>\<BB>\<^esub> b \<rbrakk> \<Longrightarrow>
      g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  shows "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<BB>: semicategory \<alpha> \<BB> by (rule assms(1))
  interpret \<CC>: semicategory \<alpha> \<CC> by (rule assms(2))  
  show ?thesis
    by 
      (
        intro subsemicategoryI subdigraphI, 
        unfold slicing_simps; 
        (intro \<BB>.smc_digraph \<CC>.smc_digraph assms)?
      )
qed


text\<open>Subsemicategory is a subdigraph.\<close>

context subsemicategory
begin

interpretation subdg: subdigraph \<alpha> \<open>smc_dg \<BB>\<close> \<open>smc_dg \<CC>\<close>
  by (rule subsmc_subdigraph)

lemmas_with [unfolded slicing_simps]:
  subsmc_Obj_vsubset = subdg.subdg_Obj_vsubset
  and subsmc_is_arr_vsubset = subdg.subdg_is_arr_vsubset
  and subsmc_subdigraph_op_dg_op_dg = subdg.subdg_subdigraph_op_dg_op_dg
  and subsmc_objD = subdg.subdg_objD
  and subsmc_arrD = subdg.subdg_arrD
  and subsmc_dom_simp = subdg.subdg_dom_simp
  and subsmc_cod_simp = subdg.subdg_cod_simp
  and subsmc_is_arrD = subdg.subdg_is_arrD
  and subsmc_dghm_inc_op_dg_is_dghm = subdg.subdg_dghm_inc_op_dg_is_dghm
  and subsmc_op_dg_dghm_inc = subdg.subdg_op_dg_dghm_inc
  and subsmc_inc_is_ft_dghm_axioms = subdg.inc.is_ft_dghm_axioms

end

lemmas subsmc_subdigraph_op_dg_op_dg[intro] = 
  subsemicategory.subsmc_subdigraph_op_dg_op_dg

lemmas [smc_sub_fw_cs_intros] = 
  subsemicategory.subsmc_Obj_vsubset
  subsemicategory.subsmc_is_arr_vsubset
  subsemicategory.subsmc_objD
  subsemicategory.subsmc_arrD
  subsemicategory.subsmc_is_arrD

lemmas [smc_sub_bw_cs_simps] =
  subsemicategory.subsmc_dom_simp
  subsemicategory.subsmc_cod_simp


text\<open>The opposite subsemicategory.\<close>

lemma (in subsemicategory) subsmc_subsemicategory_op_smc: 
  "op_smc \<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> op_smc \<CC>"
proof(rule subsemicategoryI)
  fix g b c f a assume prems: "g : b \<mapsto>\<^bsub>op_smc \<BB>\<^esub> c" "f : a \<mapsto>\<^bsub>op_smc \<BB>\<^esub> b"
  then have "g : c \<mapsto>\<^bsub>\<BB>\<^esub> b" and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> a" 
    by (simp_all add: smc_op_simps)
  with subsemicategory_axioms have g: "g : c \<mapsto>\<^bsub>\<CC>\<^esub> b" and f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
    by (cs_concl cs_intro: smc_sub_fw_cs_intros)+
  from dg.op_smc_Comp[OF this(2,1)] have "g \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g".
  with prems show "g \<circ>\<^sub>A\<^bsub>op_smc \<BB>\<^esub> f = g \<circ>\<^sub>A\<^bsub>op_smc \<CC>\<^esub> f"
    by (simp add: smc_op_simps subsmc_Comp)
qed 
  (
    auto 
      simp:
        smc_op_simps slicing_commute[symmetric] subsmc_subdigraph_op_dg_op_dg
      intro: smc_op_intros
  )

lemmas subsmc_subsemicategory_op_smc[intro, smc_op_intros] = 
  subsemicategory.subsmc_subsemicategory_op_smc


text\<open>Further rules.\<close>

lemma (in subsemicategory) subsmc_Comp_simp:
  assumes "g : b \<mapsto>\<^bsub>\<BB>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  using assms subsmc_Comp by auto

lemmas [smc_sub_bw_cs_simps] = subsemicategory.subsmc_Comp_simp

lemma (in subsemicategory) subsmc_is_idem_arrD: 
  assumes "f : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<BB>\<^esub> b" 
  shows "f : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<CC>\<^esub> b"
  using assms subsemicategory_axioms
  by (intro is_idem_arrI; elim is_idem_arrE)
    (cs_concl cs_simp: smc_sub_bw_cs_simps[symmetric] cs_intro: smc_sub_fw_cs_intros)

lemmas [smc_sub_fw_cs_intros] = subsemicategory.subsmc_is_idem_arrD


subsubsection\<open>Subsemicategory relation is a partial order\<close>

lemma subsmc_refl: 
  assumes "semicategory \<alpha> \<AA>" 
  shows "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret semicategory \<alpha> \<AA> by (rule assms)
  show ?thesis 
    by (auto intro: smc_cs_intros slicing_intros subdg_refl subsemicategoryI)
qed

lemma subsmc_trans[trans]: 
  assumes "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: subsemicategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: subsemicategory \<alpha> \<BB> \<CC> by (rule assms(2))
  show ?thesis 
  proof(rule subsemicategoryI)
    from \<AA>\<BB>.subsmc_subdigraph \<BB>\<CC>.subsmc_subdigraph 
    show "smc_dg \<AA> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> smc_dg \<CC>" by (meson subdg_trans)
    show "g \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> f = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
      if "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" for g b c f a
      by 
        (
          metis 
            that
            \<AA>\<BB>.subsmc_is_arr_vsubset 
            \<AA>\<BB>.subsmc_Comp_simp 
            \<BB>\<CC>.subsmc_Comp_simp
        )
  qed (auto intro: smc_cs_intros)
qed

lemma subsmc_antisym:
  assumes "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: subsemicategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: subsemicategory \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis
  proof(rule smc_eqI)
    from subdg_antisym[OF \<AA>\<BB>.subsmc_subdigraph \<BB>\<AA>.subsmc_subdigraph] have 
      "smc_dg \<AA>\<lparr>Obj\<rparr> = smc_dg \<BB>\<lparr>Obj\<rparr>" "smc_dg \<AA>\<lparr>Arr\<rparr> = smc_dg \<BB>\<lparr>Arr\<rparr>"
      by simp_all
    then show "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>" and Arr: "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>" 
      unfolding slicing_simps by simp_all
    show "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>" 
      by (rule vsv_eqI) (auto simp: smc_cs_simps \<AA>\<BB>.subsmc_dom_simp Arr)
    show "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
      by (rule vsv_eqI) (auto simp: smc_cs_simps \<BB>\<AA>.subsmc_cod_simp Arr)
    show "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>"
    proof(rule vsv_eqI)
      show "\<D>\<^sub>\<circ> (\<AA>\<lparr>Comp\<rparr>) = \<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>)"
      proof(intro vsubset_antisym vsubsetI)
        fix gf assume "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<AA>\<lparr>Comp\<rparr>)"
        then obtain g f b c a 
          where gf_def: "gf = [g, f]\<^sub>\<circ>" 
            and g: "g : b \<mapsto>\<^bsub>\<AA>\<^esub> c" 
            and f: "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
          by (auto simp: \<AA>\<BB>.sdg.smc_Comp_vdomain)
        from g f show "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>)"
          unfolding gf_def by (meson \<AA>\<BB>.dg.smc_Comp_vdomainI \<AA>\<BB>.subsmc_is_arrD)
      next
        fix gf assume "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<BB>\<lparr>Comp\<rparr>)"
        then obtain g f b c a 
          where gf_def: "gf = [g, f]\<^sub>\<circ>" 
            and g: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> c" 
            and f: "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
          by (auto simp: \<AA>\<BB>.dg.smc_Comp_vdomain)
        from g f show "gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<AA>\<lparr>Comp\<rparr>)"
          unfolding gf_def by (meson \<AA>\<BB>.sdg.smc_Comp_vdomainI \<BB>\<AA>.subsmc_is_arrD)
      qed
      show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<AA>\<lparr>Comp\<rparr>) \<Longrightarrow> \<AA>\<lparr>Comp\<rparr>\<lparr>a\<rparr> = \<BB>\<lparr>Comp\<rparr>\<lparr>a\<rparr>" for a
        by (metis \<AA>\<BB>.sdg.smc_Comp_vdomain \<AA>\<BB>.subsmc_Comp_simp)
    qed auto
  qed (auto intro: smc_cs_intros)
qed



subsection\<open>Inclusion semifunctor\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

abbreviation (input) smcf_inc :: "V \<Rightarrow> V \<Rightarrow> V"
  where "smcf_inc \<equiv> dghm_inc"


text\<open>Slicing.\<close>

lemma dghm_smcf_inc[slicing_commute]: 
  "dghm_inc (smc_dg \<BB>) (smc_dg \<CC>) = smcf_dghm (smcf_inc \<BB> \<CC>)"
  unfolding 
    smcf_dghm_def dghm_inc_def smc_dg_def dg_field_simps dghm_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Elementary properties.\<close>

lemmas [smc_cs_simps] = 
  dghm_inc_ObjMap_app 
  dghm_inc_ArrMap_app


subsubsection\<open>Canonical inclusion semifunctor associated with a subsemicategory\<close>

sublocale subsemicategory \<subseteq> inc: is_ft_semifunctor \<alpha> \<BB> \<CC> \<open>smcf_inc \<BB> \<CC>\<close>
proof(rule is_ft_semifunctorI)
  show "smcf_inc \<BB> \<CC> : \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  proof(rule is_semifunctorI)
    show "vfsequence (dghm_inc \<BB> \<CC>)" unfolding dghm_inc_def by auto
    show "vcard (dghm_inc \<BB> \<CC>) = 4\<^sub>\<nat>"
      unfolding dghm_inc_def by (simp add: nat_omega_simps)
    fix g b c f a assume prems: "g : b \<mapsto>\<^bsub>\<BB>\<^esub> c" "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
    then have "g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f : a \<mapsto>\<^bsub>\<BB>\<^esub> c" by (simp add: smc_cs_intros)
    with subsemicategory_axioms prems have [simp]: 
      "vid_on (\<BB>\<lparr>Arr\<rparr>)\<lparr>g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f\<rparr> = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f" 
      by (auto simp: smc_sub_bw_cs_simps)
    from prems show "dghm_inc \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>g \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f\<rparr> = 
      dghm_inc \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> dghm_inc \<BB> \<CC>\<lparr>ArrMap\<rparr>\<lparr>f\<rparr>"
      by (cs_concl cs_simp: smc_cs_simps cs_intro: smc_cs_intros smc_sub_fw_cs_intros)
  qed 
    (
      insert subsmc_inc_is_ft_dghm_axioms, 
      auto simp: slicing_commute[symmetric] dghm_inc_components smc_cs_intros
    )
qed (auto simp: slicing_commute[symmetric] subsmc_inc_is_ft_dghm_axioms)

lemmas (in subsemicategory) subsmc_smcf_inc_is_ft_semifunctor = 
  inc.is_ft_semifunctor_axioms


subsubsection\<open>Inclusion semifunctor for the opposite semicategories\<close>

lemma (in subsemicategory) 
  subsemicategory_smcf_inc_op_smc_is_semifunctor[smc_sub_cs_intros]:
  "smcf_inc (op_smc \<BB>) (op_smc \<CC>) : op_smc \<BB> \<mapsto>\<mapsto>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>a\<^sub>i\<^sub>t\<^sub>h\<^sub>f\<^sub>u\<^sub>l\<^bsub>\<alpha>\<^esub> op_smc \<CC>"
  by 
    (
      intro 
        subsemicategory.subsmc_smcf_inc_is_ft_semifunctor
        subsmc_subsemicategory_op_smc
    )

lemmas [smc_sub_cs_intros] = 
  subsemicategory.subsemicategory_smcf_inc_op_smc_is_semifunctor

lemma (in subsemicategory) subdg_op_smc_smcf_inc[smc_op_simps]: 
  "op_smcf (smcf_inc \<BB> \<CC>) = smcf_inc (op_smc \<BB>) (op_smc \<CC>)"
  by 
    (
      rule smcf_eqI[of \<alpha> \<open>op_smc \<BB>\<close> \<open>op_smc \<CC>\<close>], 
      unfold smc_op_simps dghm_inc_components
    )
    (
      auto simp: 
        is_ft_semifunctorD
        subsemicategory_smcf_inc_op_smc_is_semifunctor
        inc.is_semifunctor_op
    )

lemmas [smc_op_simps] = subsemicategory.subdg_op_smc_smcf_inc



subsection\<open>Full subsemicategory\<close>


text\<open>See Chapter I-3 in \cite{mac_lane_categories_2010}.\<close>

locale fl_subsemicategory = subsemicategory +
  assumes fl_subsemicategory_fl_subdigraph: "smc_dg \<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"

abbreviation is_fl_subsemicategory ("(_/ \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> fl_subsemicategory \<alpha> \<BB> \<CC>"


text\<open>Rules.\<close>

lemma (in fl_subsemicategory) fl_subsemicategory_axioms'[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<BB>' = \<BB>"
  shows "\<BB>' \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>'\<^esub> \<CC>"
  unfolding assms by (rule fl_subsemicategory_axioms)

lemma (in fl_subsemicategory) fl_subsemicategory_axioms''[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>f\<^sub>u\<^sub>l\<^sub>l\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule fl_subsemicategory_axioms)

mk_ide rf fl_subsemicategory_def[unfolded fl_subsemicategory_axioms_def]
  |intro fl_subsemicategoryI|
  |dest fl_subsemicategoryD[dest]|
  |elim fl_subsemicategoryE[elim!]|

lemmas [smc_sub_cs_intros] = fl_subsemicategoryD(1)


text\<open>Full subsemicategory.\<close>

sublocale fl_subsemicategory \<subseteq> inc: is_fl_semifunctor \<alpha> \<BB> \<CC> \<open>smcf_inc \<BB> \<CC>\<close>
  using fl_subsemicategory_fl_subdigraph inc.is_semifunctor_axioms
  by (intro is_fl_semifunctorI) (auto simp: slicing_commute[symmetric])



subsection\<open>Wide subsemicategory\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See \cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/wide+subcategory}
}).
\<close>

locale wide_subsemicategory = subsemicategory +
  assumes wide_subsmc_wide_subdigraph: "smc_dg \<BB> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> smc_dg \<CC>"

abbreviation is_wide_subsemicategory ("(_/ \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<index> _)" [51, 51] 50)
  where "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC> \<equiv> wide_subsemicategory \<alpha> \<BB> \<CC>"


text\<open>Rules.\<close>

lemma (in wide_subsemicategory) wide_subsemicategory_axioms'[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<BB>' = \<BB>"
  shows "\<BB>' \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>'\<^esub> \<CC>"
  unfolding assms by (rule wide_subsemicategory_axioms)

lemma (in wide_subsemicategory) wide_subsemicategory_axioms''[smc_cs_intros]:
  assumes "\<alpha>' = \<alpha>" and "\<CC>' = \<CC>"
  shows "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>'\<^esub> \<CC>'"
  unfolding assms by (rule wide_subsemicategory_axioms)

mk_ide rf wide_subsemicategory_def[unfolded wide_subsemicategory_axioms_def]
  |intro wide_subsemicategoryI|
  |dest wide_subsemicategoryD[dest]|
  |elim wide_subsemicategoryE[elim!]|

lemmas [smc_sub_cs_intros] = wide_subsemicategoryD(1)


text\<open>Wide subsemicategory is wide subdigraph.\<close>

context wide_subsemicategory
begin

interpretation wide_subdg: wide_subdigraph \<alpha> \<open>smc_dg \<BB>\<close> \<open>smc_dg \<CC>\<close>
  by (rule wide_subsmc_wide_subdigraph)

lemmas_with [unfolded slicing_simps]:
  wide_subsmc_Obj[dg_sub_bw_cs_intros] = wide_subdg.wide_subdg_Obj
  and wide_subsmc_obj_eq[dg_sub_bw_cs_simps] = wide_subdg.wide_subdg_obj_eq

end

lemmas [dg_sub_bw_cs_intros] = wide_subsemicategory.wide_subsmc_Obj
lemmas [dg_sub_bw_cs_simps] = wide_subsemicategory.wide_subsmc_obj_eq


subsubsection\<open>The wide subsemicategory relation is a partial order\<close>

lemma wide_subsmc_refl: 
  assumes "semicategory \<alpha> \<AA>" 
  shows "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret semicategory \<alpha> \<AA> by (rule assms)
  show ?thesis 
    by 
      (
        auto intro: 
          assms
          slicing_intros 
          wide_subdg_refl 
          wide_subsemicategoryI 
          subsmc_refl 
      )
qed

lemma wide_subsmc_trans[trans]:
  assumes "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<CC>"
proof-
  interpret \<AA>\<BB>: wide_subsemicategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<CC>: wide_subsemicategory \<alpha> \<BB> \<CC> by (rule assms(2))
  show ?thesis
    by 
      (
        intro 
          wide_subsemicategoryI 
          subsmc_trans[
            OF \<AA>\<BB>.subsemicategory_axioms \<BB>\<CC>.subsemicategory_axioms
            ], 
        rule wide_subdg_trans, 
        rule \<AA>\<BB>.wide_subsmc_wide_subdigraph, 
        rule \<BB>\<CC>.wide_subsmc_wide_subdigraph
     )
qed

lemma wide_subsmc_antisym:
  assumes "\<AA> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<BB>" and "\<BB> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> \<AA>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>\<BB>: wide_subsemicategory \<alpha> \<AA> \<BB> by (rule assms(1))
  interpret \<BB>\<AA>: wide_subsemicategory \<alpha> \<BB> \<AA> by (rule assms(2))
  show ?thesis 
    by 
      (
        rule subsmc_antisym[
          OF \<AA>\<BB>.subsemicategory_axioms \<BB>\<AA>.subsemicategory_axioms
          ]
      )
qed

text\<open>\newpage\<close>

end