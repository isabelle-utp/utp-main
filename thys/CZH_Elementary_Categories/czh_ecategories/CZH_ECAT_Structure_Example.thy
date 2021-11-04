(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Example: categories with additional structure\<close>
theory CZH_ECAT_Structure_Example
  imports 
    CZH_ECAT_Introduction
    CZH_ECAT_PCategory
    CZH_ECAT_Set
begin



subsection\<open>Background\<close>


text\<open>
The examples that are presented in this section showcase
how the framework developed in this article can 
be used for the formalization of the theory of 
categories with additional structure. The content of
this section also indicates some of the potential 
future directions for this body of work.
\<close>



subsection\<open>Dagger category\<close>

named_theorems dag_field_simps

named_theorems catdag_cs_simps
named_theorems catdag_cs_intros

definition DagCat :: V where [dag_field_simps]: "DagCat = 0"
definition DagDag :: V where [dag_field_simps]: "DagDag = 1\<^sub>\<nat>"

abbreviation DagDag_app :: "V \<Rightarrow> V" (\<open>\<dagger>\<^sub>C\<close>)
  where "\<dagger>\<^sub>C \<CC> \<equiv> \<CC>\<lparr>DagDag\<rparr>"


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
For further information see
\cite{noauthor_nlab_nodate}\footnote{\url{
https://ncatlab.org/nlab/show/dagger+category
}}.
\<close>

locale dagger_category =  
  \<Z> \<alpha> +
  vfsequence \<CC> + 
  DagCat: category \<alpha> \<open>\<CC>\<lparr>DagCat\<rparr>\<close> +
  DagDag: is_functor \<alpha> \<open>op_cat (\<CC>\<lparr>DagCat\<rparr>)\<close> \<open>\<CC>\<lparr>DagCat\<rparr>\<close> \<open>\<dagger>\<^sub>C \<CC>\<close> 
  for \<alpha> \<CC> +
  assumes catdag_length: "vcard \<CC> = 2\<^sub>\<nat>"
    and catdag_ObjMap_identity[catdag_cs_simps]: 
      "a \<in>\<^sub>\<circ> \<CC>\<lparr>DagCat\<rparr>\<lparr>Obj\<rparr> \<Longrightarrow> (\<dagger>\<^sub>C \<CC>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = a"
    and catdag_DagCat_idem[catdag_cs_simps]: 
      "\<dagger>\<^sub>C \<CC> \<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>C \<CC> = cf_id (\<CC>\<lparr>DagCat\<rparr>)"

lemmas [catdag_cs_simps] =
  dagger_category.catdag_ObjMap_identity
  dagger_category.catdag_DagCat_idem


text\<open>Rules.\<close>

lemma (in dagger_category) dagger_category_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "dagger_category \<alpha>' \<CC>"
  unfolding assms by (rule dagger_category_axioms)

mk_ide rf dagger_category_def[unfolded dagger_category_axioms_def]
  |intro dagger_categoryI|
  |dest dagger_categoryD[dest]|
  |elim dagger_categoryE[elim]|

lemma category_if_dagger_category[catdag_cs_intros]:
  assumes "\<CC>' = (\<CC>\<lparr>DagCat\<rparr>)" and "dagger_category \<alpha> \<CC>"
  shows "category \<alpha> \<CC>'"
  unfolding assms(1) using assms(2) by (rule dagger_categoryD(3))

lemma (in dagger_category) catdag_is_functor'[catdag_cs_intros]:
  assumes "\<AA>' = op_cat (\<CC>\<lparr>DagCat\<rparr>)" and "\<BB>' = \<CC>\<lparr>DagCat\<rparr>"
  shows "\<dagger>\<^sub>C \<CC> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  unfolding assms by (rule DagDag.is_functor_axioms)

lemmas [catdag_cs_intros] = dagger_category.catdag_is_functor'



subsection\<open>\<open>Rel\<close> as a dagger category\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
For further information see
\cite{noauthor_nlab_nodate}\footnote{\url{
https://ncatlab.org/nlab/show/Rel
}}.
\<close>

definition dagcat_Rel :: "V \<Rightarrow> V"
  where "dagcat_Rel \<alpha> = [cat_Rel \<alpha>, \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dagcat_Rel_components:
  shows "dagcat_Rel \<alpha>\<lparr>DagCat\<rparr> = cat_Rel \<alpha>"
    and "dagcat_Rel \<alpha>\<lparr>DagDag\<rparr> = \<dagger>\<^sub>C\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>"
  unfolding dagcat_Rel_def dag_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>\<open>Rel\<close> is a dagger category\<close>

lemma (in \<Z>) "dagger_category \<alpha> (dagcat_Rel \<alpha>)"
proof(intro dagger_categoryI)
  show "category \<alpha> (dagcat_Rel \<alpha>\<lparr>DagCat\<rparr>)" 
    by (cs_concl cs_simp: dagcat_Rel_components cs_intro: cat_Rel_cs_intros)
  show "\<dagger>\<^sub>C (dagcat_Rel \<alpha>) :
    op_cat (dagcat_Rel \<alpha>\<lparr>DagCat\<rparr>) \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> dagcat_Rel \<alpha>\<lparr>DagCat\<rparr>"
    unfolding dagcat_Rel_components
    by (cs_concl cs_intro: cf_cs_intros cat_cs_intros)
  show "vcard (dagcat_Rel \<alpha>) = 2\<^sub>\<nat>"
    unfolding dagcat_Rel_def by (simp add: nat_omega_simps)
  show "\<dagger>\<^sub>C (dagcat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> = a"
    if "a \<in>\<^sub>\<circ> dagcat_Rel \<alpha>\<lparr>DagCat\<rparr>\<lparr>Obj\<rparr>" for a
    using that
    unfolding dagcat_Rel_components cat_Rel_components(1)
    by (cs_concl cs_simp: cat_cs_simps cat_Rel_cs_simps)
  show "\<dagger>\<^sub>C (dagcat_Rel \<alpha>) \<^sub>C\<^sub>F\<circ> \<dagger>\<^sub>C (dagcat_Rel \<alpha>) = dghm_id (dagcat_Rel \<alpha>\<lparr>DagCat\<rparr>)"
    unfolding dagcat_Rel_components
    by (cs_concl cs_simp: cf_cn_comp_cf_dag_Rel_cf_dag_Rel)
qed (auto simp: dagcat_Rel_def)



subsection\<open>Monoidal category\<close>


text\<open>
For background information see Chapter 2 in \cite{etingof_tensor_2015}.
\<close>


subsubsection\<open>Background\<close>

named_theorems mcat_field_simps

named_theorems mcat_cs_simps
named_theorems mcat_cs_intros

definition Mcat :: V where [mcat_field_simps]: "Mcat = 0"
definition Mcf :: V where [mcat_field_simps]: "Mcf = 1\<^sub>\<nat>"
definition Me :: V where [mcat_field_simps]: "Me = 2\<^sub>\<nat>"
definition M\<alpha> :: V where [mcat_field_simps]: "M\<alpha> = 3\<^sub>\<nat>"
definition Ml :: V where [mcat_field_simps]: "Ml = 4\<^sub>\<nat>"
definition Mr :: V where [mcat_field_simps]: "Mr = 5\<^sub>\<nat>"


subsubsection\<open>Definition and elementary properties\<close>

locale monoidal_category =
  \<comment>\<open>See Definition 2.2.8 in \cite{etingof_tensor_2015}.\<close>
  \<Z> \<alpha> + 
  vfsequence \<CC> +
  Mcat: category \<alpha> \<open>\<CC>\<lparr>Mcat\<rparr>\<close> +
  Mcf: is_functor \<alpha> \<open>(\<CC>\<lparr>Mcat\<rparr>) \<times>\<^sub>C (\<CC>\<lparr>Mcat\<rparr>)\<close> \<open>\<CC>\<lparr>Mcat\<rparr>\<close> \<open>\<CC>\<lparr>Mcf\<rparr>\<close> +
  M\<alpha>: is_iso_ntcf
    \<alpha> \<open>\<CC>\<lparr>Mcat\<rparr>^\<^sub>C\<^sub>3\<close> \<open>\<CC>\<lparr>Mcat\<rparr>\<close> \<open>cf_blcomp (\<CC>\<lparr>Mcf\<rparr>)\<close> \<open>cf_brcomp (\<CC>\<lparr>Mcf\<rparr>)\<close> \<open>\<CC>\<lparr>M\<alpha>\<rparr>\<close> +
  Ml: is_iso_ntcf
    \<alpha>
    \<open>\<CC>\<lparr>Mcat\<rparr>\<close>
    \<open>\<CC>\<lparr>Mcat\<rparr>\<close>
    \<open>\<CC>\<lparr>Mcf\<rparr>\<^bsub>\<CC>\<lparr>Mcat\<rparr>,\<CC>\<lparr>Mcat\<rparr>\<^esub>(\<CC>\<lparr>Me\<rparr>,-)\<^sub>C\<^sub>F\<close>
    \<open>cf_id (\<CC>\<lparr>Mcat\<rparr>)\<close>
    \<open>\<CC>\<lparr>Ml\<rparr>\<close> +
  Mr: is_iso_ntcf
    \<alpha>
    \<open>\<CC>\<lparr>Mcat\<rparr>\<close>
    \<open>\<CC>\<lparr>Mcat\<rparr>\<close>
    \<open>\<CC>\<lparr>Mcf\<rparr>\<^bsub>\<CC>\<lparr>Mcat\<rparr>,\<CC>\<lparr>Mcat\<rparr>\<^esub>(-,\<CC>\<lparr>Me\<rparr>)\<^sub>C\<^sub>F\<close>
    \<open>cf_id (\<CC>\<lparr>Mcat\<rparr>)\<close>
    \<open>\<CC>\<lparr>Mr\<rparr>\<close>
  for \<alpha> \<CC> +
  assumes mcat_length[mcat_cs_simps]: "vcard \<CC> = 6\<^sub>\<nat>"
    and mcat_Me_is_obj[mcat_cs_intros]: "\<CC>\<lparr>Me\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>"
    and mcat_pentagon:
      "\<lbrakk> 
        a \<in>\<^sub>\<circ> \<CC>\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>;
        b \<in>\<^sub>\<circ> \<CC>\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>;
        c \<in>\<^sub>\<circ> \<CC>\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>;
        d \<in>\<^sub>\<circ> \<CC>\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>
       \<rbrakk> \<Longrightarrow> 
        (\<CC>\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<CC>\<lparr>Mcf\<rparr>\<^esub> \<CC>\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>b, c, d\<rparr>\<^sub>\<bullet>) \<circ>\<^sub>A\<^bsub>\<CC>\<lparr>Mcat\<rparr>\<^esub> 
          \<CC>\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>a, b \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<CC>\<lparr>Mcf\<rparr>\<^esub> c, d\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<lparr>Mcat\<rparr>\<^esub>
            (\<CC>\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>a, b, c\<rparr>\<^sub>\<bullet> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<CC>\<lparr>Mcf\<rparr>\<^esub> \<CC>\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>d\<rparr>) =
              \<CC>\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>a, b, c \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<CC>\<lparr>Mcf\<rparr>\<^esub> d\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>\<CC>\<lparr>Mcat\<rparr>\<^esub>
                \<CC>\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>a \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>\<CC>\<lparr>Mcf\<rparr>\<^esub> b, c, d\<rparr>\<^sub>\<bullet>"
    and mcat_triangle[mcat_cs_simps]:
      "\<lbrakk> a \<in>\<^sub>\<circ> \<CC>\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>; b \<in>\<^sub>\<circ> \<CC>\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr> \<rbrakk> \<Longrightarrow>
        (\<CC>\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<CC>\<lparr>Mcf\<rparr>\<^esub> \<CC>\<lparr>Ml\<rparr>\<lparr>NTMap\<rparr>\<lparr>b\<rparr>) \<circ>\<^sub>A\<^bsub>\<CC>\<lparr>Mcat\<rparr>\<^esub>
          \<CC>\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>a, \<CC>\<lparr>Me\<rparr>, b\<rparr>\<^sub>\<bullet> =
            (\<CC>\<lparr>Mr\<rparr>\<lparr>NTMap\<rparr>\<lparr>a\<rparr> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>\<CC>\<lparr>Mcf\<rparr>\<^esub> \<CC>\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>b\<rparr>)"

lemmas [mcat_cs_intros] = monoidal_category.mcat_Me_is_obj
lemmas [mcat_cs_simps] = monoidal_category.mcat_triangle


text\<open>Rules.\<close>

lemma (in monoidal_category) monoidal_category_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "monoidal_category \<alpha>' \<CC>"
  unfolding assms by (rule monoidal_category_axioms)

mk_ide rf monoidal_category_def[unfolded monoidal_category_axioms_def]
  |intro monoidal_categoryI|
  |dest monoidal_categoryD[dest]|
  |elim monoidal_categoryE[elim]|


text\<open>Elementary properties.\<close>

lemma mcat_eqI:
  assumes "monoidal_category \<alpha> \<AA>" 
    and "monoidal_category \<alpha> \<BB>"
    and "\<AA>\<lparr>Mcat\<rparr> = \<BB>\<lparr>Mcat\<rparr>"
    and "\<AA>\<lparr>Mcf\<rparr> = \<BB>\<lparr>Mcf\<rparr>"
    and "\<AA>\<lparr>Me\<rparr> = \<BB>\<lparr>Me\<rparr>"
    and "\<AA>\<lparr>M\<alpha>\<rparr> = \<BB>\<lparr>M\<alpha>\<rparr>"
    and "\<AA>\<lparr>Ml\<rparr> = \<BB>\<lparr>Ml\<rparr>"
    and "\<AA>\<lparr>Mr\<rparr> = \<BB>\<lparr>Mr\<rparr>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>: monoidal_category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: monoidal_category \<alpha> \<BB> by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<AA> = 6\<^sub>\<nat>" by (cs_concl cs_simp: mcat_cs_simps V_cs_simps)
    show "\<D>\<^sub>\<circ> \<AA> = \<D>\<^sub>\<circ> \<BB>" by (cs_concl cs_simp: mcat_cs_simps V_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<AA> \<Longrightarrow> \<AA>\<lparr>a\<rparr> = \<BB>\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert assms) 
        (auto simp: mcat_field_simps)
  qed auto
qed



subsection\<open>Components for \<open>M\<alpha>\<close> for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition M\<alpha>_Rel_arrow_lr :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "M\<alpha>_Rel_arrow_lr A B C =
    [
      (\<lambda>ab_c\<in>\<^sub>\<circ>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C. \<langle>vfst (vfst ab_c), \<langle>vsnd (vfst ab_c), vsnd ab_c\<rangle>\<rangle>),
      (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C,
      A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)
    ]\<^sub>\<circ>"

definition M\<alpha>_Rel_arrow_rl :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "M\<alpha>_Rel_arrow_rl A B C =
    [
      (\<lambda>a_bc\<in>\<^sub>\<circ>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C). \<langle>\<langle>vfst a_bc, vfst (vsnd a_bc)\<rangle>, vsnd (vsnd a_bc)\<rangle>),
      A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C),
      (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma M\<alpha>_Rel_arrow_lr_components:
  shows "M\<alpha>_Rel_arrow_lr A B C\<lparr>ArrVal\<rparr> =
    (\<lambda>ab_c\<in>\<^sub>\<circ>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C. \<langle>vfst (vfst ab_c), \<langle>vsnd (vfst ab_c), vsnd ab_c\<rangle>\<rangle>)"
    and [cat_cs_simps]: "M\<alpha>_Rel_arrow_lr A B C\<lparr>ArrDom\<rparr> = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and [cat_cs_simps]: "M\<alpha>_Rel_arrow_lr A B C\<lparr>ArrCod\<rparr> = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
  unfolding M\<alpha>_Rel_arrow_lr_def arr_field_simps by (simp_all add: nat_omega_simps)

lemma M\<alpha>_Rel_arrow_rl_components:
  shows "M\<alpha>_Rel_arrow_rl A B C\<lparr>ArrVal\<rparr> =
    (\<lambda>a_bc\<in>\<^sub>\<circ>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C). \<langle>\<langle>vfst a_bc, vfst (vsnd a_bc)\<rangle>, vsnd (vsnd a_bc)\<rangle>)"
    and [cat_cs_simps]: "M\<alpha>_Rel_arrow_rl A B C\<lparr>ArrDom\<rparr> = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and [cat_cs_simps]: "M\<alpha>_Rel_arrow_rl A B C\<lparr>ArrCod\<rparr> = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
  unfolding M\<alpha>_Rel_arrow_rl_def arr_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Arrow value\<close>

mk_VLambda M\<alpha>_Rel_arrow_lr_components(1)
  |vsv M\<alpha>_Rel_arrow_lr_ArrVal_vsv[cat_cs_intros]|
  |vdomain M\<alpha>_Rel_arrow_lr_ArrVal_vdomain[cat_cs_simps]|
  |app M\<alpha>_Rel_arrow_lr_ArrVal_app'|

lemma M\<alpha>_Rel_arrow_lr_ArrVal_app[cat_cs_simps]:
  assumes "ab_c = \<langle>\<langle>a, b\<rangle>, c\<rangle>" and "ab_c \<in>\<^sub>\<circ> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
  shows "M\<alpha>_Rel_arrow_lr A B C\<lparr>ArrVal\<rparr>\<lparr>ab_c\<rparr> = \<langle>a, \<langle>b, c\<rangle>\<rangle>"
  using assms(2)
  unfolding assms(1)
  by (simp_all add: M\<alpha>_Rel_arrow_lr_ArrVal_app' nat_omega_simps)

mk_VLambda M\<alpha>_Rel_arrow_rl_components(1)
  |vsv M\<alpha>_Rel_arrow_rl_ArrVal_vsv[cat_cs_intros]|
  |vdomain M\<alpha>_Rel_arrow_rl_ArrVal_vdomain[cat_cs_simps]|
  |app M\<alpha>_Rel_arrow_rl_ArrVal_app'|

lemma M\<alpha>_Rel_arrow_rl_ArrVal_app[cat_cs_simps]:
  assumes "a_bc = \<langle>a, \<langle>b, c\<rangle>\<rangle>" and "a_bc \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
  shows "M\<alpha>_Rel_arrow_rl A B C\<lparr>ArrVal\<rparr>\<lparr>a_bc\<rparr> = \<langle>\<langle>a, b\<rangle>, c\<rangle>"
  using assms(2)
  unfolding assms(1)
  by (simp_all add: M\<alpha>_Rel_arrow_rl_ArrVal_app' nat_omega_simps)


subsubsection\<open>Components for \<open>M\<alpha>\<close> for \<open>Rel\<close> are arrows\<close>

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_Vset: 
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "C \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
proof(intro cat_Set_is_arrI arr_SetI)
  show "vfsequence (M\<alpha>_Rel_arrow_lr A B C)" unfolding M\<alpha>_Rel_arrow_lr_def by auto
  show "vcard (M\<alpha>_Rel_arrow_lr A B C) = 3\<^sub>\<nat>"
    unfolding M\<alpha>_Rel_arrow_lr_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (M\<alpha>_Rel_arrow_lr A B C\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> M\<alpha>_Rel_arrow_lr A B C\<lparr>ArrCod\<rparr>"
    unfolding M\<alpha>_Rel_arrow_lr_components by auto
qed
  (
    use assms in 
      \<open>cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros\<close>
  )+

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_Vset: 
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "C \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
proof(intro cat_Set_is_arrI arr_SetI)
  show "vfsequence (M\<alpha>_Rel_arrow_rl A B C)" unfolding M\<alpha>_Rel_arrow_rl_def by auto
  show "vcard (M\<alpha>_Rel_arrow_rl A B C) = 3\<^sub>\<nat>"
    unfolding M\<alpha>_Rel_arrow_rl_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (M\<alpha>_Rel_arrow_rl A B C\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> M\<alpha>_Rel_arrow_rl A B C\<lparr>ArrCod\<rparr>"
    unfolding M\<alpha>_Rel_arrow_rl_components by auto
qed
  (
    use assms in 
      \<open>cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros\<close>
  )+

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_is_cat_Set_arr: 
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
  using assms 
  unfolding cat_Set_components 
  by (rule M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_Vset)

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_is_cat_Set_arr'[cat_rel_par_Set_cs_intros]: 
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "A' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "B' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "\<CC>' = cat_Set \<alpha>"
  shows "M\<alpha>_Rel_arrow_lr A B C : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) unfolding assms(4-6) by (rule M\<alpha>_Rel_arrow_lr_is_cat_Set_arr)

lemmas [cat_rel_par_Set_cs_intros] = \<Z>.M\<alpha>_Rel_arrow_lr_is_cat_Set_arr'

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_is_cat_Set_arr: 
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
  using assms 
  unfolding cat_Set_components 
  by (rule M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_Vset)

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_is_cat_Set_arr'[cat_rel_par_Set_cs_intros]: 
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "A' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "B' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "\<CC>' = cat_Set \<alpha>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) unfolding assms(4-6) by (rule M\<alpha>_Rel_arrow_rl_is_cat_Set_arr)

lemmas [cat_rel_par_Set_cs_intros] = \<Z>.M\<alpha>_Rel_arrow_rl_is_cat_Set_arr'

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_is_cat_Par_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
  shows "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  from assms show ?thesis
    unfolding cat_Par_components(1)
    by (intro Set_Par.subcat_is_arrD M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_is_cat_Par_arr'[cat_rel_Par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "A' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "B' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "\<CC>' = cat_Par \<alpha>"
  shows "M\<alpha>_Rel_arrow_lr A B C : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) unfolding assms(4-6) by (rule M\<alpha>_Rel_arrow_lr_is_cat_Par_arr)

lemmas [cat_rel_Par_set_cs_intros] = \<Z>.M\<alpha>_Rel_arrow_lr_is_cat_Par_arr'

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_is_cat_Par_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  from assms show ?thesis
    unfolding cat_Par_components(1)
    by (intro Set_Par.subcat_is_arrD M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_is_cat_Par_arr'[cat_rel_Par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "A' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "B' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "\<CC>' = cat_Par \<alpha>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) unfolding assms(4-6) by (rule M\<alpha>_Rel_arrow_rl_is_cat_Par_arr)

lemmas [cat_rel_Par_set_cs_intros] = \<Z>.M\<alpha>_Rel_arrow_rl_is_cat_Par_arr'

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  interpret Par_Rel: wide_replete_subcategory \<alpha> \<open>cat_Par \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Par_cat_Rel)
  interpret Set_Rel: subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by 
      ( 
        rule subcat_trans[
          OF Set_Par.subcategory_axioms Par_Rel.subcategory_axioms
          ]
      )
  from assms show ?thesis
    unfolding cat_Rel_components(1)
    by (intro Set_Rel.subcat_is_arrD M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr'[cat_Rel_par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "A' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "B' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "M\<alpha>_Rel_arrow_lr A B C : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) unfolding assms(4-6) by (rule M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr)

lemmas [cat_Rel_par_set_cs_intros] = \<Z>.M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr'

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  interpret Par_Rel: wide_replete_subcategory \<alpha> \<open>cat_Par \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Par_cat_Rel)
  interpret Set_Rel: subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by 
      ( 
        rule subcat_trans[
          OF Set_Par.subcategory_axioms Par_Rel.subcategory_axioms
          ]
      )
  from assms show ?thesis
    unfolding cat_Rel_components(1)
    by (intro Set_Rel.subcat_is_arrD M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr'[cat_Rel_par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "A' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "B' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) unfolding assms(4-6) by (rule M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr)

lemmas [cat_Rel_par_set_cs_intros] = \<Z>.M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr'


subsubsection\<open>Further properties\<close>

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_M\<alpha>_Rel_arrow_lr[cat_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "C \<in>\<^sub>\<circ> Vset \<alpha>"
  shows 
    "M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C = 
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr>"
proof-
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (cs_concl cs_intro: cat_cs_intros)
  from assms have lhs:
    "M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C :
      (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by 
      (
        cs_concl
          cs_simp: cat_Set_components(1)
          cs_intro: cat_rel_par_Set_cs_intros cat_cs_intros
      )
  then have dom_lhs:
    "\<D>\<^sub>\<circ> ((M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C)\<lparr>ArrVal\<rparr>) =
      (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms Set.category_axioms have rhs:
    "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr> :
      (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by 
      (
        cs_concl 
          cs_simp: cat_Set_components(1) cs_intro: V_cs_intros cat_cs_intros
      )
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> ((cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr>)\<lparr>ArrVal\<rparr>) = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show ?thesis
  proof(rule arr_Set_eqI)
    from lhs show arr_Set_lhs:
      "arr_Set \<alpha> (M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C)"
      by (auto dest: cat_Set_is_arrD(1))
    from rhs show arr_Set_rhs: "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr>)"
      by (auto dest: cat_Set_is_arrD(1))
    show 
      "(M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C)\<lparr>ArrVal\<rparr> = 
        cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix ab_c assume prems: "ab_c \<in>\<^sub>\<circ> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
      then obtain a b c
        where ab_c_def: "ab_c = \<langle>\<langle>a, b\<rangle>, c\<rangle>"
          and a: "a \<in>\<^sub>\<circ> A"
          and b: "b \<in>\<^sub>\<circ> B"
          and c: "c \<in>\<^sub>\<circ> C"
        by clarsimp
      from assms prems a b c lhs rhs show 
        "(M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C)\<lparr>ArrVal\<rparr>\<lparr>ab_c\<rparr> = 
          cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr>\<lparr>ArrVal\<rparr>\<lparr>ab_c\<rparr>"
        unfolding ab_c_def
        by
          (
            cs_concl
              cs_simp: cat_Set_components(1) cat_cs_simps
              cs_intro: cat_rel_par_Set_cs_intros V_cs_intros cat_cs_intros
          )
    qed (use arr_Set_lhs arr_Set_rhs in auto)
  qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
qed

lemma (in \<Z>) M\<alpha>_Rel_arrow_rl_M\<alpha>_Rel_arrow_lr'[cat_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows 
    "M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C = 
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr>"
  using assms unfolding cat_Set_components(1) by (rule M\<alpha>_Rel_arrow_rl_M\<alpha>_Rel_arrow_lr)

lemmas [cat_cs_simps] = \<Z>.M\<alpha>_Rel_arrow_rl_M\<alpha>_Rel_arrow_lr'

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_M\<alpha>_Rel_arrow_rl[cat_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "C \<in>\<^sub>\<circ> Vset \<alpha>"
  shows 
    "M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C = 
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)\<rparr>"
proof-
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (cs_concl cs_intro: cat_cs_intros)
  from assms have lhs:
    "M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C :
      A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    by 
      (
        cs_concl 
          cs_simp: cat_Set_components(1) 
          cs_intro: cat_rel_par_Set_cs_intros cat_cs_intros
      )
  then have dom_lhs:
    "\<D>\<^sub>\<circ> ((M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C)\<lparr>ArrVal\<rparr>) =
      A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms Set.category_axioms have rhs:
    "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)\<rparr> :
      A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    by 
      (
        cs_concl 
          cs_simp: cat_Set_components(1) cs_intro: V_cs_intros cat_cs_intros
      )
  then have dom_rhs: 
    "\<D>\<^sub>\<circ> ((cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)\<rparr>)\<lparr>ArrVal\<rparr>) = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show ?thesis
  proof(rule arr_Set_eqI)
    from lhs show arr_Set_lhs:
      "arr_Set \<alpha> (M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C)"
      by (auto dest: cat_Set_is_arrD(1))
    from rhs show arr_Set_rhs: "arr_Set \<alpha> (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)\<rparr>)"
      by (auto dest: cat_Set_is_arrD(1))
    show 
      "(M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C)\<lparr>ArrVal\<rparr> = 
        cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)\<rparr>\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a_bc assume prems: "a_bc \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
      then obtain a b c
        where a_bc_def: "a_bc = \<langle>a, \<langle>b, c\<rangle>\<rangle>"
          and a: "a \<in>\<^sub>\<circ> A"
          and b: "b \<in>\<^sub>\<circ> B"
          and c: "c \<in>\<^sub>\<circ> C"
        by clarsimp
      from assms prems a b c lhs rhs show 
        "(M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C)\<lparr>ArrVal\<rparr>\<lparr>a_bc\<rparr> = 
          cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a_bc\<rparr>"
        unfolding a_bc_def
        by
          (
            cs_concl
              cs_simp: cat_Set_components(1) cat_cs_simps
              cs_intro: V_cs_intros cat_rel_par_Set_cs_intros cat_cs_intros
          )
    qed (use arr_Set_lhs arr_Set_rhs in auto)
  qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
qed

lemma (in \<Z>) M\<alpha>_Rel_arrow_lr_M\<alpha>_Rel_arrow_rl'[cat_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows 
    "M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C = 
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)\<rparr>"
  using assms 
  unfolding cat_Set_components(1) 
  by (rule M\<alpha>_Rel_arrow_lr_M\<alpha>_Rel_arrow_rl)

lemmas [cat_cs_simps] = \<Z>.M\<alpha>_Rel_arrow_lr_M\<alpha>_Rel_arrow_rl'


subsubsection\<open>Components for \<open>M\<alpha>\<close> for \<open>Rel\<close> are isomorphisms\<close>

lemma (in \<Z>) 
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "C \<in>\<^sub>\<circ> Vset \<alpha>"
  shows M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism_Vset: 
    "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism_Vset:
    "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
proof-
  interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (cs_concl cs_intro: cat_cs_intros)
  have lhs: "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by (intro M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_Vset assms)
  from assms have [cat_cs_simps]:
    "M\<alpha>_Rel_arrow_rl A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_lr A B C =
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>(A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: cat_Set_components(1) cat_cs_simps cs_intro: cat_cs_intros
      )
  from assms have [cat_cs_simps]: 
    "M\<alpha>_Rel_arrow_lr A B C \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> M\<alpha>_Rel_arrow_rl A B C =
      cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> B \<times>\<^sub>\<circ> C\<rparr>"
    by 
      (
        cs_concl 
          cs_simp: cat_Set_components(1) cat_cs_simps cs_intro: cat_cs_intros
      )
  from 
    Set.is_arr_isomorphismI'
      [
        OF lhs M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_Vset[OF assms], 
        unfolded cat_cs_simps,
        simplified
      ]
  show "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by auto
qed

lemma (in \<Z>) 
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism:
    "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism:
    "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
  using assms
  unfolding cat_Set_components(1)
  by
    (
      all
        \<open>
          intro
            M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism_Vset
            M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism_Vset
        \<close>
    )

lemma (in \<Z>) 
  M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism'[cat_rel_par_Set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "A' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "B' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "\<CC>' = cat_Set \<alpha>"
  shows "M\<alpha>_Rel_arrow_lr A B C : A' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) 
  unfolding assms(4-6) 
  by (rule M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism)

lemmas [cat_rel_par_Set_cs_intros] = 
  \<Z>.M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism'

lemma (in \<Z>) 
  M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism'[cat_rel_par_Set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "A' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "B' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "\<CC>' = cat_Set \<alpha>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) 
  unfolding assms(4-6)
  by (rule M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism)

lemmas [cat_rel_par_Set_cs_intros] = 
  \<Z>.M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism'

lemma (in \<Z>) 
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
  shows M\<alpha>_Rel_arrow_lr_is_cat_Par_arr_isomorphism: 
    "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and M\<alpha>_Rel_arrow_rl_is_cat_Par_arr_isomorphism: 
    "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  show "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    by 
      (
        rule Set_Par.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Par_components]
              ]
          ]
      )
  show "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by 
      (
        rule Set_Par.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Par_components]
              ]
          ]
      )
qed

lemma (in \<Z>) 
  M\<alpha>_Rel_arrow_lr_is_cat_Par_arr_isomorphism'[cat_rel_Par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "A' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "B' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "\<CC>' = cat_Par \<alpha>"
  shows "M\<alpha>_Rel_arrow_lr A B C : A' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) 
  unfolding assms(4-6) 
  by (rule M\<alpha>_Rel_arrow_lr_is_cat_Par_arr_isomorphism)

lemmas [cat_rel_Par_set_cs_intros] = 
  \<Z>.M\<alpha>_Rel_arrow_lr_is_cat_Par_arr_isomorphism'

lemma (in \<Z>) 
  M\<alpha>_Rel_arrow_rl_is_cat_Par_arr_isomorphism'[cat_rel_Par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "A' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "B' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "\<CC>' = cat_Par \<alpha>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) 
  unfolding assms(4-6)
  by (rule M\<alpha>_Rel_arrow_rl_is_cat_Par_arr_isomorphism)

lemmas [cat_rel_Par_set_cs_intros] = 
  \<Z>.M\<alpha>_Rel_arrow_rl_is_cat_Par_arr_isomorphism'

lemma (in \<Z>) 
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr_isomorphism: 
    "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr_isomorphism: 
    "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  interpret Par_Rel: wide_replete_subcategory \<alpha> \<open>cat_Par \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Par_cat_Rel)
  interpret Set_Rel: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by 
      ( 
        rule wr_subcat_trans
          [
            OF 
              Set_Par.wide_replete_subcategory_axioms
              Par_Rel.wide_replete_subcategory_axioms
          ]
      )
  show "M\<alpha>_Rel_arrow_lr A B C : (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    by 
      (
        rule Set_Rel.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF M\<alpha>_Rel_arrow_lr_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Rel_components]
              ]
          ]
      )
  show "M\<alpha>_Rel_arrow_rl A B C : A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C) \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    by 
      (
        rule Set_Rel.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF M\<alpha>_Rel_arrow_rl_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Rel_components]
              ]
          ]
      )
qed

lemma (in \<Z>) 
  M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr_isomorphism'[cat_Rel_par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "A' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "B' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "M\<alpha>_Rel_arrow_lr A B C : A' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) 
  unfolding assms(4-6) 
  by (rule M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr_isomorphism)

lemmas [cat_Rel_par_set_cs_intros] =
  \<Z>.M\<alpha>_Rel_arrow_lr_is_cat_Rel_arr_isomorphism'

lemma (in \<Z>) 
  M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr_isomorphism'[cat_Rel_par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "A' = A \<times>\<^sub>\<circ> (B \<times>\<^sub>\<circ> C)"
    and "B' = (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "M\<alpha>_Rel_arrow_rl A B C : A' \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-3) 
  unfolding assms(4-6)
  by (rule M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr_isomorphism)

lemmas [cat_Rel_par_set_cs_intros] = 
  \<Z>.M\<alpha>_Rel_arrow_rl_is_cat_Rel_arr_isomorphism'



subsection\<open>\<open>M\<alpha>\<close> for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition M\<alpha>_Rel :: "V \<Rightarrow> V"
  where "M\<alpha>_Rel \<CC> =
    [
      (\<lambda>abc\<in>\<^sub>\<circ>(\<CC>^\<^sub>C\<^sub>3)\<lparr>Obj\<rparr>. M\<alpha>_Rel_arrow_lr (abc\<lparr>0\<rparr>) (abc\<lparr>1\<^sub>\<nat>\<rparr>) (abc\<lparr>2\<^sub>\<nat>\<rparr>)),
      cf_blcomp (cf_prod_2_Rel \<CC>),
      cf_brcomp (cf_prod_2_Rel \<CC>),
      \<CC>^\<^sub>C\<^sub>3,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma M\<alpha>_Rel_components:
  shows "M\<alpha>_Rel \<CC>\<lparr>NTMap\<rparr> =
    (\<lambda>abc\<in>\<^sub>\<circ>(\<CC>^\<^sub>C\<^sub>3)\<lparr>Obj\<rparr>. M\<alpha>_Rel_arrow_lr (abc\<lparr>0\<rparr>) (abc\<lparr>1\<^sub>\<nat>\<rparr>) (abc\<lparr>2\<^sub>\<nat>\<rparr>))"
    and [cat_cs_simps]: "M\<alpha>_Rel \<CC>\<lparr>NTDom\<rparr> = cf_blcomp (cf_prod_2_Rel \<CC>)"
    and [cat_cs_simps]: "M\<alpha>_Rel \<CC>\<lparr>NTCod\<rparr> = cf_brcomp (cf_prod_2_Rel \<CC>)"
    and [cat_cs_simps]: "M\<alpha>_Rel \<CC>\<lparr>NTDGDom\<rparr> = \<CC>^\<^sub>C\<^sub>3"
    and [cat_cs_simps]: "M\<alpha>_Rel \<CC>\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding M\<alpha>_Rel_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda M\<alpha>_Rel_components(1)
  |vsv M\<alpha>_Rel_NTMap_vsv[cat_cs_intros]|
  |vdomain M\<alpha>_Rel_NTMap_vdomain[cat_cs_simps]|
  |app M\<alpha>_Rel_NTMap_app'|

lemma M\<alpha>_Rel_NTMap_app[cat_cs_simps]: 
  assumes "ABC = [A, B, C]\<^sub>\<circ>" and "ABC \<in>\<^sub>\<circ> (\<CC>^\<^sub>C\<^sub>3)\<lparr>Obj\<rparr>"
  shows "M\<alpha>_Rel \<CC>\<lparr>NTMap\<rparr>\<lparr>ABC\<rparr> = M\<alpha>_Rel_arrow_lr A B C"
  using assms(2) 
  unfolding assms(1) 
  by (simp add: M\<alpha>_Rel_NTMap_app' nat_omega_simps)


subsubsection\<open>\<open>M\<alpha>\<close> for \<open>Rel\<close> is a natural isomorphism\<close>

lemma (in \<Z>) M\<alpha>_Rel_is_iso_ntcf: 
  "M\<alpha>_Rel (cat_Rel \<alpha>) :
    cf_blcomp (cf_prod_2_Rel (cat_Rel \<alpha>)) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o
    cf_brcomp (cf_prod_2_Rel (cat_Rel \<alpha>)) :
    cat_Rel \<alpha>^\<^sub>C\<^sub>3 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
proof-

  interpret cf_prod: is_functor 
    \<alpha> \<open>cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> \<open>cf_prod_2_Rel (cat_Rel \<alpha>)\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_Rel_cs_intros)

  show ?thesis
  proof(intro is_iso_ntcfI is_ntcfI')

    show "vfsequence (M\<alpha>_Rel (cat_Rel \<alpha>))" unfolding M\<alpha>_Rel_def by auto
    show "vcard (M\<alpha>_Rel (cat_Rel \<alpha>)) = 5\<^sub>\<nat>"
      unfolding M\<alpha>_Rel_def by (simp add: nat_omega_simps)

    show "M\<alpha>_Rel (cat_Rel \<alpha>)\<lparr>NTMap\<rparr>\<lparr>ABC\<rparr> :
      cf_blcomp (cf_prod_2_Rel (cat_Rel \<alpha>))\<lparr>ObjMap\<rparr>\<lparr>ABC\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub>
      cf_brcomp (cf_prod_2_Rel (cat_Rel \<alpha>))\<lparr>ObjMap\<rparr>\<lparr>ABC\<rparr>"
      if "ABC \<in>\<^sub>\<circ> (cat_Rel \<alpha>^\<^sub>C\<^sub>3)\<lparr>Obj\<rparr>" for ABC
    proof-
      from that category_cat_Rel obtain A B C 
        where ABC_def: "ABC = [A, B, C]\<^sub>\<circ>"
          and A: "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
          and B: "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
          and C: "C \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
        by (elim cat_prod_3_ObjE[rotated 3])
      from that A B C show ?thesis
        unfolding ABC_def
        by
          (
            cs_concl
              cs_intro:
                cat_cs_intros cat_Rel_par_set_cs_intros cat_prod_cs_intros
              cs_simp: cat_cs_simps cat_Rel_cs_simps
          )
    qed
    then show "M\<alpha>_Rel (cat_Rel \<alpha>)\<lparr>NTMap\<rparr>\<lparr>ABC\<rparr> :
      cf_blcomp (cf_prod_2_Rel (cat_Rel \<alpha>))\<lparr>ObjMap\<rparr>\<lparr>ABC\<rparr> \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub>
      cf_brcomp (cf_prod_2_Rel (cat_Rel \<alpha>))\<lparr>ObjMap\<rparr>\<lparr>ABC\<rparr>"
      if "ABC \<in>\<^sub>\<circ> (cat_Rel \<alpha>^\<^sub>C\<^sub>3)\<lparr>Obj\<rparr>" for ABC
      using that by (simp add: cat_Rel_is_arr_isomorphismD(1))
    show 
      "M\<alpha>_Rel (cat_Rel \<alpha>)\<lparr>NTMap\<rparr>\<lparr>ABC'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub>
        cf_blcomp (cf_prod_2_Rel (cat_Rel \<alpha>))\<lparr>ArrMap\<rparr>\<lparr>HGF\<rparr> =
          cf_brcomp (cf_prod_2_Rel (cat_Rel \<alpha>))\<lparr>ArrMap\<rparr>\<lparr>HGF\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub>
            M\<alpha>_Rel (cat_Rel \<alpha>)\<lparr>NTMap\<rparr>\<lparr>ABC\<rparr>"
      if "HGF : ABC \<mapsto>\<^bsub>cat_Rel \<alpha>^\<^sub>C\<^sub>3\<^esub> ABC'" for ABC ABC' HGF
    proof-

      from that obtain H G F A B C A' B' C' 
        where HGF_def: "HGF = [H, G, F]\<^sub>\<circ>"
          and ABC_def: "ABC = [A, B, C]\<^sub>\<circ>"
          and ABC'_def: "ABC' = [A', B', C']\<^sub>\<circ>" 
          and H_is_arr: "H : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A'"
          and G_is_arr: "G : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B'"
          and F_is_arr: "F : C \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> C'"
        by 
          (
            elim cat_prod_3_is_arrE[
              OF category_cat_Rel category_cat_Rel category_cat_Rel 
              ]
          )

      note H = cat_Rel_is_arrD[OF H_is_arr]
      note G = cat_Rel_is_arrD[OF G_is_arr]
      note F = cat_Rel_is_arrD[OF F_is_arr]

      interpret H: arr_Rel \<alpha> H
        rewrites "H\<lparr>ArrDom\<rparr> = A" and "H\<lparr>ArrCod\<rparr> = A'"
        by (intro H)+
      interpret G: arr_Rel \<alpha> G
        rewrites "G\<lparr>ArrDom\<rparr> = B" and "G\<lparr>ArrCod\<rparr> = B'"
        by (intro G)+
      interpret F: arr_Rel \<alpha> F
        rewrites "F\<lparr>ArrDom\<rparr> = C" and "F\<lparr>ArrCod\<rparr> = C'"
        by (intro F)+

      let ?ABC' = \<open>M\<alpha>_Rel_arrow_lr A' B' C'\<close>
        and ?ABC = \<open>M\<alpha>_Rel_arrow_lr A B C\<close>
        and ?HG_F = 
          \<open>
            prod_2_Rel_ArrVal
              (prod_2_Rel_ArrVal (H\<lparr>ArrVal\<rparr>) (G\<lparr>ArrVal\<rparr>)) 
              (F\<lparr>ArrVal\<rparr>)
          \<close>
        and ?H_GF = 
          \<open>
            prod_2_Rel_ArrVal
              (H\<lparr>ArrVal\<rparr>)
              (prod_2_Rel_ArrVal (G\<lparr>ArrVal\<rparr>) (F\<lparr>ArrVal\<rparr>))
          \<close>

      have [cat_cs_simps]:
        "?ABC' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel (prod_2_Rel H G) F =
          prod_2_Rel H (prod_2_Rel G F) \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?ABC"
      proof-

        from H_is_arr G_is_arr F_is_arr have lhs:
          "?ABC' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel (prod_2_Rel H G) F :
            (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A' \<times>\<^sub>\<circ> (B' \<times>\<^sub>\<circ> C')"
          by (cs_concl cs_intro: cat_Rel_par_set_cs_intros cat_cs_intros)
        from H_is_arr G_is_arr F_is_arr have rhs:
          "prod_2_Rel H (prod_2_Rel G F) \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?ABC :
            (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A' \<times>\<^sub>\<circ> (B' \<times>\<^sub>\<circ> C')"
          by (cs_concl cs_intro: cat_Rel_par_set_cs_intros cat_cs_intros)
        
        show ?thesis
        proof(rule arr_Rel_eqI)

          from lhs show arr_Rel_lhs: 
            "arr_Rel \<alpha> (?ABC' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel (prod_2_Rel H G) F)"
            by (auto dest: cat_Rel_is_arrD)
          from rhs show arr_Rel_rhs: 
            "arr_Rel \<alpha> (prod_2_Rel H (prod_2_Rel G F) \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?ABC)"
            by (auto dest: cat_Rel_is_arrD)

          have [cat_cs_simps]: "?ABC'\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?HG_F = ?H_GF \<circ>\<^sub>\<circ> ?ABC\<lparr>ArrVal\<rparr>"
          proof(intro vsubset_antisym vsubsetI)
            fix abc_abc'' assume prems: "abc_abc'' \<in>\<^sub>\<circ> ?ABC'\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?HG_F"
            then obtain abc abc' abc'' 
              where abc_abc''_def: "abc_abc'' = \<langle>abc, abc''\<rangle>"
                and abc_abc': "\<langle>abc, abc'\<rangle> \<in>\<^sub>\<circ> ?HG_F"
                and abc'_abc'': "\<langle>abc', abc''\<rangle> \<in>\<^sub>\<circ> ?ABC'\<lparr>ArrVal\<rparr>"
              by clarsimp
            from abc_abc' obtain ab c ab' c' 
              where abc_abc'_def: "\<langle>abc, abc'\<rangle> = \<langle>\<langle>ab, c\<rangle>, \<langle>ab', c'\<rangle>\<rangle>"
                and ab_ab':
                  "\<langle>ab, ab'\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal (H\<lparr>ArrVal\<rparr>) (G\<lparr>ArrVal\<rparr>)"
                and cc': "\<langle>c, c'\<rangle> \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr>"
              by auto
            then have abc_def: "abc = \<langle>ab, c\<rangle>" and abc'_def: "abc' = \<langle>ab', c'\<rangle>" 
              by auto
            from ab_ab' obtain a b a' b'
              where ab_ab'_def: "\<langle>ab, ab'\<rangle> = \<langle>\<langle>a, b\<rangle>, \<langle>a', b'\<rangle>\<rangle>"
                and aa': "\<langle>a, a'\<rangle> \<in>\<^sub>\<circ> H\<lparr>ArrVal\<rparr>"
                and bb': "\<langle>b, b'\<rangle> \<in>\<^sub>\<circ> G\<lparr>ArrVal\<rparr>"
              by auto
            then have ab_def: "ab = \<langle>a, b\<rangle>" and ab'_def: "ab' = \<langle>a', b'\<rangle>"  
              by auto
            from cc' F.arr_Rel_ArrVal_vdomain F.arr_Rel_ArrVal_vrange 
            have c: "c \<in>\<^sub>\<circ> C" and c': "c' \<in>\<^sub>\<circ> C'"
              by auto
            from bb' G.arr_Rel_ArrVal_vdomain G.arr_Rel_ArrVal_vrange 
            have b: "b \<in>\<^sub>\<circ> B" and b': "b' \<in>\<^sub>\<circ> B'"
              by auto
            from aa' H.arr_Rel_ArrVal_vdomain H.arr_Rel_ArrVal_vrange 
            have a: "a \<in>\<^sub>\<circ> A" and a': "a' \<in>\<^sub>\<circ> A'"
              by auto
            from abc'_abc'' have "abc'' = ?ABC'\<lparr>ArrVal\<rparr>\<lparr>abc'\<rparr>"
              by (simp add: vsv.vsv_appI[OF M\<alpha>_Rel_arrow_lr_ArrVal_vsv])
            also from a' b' c' have "\<dots> = \<langle>a', \<langle>b', c'\<rangle>\<rangle>"
              unfolding abc'_def ab'_def
              by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
            finally have abc''_def: "abc'' = \<langle>a', \<langle>b', c'\<rangle>\<rangle>" by auto
            from aa' bb' cc' a a' b b' c c' show 
              "abc_abc'' \<in>\<^sub>\<circ> ?H_GF \<circ>\<^sub>\<circ> ?ABC\<lparr>ArrVal\<rparr>"
              unfolding abc_abc''_def abc_def abc'_def abc''_def ab'_def ab_def
              by (intro vcompI prod_2_Rel_ArrValI)
                (
                  cs_concl 
                    cs_simp: cat_cs_simps 
                    cs_intro: 
                      vsv.vsv_ex1_app2[THEN iffD1] 
                      V_cs_intros 
                      cat_cs_intros 
                      cat_Rel_cs_intros
                )+
          next
            fix abc_abc'' assume prems: "abc_abc'' \<in>\<^sub>\<circ> ?H_GF \<circ>\<^sub>\<circ> ?ABC\<lparr>ArrVal\<rparr>"
            then obtain abc abc' abc'' 
              where abc_abc''_def: "abc_abc'' = \<langle>abc, abc''\<rangle>"
                and abc_abc': "\<langle>abc, abc'\<rangle> \<in>\<^sub>\<circ> ?ABC\<lparr>ArrVal\<rparr>"
                and abc'_abc'': "\<langle>abc', abc''\<rangle> \<in>\<^sub>\<circ> ?H_GF"
              by clarsimp
            from abc'_abc'' obtain a' bc' a'' bc'' 
              where abc'_abc''_def: "\<langle>abc', abc''\<rangle> = \<langle>\<langle>a', bc'\<rangle>, \<langle>a'', bc''\<rangle>\<rangle>"
                and aa'': "\<langle>a', a''\<rangle> \<in>\<^sub>\<circ> H\<lparr>ArrVal\<rparr>"
                and bc'_bc'':
                  "\<langle>bc', bc''\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal (G\<lparr>ArrVal\<rparr>) (F\<lparr>ArrVal\<rparr>)"
              by auto
            then have abc'_def: "abc' = \<langle>a', bc'\<rangle>" 
              and abc''_def: "abc'' = \<langle>a'', bc''\<rangle>" 
              by auto
            from bc'_bc'' obtain b' c' b'' c''
              where bc'_bc''_def: "\<langle>bc', bc''\<rangle> = \<langle>\<langle>b', c'\<rangle>, \<langle>b'', c''\<rangle>\<rangle>"
                and bb'': "\<langle>b', b''\<rangle> \<in>\<^sub>\<circ> G\<lparr>ArrVal\<rparr>"
                and cc'': "\<langle>c', c''\<rangle> \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr>"
              by auto
            then have bc'_def: "bc' = \<langle>b', c'\<rangle>" 
              and bc''_def: "bc'' = \<langle>b'', c''\<rangle>"  
              by auto
            from cc'' F.arr_Rel_ArrVal_vdomain F.arr_Rel_ArrVal_vrange 
            have c': "c' \<in>\<^sub>\<circ> C" and c'': "c'' \<in>\<^sub>\<circ> C'"
              by auto
            from bb'' G.arr_Rel_ArrVal_vdomain G.arr_Rel_ArrVal_vrange 
            have b': "b' \<in>\<^sub>\<circ> B" and b'': "b'' \<in>\<^sub>\<circ> B'"
              by auto
            from aa'' H.arr_Rel_ArrVal_vdomain H.arr_Rel_ArrVal_vrange 
            have a': "a' \<in>\<^sub>\<circ> A" and a'': "a'' \<in>\<^sub>\<circ> A'"
              by auto
            from abc_abc' have "abc \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (?ABC\<lparr>ArrVal\<rparr>)" by auto
            then have "abc \<in>\<^sub>\<circ> (A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C" by (simp add: cat_cs_simps)
            then obtain a b c
              where abc_def: "abc = \<langle>\<langle>a, b\<rangle>, c\<rangle>"
                and a: "a \<in>\<^sub>\<circ> A"
                and b: "b \<in>\<^sub>\<circ> B"
                and c: "c \<in>\<^sub>\<circ> C"
              by auto
            from abc_abc' have "abc' = ?ABC\<lparr>ArrVal\<rparr>\<lparr>abc\<rparr>"
              by (simp add: vsv.vsv_appI[OF M\<alpha>_Rel_arrow_lr_ArrVal_vsv])
            also from a b c have "\<dots> = \<langle>a, \<langle>b, c\<rangle>\<rangle>"
              unfolding abc_def bc'_def
              by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
            finally have abc'_def': "abc' = \<langle>a, \<langle>b, c\<rangle>\<rangle>" by auto
            with abc'_def[unfolded bc'_def] have [cat_cs_simps]:
              "a = a'" "b = b'" "c = c'"
              by auto
            from a'' b'' c'' have "\<langle>\<langle>a'', b''\<rangle>, c''\<rangle> \<in>\<^sub>\<circ> (A' \<times>\<^sub>\<circ> B') \<times>\<^sub>\<circ> C'"
              by (cs_concl cs_intro: V_cs_intros)
            with aa'' bb'' cc'' a a' b b' c c' show 
              "abc_abc'' \<in>\<^sub>\<circ> ?ABC'\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?HG_F"
              unfolding abc_abc''_def abc_def abc'_def abc''_def bc''_def
              by (intro vcompI prod_2_Rel_ArrValI)
               (
                 cs_concl 
                  cs_simp: cat_cs_simps 
                  cs_intro: 
                    vsv.vsv_ex1_app2[THEN iffD1] 
                    V_cs_intros cat_cs_intros cat_Rel_cs_intros
               )+
          qed

          from that H_is_arr G_is_arr F_is_arr show 
            "(?ABC' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel (prod_2_Rel H G) F)\<lparr>ArrVal\<rparr> =
              (prod_2_Rel H (prod_2_Rel G F) \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?ABC)\<lparr>ArrVal\<rparr>"
            by
              (
                cs_concl
                  cs_simp:
                    prod_2_Rel_components comp_Rel_components
                    cat_Rel_cs_simps cat_cs_simps 
                  cs_intro: 
                    cat_Rel_par_set_cs_intros cat_cs_intros cat_prod_cs_intros
              )

        qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

      qed

      from that H_is_arr G_is_arr F_is_arr show ?thesis
        unfolding HGF_def ABC_def ABC'_def
        by 
          (
            cs_concl 
              cs_intro: 
                cat_Rel_par_set_cs_intros cat_cs_intros cat_prod_cs_intros 
              cs_simp: cat_Rel_cs_simps cat_cs_simps
          )

    qed

  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

qed

lemma (in \<Z>) M\<alpha>_Rel_is_iso_ntcf'[cat_cs_intros]: 
  assumes "\<FF>' = cf_blcomp (cf_prod_2_Rel (cat_Rel \<alpha>))"
    and "\<GG>' = cf_brcomp (cf_prod_2_Rel (cat_Rel \<alpha>))"
    and "\<AA>' = cat_Rel \<alpha>^\<^sub>C\<^sub>3"
    and "\<BB>' = cat_Rel \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "M\<alpha>_Rel (cat_Rel \<alpha>) : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule M\<alpha>_Rel_is_iso_ntcf)

lemmas [cat_cs_intros] = \<Z>.M\<alpha>_Rel_is_iso_ntcf'



subsection\<open>\<open>Ml\<close> and \<open>Mr\<close> for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition Ml_Rel :: "V \<Rightarrow> V \<Rightarrow> V"
  where "Ml_Rel \<CC> a =
    [
      (\<lambda>B\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. vsnd_arrow (set {a}) B),
      cf_prod_2_Rel \<CC>\<^bsub>\<CC>,\<CC>\<^esub>(set {a},-)\<^sub>C\<^sub>F,
      cf_id \<CC>,
      \<CC>,
      \<CC>
    ]\<^sub>\<circ>"

definition Mr_Rel :: "V \<Rightarrow> V \<Rightarrow> V"
  where "Mr_Rel \<CC> b =
    [
      (\<lambda>A\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. vfst_arrow A (set {b})),
      cf_prod_2_Rel \<CC>\<^bsub>\<CC>,\<CC>\<^esub>(-,set {b})\<^sub>C\<^sub>F,
      cf_id \<CC>,
      \<CC>,
      \<CC>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma Ml_Rel_components:
  shows "Ml_Rel \<CC> a\<lparr>NTMap\<rparr> = (\<lambda>B\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. vsnd_arrow (set {a}) B)"
    and [cat_cs_simps]: "Ml_Rel \<CC> a\<lparr>NTDom\<rparr> = cf_prod_2_Rel \<CC>\<^bsub>\<CC>,\<CC>\<^esub>(set {a},-)\<^sub>C\<^sub>F"
    and [cat_cs_simps]: "Ml_Rel \<CC> a\<lparr>NTCod\<rparr> = cf_id \<CC>"
    and [cat_cs_simps]: "Ml_Rel \<CC> a\<lparr>NTDGDom\<rparr> = \<CC>"
    and [cat_cs_simps]: "Ml_Rel \<CC> a\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding Ml_Rel_def nt_field_simps by (simp_all add: nat_omega_simps)

lemma Mr_Rel_components:
  shows "Mr_Rel \<CC> b\<lparr>NTMap\<rparr> = (\<lambda>A\<in>\<^sub>\<circ>\<CC>\<lparr>Obj\<rparr>. vfst_arrow A (set {b}))"
    and [cat_cs_simps]: "Mr_Rel \<CC> b\<lparr>NTDom\<rparr> = cf_prod_2_Rel \<CC>\<^bsub>\<CC>,\<CC>\<^esub>(-,set {b})\<^sub>C\<^sub>F"
    and [cat_cs_simps]: "Mr_Rel \<CC> b\<lparr>NTCod\<rparr> = cf_id \<CC>"
    and [cat_cs_simps]: "Mr_Rel \<CC> b\<lparr>NTDGDom\<rparr> = \<CC>"
    and [cat_cs_simps]: "Mr_Rel \<CC> b\<lparr>NTDGCod\<rparr> = \<CC>"
  unfolding Mr_Rel_def nt_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Natural transformation map\<close>

mk_VLambda Ml_Rel_components(1)
  |vsv Ml_Rel_components_NTMap_vsv[cat_cs_intros]|
  |vdomain Ml_Rel_components_NTMap_vdomain[cat_cs_simps]|
  |app Ml_Rel_components_NTMap_app[cat_cs_simps]|

mk_VLambda Mr_Rel_components(1)
  |vsv Mr_Rel_components_NTMap_vsv[cat_cs_intros]|
  |vdomain Mr_Rel_components_NTMap_vdomain[cat_cs_simps]|
  |app Mr_Rel_components_NTMap_app[cat_cs_simps]|


subsubsection\<open>\<open>Ml\<close> and \<open>Mr\<close> for \<open>Rel\<close> are natural isomorphisms\<close>

lemma (in \<Z>) Ml_Rel_is_iso_ntcf:
  assumes "a \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "Ml_Rel (cat_Rel \<alpha>) a:
    cf_prod_2_Rel (cat_Rel \<alpha>)\<^bsub>cat_Rel \<alpha>,cat_Rel \<alpha>\<^esub>(set {a},-)\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o 
    cf_id (cat_Rel \<alpha>) : 
    cat_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
proof-

  let ?cf_prod = \<open>cf_prod_2_Rel (cat_Rel \<alpha>)\<^bsub>cat_Rel \<alpha>,cat_Rel \<alpha>\<^esub> (set {a},-)\<^sub>C\<^sub>F\<close>
  note [cat_cs_simps] = set_empty

  interpret cf_prod: is_functor 
    \<alpha> \<open>cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> \<open>cf_prod_2_Rel (cat_Rel \<alpha>)\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_Rel_cs_intros)
  
  show ?thesis
  proof(intro is_iso_ntcfI is_ntcfI')
    show "vfsequence (Ml_Rel (cat_Rel \<alpha>) a)" unfolding Ml_Rel_def by auto
    show "vcard (Ml_Rel (cat_Rel \<alpha>) a) = 5\<^sub>\<nat>"
      unfolding Ml_Rel_def by (simp add: nat_omega_simps)
    from assms show "?cf_prod : cat_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
      by
        (
          cs_concl
            cs_simp: cat_Rel_components(1) cat_cs_simps 
            cs_intro: cat_cs_intros V_cs_intros
        )
    show "Ml_Rel (cat_Rel \<alpha>) a\<lparr>NTMap\<rparr>\<lparr>B\<rparr> :
      ?cf_prod\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> cf_id (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" for B 
      using assms that
      by
        (
          cs_concl
            cs_simp: cat_Rel_components(1) V_cs_simps cat_cs_simps 
            cs_intro:
              cat_Rel_par_set_cs_intros
              cat_cs_intros 
              V_cs_intros
              cat_prod_cs_intros
        )
    with cat_Rel_is_arr_isomorphismD[OF this] show 
      "Ml_Rel (cat_Rel \<alpha>) a\<lparr>NTMap\<rparr>\<lparr>B\<rparr> :
        ?cf_prod\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> cf_id (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" for B
      using that by simp
    show
      "Ml_Rel (cat_Rel \<alpha>) a\<lparr>NTMap\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?cf_prod\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
        cf_id (cat_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> Ml_Rel (cat_Rel \<alpha>) a\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
      if "F : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" for A B F 
    proof-
      note F = cat_Rel_is_arrD[OF that]
      interpret F: arr_Rel \<alpha> F
        rewrites "F\<lparr>ArrDom\<rparr> = A" and "F\<lparr>ArrCod\<rparr> = B"
        by (intro F)+
      have [cat_cs_simps]:
        "vsnd_arrow (set {a}) B \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> 
          prod_2_Rel (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>set {a}\<rparr>) F =
            F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> vsnd_arrow (set {a}) A"
        (is \<open>?B2 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?aF = F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A2\<close>)
      proof-
        from assms that have lhs:
          "?B2 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?aF : set {a} \<times>\<^sub>\<circ> A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B"
          by
            (
              cs_concl
                cs_simp: cat_Rel_components(1) cat_cs_simps
                cs_intro: cat_Rel_par_set_cs_intros cat_cs_intros V_cs_intros
            )
        from assms that have rhs:
          "F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A2 : set {a} \<times>\<^sub>\<circ> A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B"
          by
            (
              cs_concl
                cs_simp: cat_Rel_components(1) cat_cs_simps
                cs_intro: cat_Rel_par_set_cs_intros cat_cs_intros V_cs_intros
            )
        have [cat_cs_simps]: 
          "?B2\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal (vid_on (set {a})) (F\<lparr>ArrVal\<rparr>) =
            F\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?A2\<lparr>ArrVal\<rparr>"
        proof(intro vsubset_antisym vsubsetI)
          fix xx'_z assume "xx'_z \<in>\<^sub>\<circ>
            ?B2\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal (vid_on (set {a})) (F\<lparr>ArrVal\<rparr>)"
          then obtain xx' yy' z
            where xx'_z_def: "xx'_z = \<langle>xx', z\<rangle>" 
              and xx'_yy':
                "\<langle>xx', yy'\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal (vid_on (set {a})) (F\<lparr>ArrVal\<rparr>)"
              and yy'_z: "\<langle>yy', z\<rangle> \<in>\<^sub>\<circ> ?B2\<lparr>ArrVal\<rparr>" 
            by auto
          from xx'_yy' obtain x x' y y'
            where "\<langle>xx', yy'\<rangle> = \<langle>\<langle>x, x'\<rangle>, \<langle>y, y'\<rangle>\<rangle>"
              and "\<langle>x, y\<rangle> \<in>\<^sub>\<circ> vid_on (set {a})"
              and xy': "\<langle>x', y'\<rangle> \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr>"
            by auto
          then have xx'_def: "xx' = \<langle>a, x'\<rangle>" and yy'_def: "yy' = \<langle>a, y'\<rangle>"
            by simp_all
          with yy'_z have y': "y' \<in>\<^sub>\<circ> B" and z_def: "z = y'"
            unfolding vsnd_arrow_components by auto
          from xy' vsubsetD have x': "x' \<in>\<^sub>\<circ> A"
            by (auto intro: F.arr_Rel_ArrVal_vdomain)
          show "xx'_z \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?A2\<lparr>ArrVal\<rparr>"
            unfolding xx'_z_def z_def xx'_def
            by (intro vcompI, rule xy') 
              (auto simp: vsnd_arrow_components x' VLambda_iff2)
        next
          fix ay_z assume "ay_z \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?A2\<lparr>ArrVal\<rparr>"
          then obtain ay y z
            where xx'_z_def: "ay_z = \<langle>ay, z\<rangle>" 
              and ay_y: "\<langle>ay, y\<rangle> \<in>\<^sub>\<circ> ?A2\<lparr>ArrVal\<rparr>"
              and yz[cat_cs_intros]: "\<langle>y, z\<rangle> \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr>" 
            by auto
          then have ay_z_def: "ay_z = \<langle>\<langle>a, y\<rangle>, z\<rangle>"
            and y: "y \<in>\<^sub>\<circ> A"
            and ay_def: "ay = \<langle>a, y\<rangle>"
            unfolding vsnd_arrow_components by auto
          from yz vsubsetD have z: "z \<in>\<^sub>\<circ> B"
            by (auto intro: F.arr_Rel_ArrVal_vrange)
          have [cat_cs_intros]: "\<langle>a, a\<rangle> \<in>\<^sub>\<circ> vid_on (set {a})" by auto 
          show "ay_z \<in>\<^sub>\<circ>
            ?B2\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal (vid_on (set {a})) (F\<lparr>ArrVal\<rparr>)"
            unfolding ay_z_def
            by
              (
                intro vcompI prod_2_Rel_ArrValI, 
                rule vsv.vsv_ex1_app1[THEN iffD1], 
                unfold cat_cs_simps, 
                insert z
              )
              (
                cs_concl 
                  cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros
              )
        qed
        show ?thesis
        proof(rule arr_Rel_eqI)
          from lhs show arr_Rel_lhs: "arr_Rel \<alpha> (?B2 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?aF)"
            by (auto dest: cat_Rel_is_arrD)
          from rhs show "arr_Rel \<alpha> (F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A2)"
            by (auto dest: cat_Rel_is_arrD)
          note cat_Rel_CId_app[cat_Rel_cs_simps del]
          note \<Z>.cat_Rel_CId_app[cat_Rel_cs_simps del]
          from that assms show
            "(?B2 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?aF)\<lparr>ArrVal\<rparr> = (F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A2)\<lparr>ArrVal\<rparr>"
            by (*slow*)
              (
                cs_concl
                  cs_simp: cat_cs_simps cat_Rel_cs_simps
                  cs_intro: cat_cs_intros cat_Rel_par_set_cs_intros V_cs_intros
                  cs_simp: 
                    id_Rel_components 
                    cat_Rel_CId_app 
                    comp_Rel_components(1) 
                    prod_2_Rel_components 
                    cat_Rel_components(1)
              )
        qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
      qed
      from that assms show ?thesis
        by
          (
            cs_concl
              cs_simp: cat_cs_simps
              cs_intro: cat_cs_intros V_cs_intros cat_prod_cs_intros
              cs_simp: cat_Rel_components(1) V_cs_simps
          )
    qed
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

qed

lemma (in \<Z>) Ml_Rel_is_iso_ntcf'[cat_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "\<FF>' = cf_prod_2_Rel (cat_Rel \<alpha>)\<^bsub>cat_Rel \<alpha>,cat_Rel \<alpha>\<^esub>(set {a},-)\<^sub>C\<^sub>F"
    and "\<GG>' = cf_id (cat_Rel \<alpha>)"
    and "\<AA>' = cat_Rel \<alpha>"
    and "\<BB>' = cat_Rel \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "Ml_Rel (cat_Rel \<alpha>) a : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2-6) by (rule Ml_Rel_is_iso_ntcf)

lemmas [cat_cs_intros] = \<Z>.Ml_Rel_is_iso_ntcf'

lemma (in \<Z>) Mr_Rel_is_iso_ntcf:
  assumes "b \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "Mr_Rel (cat_Rel \<alpha>) b :
    cf_prod_2_Rel (cat_Rel \<alpha>)\<^bsub>cat_Rel \<alpha>,cat_Rel \<alpha>\<^esub>(-,set {b})\<^sub>C\<^sub>F \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o 
    cf_id (cat_Rel \<alpha>) : 
    cat_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
proof-

  let ?cf_prod = \<open>cf_prod_2_Rel (cat_Rel \<alpha>)\<^bsub>cat_Rel \<alpha>,cat_Rel \<alpha>\<^esub> (-,set {b})\<^sub>C\<^sub>F\<close>
  note [cat_cs_simps] = set_empty

  interpret cf_prod: is_functor 
    \<alpha> \<open>cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> \<open>cf_prod_2_Rel (cat_Rel \<alpha>)\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_Rel_cs_intros)
  
  show ?thesis
  proof(intro is_iso_ntcfI is_ntcfI')
    show "vfsequence (Mr_Rel (cat_Rel \<alpha>) b)" unfolding Mr_Rel_def by auto
    show "vcard (Mr_Rel (cat_Rel \<alpha>) b) = 5\<^sub>\<nat>"
      unfolding Mr_Rel_def by (simp add: nat_omega_simps)
    from assms show "?cf_prod : cat_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
      by
        (
          cs_concl
            cs_simp: cat_Rel_components(1) cat_cs_simps 
            cs_intro: cat_cs_intros V_cs_intros
        )
    show "Mr_Rel (cat_Rel \<alpha>) b\<lparr>NTMap\<rparr>\<lparr>B\<rparr> :
      ?cf_prod\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> cf_id (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" for B 
      using assms that
      by
        (
          cs_concl
            cs_simp: cat_Rel_components(1) V_cs_simps cat_cs_simps
            cs_intro:
              cat_cs_intros
              cat_Rel_par_set_cs_intros
              V_cs_intros
              cat_prod_cs_intros
        )
    with cat_Rel_is_arr_isomorphismD[OF this] show 
      "Mr_Rel (cat_Rel \<alpha>) b\<lparr>NTMap\<rparr>\<lparr>B\<rparr> :
        ?cf_prod\<lparr>ObjMap\<rparr>\<lparr>B\<rparr> \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> cf_id (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" for B
      using that by simp
    show
      "Mr_Rel (cat_Rel \<alpha>) b\<lparr>NTMap\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?cf_prod\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> =
        cf_id (cat_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> Mr_Rel (cat_Rel \<alpha>) b\<lparr>NTMap\<rparr>\<lparr>A\<rparr>"
      if "F : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" for A B F 
    proof-
      note F = cat_Rel_is_arrD[OF that]
      interpret F: arr_Rel \<alpha> F
        rewrites "F\<lparr>ArrDom\<rparr> = A" and "F\<lparr>ArrCod\<rparr> = B"
        by (intro F)+
      have [cat_cs_simps]:
        "vfst_arrow B (set {b}) \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub>
          prod_2_Rel F (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>set {b}\<rparr>) =
            F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> vfst_arrow A (set {b})"
        (is \<open>?B1 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?bF = F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A1\<close>)
      proof-
        from assms that have lhs:
          "?B1 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?bF : A \<times>\<^sub>\<circ> set {b} \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B"
          by
            (
              cs_concl
                cs_simp: cat_Rel_components(1) cat_cs_simps
                cs_intro: cat_cs_intros cat_Rel_par_set_cs_intros V_cs_intros
            )
        from assms that have rhs:
          "F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A1 : A \<times>\<^sub>\<circ> set {b} \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B"
          by
            (
              cs_concl
                cs_simp: cat_Rel_components(1) cat_cs_simps
                cs_intro: cat_cs_intros cat_Rel_par_set_cs_intros V_cs_intros
            )
        have [cat_cs_simps]: 
          "?B1\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal (F\<lparr>ArrVal\<rparr>) (vid_on (set {b})) =
            F\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?A1\<lparr>ArrVal\<rparr>"
        proof(intro vsubset_antisym vsubsetI)
          fix xx'_z assume "xx'_z \<in>\<^sub>\<circ>
            ?B1\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal (F\<lparr>ArrVal\<rparr>) (vid_on (set {b}))"
          then obtain xx' yy' z
            where xx'_z_def: "xx'_z = \<langle>xx', z\<rangle>" 
              and xx'_yy':
                "\<langle>xx', yy'\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal (F\<lparr>ArrVal\<rparr>) (vid_on (set {b}))"
              and yy'_z: "\<langle>yy', z\<rangle> \<in>\<^sub>\<circ> ?B1\<lparr>ArrVal\<rparr>" 
            by auto
          from xx'_yy' obtain x x' y y'
            where "\<langle>xx', yy'\<rangle> = \<langle>\<langle>x, x'\<rangle>, \<langle>y, y'\<rangle>\<rangle>"
              and "\<langle>x', y'\<rangle> \<in>\<^sub>\<circ> vid_on (set {b})"
              and xy: "\<langle>x, y\<rangle> \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr>"
            by auto
          then have xx'_def: "xx' = \<langle>x, b\<rangle>" and yy'_def: "yy' = \<langle>y, b\<rangle>"
            by simp_all
          with yy'_z have y': "y \<in>\<^sub>\<circ> B" and z_def: "z = y"
            unfolding vfst_arrow_components by auto
          from xy vsubsetD have x: "x \<in>\<^sub>\<circ> A"
            by (auto intro: F.arr_Rel_ArrVal_vdomain)
          show "xx'_z \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?A1\<lparr>ArrVal\<rparr>"
            unfolding xx'_z_def z_def xx'_def
            by (intro vcompI, rule xy) 
              (auto simp: vfst_arrow_components x VLambda_iff2)
        next
          fix xy_z assume "xy_z \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> ?A1\<lparr>ArrVal\<rparr>"
          then obtain xy y z
            where xx'_z_def: "xy_z = \<langle>xy, z\<rangle>" 
              and xy_y: "\<langle>xy, y\<rangle> \<in>\<^sub>\<circ> ?A1\<lparr>ArrVal\<rparr>"
              and yz[cat_cs_intros]: "\<langle>y, z\<rangle> \<in>\<^sub>\<circ> F\<lparr>ArrVal\<rparr>" 
            by auto
          then have xy_z_def: "xy_z = \<langle>\<langle>y, b\<rangle>, z\<rangle>"
            and y: "y \<in>\<^sub>\<circ> A"
            and xy_def: "xy = \<langle>y, b\<rangle>"
            unfolding vfst_arrow_components by auto
          from yz vsubsetD have z: "z \<in>\<^sub>\<circ> B"
            by (auto intro: F.arr_Rel_ArrVal_vrange)
          have [cat_cs_intros]: "\<langle>b, b\<rangle> \<in>\<^sub>\<circ> vid_on (set {b})" by auto 
          show "xy_z \<in>\<^sub>\<circ>
            ?B1\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal (F\<lparr>ArrVal\<rparr>) (vid_on (set {b}))"
            unfolding xy_z_def
            by
              (
                intro vcompI prod_2_Rel_ArrValI, 
                rule vsv.vsv_ex1_app1[THEN iffD1], 
                unfold cat_cs_simps, 
                insert z
              )
              (
                cs_concl
                  cs_simp: cat_cs_simps cs_intro: V_cs_intros cat_cs_intros
              )
        qed
        show ?thesis
        proof(rule arr_Rel_eqI)
          from lhs show arr_Rel_lhs: "arr_Rel \<alpha> (?B1 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?bF)"
            by (auto dest: cat_Rel_is_arrD)
          from rhs show "arr_Rel \<alpha> (F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A1)"
            by (auto dest: cat_Rel_is_arrD)
          note cat_Rel_CId_app[cat_Rel_cs_simps del]
          note \<Z>.cat_Rel_CId_app[cat_Rel_cs_simps del]
          from that assms show
            "(?B1 \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?bF)\<lparr>ArrVal\<rparr> = (F \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?A1)\<lparr>ArrVal\<rparr>"
            by (*slow*)
              (
                cs_concl 
                  cs_simp: cat_cs_simps cat_Rel_cs_simps 
                  cs_intro: cat_cs_intros cat_Rel_par_set_cs_intros V_cs_intros 
                  cs_simp:
                    id_Rel_components
                    cat_Rel_CId_app
                    comp_Rel_components(1) 
                    prod_2_Rel_components
                    cat_Rel_components(1)
              )
        qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
      qed
      from that assms show ?thesis
        by
          (
            cs_concl 
              cs_simp: cat_cs_simps 
              cs_intro: cat_cs_intros V_cs_intros cat_prod_cs_intros
              cs_simp: cat_Rel_components(1) V_cs_simps
          )
    qed
  qed (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)+

qed

lemma (in \<Z>) Mr_Rel_is_iso_ntcf'[cat_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "\<FF>' = cf_prod_2_Rel (cat_Rel \<alpha>)\<^bsub>cat_Rel \<alpha>,cat_Rel \<alpha>\<^esub>(-,set {b})\<^sub>C\<^sub>F"
    and "\<GG>' = cf_id (cat_Rel \<alpha>)"
    and "\<AA>' = cat_Rel \<alpha>"
    and "\<BB>' = cat_Rel \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "Mr_Rel (cat_Rel \<alpha>) b : \<FF>' \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o \<GG>' : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2-6) by (rule Mr_Rel_is_iso_ntcf)

lemmas [cat_cs_intros] = \<Z>.Mr_Rel_is_iso_ntcf'



subsection\<open>\<open>Rel\<close> as a monoidal category\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
For further information see
\cite{noauthor_wikipedia_2001}\footnote{\url{
https://en.wikipedia.org/wiki/Category_of_relations
}}.
\<close>

definition mcat_Rel :: "V \<Rightarrow> V \<Rightarrow> V"
  where "mcat_Rel \<alpha> a =
    [
      cat_Rel \<alpha>,
      cf_prod_2_Rel (cat_Rel \<alpha>),
      set {a},
      M\<alpha>_Rel (cat_Rel \<alpha>),
      Ml_Rel (cat_Rel \<alpha>) a,
      Mr_Rel (cat_Rel \<alpha>) a
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma mcat_Rel_components:
  shows "mcat_Rel \<alpha> a\<lparr>Mcat\<rparr> = cat_Rel \<alpha>"
    and "mcat_Rel \<alpha> a\<lparr>Mcf\<rparr> = cf_prod_2_Rel (cat_Rel \<alpha>)"
    and "mcat_Rel \<alpha> a\<lparr>Me\<rparr> = set {a}"
    and "mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr> = M\<alpha>_Rel (cat_Rel \<alpha>)"
    and "mcat_Rel \<alpha> a\<lparr>Ml\<rparr> = Ml_Rel (cat_Rel \<alpha>) a"
    and "mcat_Rel \<alpha> a\<lparr>Mr\<rparr> = Mr_Rel (cat_Rel \<alpha>) a"
  unfolding mcat_Rel_def mcat_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>\<open>Rel\<close> is a monoidal category\<close>

lemma (in \<Z>) 
  assumes "a \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "monoidal_category \<alpha> (mcat_Rel \<alpha> a)"
proof-

  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  interpret Par_Rel: wide_replete_subcategory \<alpha> \<open>cat_Par \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Par_cat_Rel)
  interpret Set_Rel: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Rel \<alpha>\<close> 
    by 
      ( 
        rule wr_subcat_trans
          [
            OF 
              Set_Par.wide_replete_subcategory_axioms 
              Par_Rel.wide_replete_subcategory_axioms
          ]
      )

  show ?thesis
  proof(rule monoidal_categoryI)
    show "vfsequence (mcat_Rel \<alpha> a)" unfolding mcat_Rel_def by auto
    show "category \<alpha> (mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>)"
      unfolding mcat_Rel_components by (cs_concl cs_intro: cat_cs_intros)
    show "mcat_Rel \<alpha> a\<lparr>Mcf\<rparr> :
      mcat_Rel \<alpha> a\<lparr>Mcat\<rparr> \<times>\<^sub>C mcat_Rel \<alpha> a\<lparr>Mcat\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>"
      unfolding mcat_Rel_components by (cs_concl cs_intro: cat_cs_intros)
    show "mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr> :
      cf_blcomp (mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>) \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o cf_brcomp (mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>) : 
      mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>^\<^sub>C\<^sub>3 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>"
      unfolding mcat_Rel_components by (cs_concl cs_intro: cat_cs_intros)
    from assms show "mcat_Rel \<alpha> a\<lparr>Ml\<rparr> :
      mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>,mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<^esub> (mcat_Rel \<alpha> a\<lparr>Me\<rparr>,-)\<^sub>C\<^sub>F
        \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o 
      cf_id (mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>) :
      mcat_Rel \<alpha> a\<lparr>Mcat\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>"
      unfolding mcat_Rel_components by (cs_concl cs_intro: cat_cs_intros)
    from assms show "mcat_Rel \<alpha> a\<lparr>Mr\<rparr> :
      mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>,mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<^esub> (-,mcat_Rel \<alpha> a\<lparr>Me\<rparr>)\<^sub>C\<^sub>F
        \<mapsto>\<^sub>C\<^sub>F\<^sub>.\<^sub>i\<^sub>s\<^sub>o 
      cf_id (mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>) : mcat_Rel \<alpha> a\<lparr>Mcat\<rparr> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>"
      unfolding mcat_Rel_components by (cs_concl cs_intro: cat_cs_intros)
    show "vcard (mcat_Rel \<alpha> a) = 6\<^sub>\<nat>"
      unfolding mcat_Rel_def by (simp add: nat_omega_simps)
    from assms show "mcat_Rel \<alpha> a\<lparr>Me\<rparr> \<in>\<^sub>\<circ> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>"
      unfolding mcat_Rel_components cat_Rel_components by force
    show
      "mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>A\<rparr> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^esub> 
        mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>B, C, D\<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<^esub> 
          mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>
            A, B \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^esub> C, D
            \<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<^esub> 
              (mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>A, B, C\<rparr>\<^sub>\<bullet> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^esub> 
                mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>D\<rparr>) = 
                  mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>
                    A, B, C \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^esub> D
                    \<rparr>\<^sub>\<bullet> \<circ>\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<^esub> 
                      mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>A \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^esub> B, C, D\<rparr>\<^sub>\<bullet>"
      if "A \<in>\<^sub>\<circ> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>"
        and "B \<in>\<^sub>\<circ> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>"
        and "C \<in>\<^sub>\<circ> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>"
        and "D \<in>\<^sub>\<circ> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>"
      for A B C D
    proof-

      have [cat_cs_simps]:
        "prod_2_Rel (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>) (M\<alpha>_Rel_arrow_lr B C D) \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub>
          (
            M\<alpha>_Rel_arrow_lr A (B \<times>\<^sub>\<circ> C) D \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub>
            prod_2_Rel (M\<alpha>_Rel_arrow_lr A B C) (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>D\<rparr>)
          ) =
            M\<alpha>_Rel_arrow_lr A B (C \<times>\<^sub>\<circ> D) \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub>
              M\<alpha>_Rel_arrow_lr (A \<times>\<^sub>\<circ> B) C D"
        (
          is 
            \<open>
              ?A_BCD \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> (?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?ABC_D) = 
              ?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> ?AB_C_D
            \<close>
        )
      proof-

        have [cat_cs_simps]:
          "prod_2_Rel (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>) (M\<alpha>_Rel_arrow_lr B C D) \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
            (
              ?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> 
              prod_2_Rel (M\<alpha>_Rel_arrow_lr A B C) (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>D\<rparr>)
            ) = ?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AB_C_D"
          (
            is 
              \<open>
                ?A_BCD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?ABC_D) = 
                ?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AB_C_D
              \<close>
          )
        proof-
          from that have lhs: 
            "?A_BCD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?ABC_D) :
              ((A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C) \<times>\<^sub>\<circ> D \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> B \<times>\<^sub>\<circ> C \<times>\<^sub>\<circ> D"
            unfolding mcat_Rel_components cat_Rel_components(1)
            by
              (
                cs_concl
                  cs_simp: cat_Set_components(1)
                  cs_intro: cat_rel_par_Set_cs_intros cat_cs_intros V_cs_intros
               )
          then have dom_lhs:
            "\<D>\<^sub>\<circ> ((?A_BCD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?ABC_D))\<lparr>ArrVal\<rparr>) = 
              ((A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C) \<times>\<^sub>\<circ> D"
            by (cs_concl cs_simp: cat_cs_simps)
          from that have rhs: "?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AB_C_D :
            ((A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C) \<times>\<^sub>\<circ> D \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> B \<times>\<^sub>\<circ> C \<times>\<^sub>\<circ> D"
            unfolding mcat_Rel_components cat_Rel_components(1)
            by
              (
                cs_concl
                  cs_simp: cat_Rel_components(1) cat_Set_components(1) 
                  cs_intro: 
                    cat_cs_intros V_cs_intros M\<alpha>_Rel_arrow_lr_is_cat_Set_arr' 
               )
          then have dom_rhs:
            "\<D>\<^sub>\<circ> ((?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AB_C_D)\<lparr>ArrVal\<rparr>) = 
              ((A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C) \<times>\<^sub>\<circ> D"
            by (cs_concl cs_simp: cat_cs_simps)
          show ?thesis
          proof(rule arr_Set_eqI)
            from lhs show arr_Set_lhs: 
              "arr_Set \<alpha> (?A_BCD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?ABC_D))"
              by (auto dest: cat_Set_is_arrD(1))
            from rhs show arr_Set_rhs:
              "arr_Set \<alpha> (?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AB_C_D)"
              by (auto dest: cat_Set_is_arrD(1))
            show 
              "(?A_BCD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> (?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?ABC_D))\<lparr>ArrVal\<rparr> =
                (?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AB_C_D)\<lparr>ArrVal\<rparr>"
            proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
              fix abcd assume prems: "abcd \<in>\<^sub>\<circ> ((A \<times>\<^sub>\<circ> B) \<times>\<^sub>\<circ> C) \<times>\<^sub>\<circ> D"
              then obtain a b c d 
                where abcd_def: "abcd = \<langle>\<langle>\<langle>a, b\<rangle>, c\<rangle>, d\<rangle>" 
                  and a: "a \<in>\<^sub>\<circ> A" 
                  and b: "b \<in>\<^sub>\<circ> B" 
                  and c: "c \<in>\<^sub>\<circ> C" 
                  and d: "d \<in>\<^sub>\<circ> D"
                by clarsimp
              from that prems a b c d show 
                "(
                  ?A_BCD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
                    (?A_BC_D \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?ABC_D)
                 )\<lparr>ArrVal\<rparr>\<lparr>abcd\<rparr> =
                  (?A_B_CD \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AB_C_D)\<lparr>ArrVal\<rparr>\<lparr>abcd\<rparr>"
                unfolding abcd_def mcat_Rel_components(1) cat_Rel_components(1)
                by (*slow*)
                  (
                    cs_concl
                      cs_simp: 
                        cat_Set_components(1) 
                        cat_cs_simps 
                        cat_rel_par_Set_cs_simps
                      cs_intro: 
                        cat_cs_intros cat_rel_par_Set_cs_intros V_cs_intros
                  )
            qed (use arr_Set_lhs arr_Set_rhs in auto)
          qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
        qed

        from assms that show ?thesis
          unfolding mcat_Rel_components cat_Rel_components(1)
          by
            (
              cs_concl
                cs_simp:
                  cat_cs_simps
                  cat_Rel_components(1)
                  cat_Set_components(1)
                  Set_Rel.subcat_CId[symmetric]
                  Set_Rel.subcat_Comp_simp[symmetric]
                cs_intro: cat_cs_intros cat_rel_par_Set_cs_intros V_cs_intros
            )+

      qed

      from that show ?thesis 
        unfolding mcat_Rel_components cat_Rel_components(1)
        by
          (
            cs_concl
              cs_simp: cat_Rel_components(1) cat_cs_simps
              cs_intro: 
                cat_cs_intros 
                cat_Rel_par_set_cs_intros
                V_cs_intros 
                cat_prod_cs_intros
          )
  
    qed

    show
      "mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>A\<rparr> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^esub>
        mcat_Rel \<alpha> a\<lparr>Ml\<rparr>\<lparr>NTMap\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<^esub>
          mcat_Rel \<alpha> a\<lparr>M\<alpha>\<rparr>\<lparr>NTMap\<rparr>\<lparr>A, mcat_Rel \<alpha> a\<lparr>Me\<rparr>, B\<rparr>\<^sub>\<bullet> =
            mcat_Rel \<alpha> a\<lparr>Mr\<rparr>\<lparr>NTMap\<rparr>\<lparr>A\<rparr> \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>mcat_Rel \<alpha> a\<lparr>Mcf\<rparr>\<^esub>
              mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>CId\<rparr>\<lparr>B\<rparr>"
      if "A \<in>\<^sub>\<circ> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> mcat_Rel \<alpha> a\<lparr>Mcat\<rparr>\<lparr>Obj\<rparr>" for A B 
    proof-
  
      note [cat_cs_simps] = set_empty
  
      have [cat_cs_simps]: 
        "prod_2_Rel (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>) (vsnd_arrow (set {a}) B) \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub>
          M\<alpha>_Rel_arrow_lr A (set {a}) B =
            prod_2_Rel (vfst_arrow A (set {a})) (cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>)"
        (is \<open>?A_aB \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AaB = ?Aa_B\<close>)
      proof-
        from assms that have lhs: 
          "?A_aB \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AaB : (A \<times>\<^sub>\<circ> set {a}) \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> B"
          unfolding mcat_Rel_components cat_Rel_components(1)
          by 
            (
              cs_concl 
                cs_simp: cat_cs_simps cat_Rel_components(1) cat_Set_components(1)
                cs_intro: cat_cs_intros cat_rel_par_Set_cs_intros V_cs_intros
            )
        then have dom_lhs: 
          "\<D>\<^sub>\<circ> ((?A_aB \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AaB)\<lparr>ArrVal\<rparr>) = (A \<times>\<^sub>\<circ> set {a}) \<times>\<^sub>\<circ> B"
          by (cs_concl cs_simp: cat_cs_simps)
        from assms that have rhs:
          "?Aa_B : (A \<times>\<^sub>\<circ> set {a}) \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A \<times>\<^sub>\<circ> B"
          unfolding mcat_Rel_components cat_Rel_components(1)
          by
            (
              cs_concl
                cs_simp: cat_cs_simps cat_Set_components(1)
                cs_intro: cat_cs_intros cat_rel_par_Set_cs_intros V_cs_intros
            )
        then have dom_rhs: "\<D>\<^sub>\<circ> (?Aa_B\<lparr>ArrVal\<rparr>) = (A \<times>\<^sub>\<circ> set {a}) \<times>\<^sub>\<circ> B"
          by (cs_concl cs_simp: cat_cs_simps)
        show ?thesis
        proof(rule arr_Set_eqI)
          from lhs show arr_Set_lhs: "arr_Set \<alpha> (?A_aB \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AaB)"
            by (auto dest: cat_Set_is_arrD(1))
          from rhs show arr_Set_rhs: "arr_Set \<alpha> ?Aa_B"
            by (auto dest: cat_Set_is_arrD(1))
          show "(?A_aB \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AaB)\<lparr>ArrVal\<rparr> = ?Aa_B\<lparr>ArrVal\<rparr>"
          proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
            fix xay assume "xay \<in>\<^sub>\<circ> (A \<times>\<^sub>\<circ> set {a}) \<times>\<^sub>\<circ> B"
            then obtain x y 
              where xay_def: "xay = \<langle>\<langle>x, a\<rangle>, y\<rangle>" and x: "x \<in>\<^sub>\<circ> A" and y: "y \<in>\<^sub>\<circ> B"
              by auto
            from assms that x y show 
              "(?A_aB \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?AaB)\<lparr>ArrVal\<rparr>\<lparr>xay\<rparr> = ?Aa_B\<lparr>ArrVal\<rparr>\<lparr>xay\<rparr>"
              unfolding xay_def mcat_Rel_components cat_Rel_components(1)
              by
                (
                  cs_concl
                    cs_simp:
                      cat_Rel_components(1) cat_Set_components(1)
                      cat_cs_simps cat_rel_par_Set_cs_simps 
                    cs_intro: 
                      cat_cs_intros cat_rel_par_Set_cs_intros V_cs_intros
                )
          qed (use arr_Set_lhs arr_Set_rhs in auto)
        qed (use lhs rhs in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
      qed
  
      from assms that show ?thesis
        unfolding mcat_Rel_components cat_Rel_components(1)
        by
          (
            cs_concl
              cs_simp: 
                cat_cs_simps 
                cat_Rel_components(1) 
                cat_Set_components(1) 
                Set_Rel.subcat_CId[symmetric] 
                Set_Rel.subcat_Comp_simp[symmetric] 
              cs_intro:
                cat_cs_intros 
                cat_rel_par_Set_cs_intros
                V_cs_intros 
                cat_prod_cs_intros 
                Set_Rel.subcat_is_arrD
          )
  
    qed
  
  qed auto

qed

text\<open>\newpage\<close>

end