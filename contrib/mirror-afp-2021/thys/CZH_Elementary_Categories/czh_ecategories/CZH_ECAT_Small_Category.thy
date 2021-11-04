(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Smallness for categories\<close>
theory CZH_ECAT_Small_Category
  imports 
    CZH_Foundations.CZH_SMC_Small_Semicategory
    CZH_ECAT_Category
begin



subsection\<open>Background\<close>


text\<open>
An explanation of the methodology chosen for the exposition of all
matters related to the size of the categories and associated entities
is given in \cite{milehins_category_2021}.
\<close>

named_theorems cat_small_cs_simps
named_theorems cat_small_cs_intros



subsection\<open>Tiny category\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale tiny_category = \<Z> \<alpha> + vfsequence \<CC> + CId: vsv \<open>\<CC>\<lparr>CId\<rparr>\<close> for \<alpha> \<CC> +
  assumes tiny_cat_length[cat_cs_simps]: "vcard \<CC> = 6\<^sub>\<nat>"
    and tiny_cat_tiny_semicategory[slicing_intros]: 
      "tiny_semicategory \<alpha> (cat_smc \<CC>)"
    and tiny_cat_CId_vdomain[cat_cs_simps]: "\<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    and tiny_cat_CId_is_arr[cat_cs_intros]: 
      "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and tiny_cat_CId_left_left[cat_cs_simps]:
      "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f"
    and tiny_cat_CId_right_left[cat_cs_simps]:
      "f : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<Longrightarrow> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"

lemmas [slicing_intros] = tiny_category.tiny_cat_tiny_semicategory


text\<open>Rules.\<close>

lemma (in tiny_category) tiny_category_axioms'[cat_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "tiny_category \<alpha>' \<CC>"
  unfolding assms by (rule tiny_category_axioms)

mk_ide rf tiny_category_def[unfolded tiny_category_axioms_def]
  |intro tiny_categoryI|
  |dest tiny_categoryD[dest]|
  |elim tiny_categoryE[elim]|

lemma tiny_categoryI':
  assumes "category \<alpha> \<CC>" and "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" and "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tiny_category \<alpha> \<CC>"
proof-
  interpret category \<alpha> \<CC> by (rule assms(1))
  show ?thesis
  proof(intro tiny_categoryI)
    from assms show "tiny_semicategory \<alpha> (cat_smc \<CC>)"
      by (intro tiny_semicategoryI') (auto simp: slicing_simps)
  qed (auto simp: vfsequence_axioms cat_cs_simps cat_cs_intros)
qed

lemma tiny_categoryI'':
  assumes "\<Z> \<alpha>"
    and "vfsequence \<CC>"
    and "vcard \<CC> = 6\<^sub>\<nat>"
    and "vsv (\<CC>\<lparr>Dom\<rparr>)"
    and "vsv (\<CC>\<lparr>Cod\<rparr>)"
    and "vsv (\<CC>\<lparr>Comp\<rparr>)"
    and "vsv (\<CC>\<lparr>CId\<rparr>)"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<And>gf. gf \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Comp\<rparr>) \<longleftrightarrow>
      (\<exists>g f b c a. gf = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b)"
    and "\<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    and "\<And>b c g a f. \<lbrakk> g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "\<And>c d h b g a f. \<lbrakk> h : c \<mapsto>\<^bsub>\<CC>\<^esub> d; g : b \<mapsto>\<^bsub>\<CC>\<^esub> c; f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<rbrakk> \<Longrightarrow>
      (h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
    and "\<And>a. a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and "\<And>a b f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f"
    and "\<And>b c f. f : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<Longrightarrow> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"
    and "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "tiny_category \<alpha> \<CC>"
  by (intro tiny_categoryI tiny_semicategoryI'', unfold slicing_simps) 
    (simp_all add: cat_smc_def nat_omega_simps assms)


text\<open>Slicing.\<close>

context tiny_category
begin

interpretation smc: tiny_semicategory \<alpha> \<open>cat_smc \<CC>\<close>
  by (rule tiny_cat_tiny_semicategory) 

lemmas_with [unfolded slicing_simps]:
  tiny_cat_semicategory = smc.semicategory_axioms
  and tiny_cat_Obj_in_Vset[cat_small_cs_intros] = smc.tiny_smc_Obj_in_Vset
  and tiny_cat_Arr_in_Vset[cat_small_cs_intros] = smc.tiny_smc_Arr_in_Vset
  and tiny_cat_Dom_in_Vset[cat_small_cs_intros] = smc.tiny_smc_Dom_in_Vset
  and tiny_cat_Cod_in_Vset[cat_small_cs_intros] = smc.tiny_smc_Cod_in_Vset
  and tiny_cat_Comp_in_Vset[cat_small_cs_intros] = smc.tiny_smc_Comp_in_Vset

end


text\<open>Elementary properties.\<close>

sublocale tiny_category \<subseteq> category
  by (rule categoryI) 
    (
      auto simp: 
        vfsequence_axioms tiny_cat_semicategory cat_cs_intros cat_cs_simps
    )

lemmas (in tiny_category) tiny_dg_category = category_axioms

lemmas [cat_small_cs_intros] = tiny_category.tiny_dg_category


text\<open>Size.\<close>

lemma (in tiny_category) tiny_cat_CId_in_Vset: "\<CC>\<lparr>CId\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from tiny_cat_Obj_in_Vset have "\<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (simp add: tiny_cat_Obj_in_Vset cat_cs_simps)
  moreover from tiny_cat_Arr_in_Vset cat_CId_vrange tiny_cat_Arr_in_Vset have 
    "\<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"  
    by auto
  ultimately show ?thesis by (blast intro: \<Z>_Limit_\<alpha>\<omega>)
qed

lemma (in tiny_category) tiny_cat_in_Vset: "\<CC> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [cat_cs_intros] = 
    tiny_cat_Obj_in_Vset 
    tiny_cat_Arr_in_Vset
    tiny_cat_Dom_in_Vset
    tiny_cat_Cod_in_Vset
    tiny_cat_Comp_in_Vset
    tiny_cat_CId_in_Vset
  show ?thesis by (subst cat_def) (cs_concl cs_intro: cat_cs_intros V_cs_intros)
qed

lemma tiny_category[simp]: "small {\<CC>. tiny_category \<alpha> \<CC>}"
proof(rule down)
  show "{\<CC>. tiny_category \<alpha> \<CC>} \<subseteq> elts (set {\<CC>. category \<alpha> \<CC>})" 
    by (auto intro: cat_small_cs_intros)
qed

lemma small_categories_vsubset_Vset: "set {\<CC>. tiny_category \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset \<alpha>" 
  by (rule vsubsetI) (simp_all add: tiny_category.tiny_cat_in_Vset)

lemma (in category) cat_tiny_category_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "tiny_category \<beta> \<CC>"
proof(intro tiny_categoryI)
  show "tiny_semicategory \<beta> (cat_smc \<CC>)"
    by 
      (
        rule semicategory.smc_tiny_semicategory_if_ge_Limit, 
        rule cat_semicategory;
        intro assms
      )
qed (auto simp:  assms(1) cat_cs_simps cat_cs_intros vfsequence_axioms)


subsubsection\<open>Opposite tiny category\<close>

lemma (in tiny_category) tiny_category_op: "tiny_category \<alpha> (op_cat \<CC>)"
  by (intro tiny_categoryI') 
    (auto simp: cat_op_simps cat_cs_intros cat_small_cs_intros)

lemmas tiny_category_op[cat_op_intros] = tiny_category.tiny_category_op



subsection\<open>Finite category\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
A definition of a finite category can be found in nLab 
\cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/finite+category}
}.
\<close>

(*TODO: implicit redundant assumption*)
locale finite_category = \<Z> \<alpha> + vfsequence \<CC> + CId: vsv \<open>\<CC>\<lparr>CId\<rparr>\<close> for \<alpha> \<CC> +
  assumes fin_cat_length[cat_cs_simps]: "vcard \<CC> = 6\<^sub>\<nat>"
    and fin_cat_finite_semicategory[slicing_intros]: 
      "finite_semicategory \<alpha> (cat_smc \<CC>)"
    and fin_cat_CId_vdomain[cat_cs_simps]: "\<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    and fin_cat_CId_is_arr[cat_cs_intros]: 
      "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and fin_cat_CId_left_left[cat_cs_simps]:
      "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f"
    and fin_cat_CId_right_left[cat_cs_simps]:
      "f : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<Longrightarrow> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"

lemmas [slicing_intros] = finite_category.fin_cat_finite_semicategory


text\<open>Rules.\<close>

lemma (in finite_category) fin_category_axioms'[cat_small_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "finite_category \<alpha>' \<CC>"
  unfolding assms by (rule finite_category_axioms)

mk_ide rf finite_category_def[unfolded finite_category_axioms_def]
  |intro finite_categoryI|
  |dest finite_categoryD[dest]|
  |elim finite_categoryE[elim]|

lemma finite_categoryI':
  assumes "category \<alpha> \<CC>"  and "vfinite (\<CC>\<lparr>Obj\<rparr>)" and "vfinite (\<CC>\<lparr>Arr\<rparr>)"
  shows "finite_category \<alpha> \<CC>"
proof-
  interpret category \<alpha> \<CC> by (rule assms(1))
  show ?thesis
  proof(intro finite_categoryI)
    from assms show "finite_semicategory \<alpha> (cat_smc \<CC>)"
      by (intro finite_semicategoryI') (auto simp: slicing_simps)
  qed (auto simp: vfsequence_axioms cat_cs_simps cat_cs_intros)
qed

lemma finite_categoryI'': 
  assumes "tiny_category \<alpha> \<CC>" and "vfinite (\<CC>\<lparr>Obj\<rparr>)" and "vfinite (\<CC>\<lparr>Arr\<rparr>)"
  shows "finite_category \<alpha> \<CC>"
  using assms by (intro finite_categoryI') (auto intro: cat_small_cs_intros)


text\<open>Slicing.\<close>

context finite_category
begin

interpretation smc: finite_semicategory \<alpha> \<open>cat_smc \<CC>\<close>
  by (rule fin_cat_finite_semicategory) 

lemmas_with [unfolded slicing_simps]:
  fin_cat_tiny_semicategory = smc.tiny_semicategory_axioms
  and fin_smc_Obj_vfinite[cat_small_cs_intros] = smc.fin_smc_Obj_vfinite
  and fin_smc_Arr_vfinite[cat_small_cs_intros] = smc.fin_smc_Arr_vfinite

end


text\<open>Elementary properties.\<close>

sublocale finite_category \<subseteq> tiny_category
  by (rule tiny_categoryI) 
    (
      auto 
        simp: vfsequence_axioms 
        intro:
          cat_cs_intros cat_cs_simps cat_small_cs_intros
          finite_category.fin_cat_tiny_semicategory
    )

lemmas (in finite_category) fin_cat_tiny_category = tiny_category_axioms

lemmas [cat_small_cs_intros] = finite_category.fin_cat_tiny_category

lemma (in finite_category) fin_cat_in_Vset: "\<CC> \<in>\<^sub>\<circ> Vset \<alpha>"
  by (rule tiny_cat_in_Vset)


text\<open>Size.\<close>

lemma small_finite_categories[simp]: "small {\<CC>. finite_category \<alpha> \<CC>}"
proof(rule down)
  show "{\<CC>. finite_category \<alpha> \<CC>} \<subseteq> elts (set {\<CC>. tiny_category  \<alpha> \<CC>})" 
    by (auto intro: cat_small_cs_intros)
qed

lemma small_finite_categories_vsubset_Vset: 
  "set {\<CC>. finite_category \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset \<alpha>" 
  by (rule vsubsetI) (simp_all add: finite_category.fin_cat_in_Vset)


subsubsection\<open>Opposite finite category\<close>

lemma (in finite_category) finite_category_op: "finite_category \<alpha> (op_cat \<CC>)"
  by (intro finite_categoryI', unfold cat_op_simps) 
    (auto simp: cat_cs_intros cat_small_cs_intros)

lemmas finite_category_op[cat_op_intros] = finite_category.finite_category_op

text\<open>\newpage\<close>

end