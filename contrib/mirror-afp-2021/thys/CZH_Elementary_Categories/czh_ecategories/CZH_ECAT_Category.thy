(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Category\<close>
theory CZH_ECAT_Category
  imports 
    CZH_ECAT_Introduction
    CZH_Foundations.CZH_SMC_Semicategory
begin



subsection\<open>Background\<close>

lemmas [cat_cs_simps] = dg_shared_cs_simps
lemmas [cat_cs_intros] = dg_shared_cs_intros

definition CId :: V
  where [dg_field_simps]: "CId = 5\<^sub>\<nat>"



subsubsection\<open>Slicing\<close>

definition cat_smc :: "V \<Rightarrow> V"
  where "cat_smc \<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_smc_components[slicing_simps]:
  shows "cat_smc \<CC>\<lparr>Obj\<rparr> = \<CC>\<lparr>Obj\<rparr>"
    and "cat_smc \<CC>\<lparr>Arr\<rparr> = \<CC>\<lparr>Arr\<rparr>"
    and "cat_smc \<CC>\<lparr>Dom\<rparr> = \<CC>\<lparr>Dom\<rparr>"
    and "cat_smc \<CC>\<lparr>Cod\<rparr> = \<CC>\<lparr>Cod\<rparr>"
    and "cat_smc \<CC>\<lparr>Comp\<rparr> = \<CC>\<lparr>Comp\<rparr>"
  unfolding cat_smc_def dg_field_simps by (auto simp: nat_omega_simps)


text\<open>Regular definitions.\<close>

lemma cat_smc_is_arr[slicing_simps]: 
  "f : a \<mapsto>\<^bsub>cat_smc \<CC>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding is_arr_def slicing_simps ..

lemmas [slicing_intros] = cat_smc_is_arr[THEN iffD2]

lemma cat_smc_composable_arrs[slicing_simps]:
  "composable_arrs (cat_smc \<CC>) = composable_arrs \<CC>"
  unfolding composable_arrs_def slicing_simps ..

lemma cat_smc_is_monic_arr[slicing_simps]: 
  "f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>cat_smc \<CC>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> b"
  unfolding is_monic_arr_def slicing_simps ..

lemmas [slicing_intros] = cat_smc_is_monic_arr[THEN iffD2]

lemma cat_smc_is_epic_arr[slicing_simps]: 
  "f : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>cat_smc \<CC>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  unfolding is_epic_arr_def slicing_simps op_smc_def 
  by (simp add: nat_omega_simps)

lemmas [slicing_intros] = cat_smc_is_epic_arr[THEN iffD2]

lemma cat_smc_is_idem_arr[slicing_simps]:
  "f : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<^bsub>cat_smc \<CC>\<^esub> b \<longleftrightarrow> f : \<mapsto>\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<CC>\<^esub> b"
  unfolding is_idem_arr_def slicing_simps ..

lemmas [slicing_intros] = cat_smc_is_idem_arr[THEN iffD2]

lemma cat_smc_obj_terminal[slicing_simps]:
  "obj_terminal (cat_smc \<CC>) a \<longleftrightarrow> obj_terminal \<CC> a"
  unfolding obj_terminal_def slicing_simps ..

lemmas [slicing_intros] = cat_smc_obj_terminal[THEN iffD2]

lemma cat_smc_obj_intial[slicing_simps]:
  "obj_initial (cat_smc \<CC>) a \<longleftrightarrow> obj_initial \<CC> a"
  unfolding obj_initial_def obj_terminal_def 
  unfolding smc_op_simps slicing_simps
  ..

lemmas [slicing_intros] = cat_smc_obj_intial[THEN iffD2]

lemma cat_smc_obj_null[slicing_simps]: 
  "obj_null (cat_smc \<CC>) a \<longleftrightarrow> obj_null \<CC> a"
  unfolding obj_null_def slicing_simps smc_op_simps ..

lemmas [slicing_intros] = cat_smc_obj_null[THEN iffD2]

lemma cat_smc_is_zero_arr[slicing_simps]:
  "f : a \<mapsto>\<^sub>0\<^bsub>cat_smc \<CC>\<^esub> b \<longleftrightarrow> f : a \<mapsto>\<^sub>0\<^bsub>\<CC>\<^esub> b"
  unfolding is_zero_arr_def slicing_simps ..

lemmas [slicing_intros] = cat_smc_is_zero_arr[THEN iffD2]



subsection\<open>Definition and elementary properties\<close>


text\<open>
The definition of a category that is used in this work is
is similar to the definition that can be found in Chapter I-2 in 
\cite{mac_lane_categories_2010}. The amendments to the definitions that are 
associated with size have already been explained in 
\cite{milehins_category_2021}.
\<close>

locale category = \<Z> \<alpha> + vfsequence \<CC> + CId: vsv \<open>\<CC>\<lparr>CId\<rparr>\<close> for \<alpha> \<CC> +
  assumes cat_length[cat_cs_simps]: "vcard \<CC> = 6\<^sub>\<nat>"
    and cat_semicategory[slicing_intros]: "semicategory \<alpha> (cat_smc \<CC>)"
    and cat_CId_vdomain[cat_cs_simps]: "\<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) = \<CC>\<lparr>Obj\<rparr>"
    and cat_CId_is_arr[cat_cs_intros]: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and cat_CId_left_left[cat_cs_simps]: 
      "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<Longrightarrow> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = f"
    and cat_CId_right_left[cat_cs_simps]: 
      "f : b \<mapsto>\<^bsub>\<CC>\<^esub> c \<Longrightarrow> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"

lemmas [cat_cs_simps] = 
  category.cat_length
  category.cat_CId_vdomain
  category.cat_CId_left_left
  category.cat_CId_right_left

lemma (in category) cat_CId_is_arr'[cat_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b = a" and "c = a" and "\<CC>' = \<CC>"
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : b \<mapsto>\<^bsub>\<CC>'\<^esub> c"
  using assms(1) unfolding assms(2-4) by (rule cat_CId_is_arr)

lemmas [cat_cs_intros] = category.cat_CId_is_arr'

lemma (in category) cat_CId_is_arr''[cat_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
  shows "f : a \<mapsto>\<^bsub>\<CC>\<^esub> a"
  using assms(1) unfolding assms(2) by (cs_concl cs_intro: cat_cs_intros)

lemmas [cat_cs_intros] = category.cat_CId_is_arr''

lemmas [slicing_intros] = category.cat_semicategory

lemma (in category) cat_CId_vrange: "\<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
proof
  fix f assume "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)"
  with cat_CId_vdomain obtain a where "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" 
    by (auto elim!: CId.vrange_atE)
  with cat_CId_is_arr show "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by auto
qed


text\<open>Rules.\<close>

lemma (in category) category_axioms'[cat_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "category \<alpha>' \<CC>"
  unfolding assms by (rule category_axioms)

mk_ide rf category_def[unfolded category_axioms_def]
  |intro categoryI|
  |dest categoryD[dest]|
  |elim categoryE[elim]|

lemma categoryI':
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
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "category \<alpha> \<CC>"
  by (intro categoryI semicategoryI', unfold cat_smc_components slicing_simps)
    (simp_all add: assms smc_dg_def nat_omega_simps cat_smc_def)

lemma categoryD':
  assumes "category \<alpha> \<CC>" 
  shows "\<Z> \<alpha>"
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
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  by 
    (
      simp_all add: 
        categoryD(2-9)[OF assms] 
        semicategoryD'[OF categoryD(5)[OF assms], unfolded slicing_simps]
    )

lemma categoryE':
  assumes "category \<alpha> \<CC>" 
  obtains "\<Z> \<alpha>"
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
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by (simp add: categoryD')


text\<open>Slicing.\<close>

context category
begin

interpretation smc: semicategory \<alpha> \<open>cat_smc \<CC>\<close> by (rule cat_semicategory)

sublocale Dom: vsv \<open>\<CC>\<lparr>Dom\<rparr>\<close> 
  by (rule smc.Dom.vsv_axioms[unfolded slicing_simps])
sublocale Cod: vsv \<open>\<CC>\<lparr>Cod\<rparr>\<close> 
  by (rule smc.Cod.vsv_axioms[unfolded slicing_simps])
sublocale Comp: pbinop \<open>\<CC>\<lparr>Arr\<rparr>\<close> \<open>\<CC>\<lparr>Comp\<rparr>\<close>
  by (rule smc.Comp.pbinop_axioms[unfolded slicing_simps])

lemmas_with [unfolded slicing_simps]:
  cat_Dom_vdomain[cat_cs_simps] = smc.smc_Dom_vdomain
  and cat_Dom_vrange = smc.smc_Dom_vrange
  and cat_Cod_vdomain[cat_cs_simps] = smc.smc_Cod_vdomain
  and cat_Cod_vrange = smc.smc_Cod_vrange
  and cat_Obj_vsubset_Vset = smc.smc_Obj_vsubset_Vset
  and cat_Hom_vifunion_in_Vset[cat_cs_intros] = smc.smc_Hom_vifunion_in_Vset
  and cat_Obj_if_Dom_vrange = smc.smc_Obj_if_Dom_vrange
  and cat_Obj_if_Cod_vrange = smc.smc_Obj_if_Cod_vrange
  and cat_is_arrD = smc.smc_is_arrD
  and cat_is_arrE[elim] = smc.smc_is_arrE
  and cat_in_ArrE[elim] = smc.smc_in_ArrE
  and cat_Hom_in_Vset[cat_cs_intros] = smc.smc_Hom_in_Vset
  and cat_Arr_vsubset_Vset = smc.smc_Arr_vsubset_Vset
  and cat_Dom_vsubset_Vset = smc.smc_Dom_vsubset_Vset
  and cat_Cod_vsubset_Vset = smc.smc_Cod_vsubset_Vset
  and cat_Obj_in_Vset = smc.smc_Obj_in_Vset
  and cat_in_Obj_in_Vset[cat_cs_intros] = smc.smc_in_Obj_in_Vset
  and cat_Arr_in_Vset = smc.smc_Arr_in_Vset
  and cat_in_Arr_in_Vset[cat_cs_intros] = smc.smc_in_Arr_in_Vset
  and cat_Dom_in_Vset = smc.smc_Dom_in_Vset
  and cat_Cod_in_Vset = smc.smc_Cod_in_Vset
  and cat_semicategory_if_ge_Limit = smc.smc_semicategory_if_ge_Limit
  and cat_Dom_app_in_Obj = smc.smc_Dom_app_in_Obj
  and cat_Cod_app_in_Obj = smc.smc_Cod_app_in_Obj
  and cat_Arr_vempty_if_Obj_vempty = smc.smc_Arr_vempty_if_Obj_vempty
  and cat_Dom_vempty_if_Arr_vempty = smc.smc_Dom_vempty_if_Arr_vempty
  and cat_Cod_vempty_if_Arr_vempty = smc.smc_Cod_vempty_if_Arr_vempty

lemmas [cat_cs_intros] = cat_is_arrD(2,3)

lemmas_with [unfolded slicing_simps slicing_commute]:
  cat_Comp_vdomain = smc.smc_Comp_vdomain
  and cat_Comp_is_arr[cat_cs_intros] = smc.smc_Comp_is_arr
  and cat_Comp_assoc[cat_cs_intros] = smc.smc_Comp_assoc
  and cat_Comp_vdomainI[cat_cs_intros] = smc.smc_Comp_vdomainI
  and cat_Comp_vdomainE[elim!] = smc.smc_Comp_vdomainE
  and cat_Comp_vdomain_is_composable_arrs = 
    smc.smc_Comp_vdomain_is_composable_arrs
  and cat_Comp_vrange = smc.smc_Comp_vrange
  and cat_Comp_vsubset_Vset = smc.smc_Comp_vsubset_Vset
  and cat_Comp_in_Vset = smc.smc_Comp_in_Vset
  and cat_Comp_vempty_if_Arr_vempty = smc.smc_Comp_vempty_if_Arr_vempty
  and cat_assoc_helper = smc.smc_assoc_helper
  and cat_pattern_rectangle_right = smc.smc_pattern_rectangle_right
  and cat_pattern_rectangle_left = smc.smc_pattern_rectangle_left
  and is_epic_arrI = smc.is_epic_arrI
  and is_epic_arrD[dest] = smc.is_epic_arrD
  and is_epic_arrE[elim!] = smc.is_epic_arrE
  and cat_comp_is_monic_arr[cat_arrow_cs_intros] = smc.smc_Comp_is_monic_arr
  and cat_comp_is_epic_arr[cat_arrow_cs_intros] = smc.smc_Comp_is_epic_arr
  and cat_comp_is_monic_arr_is_monic_arr =
    smc.smc_Comp_is_monic_arr_is_monic_arr
  and cat_is_zero_arr_comp_right[cat_arrow_cs_intros] = 
    smc.smc_is_zero_arr_Comp_right
  and cat_is_zero_arr_comp_left[cat_arrow_cs_intros] = 
    smc.smc_is_zero_arr_Comp_left

lemma cat_Comp_is_arr'[cat_cs_intros]:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "\<CC>' = \<CC>"
  shows "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>'\<^esub> c"
  using assms(1,2) unfolding assms(3) by (rule cat_Comp_is_arr)

end

lemmas [cat_cs_simps] = is_idem_arrD(2)

lemmas [cat_cs_simps] = category.cat_Comp_assoc

lemmas [cat_cs_intros] =
  category.cat_Comp_vdomainI
  category.cat_is_arrD(1-3)
  category.cat_Comp_is_arr'
  category.cat_Comp_is_arr

lemmas [cat_arrow_cs_intros] = 
  is_monic_arrD(1) 
  is_epic_arr_is_arr
  category.cat_comp_is_monic_arr
  category.cat_comp_is_epic_arr
  category.cat_is_zero_arr_comp_right
  category.cat_is_zero_arr_comp_left

lemmas [cat_cs_intros] = HomI
lemmas [cat_cs_simps] = in_Hom_iff


text\<open>Elementary properties.\<close>

lemma cat_eqI:
  assumes "category \<alpha> \<AA>" 
    and "category \<alpha> \<BB>"
    and "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>"
    and "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>"
    and "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>"
    and "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
    and "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>"
    and "\<AA>\<lparr>CId\<rparr> = \<BB>\<lparr>CId\<rparr>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> \<AA> = 6\<^sub>\<nat>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
    show "\<D>\<^sub>\<circ> \<AA> = \<D>\<^sub>\<circ> \<BB>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<AA> \<Longrightarrow> \<AA>\<lparr>a\<rparr> = \<BB>\<lparr>a\<rparr>" for a 
      by (unfold dom, elim_in_numeral, insert assms) (auto simp: dg_field_simps)
  qed auto
qed

lemma cat_smc_eqI:
  assumes "category \<alpha> \<AA>"
    and "category \<alpha> \<BB>"
    and "\<AA>\<lparr>CId\<rparr> = \<BB>\<lparr>CId\<rparr>"
    and "cat_smc \<AA> = cat_smc \<BB>"
  shows "\<AA> = \<BB>"
proof(rule cat_eqI[of \<alpha>])
  from assms(4) have 
    "cat_smc \<AA>\<lparr>Obj\<rparr> = cat_smc \<BB>\<lparr>Obj\<rparr>"
    "cat_smc \<AA>\<lparr>Arr\<rparr> = cat_smc \<BB>\<lparr>Arr\<rparr>"
    "cat_smc \<AA>\<lparr>Dom\<rparr> = cat_smc \<BB>\<lparr>Dom\<rparr>"
    "cat_smc \<AA>\<lparr>Cod\<rparr> = cat_smc \<BB>\<lparr>Cod\<rparr>" 
    "cat_smc \<AA>\<lparr>Comp\<rparr> = cat_smc \<BB>\<lparr>Comp\<rparr>" 
    by auto
  then show
    "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>"
    "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>"
    "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>"
    "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
    "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>" 
    unfolding slicing_simps by simp_all
qed (auto simp: assms)

lemma (in category) cat_def: 
  "\<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>, \<CC>\<lparr>CId\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<CC> = 6\<^sub>\<nat>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>, \<CC>\<lparr>CId\<rparr>]\<^sub>\<circ> = 6\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> \<CC> = \<D>\<^sub>\<circ> [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>, \<CC>\<lparr>CId\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<CC> \<Longrightarrow>
    \<CC>\<lparr>a\<rparr> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Comp\<rparr>, \<CC>\<lparr>CId\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" 
    for a
    unfolding dom_lhs
    by elim_in_numeral (simp_all add: dg_field_simps nat_omega_simps)
qed auto


text\<open>Size.\<close>

lemma (in category) cat_CId_vsubset_Vset: "\<CC>\<lparr>CId\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro vsubsetI)
  fix af assume "af \<in>\<^sub>\<circ> \<CC>\<lparr>CId\<rparr>"
  then obtain a f 
    where af_def: "af = \<langle>a, f\<rangle>" 
      and a: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)" 
      and f: "f \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>)"
    by (auto elim: CId.vbrelation_vinE)
  from a have "a \<in>\<^sub>\<circ> Vset \<alpha>" by (auto simp: cat_cs_simps intro: cat_cs_intros)
  from f cat_CId_vrange have "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by auto
  then have "f \<in>\<^sub>\<circ> Vset \<alpha>" by (auto simp: cat_cs_simps intro: cat_cs_intros)
  then show "af \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: af_def Limit_vpair_in_VsetI \<open>a \<in>\<^sub>\<circ> Vset \<alpha>\<close>)
qed

lemma (in category) cat_category_in_Vset_4: "\<CC> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], cat_cs_intros] =
    cat_Obj_vsubset_Vset
    cat_Arr_vsubset_Vset
    cat_Dom_vsubset_Vset
    cat_Cod_vsubset_Vset
    cat_Comp_vsubset_Vset
    cat_CId_vsubset_Vset
  show ?thesis
    by (subst cat_def, succ_of_numeral)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps 
          cs_intro: cat_cs_intros V_cs_intros
      )
qed

lemma (in category) cat_CId_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC>\<lparr>CId\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<Z> \<beta> by (rule assms(1))
  from assms have "\<D>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) \<in>\<^sub>\<circ> Vset \<beta>" 
    by (auto simp: cat_cs_simps cat_Obj_in_Vset)
  moreover from assms cat_CId_vrange have "\<R>\<^sub>\<circ> (\<CC>\<lparr>CId\<rparr>) \<in>\<^sub>\<circ> Vset \<beta>"  
    by (auto intro: cat_Arr_in_Vset)
  ultimately show ?thesis by (blast intro: \<Z>_Limit_\<alpha>\<omega>)
qed

lemma (in category) cat_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show ?thesis
  proof(rule vsv.vsv_Limit_vsv_in_VsetI)
    have dom: "\<D>\<^sub>\<circ> \<CC> = 6\<^sub>\<nat>" by (cs_concl cs_simp: cat_cs_simps V_cs_simps)
    from assms show "\<D>\<^sub>\<circ> \<CC> \<in>\<^sub>\<circ> Vset \<beta>"
      unfolding dom by (simp add: \<Z>.ord_of_nat_in_Vset)
    have "n \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<CC> \<Longrightarrow> \<CC>\<lparr>n\<rparr> \<in>\<^sub>\<circ> Vset \<beta>" for n
      unfolding dom
      by 
        (
          elim_in_numeral, 
          all\<open>rewrite in "\<hole> \<in>\<^sub>\<circ> _" dg_field_simps[symmetric]\<close>,
          insert assms
        )
        (
          auto simp:
            cat_Obj_in_Vset
            cat_Arr_in_Vset
            cat_Dom_in_Vset
            cat_Cod_in_Vset
            cat_Comp_in_Vset
            cat_CId_in_Vset
        )
    then show "\<R>\<^sub>\<circ> \<CC> \<subseteq>\<^sub>\<circ> Vset \<beta>" by (metis vsubsetI vrange_atD)
    show "vfinite (\<D>\<^sub>\<circ> \<CC>)" unfolding dom by auto
  qed (simp_all add: \<Z>_Limit_\<alpha>\<omega> vsv_axioms)
qed

lemma (in category) cat_category_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "category \<beta> \<CC>"
  by (rule categoryI)
    (
      auto 
        intro: cat_cs_intros 
        simp: cat_cs_simps assms vfsequence_axioms cat_semicategory_if_ge_Limit 
    )

lemma tiny_category[simp]: "small {\<CC>. category \<alpha> \<CC>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  from category.cat_in_Vset[of \<alpha>] show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>])
      (auto simp: True \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<CC>. category \<alpha> \<CC>} = {}" by auto
  then show ?thesis by simp
qed

lemma (in \<Z>) categories_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "set {\<CC>. category \<alpha> \<CC>} \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "set {\<CC>. category \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<CC> assume prems: "\<CC> \<in>\<^sub>\<circ> set {\<CC>. category \<alpha> \<CC>}"
    interpret category \<alpha> \<CC> using prems by simp
    show "\<CC> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
      unfolding VPow_iff by (rule cat_category_in_Vset_4)
  qed
  from assms(2) show "Vset (\<alpha> + 4\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed

lemma category_if_category:
  assumes "category \<beta> \<CC>"
    and "\<Z> \<alpha>"
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "category \<alpha> \<CC>"
proof-
  interpret category \<beta> \<CC> by (rule assms(1))
  interpret \<alpha>: \<Z> \<alpha> by (rule assms(2))
  show ?thesis
  proof(intro categoryI)
    show "vfsequence \<CC>" by (simp add: vfsequence_axioms)
    show "semicategory \<alpha> (cat_smc \<CC>)"
      by (rule semicategory_if_semicategory, unfold slicing_simps)
        (auto intro!: assms(1,3,4) slicing_intros)
  qed (auto intro: cat_cs_intros simp: cat_cs_simps)
qed


text\<open>Further elementary properties.\<close>

sublocale category \<subseteq> CId: v11 \<open>\<CC>\<lparr>CId\<rparr>\<close>
proof(rule vsv.vsv_valeq_v11I, unfold cat_cs_simps)
  fix a b assume prems:
    "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  have "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : b \<mapsto>\<^bsub>\<CC>\<^esub> b" "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<CC>\<^esub> a"  
    by (subst prems(3))
      (cs_concl cs_simp: cat_cs_simps cs_intro: prems(1,2) cat_cs_intros)+
  with prems show "a = b" by auto (*slow*)
qed auto

lemma (in category) cat_CId_vempty_if_Arr_vempty:
  assumes "\<CC>\<lparr>Arr\<rparr> = 0"
  shows "\<CC>\<lparr>CId\<rparr> = 0"
  using assms cat_CId_vrange by (auto intro: CId.vsv_vrange_vempty)



subsection\<open>Opposite category\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-2 in \cite{mac_lane_categories_2010}.\<close>

definition op_cat :: "V \<Rightarrow> V"
  where "op_cat \<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Dom\<rparr>, fflip (\<CC>\<lparr>Comp\<rparr>), \<CC>\<lparr>CId\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_cat_components:
  shows [cat_op_simps]: "op_cat \<CC>\<lparr>Obj\<rparr> = \<CC>\<lparr>Obj\<rparr>"
    and [cat_op_simps]: "op_cat \<CC>\<lparr>Arr\<rparr> = \<CC>\<lparr>Arr\<rparr>"
    and [cat_op_simps]: "op_cat \<CC>\<lparr>Dom\<rparr> = \<CC>\<lparr>Cod\<rparr>"
    and [cat_op_simps]: "op_cat \<CC>\<lparr>Cod\<rparr> = \<CC>\<lparr>Dom\<rparr>"
    and "op_cat \<CC>\<lparr>Comp\<rparr> = fflip (\<CC>\<lparr>Comp\<rparr>)"
    and [cat_op_simps]: "op_cat \<CC>\<lparr>CId\<rparr> = \<CC>\<lparr>CId\<rparr>"
  unfolding op_cat_def dg_field_simps by (auto simp: nat_omega_simps)

lemma op_cat_component_intros[cat_op_intros]:
  shows "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>"
    and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<Longrightarrow> f \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Arr\<rparr>"
  unfolding cat_op_simps by simp_all


text\<open>Slicing.\<close>

lemma cat_smc_op_cat[slicing_commute]: "op_smc (cat_smc \<CC>) = cat_smc (op_cat \<CC>)"
  unfolding cat_smc_def op_cat_def op_smc_def dg_field_simps
  by (simp add: nat_omega_simps)

lemma (in category) op_smc_op_cat[cat_op_simps]: "op_smc (op_cat \<CC>) = cat_smc \<CC>"
  using Comp.pbinop_fflip_fflip
  unfolding op_smc_def op_cat_def cat_smc_def dg_field_simps
  by (simp add: nat_omega_simps)

lemma op_cat_is_arr[cat_op_simps]: "f : b \<mapsto>\<^bsub>op_cat \<CC>\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding cat_op_simps is_arr_def by auto

lemmas [cat_op_intros] = op_cat_is_arr[THEN iffD2]

lemma op_cat_Hom[cat_op_simps]: "Hom (op_cat \<CC>) a b = Hom \<CC> b a"
  unfolding cat_op_simps by simp

lemma op_cat_obj_initial[cat_op_simps]: 
  "obj_initial (op_cat \<CC>) a \<longleftrightarrow> obj_terminal \<CC> a"
  unfolding obj_initial_def obj_terminal_def 
  unfolding smc_op_simps cat_op_simps 
  ..

lemmas [cat_op_intros] = op_cat_obj_initial[THEN iffD2]

lemma op_cat_obj_terminal[cat_op_simps]: 
  "obj_terminal (op_cat \<CC>) a \<longleftrightarrow> obj_initial \<CC> a"
  unfolding obj_initial_def obj_terminal_def 
  unfolding smc_op_simps cat_op_simps 
  ..

lemmas [cat_op_intros] = op_cat_obj_terminal[THEN iffD2]

lemma op_cat_obj_null[cat_op_simps]: "obj_null (op_cat \<CC>) a \<longleftrightarrow> obj_null \<CC> a"
  unfolding obj_null_def cat_op_simps by auto

lemmas [cat_op_intros] = op_cat_obj_null[THEN iffD2]

context category
begin

interpretation smc: semicategory \<alpha> \<open>cat_smc \<CC>\<close> by (rule cat_semicategory)

lemmas_with [unfolded slicing_simps slicing_commute]:
  op_cat_Comp_vrange[cat_op_simps] = smc.op_smc_Comp_vrange
  and op_cat_Comp[cat_op_simps] = smc.op_smc_Comp
  and op_cat_is_epic_arr[cat_op_simps] = smc.op_smc_is_epic_arr
  and op_cat_is_monic_arr[cat_op_simps] = smc.op_smc_is_monic_arr
  and op_cat_is_zero_arr[cat_op_simps] = smc.op_smc_is_zero_arr

end

lemmas [cat_op_simps] = 
  category.op_cat_Comp_vrange
  category.op_cat_Comp
  category.op_cat_is_epic_arr
  category.op_cat_is_monic_arr
  category.op_cat_is_zero_arr

context
  fixes \<CC> :: V
begin

lemmas_with [
  where \<CC>=\<open>cat_smc \<CC>\<close>, unfolded slicing_simps slicing_commute[symmetric]
  ]:   
  op_cat_Comp_vdomain[cat_op_simps] = op_smc_Comp_vdomain

end


text\<open>Elementary properties.\<close>

lemma op_cat_vsv[cat_op_intros]: "vsv (op_cat \<CC>)" unfolding op_cat_def by auto


subsubsection\<open>Further properties\<close>

lemma (in category) category_op[cat_cs_intros]: "category \<alpha> (op_cat \<CC>)"
proof(intro categoryI, unfold cat_op_simps)
  show "vfsequence (op_cat \<CC>)" unfolding op_cat_def by simp
  show "vcard (op_cat \<CC>) = 6\<^sub>\<nat>" 
    unfolding op_cat_def by (simp add: nat_omega_simps)
next
  fix f a b assume "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
  with category_axioms show "\<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> f = f"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
next
  fix f b c assume "f : c \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  with category_axioms show "f \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"
    by (cs_concl cs_simp: cat_cs_simps cat_op_simps cs_intro: cat_cs_intros)
qed 
  (
    auto simp:
      cat_cs_simps 
      cat_op_simps 
      slicing_commute[symmetric] 
      smc_op_intros 
      cat_cs_intros
      cat_semicategory 
  )

lemmas category_op[cat_op_intros] = category.category_op

lemma (in category) cat_op_cat_op_cat[cat_op_simps]: "op_cat (op_cat \<CC>) = \<CC>"
proof(rule cat_eqI, unfold cat_op_simps op_cat_components)
  show "category \<alpha> (op_cat (op_cat \<CC>))" 
    by (simp add: category.category_op category_op)
  show "fflip (fflip (\<CC>\<lparr>Comp\<rparr>)) = \<CC>\<lparr>Comp\<rparr>" by (rule Comp.pbinop_fflip_fflip)
qed (auto simp: cat_cs_intros)

lemmas cat_op_cat_op_cat[cat_op_simps] = category.cat_op_cat_op_cat

lemma eq_op_cat_iff[cat_op_simps]: 
  assumes "category \<alpha> \<AA>" and "category \<alpha> \<BB>"
  shows "op_cat \<AA> = op_cat \<BB> \<longleftrightarrow> \<AA> = \<BB>"
proof
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  assume prems: "op_cat \<AA> = op_cat \<BB>"
  show "\<AA> = \<BB>"
  proof(rule cat_eqI)
    show 
      "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>" 
      "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>" 
      "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>"
      "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
      "\<AA>\<lparr>Comp\<rparr> = \<BB>\<lparr>Comp\<rparr>"
      "\<AA>\<lparr>CId\<rparr> = \<BB>\<lparr>CId\<rparr>"
      by (metis \<AA>.cat_op_cat_op_cat \<BB>.cat_op_cat_op_cat prems)+
  qed (auto intro: cat_cs_intros)
qed auto



subsection\<open>Monic arrow and epic arrow\<close>

lemma (in category) cat_CId_is_monic_arr[cat_arrow_cs_intros]: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> a"
  using assms cat_CId_is_arr' cat_CId_left_left by (force intro!: is_monic_arrI)

lemmas [cat_arrow_cs_intros] = category.cat_CId_is_monic_arr

lemma (in category) cat_CId_is_epic_arr[cat_arrow_cs_intros]: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> a"
proof-
  from assms have "a \<in>\<^sub>\<circ> op_cat \<CC>\<lparr>Obj\<rparr>" unfolding cat_op_simps .
  from category.cat_CId_is_monic_arr[OF category_op this, unfolded cat_op_simps]
  show ?thesis.
qed

lemmas [cat_arrow_cs_intros] = category.cat_CId_is_epic_arr



subsection\<open>Right inverse and left inverse of an arrow\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition is_right_inverse :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_right_inverse \<CC> g f = 
    (\<exists>a b. g : b \<mapsto>\<^bsub>\<CC>\<^esub> a \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<and> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>)"

definition is_left_inverse :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_left_inverse \<CC> \<equiv> is_right_inverse (op_cat \<CC>)"


text\<open>Rules.\<close>

lemma is_right_inverseI:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  shows "is_right_inverse \<CC> g f"
  using assms unfolding is_right_inverse_def by auto

lemma is_right_inverseD[dest]:
  assumes "is_right_inverse \<CC> g f"
  shows "\<exists>a b. g : b \<mapsto>\<^bsub>\<CC>\<^esub> a \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<and> f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  using assms unfolding is_right_inverse_def by clarsimp

lemma is_right_inverseE[elim]:
  assumes "is_right_inverse \<CC> g f"
  obtains a b where "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    and "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  using assms by auto

lemma (in category) is_left_inverseI:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
  shows "is_left_inverse \<CC> g f"
proof-
  from assms(3) have "f \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    unfolding op_cat_Comp[OF assms(1,2)].
  from 
    is_right_inverseI[of \<open>op_cat \<CC>\<close>, unfolded cat_op_simps, OF assms(1,2) this]
  show ?thesis
    unfolding is_left_inverse_def .
qed

lemma (in category) is_left_inverseD[dest]:
  assumes "is_left_inverse \<CC> g f"
  shows "\<exists>a b. g : b \<mapsto>\<^bsub>\<CC>\<^esub> a \<and> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<and> g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
proof-
  from is_right_inverseD[OF assms[unfolded is_left_inverse_def]] obtain a b
    where "g : b \<mapsto>\<^bsub>op_cat \<CC>\<^esub> a" 
      and "f : a \<mapsto>\<^bsub>op_cat \<CC>\<^esub> b" 
      and fg: "f \<circ>\<^sub>A\<^bsub>op_cat \<CC>\<^esub> g = op_cat \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    by clarsimp
  then have g: "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and f: "f : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    unfolding cat_op_simps by simp_all
  moreover from fg have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    unfolding op_cat_Comp[OF g f] cat_op_simps by simp
  ultimately show ?thesis by blast  
qed

lemma (in category) is_left_inverseE[elim]:
  assumes "is_left_inverse \<CC> g f"
  obtains a b where "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in category) op_cat_is_left_inverse[cat_op_simps]:
  "is_left_inverse (op_cat \<CC>) g f \<longleftrightarrow> is_right_inverse \<CC> g f"
  unfolding is_left_inverse_def is_right_inverse_def cat_op_simps by simp

lemmas [cat_op_simps] = category.op_cat_is_left_inverse

lemmas [cat_op_intros] = category.op_cat_is_left_inverse[THEN iffD2]

lemma (in category) op_cat_is_right_inverse[cat_op_simps]:
  "is_right_inverse (op_cat \<CC>) g f \<longleftrightarrow> is_left_inverse \<CC> g f"
  unfolding is_left_inverse_def is_right_inverse_def cat_op_simps by simp

lemmas [cat_op_simps] = category.op_cat_is_right_inverse

lemmas [cat_op_intros] = category.op_cat_is_right_inverse[THEN iffD2]



subsection\<open>Inverse of an arrow\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition is_inverse :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_inverse \<CC> g f =
    (
      \<exists>a b.
        g : b \<mapsto>\<^bsub>\<CC>\<^esub> a \<and>
        f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<and>
        g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<and>
        f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>
    )"


text\<open>Rules.\<close>

lemma is_inverseI:
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    and "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  shows "is_inverse \<CC> g f"
  using assms unfolding is_inverse_def by auto

lemma is_inverseD[dest]: 
  assumes "is_inverse \<CC> g f"
  shows 
    "(
      \<exists>a b.
        g : b \<mapsto>\<^bsub>\<CC>\<^esub> a \<and>
        f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<and>
        g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> \<and>
        f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>
    )"
  using assms unfolding is_inverse_def by auto

lemma is_inverseE[elim]:
  assumes "is_inverse \<CC> g f"
  obtains a b where "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    and "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in category) op_cat_is_inverse[cat_op_simps]: 
  "is_inverse (op_cat \<CC>) g f \<longleftrightarrow> is_inverse \<CC> g f"
  by (rule iffI; unfold is_inverse_def cat_op_simps) (metis op_cat_Comp)+

lemmas [cat_op_simps] = category.op_cat_is_inverse

lemmas [cat_op_intros] = category.op_cat_is_inverse[THEN iffD2]

lemma is_inverse_sym: "is_inverse \<CC> g f \<longleftrightarrow> is_inverse \<CC> f g"
  unfolding is_inverse_def by auto

lemma (in category) cat_is_inverse_eq:
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "is_inverse \<CC> h f" and "is_inverse \<CC> g f"
  shows "h = g"
  using assms
proof(elim is_inverseE)
  fix a b a' b'
  assume prems: 
    "h : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
    "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    "h \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    "g : b' \<mapsto>\<^bsub>\<CC>\<^esub> a'" 
    "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'" 
    "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a'\<rparr>" 
  then have ab: "a' = a" "b' = b" by auto 
  from prems have gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" and g: "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a" 
    unfolding ab by simp_all
  from prems(1) have "h = (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h" 
    unfolding gf by (simp add: cat_cs_simps)
  also with category_axioms prems(1,2) g have "\<dots> = g"
    by (cs_concl cs_simp: prems(4) cat_cs_simps cs_intro: cat_cs_intros)
  finally show "h = g" by simp
qed

lemma is_inverse_Comp_CId_left:
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "is_inverse \<CC> g' g" and "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "g' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
  using assms by auto

lemma is_inverse_Comp_CId_right:
  assumes "is_inverse \<CC> g' g" and "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g' = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  by (metis assms is_arrD(3) is_inverseE)

lemma (in category) cat_is_inverse_Comp:
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes gbc[intro]: "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and fab[intro]: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and g'g[intro]: "is_inverse \<CC> g' g"
    and f'f[intro]: "is_inverse \<CC> f' f"
  shows "is_inverse \<CC> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g') (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
proof-
  from g'g gbc f'f fab have g'cb: "g' : c \<mapsto>\<^bsub>\<CC>\<^esub> b" and f'ba: "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    by (metis is_arrD(2,3) is_inverseD)+
  with assms have f'g': "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g' : c \<mapsto>\<^bsub>\<CC>\<^esub> a" and gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    by (auto intro: cat_Comp_is_arr)
  have ff': "is_inverse \<CC> f f'" using assms by (simp add: is_inverse_sym)
  note [simp] = 
    cat_Comp_assoc[symmetric, OF f'g' gbc fab] 
    cat_Comp_assoc[OF f'ba g'cb gbc]
    is_inverse_Comp_CId_left[OF g'g gbc]
    cat_Comp_assoc[symmetric, OF gf f'ba g'cb]
    cat_Comp_assoc[OF gbc fab f'ba]
    is_inverse_Comp_CId_left[OF ff' f'ba]
    cat_CId_right_left[OF f'ba]
    cat_CId_right_left[OF gbc]
  show ?thesis 
    by (intro is_inverseI, rule f'g', rule gf) 
      (auto intro: is_inverse_Comp_CId_left is_inverse_Comp_CId_right)
qed

lemma (in category) cat_is_inverse_Comp':
  assumes "g : b \<mapsto>\<^bsub>\<CC>\<^esub> c"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and "is_inverse \<CC> g' g"
    and "is_inverse \<CC> f' f"
    and "f'g' = f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g'"
    and "gf = g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  shows "is_inverse \<CC> f'g' gf"
  using assms(1-4) unfolding assms(5,6) by (intro cat_is_inverse_Comp)

lemmas [cat_cs_intros] = category.cat_is_inverse_Comp'

lemma is_inverse_is_right_inverse[dest]:
  assumes "is_inverse \<CC> g f" 
  shows "is_right_inverse \<CC> g f"
  using assms by (auto intro: is_right_inverseI)

lemma (in category) cat_is_inverse_is_left_inverse[dest]:
  assumes "is_inverse \<CC> g f" 
  shows "is_left_inverse \<CC> g f"
proof-
  interpret op: category \<alpha> \<open>op_cat \<CC>\<close> by (auto intro!: cat_cs_intros)
  from assms have "is_inverse (op_cat \<CC>) g f" by (simp add: cat_op_simps)
  from is_inverse_is_right_inverse[OF this] show ?thesis
    unfolding is_left_inverse_def .
qed

lemma (in category) cat_is_right_left_inverse_is_inverse:
  assumes "is_right_inverse \<CC> g f" "is_left_inverse \<CC> g f"
  shows "is_inverse \<CC> g f"
  using assms
proof(elim is_right_inverseE is_left_inverseE)
  fix a b c d assume prems:
    "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    "g : d \<mapsto>\<^bsub>\<CC>\<^esub> c"
    "f : c \<mapsto>\<^bsub>\<CC>\<^esub> d"
    "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>c\<rparr>"
  then have dbca: "d = b" "c = a" by auto
  note [cat_cs_simps] = prems(3,6)[unfolded dbca]
  from prems(1,2) show "is_inverse \<CC> g f"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros is_inverseI)
qed



subsection\<open>Isomorphism\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition is_arr_isomorphism :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_arr_isomorphism \<CC> a b f \<longleftrightarrow>
    (f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<and> (\<exists>g. is_inverse \<CC> g f))"

syntax "_is_arr_isomorphism" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  (\<open>_ : _ \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<index> _\<close> [51, 51, 51] 51)
translations "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b" \<rightleftharpoons> "CONST is_arr_isomorphism \<CC> a b f"


text\<open>Rules.\<close>

lemma is_arr_isomorphismI:
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "is_inverse \<CC> g f"
  shows "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  using assms unfolding is_arr_isomorphism_def by auto

lemma is_arr_isomorphismD[dest]:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "\<exists>g. is_inverse \<CC> g f"
  using assms unfolding is_arr_isomorphism_def by auto

lemma is_arr_isomorphismE[elim]:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  obtains g where "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "is_inverse \<CC> g f"
  using assms by force

lemma is_arr_isomorphismE':
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  obtains g where "g : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
    and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    and "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
proof-
  from assms obtain g where f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" "is_inverse \<CC> g f" by auto
  then have "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    and gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    and fg: "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    by auto
  then have g: "g : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a" 
    by (cs_concl cs_intro: is_inverseI is_arr_isomorphismI)
  from that f g gf fg show ?thesis by simp
qed


text\<open>Elementary properties.\<close>

lemma (in category) op_cat_is_arr_isomorphism[cat_op_simps]:
  "f : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>op_cat \<CC>\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  unfolding is_arr_isomorphism_def cat_op_simps by simp

lemmas [cat_op_simps] = category.op_cat_is_arr_isomorphism

lemmas [cat_op_intros] = category.op_cat_is_arr_isomorphism[THEN iffD2]

lemma (in category) is_arr_isomorphismI':
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    and "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    and "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    and "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
  shows "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b" and "g : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
proof-
  from assms have gf: "is_inverse \<CC> g f" by (auto intro: is_inverseI)
  from assms have fg: "is_inverse \<CC> f g" by (auto intro: is_inverseI)
  show "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b" and "g : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
    by 
      (
        intro 
          is_arr_isomorphismI[OF assms(1) gf]
          is_arr_isomorphismI[OF assms(2) fg]
      )+
qed

lemma (in category) cat_is_inverse_is_arr_isomorphism:
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "is_inverse \<CC> g f"
  shows "g : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
proof(intro is_arr_isomorphismI is_inverseI) 
  from assms(2) obtain a' b' 
    where g: "g : b' \<mapsto>\<^bsub>\<CC>\<^esub> a'"
      and f: "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'"
      and gf: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a'\<rparr>"
      and fg: "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b'\<rparr>"
    by auto
  with assms(1) have a'b': "a' = a" "b' = b" by auto
  from g f gf fg show 
    "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
    "g : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    unfolding a'b' by auto
qed

lemma (in category) cat_Comp_is_arr_isomorphism[cat_arrow_cs_intros]:
  assumes "g : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> c"
proof-
  from assms have [intro]: "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^bsub>\<CC>\<^esub> c" 
    by (auto intro: cat_cs_intros)
  from assms(1) obtain g' where g'g: "is_inverse \<CC> g' g" by force
  with assms(1) have [intro]: "g' : c \<mapsto>\<^bsub>\<CC>\<^esub> b" 
    by (elim is_arr_isomorphismE)
      (auto simp: is_arr_isomorphismD cat_is_inverse_is_arr_isomorphism)
  from assms(2) obtain f' where f'f: "is_inverse \<CC> f' f" by auto
  with assms(2) have [intro]: "f' : b \<mapsto>\<^bsub>\<CC>\<^esub> a"
    by (elim is_arr_isomorphismE)
      (auto simp: is_arr_isomorphismD cat_is_inverse_is_arr_isomorphism)
  have "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g' : c \<mapsto>\<^bsub>\<CC>\<^esub> a" by (auto intro: cat_cs_intros)
  from cat_is_inverse_Comp[OF _ _ g'g f'f] assms 
  have "is_inverse \<CC> (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g') (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)" 
    by (elim is_arr_isomorphismE) simp
  then show ?thesis by (auto intro: is_arr_isomorphismI)
qed

lemmas [cat_arrow_cs_intros] = category.cat_Comp_is_arr_isomorphism

lemma (in category) cat_CId_is_arr_isomorphism: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
  using assms 
  by 
    (
      cs_concl 
        cs_intro: cat_cs_intros is_inverseI cat_is_inverse_is_arr_isomorphism 
        cs_simp: cat_cs_simps
    )

lemma (in category) cat_CId_is_arr_isomorphism'[cat_arrow_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<CC>' = \<CC>"
    and "b = a"
    and "c = a"
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> c"
  using assms(1) 
  unfolding assms(2-4)
  by (rule cat_CId_is_arr_isomorphism)

lemmas [cat_arrow_cs_intros] = category.cat_CId_is_arr_isomorphism'

lemma (in category) cat_is_arr_isomorphism_is_monic_arr[cat_arrow_cs_intros]:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "f : a \<mapsto>\<^sub>m\<^sub>o\<^sub>n\<^bsub>\<CC>\<^esub> b"
proof(intro is_monic_arrI)
  note [cat_cs_intros] = is_arr_isomorphismD(1)
  show "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by (intro is_arr_isomorphismD(1)[OF assms])
  fix h g c assume prems: 
    "h : c \<mapsto>\<^bsub>\<CC>\<^esub> a" "g : c \<mapsto>\<^bsub>\<CC>\<^esub> a" "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h = f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g"
  from assms obtain f' 
    where f': "f' : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a" 
      and [cat_cs_simps]: "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>" 
    by (auto elim: is_arr_isomorphismE')
  from category_axioms assms prems(1,2) have "h = (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> h"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  also from category_axioms assms prems(1,2) f' have "\<dots> = (f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f) \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g"
    by (cs_concl cs_simp: prems(3) cat_cs_simps cs_intro: cat_cs_intros)
  also from category_axioms assms prems(1,2) f' have "\<dots> = g"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  finally show "h = g" by simp
qed

lemmas [cat_arrow_cs_intros] = category.cat_is_arr_isomorphism_is_monic_arr

lemma (in category) cat_is_arr_isomorphism_is_epic_arr:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "f : a \<mapsto>\<^sub>e\<^sub>p\<^sub>i\<^bsub>\<CC>\<^esub> b"
  using assms
  by 
    (
      rule 
        category.cat_is_arr_isomorphism_is_monic_arr[
          OF category_op, unfolded cat_op_simps
          ]
    )

lemmas [cat_arrow_cs_intros] = category.cat_is_arr_isomorphism_is_epic_arr



subsection\<open>The inverse arrow\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition the_inverse :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_\<inverse>\<^sub>C\<index>)\<close> [1000] 999)
  where "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = (THE g. is_inverse \<CC> g f)"


text\<open>Elementary properties.\<close>

lemma (in category) cat_is_inverse_is_inverse_the_inverse:
  assumes "is_inverse \<CC> g f"
  shows "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) f"
  unfolding the_inverse_def
proof(rule theI)
  fix g' assume "is_inverse \<CC> g' f"
  then show "g' = g" by (meson cat_is_inverse_eq assms)
qed (rule assms)

lemma (in category) cat_is_inverse_eq_the_inverse:
  assumes "is_inverse \<CC> g f"
  shows "g = f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>"
  by (meson assms cat_is_inverse_is_inverse_the_inverse cat_is_inverse_eq)


text\<open>The inverse arrow is an inverse of an isomorphism.\<close>

lemma (in category) cat_the_inverse_is_inverse:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) f"
proof-
  from assms obtain g where "is_inverse \<CC> g f" by auto
  then show "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) f"
    by (rule cat_is_inverse_is_inverse_the_inverse)
qed

lemma (in category) cat_the_inverse_is_arr_isomorphism:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> a"
proof-
  from assms have f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" by auto
  have "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) f" by (rule cat_the_inverse_is_inverse[OF assms])
  from cat_is_inverse_is_arr_isomorphism[OF f this] show ?thesis .
qed

lemma (in category) cat_the_inverse_is_arr_isomorphism':
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b" and "\<CC>' = \<CC>"
  shows "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> a"
  using assms(1) 
  unfolding assms(2)
  by (rule cat_the_inverse_is_arr_isomorphism)

lemmas [cat_cs_intros] = category.cat_the_inverse_is_arr_isomorphism'

lemma (in category) op_cat_the_inverse:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "f\<inverse>\<^sub>C\<^bsub>op_cat \<CC>\<^esub> = f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>"
proof-
  from assms have "f : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>op_cat \<CC>\<^esub> a" unfolding cat_op_simps by simp
  from assms show ?thesis
    by 
      (
        intro 
          category.cat_is_inverse_eq_the_inverse[
            symmetric, OF category_op, unfolded cat_op_simps
            ] 
          cat_the_inverse_is_inverse
      )
qed

lemmas [cat_op_simps] = category.op_cat_the_inverse

lemma (in category) cat_Comp_the_inverse:
  assumes "g : b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> c" and "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "(g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>"
proof-
  from assms have "g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> c" 
    by (cs_concl cs_intro: cat_arrow_cs_intros)
  then have inv_gf: "is_inverse \<CC> ((g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
    by (intro cat_the_inverse_is_inverse)
  from assms have "is_inverse \<CC> (g\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) g" "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) f"
    by (auto intro: cat_the_inverse_is_inverse)
  with category_axioms assms have 
    "is_inverse \<CC> (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>) (g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)"
    by (cs_concl cs_intro: cat_cs_intros cat_arrow_cs_intros) 
  from inv_gf this show "(g \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> g\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>"
    by (meson cat_is_inverse_eq)
qed

lemmas [cat_cs_simps] = category.cat_Comp_the_inverse

lemma (in category) cat_the_inverse_Comp_CId:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows cat_the_inverse_Comp_CId_left: "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    and cat_the_inverse_Comp_CId_right: "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
proof-
  from assms show "f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f = \<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr>"
    by 
      (
        cs_concl
          cs_simp: is_inverse_Comp_CId_left
          cs_intro: cat_the_inverse_is_inverse cat_arrow_cs_intros
      )
  from assms show "f \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = \<CC>\<lparr>CId\<rparr>\<lparr>b\<rparr>"
    by 
      (
        cs_concl
          cs_simp: is_inverse_Comp_CId_right
          cs_intro: cat_the_inverse_is_inverse cat_arrow_cs_intros
      )
qed

lemmas [cat_cs_simps] = category.cat_the_inverse_Comp_CId

lemma (in category) cat_the_inverse_the_inverse:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  shows "(f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = f"
proof-
  from assms have 
    "(f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> = (f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub>)\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f\<inverse>\<^sub>C\<^bsub>\<CC>\<^esub> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by (*slow*)
      (
        cs_concl 
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_arrow_cs_intros 
      )
  also from assms have "\<dots> = f"
    by 
      (
        cs_concl 
          cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_arrow_cs_intros
      )
  finally show ?thesis .
qed

lemmas [cat_cs_simps] = category.cat_the_inverse_the_inverse



subsection\<open>Isomorphic objects\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

definition obj_iso :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" 
  where "obj_iso \<CC> a b \<longleftrightarrow> (\<exists>f. f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b)"

syntax "_obj_iso" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" (\<open>(_/ \<approx>\<^sub>o\<^sub>b\<^sub>j\<index> _)\<close> [55, 56] 55)
translations "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> b" \<rightleftharpoons> "CONST obj_iso \<CC> a b"


text\<open>Rules.\<close>

lemma obj_isoI:
  assumes "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b" 
  shows "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> b"
  using assms unfolding obj_iso_def by auto

lemma obj_isoD[dest]:
  assumes "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> b" 
  shows "\<exists>f. f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b" 
  using assms unfolding obj_iso_def by auto
  
lemma obj_isoE[elim!]:
  assumes "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> b" 
  obtains f where "f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"
  using assms by auto


text\<open>Elementary properties.\<close>

lemma (in category) op_cat_obj_iso[cat_op_simps]: 
  "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>op_cat \<CC>\<^esub> b = b \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> a"
  unfolding obj_iso_def cat_op_simps ..

lemmas [cat_op_simps] = category.op_cat_obj_iso

lemmas [cat_op_intros] = category.op_cat_obj_iso[THEN iffD2]


text\<open>Equivalence relation.\<close>

lemma (in category) cat_obj_iso_refl:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
  shows "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> a"
  using assms by (auto intro: obj_isoI cat_arrow_cs_intros)

lemma (in category) cat_obj_iso_sym[sym]: 
  assumes "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> b" 
  shows "b \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> a"
  using assms 
  by (elim obj_isoE is_arr_isomorphismE) 
    (metis obj_iso_def cat_is_inverse_is_arr_isomorphism)

lemma (in category) cat_obj_iso_trans[trans]:
  assumes "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> b" and "b \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> c" 
  shows "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> c"
  using assms by (auto intro: cat_Comp_is_arr_isomorphism obj_isoI)



subsection\<open>Terminal object and initial object\<close>

lemma (in category) cat_obj_terminal_CId:
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "obj_terminal \<CC> a" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> a"
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> = f"
  using assms by (elim obj_terminalE) (metis cat_CId_is_arr)

lemma (in category) cat_obj_initial_CId: 
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "obj_initial \<CC> a" and "f : a \<mapsto>\<^bsub>\<CC>\<^esub> a"
  shows "\<CC>\<lparr>CId\<rparr>\<lparr>a\<rparr> = f"
  using assms 
  by (rule category.cat_obj_terminal_CId[OF category_op, unfolded cat_op_simps])

lemma (in category) cat_obj_terminal_obj_iso:
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "obj_terminal \<CC> a" and "obj_terminal \<CC> a'"
  shows "a \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> a'"
proof-
  from assms obtain f where f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> a'" by auto
  from assms obtain f' where f': "f' : a' \<mapsto>\<^bsub>\<CC>\<^esub> a" by auto
  from f f' cat_obj_terminal_CId cat_Comp_is_arr 
  have f'f: "is_inverse \<CC> f' f"
    by (intro is_inverseI[OF f' f]) (metis assms(1), metis assms(2))
  with f show ?thesis by (cs_concl cs_intro: obj_isoI is_arr_isomorphismI)
qed

lemma (in category) cat_obj_initial_obj_iso:
  \<comment>\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "obj_initial \<CC> a" and "obj_initial \<CC> a'"
  shows "a' \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> a"
proof-
  interpret op: category \<alpha> \<open>op_cat \<CC>\<close> by (auto intro: cat_cs_intros)
  from assms show ?thesis
    by (rule op.cat_obj_terminal_obj_iso[unfolded cat_op_simps])  
qed                     



subsection\<open>Null object\<close>

lemma (in category) cat_obj_null_obj_iso:
  \<comment>\<open>see Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>
  assumes "obj_null \<CC> z" and "obj_null \<CC> z'"
  shows "z \<approx>\<^sub>o\<^sub>b\<^sub>j\<^bsub>\<CC>\<^esub> z'"
  using assms by (simp add: cat_obj_terminal_obj_iso obj_nullD(2))



subsection\<open>Groupoid\<close>


text\<open>See Chapter I-5 in \cite{mac_lane_categories_2010}.\<close>

locale groupoid = category \<alpha> \<CC> for \<alpha> \<CC> +
  assumes grpd_is_arr_isomorphism: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b \<Longrightarrow> f : a \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>\<^esub> b"


text\<open>Rules.\<close>

mk_ide rf groupoid_def[unfolded groupoid_axioms_def]
  |intro groupoidI|
  |dest groupoidD[dest]|
  |elim groupoidE[elim]|

text\<open>\newpage\<close>

end