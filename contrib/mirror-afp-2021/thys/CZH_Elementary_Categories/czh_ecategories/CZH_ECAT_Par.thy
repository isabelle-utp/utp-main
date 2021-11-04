(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Par\<close>\<close>
theory CZH_ECAT_Par
  imports 
    CZH_Foundations.CZH_SMC_Par
    CZH_ECAT_Rel
    CZH_ECAT_Subcategory
begin



subsection\<open>Background\<close>


text\<open>
The methodology chosen for the exposition of \<open>Par\<close> as a category is 
analogous to the one used in \cite{milehins_category_2021} 
for the exposition of \<open>Par\<close> as a semicategory. 
\<close>

named_theorems cat_Par_cs_simps
named_theorems cat_Par_cs_intros

lemmas (in arr_Rel) [cat_Par_cs_simps] = 
  dg_Rel_shared_cs_simps

lemmas [cat_Par_cs_simps] = 
  dg_Rel_shared_cs_simps
  arr_Par.arr_Par_length
  arr_Par_comp_Par_id_Par_left
  arr_Par_comp_Par_id_Par_right

lemmas [cat_Par_cs_intros] = 
  arr_Par_comp_Par



subsection\<open>\<open>Par\<close> as a category\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_Par :: "V \<Rightarrow> V"
  where "cat_Par \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Par \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrCod\<rparr>),
      (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Par \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>),
      VLambda (Vset \<alpha>) id_Par 
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_Par_components:
  shows "cat_Par \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "cat_Par \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Par \<alpha> T}"
    and "cat_Par \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "cat_Par \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
    and "cat_Par \<alpha>\<lparr>Comp\<rparr> = (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Par \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>P\<^sub>a\<^sub>r ST\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_Par \<alpha>\<lparr>CId\<rparr> = VLambda (Vset \<alpha>) id_Par"
  unfolding cat_Par_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_cat_Par: "cat_smc (cat_Par \<alpha>) = smc_Par \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_Par \<alpha>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_Par \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_Par_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_Par \<alpha>)) = \<D>\<^sub>\<circ> (smc_Par \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_Par \<alpha>)) \<Longrightarrow> cat_smc (cat_Par \<alpha>)\<lparr>a\<rparr> = smc_Par \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral,
        unfold cat_smc_def dg_field_simps cat_Par_def smc_Par_def
      )
      (auto simp: nat_omega_simps)
qed (auto simp: cat_smc_def smc_Par_def)

lemmas_with [folded cat_smc_cat_Par, unfolded slicing_simps]:
  cat_Par_Obj_iff = smc_Par_Obj_iff
  and cat_Par_Arr_iff[cat_Par_cs_simps] = smc_Par_Arr_iff
  and cat_Par_Dom_vsv[cat_Par_cs_intros] = smc_Par_Dom_vsv
  and cat_Par_Dom_vdomain[cat_Par_cs_simps] = smc_Par_Dom_vdomain
  and cat_Par_Dom_vrange = smc_Par_Dom_vrange
  and cat_Par_Dom_app[cat_Par_cs_simps] = smc_Par_Dom_app
  and cat_Par_Cod_vsv[cat_Par_cs_intros] = smc_Par_Cod_vsv
  and cat_Par_Cod_vdomain[cat_Par_cs_simps] = smc_Par_Cod_vdomain
  and cat_Par_Cod_vrange = smc_Par_Cod_vrange
  and cat_Par_Cod_app[cat_Par_cs_simps] = smc_Par_Cod_app
  and cat_Par_is_arrI = smc_Par_is_arrI
  and cat_Par_is_arrD = smc_Par_is_arrD
  and cat_Par_is_arrE = smc_Par_is_arrE

lemmas_with [folded cat_smc_cat_Par, unfolded slicing_simps]: 
  cat_Par_composable_arrs_dg_Par = smc_Par_composable_arrs_dg_Par
  and cat_Par_Comp = smc_Par_Comp
  and cat_Par_Comp_app[cat_Par_cs_simps] = smc_Par_Comp_app
  and cat_Par_Comp_vdomain[cat_Par_cs_simps] = smc_Par_Comp_vdomain

lemmas [cat_cs_simps] = cat_Par_is_arrD(2,3)

lemmas [cat_Par_cs_intros] = cat_Par_is_arrI

lemmas_with (in \<Z>) [folded cat_smc_cat_Par, unfolded slicing_simps]:
  cat_Par_Hom_vifunion_in_Vset = smc_Par_Hom_vifunion_in_Vset
  and cat_Par_incl_Par_is_arr = smc_Par_incl_Par_is_arr
  and cat_Par_incl_Par_is_arr'[cat_Par_cs_intros] = smc_Par_incl_Par_is_arr'
  and cat_Par_Comp_vrange = smc_Par_Comp_vrange
  and cat_Par_is_monic_arrI = smc_Par_is_monic_arrI
  and cat_Par_is_monic_arr = smc_Par_is_monic_arr
  and cat_Par_is_epic_arrI = smc_Par_is_epic_arrI
  and cat_Par_is_epic_arrD = smc_Par_is_epic_arrD
  and cat_Par_is_epic_arr = smc_Par_is_epic_arr
  and cat_Par_obj_terminal = smc_Par_obj_terminal
  and cat_Par_obj_initial = smc_Par_obj_initial
  and cat_Par_obj_terminal_obj_initial = smc_Par_obj_terminal_obj_initial
  and cat_Par_obj_null = smc_Par_obj_null
  and cat_Par_is_zero_arr = smc_Par_is_zero_arr

lemmas [cat_Par_cs_intros] = \<Z>.cat_Par_incl_Par_is_arr'


subsubsection\<open>Identity\<close>

lemma cat_Par_CId_app[cat_Par_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "cat_Par \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> = id_Par A"
  using assms unfolding cat_Par_components by simp

lemma id_Par_CId_app_app[cat_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "a \<in>\<^sub>\<circ> A"
  shows "cat_Par \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = a"
  unfolding cat_Par_CId_app[OF assms(1)] id_Rel_ArrVal_app[OF assms(2)] by simp


subsubsection\<open>\<open>Par\<close> is a category\<close>

lemma (in \<Z>) category_cat_Par: "category \<alpha> (cat_Par \<alpha>)"
proof(intro categoryI, unfold cat_smc_cat_Rel cat_smc_cat_Par cat_op_simps)

  interpret Par: semicategory \<alpha> \<open>cat_smc (cat_Par \<alpha>)\<close>
    unfolding cat_smc_cat_Par by (simp add: semicategory_smc_Par)

  show "vfsequence (cat_Par \<alpha>)" unfolding cat_Par_def by simp
  show "vcard (cat_Par \<alpha>) = 6\<^sub>\<nat>" 
    unfolding cat_Par_def by (simp add: nat_omega_simps)
  show "cat_Par \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> : A \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> A" if "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" for A
    using that
    unfolding cat_Par_Obj_iff
    by 
      (
        cs_concl 
          cs_simp: cat_Par_cs_simps cs_intro: cat_Par_cs_intros arr_Par_id_ParI
      )

  show "cat_Par \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>cat_Par \<alpha>\<^esub> F = F"
    if "F : A \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> B" for F A B
  proof-
    from that have "arr_Par \<alpha> F" "B \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto elim: cat_Par_is_arrE simp: cat_Par_cs_simps)
    with that \<Z>_axioms show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Par_cs_simps
            cs_intro: cat_Par_cs_intros arr_Par_id_ParI
        )
  qed

  show "F \<circ>\<^sub>A\<^bsub>cat_Par \<alpha>\<^esub> cat_Par \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr> = F"
    if "F : B \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> C" for F B C
  proof-
    from that have "arr_Par \<alpha> F" "B \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto elim: cat_Par_is_arrE simp: cat_Par_cs_simps)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Par_cs_simps
            cs_intro: cat_Par_cs_intros arr_Par_id_ParI
        )
  qed

qed (auto simp: semicategory_smc_Par cat_Par_components)


subsubsection\<open>\<open>Par\<close> is a wide replete subcategory of \<open>Rel\<close>\<close>

lemma (in \<Z>) wide_replete_subcategory_cat_Par_cat_Rel: 
  "cat_Par \<alpha> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
proof(intro wide_replete_subcategoryI)
  show wide_subcategory_cat_Par_cat_Rel: "cat_Par \<alpha> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
  proof(intro wide_subcategoryI, unfold cat_smc_cat_Rel cat_smc_cat_Par)
    interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
    interpret Par: category \<alpha> \<open>cat_Par \<alpha>\<close> by (rule category_cat_Par)
    interpret wide_subsemicategory \<alpha> \<open>smc_Par \<alpha>\<close> \<open>smc_Rel \<alpha>\<close>
      by (simp add: wide_subsemicategory_smc_Par_smc_Rel)
    show "cat_Par \<alpha> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
    proof(intro subcategoryI, unfold cat_smc_cat_Rel cat_smc_cat_Par)
      show "smc_Par \<alpha> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_Rel \<alpha>" by (simp add: subsemicategory_axioms)
      fix A assume "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
      then show "cat_Par \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>"
        unfolding cat_Par_components cat_Rel_components by simp
    qed 
      (
        auto simp: 
          subsemicategory_axioms Rel.category_axioms Par.category_axioms
      )
  qed (rule wide_subsemicategory_smc_Par_smc_Rel)
  show "cat_Par \<alpha> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
  proof(intro replete_subcategoryI)
    interpret wide_subcategory \<alpha> \<open>cat_Par \<alpha>\<close> \<open>cat_Rel \<alpha>\<close>
      by (rule wide_subcategory_cat_Par_cat_Rel)
    show "cat_Par \<alpha> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>" by (rule subcategory_axioms)    
    fix A B F assume prems: "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" "F : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
    note arr_Rel = cat_Rel_is_arr_isomorphismD[OF prems(2)]
    from arr_Rel(2) show "F : A \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> B"
      by (intro cat_Par_is_arrI arr_Par_arr_RelI cat_Rel_is_arrD[OF arr_Rel(1)])
        auto
  qed
qed



subsection\<open>Isomorphism\<close>

lemma (in \<Z>) cat_Par_is_arr_isomorphismI[intro]:
  assumes "T : A \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> B" 
    and "v11 (T\<lparr>ArrVal\<rparr>)"
    and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  shows "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
proof-
  note [cat_cs_intros] = cat_Rel_is_arr_isomorphismI
  from wide_replete_subcategory_cat_Par_cat_Rel assms have 
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
    by (cs_concl cs_intro: cat_cs_intros cat_sub_cs_intros cat_sub_fw_cs_intros)
  with wide_replete_subcategory_cat_Par_cat_Rel assms show 
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
    by (cs_concl cs_simp: cat_sub_bw_cs_simps)
qed

lemma (in \<Z>) cat_Par_is_arr_isomorphismD[dest]:
  assumes "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
  shows "T : A \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> B"
    and "v11 (T\<lparr>ArrVal\<rparr>)"
    and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
proof-
  from wide_replete_subcategory_cat_Par_cat_Rel assms have T: 
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
    by (cs_concl cs_intro: cat_sub_cs_intros cat_sub_fw_cs_intros)
  show "v11 (T\<lparr>ArrVal\<rparr>)" "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A" "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
    by (intro cat_Rel_is_arr_isomorphismD[OF T])+
qed (rule is_arr_isomorphismD(1)[OF assms])

lemma (in \<Z>) cat_Par_is_arr_isomorphism:
  "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B \<longleftrightarrow>
    T : A \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> B \<and>
    v11 (T\<lparr>ArrVal\<rparr>) \<and>
    \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A \<and>
    \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  by auto



subsection\<open>The inverse arrow\<close>

abbreviation (input) converse_Par :: "V \<Rightarrow> V" ("(_\<inverse>\<^sub>P\<^sub>a\<^sub>r)" [1000] 999)
  where "a\<inverse>\<^sub>P\<^sub>a\<^sub>r \<equiv> a\<inverse>\<^sub>R\<^sub>e\<^sub>l"

lemma (in \<Z>) cat_Par_the_inverse:
  assumes "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
  shows "T\<inverse>\<^sub>C\<^bsub>cat_Par \<alpha>\<^esub> = T\<inverse>\<^sub>P\<^sub>a\<^sub>r"
proof-
  from wide_replete_subcategory_cat_Par_cat_Rel assms have T:
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
    by (cs_concl cs_intro: cat_sub_cs_intros cat_sub_fw_cs_intros)
  from wide_replete_subcategory_cat_Par_cat_Rel assms have [cat_cs_simps]:
    "T\<inverse>\<^sub>C\<^bsub>cat_Par \<alpha>\<^esub> = T\<inverse>\<^sub>C\<^bsub>cat_Rel \<alpha>\<^esub>"
    by (cs_concl cs_full cs_simp: cat_sub_bw_cs_simps cs_intro: cat_sub_cs_intros)
  from T show "T\<inverse>\<^sub>C\<^bsub>cat_Par \<alpha>\<^esub> = T\<inverse>\<^sub>R\<^sub>e\<^sub>l"
    by (cs_concl cs_simp: cat_Rel_cs_simps cat_cs_simps cs_intro: cat_cs_intros)
qed

lemmas [cat_Par_cs_simps] = \<Z>.cat_Par_the_inverse

text\<open>\newpage\<close>

end