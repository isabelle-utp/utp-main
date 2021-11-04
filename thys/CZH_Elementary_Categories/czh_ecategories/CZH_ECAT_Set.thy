(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Set\<close>\<close>
theory CZH_ECAT_Set
  imports 
    CZH_Foundations.CZH_SMC_Set
    CZH_ECAT_Par
    CZH_ECAT_Subcategory
    CZH_ECAT_PCategory
begin



subsection\<open>Background\<close>


text\<open>
The methodology chosen for the exposition of \<open>Set\<close> as a category is 
analogous to the one used in \cite{milehins_category_2021} 
for the exposition of \<open>Set\<close> as a semicategory. 
\<close>

named_theorems cat_Set_cs_simps
named_theorems cat_Set_cs_intros

lemmas (in arr_Set) [cat_Set_cs_simps] = 
  dg_Rel_shared_cs_simps

lemmas [cat_Set_cs_simps] =
  dg_Rel_shared_cs_simps
  arr_Set.arr_Set_ArrVal_vdomain
  arr_Set_comp_Set_id_Set_left
  arr_Set_comp_Set_id_Set_right

lemmas [cat_Set_cs_intros] = 
  dg_Rel_shared_cs_intros
  arr_Set_comp_Set

(*
Certain lemmas are applicable to any of the categories among
Rel, Par, Set. If these lemmas are included in general-purpose
collections like cat_cs_simps/cat_cs_intros, then backtracking
can become slow. The following collections were created to resolve
such issues.
*)
named_theorems cat_rel_par_Set_cs_intros
named_theorems cat_rel_par_Set_cs_simps
named_theorems cat_rel_Par_set_cs_intros
named_theorems cat_rel_Par_set_cs_simps
named_theorems cat_Rel_par_set_cs_intros
named_theorems cat_Rel_par_set_cs_simps



subsection\<open>\<open>Set\<close> as a category\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_Set :: "V \<Rightarrow> V"
  where "cat_Set \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Set \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrCod\<rparr>),
      (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Set \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>R\<^sub>e\<^sub>l ST\<lparr>1\<^sub>\<nat>\<rparr>),
      VLambda (Vset \<alpha>) id_Set 
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_Set_components:
  shows "cat_Set \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "cat_Set \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Set \<alpha> T}"
    and "cat_Set \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "cat_Set \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
    and "cat_Set \<alpha>\<lparr>Comp\<rparr> =
      (\<lambda>ST\<in>\<^sub>\<circ>composable_arrs (dg_Set \<alpha>). ST\<lparr>0\<rparr> \<circ>\<^sub>P\<^sub>a\<^sub>r ST\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cat_Set \<alpha>\<lparr>CId\<rparr> = VLambda (Vset \<alpha>) id_Set"
  unfolding cat_Set_def dg_field_simps by (simp_all add: nat_omega_simps)


text\<open>Slicing.\<close>

lemma cat_smc_cat_Set: "cat_smc (cat_Set \<alpha>) = smc_Set \<alpha>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> (cat_smc (cat_Set \<alpha>)) = 5\<^sub>\<nat>" 
    unfolding cat_smc_def by (simp add: nat_omega_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> (smc_Set \<alpha>) = 5\<^sub>\<nat>"
    unfolding smc_Set_def by (simp add: nat_omega_simps)
  show "\<D>\<^sub>\<circ> (cat_smc (cat_Set \<alpha>)) = \<D>\<^sub>\<circ> (smc_Set \<alpha>)"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (cat_smc (cat_Set \<alpha>)) \<Longrightarrow> cat_smc (cat_Set \<alpha>)\<lparr>a\<rparr> = smc_Set \<alpha>\<lparr>a\<rparr>"
    for a
    by 
      (
        unfold dom_lhs, 
        elim_in_numeral, 
        unfold cat_smc_def dg_field_simps cat_Set_def smc_Set_def
      )
      (auto simp: nat_omega_simps)
qed (auto simp: cat_smc_def smc_Set_def)

lemmas_with [folded cat_smc_cat_Set, unfolded slicing_simps]:
  cat_Set_Obj_iff = smc_Set_Obj_iff
  and cat_Set_Arr_iff[cat_Set_cs_simps] = smc_Set_Arr_iff
  and cat_Set_Dom_vsv[intro] = smc_Set_Dom_vsv
  and cat_Set_Dom_vdomain[simp] = smc_Set_Dom_vdomain
  and cat_Set_Dom_vrange = smc_Set_Dom_vrange
  and cat_Set_Dom_app = smc_Set_Dom_app
  and cat_Set_Cod_vsv[intro] = smc_Set_Cod_vsv
  and cat_Set_Cod_vdomain[simp] = smc_Set_Cod_vdomain
  and cat_Set_Cod_vrange = smc_Set_Cod_vrange
  and cat_Set_Cod_app[cat_Set_cs_simps] = smc_Set_Cod_app
  and cat_Set_is_arrI = smc_Set_is_arrI
  and cat_Set_is_arrD = smc_Set_is_arrD
  and cat_Set_is_arrE = smc_Set_is_arrE
  and cat_Set_ArrVal_vdomain[cat_cs_simps] = smc_Set_ArrVal_vdomain
  and cat_Set_ArrVal_app_vrange[cat_Set_cs_intros] = smc_Set_ArrVal_app_vrange

lemmas [cat_cs_simps] = cat_Set_is_arrD(2,3)

lemmas [cat_Set_cs_intros] = 
  cat_Set_is_arrI

lemmas_with [folded cat_smc_cat_Set, unfolded slicing_simps]: 
  cat_Set_composable_arrs_dg_Set = smc_Set_composable_arrs_dg_Set
  and cat_Set_Comp = smc_Set_Comp
  and cat_Set_Comp_app[cat_Set_cs_simps] = smc_Set_Comp_app
  and cat_Set_Comp_vdomain[cat_Set_cs_simps] = smc_Set_Comp_vdomain

lemmas_with (in \<Z>) [folded cat_smc_cat_Set, unfolded slicing_simps]:
  cat_Set_Hom_vifunion_in_Vset = smc_Set_Hom_vifunion_in_Vset
  and cat_Set_incl_Set_is_arr = smc_Set_incl_Set_is_arr
  and cat_Set_incl_Set_is_arr'[cat_Set_cs_intros] = smc_Set_incl_Set_is_arr'
  and cat_Set_Comp_ArrVal = smc_Set_Comp_ArrVal
  and cat_Set_Comp_vrange = smc_Set_Comp_vrange
  and cat_Set_is_monic_arrI = smc_Set_is_monic_arrI
  and cat_Set_is_monic_arr = smc_Set_is_monic_arr
  and cat_Set_is_epic_arrI = smc_Set_is_epic_arrI
  and cat_Set_is_epic_arrD = smc_Set_is_epic_arrD
  and cat_Set_is_epic_arr = smc_Set_is_epic_arr
  and cat_Set_obj_terminal = smc_Set_obj_terminal
  and cat_Set_obj_initial = smc_Set_obj_initial
  and cat_Set_obj_null = smc_Set_obj_null
  and cat_Set_is_zero_arr = smc_Set_is_zero_arr

lemmas [cat_Set_cs_intros] = \<Z>.cat_Set_incl_Set_is_arr'

lemmas [cat_cs_simps] = 
  \<Z>.cat_Set_Comp_ArrVal


subsubsection\<open>Identity\<close>

lemma cat_Set_CId_app[cat_Set_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> = id_Set A"
  using assms unfolding cat_Set_components by simp

lemma id_Par_CId_app_app[cat_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "a \<in>\<^sub>\<circ> A"
  shows "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = a"
  unfolding cat_Set_CId_app[OF assms(1)] id_Rel_ArrVal_app[OF assms(2)] by simp


subsubsection\<open>\<open>Set\<close> is a category\<close>

lemma (in \<Z>) category_cat_Set: "category \<alpha> (cat_Set \<alpha>)"
proof(rule categoryI, unfold cat_smc_cat_Par cat_smc_cat_Set)

  interpret Set: semicategory \<alpha> \<open>cat_smc (cat_Set \<alpha>)\<close>
    unfolding cat_smc_cat_Set by (simp add: semicategory_smc_Set)

  show "vfsequence (cat_Set \<alpha>)" unfolding cat_Set_def by simp
  show "vcard (cat_Set \<alpha>) = 6\<^sub>\<nat>"
    unfolding cat_Set_def by (simp add: nat_omega_simps)
  show "semicategory \<alpha> (smc_Set \<alpha>)" by (simp add: semicategory_smc_Set)
  show "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A"
    if "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" for A
    using that
    unfolding cat_Set_Obj_iff
    by 
      (
        cs_concl 
          cs_simp: cat_Set_cs_simps cs_intro: cat_Set_cs_intros arr_Set_id_SetI
      )

  show "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F = F" 
    if "F : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" for F A B
  proof-
    from that have "arr_Set \<alpha> F" "B \<in>\<^sub>\<circ> Vset \<alpha>" by (auto elim: cat_Set_is_arrE)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Set_cs_simps
            cs_intro: cat_Set_cs_intros arr_Set_id_SetI
        )
  qed

  show "F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr> = F"
    if "F : B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> C" for F B C
  proof-
    from that have "arr_Set \<alpha> F" "B \<in>\<^sub>\<circ> Vset \<alpha>" by (auto elim: cat_Set_is_arrE)
    with that show ?thesis
      by 
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_Set_cs_simps
            cs_intro: cat_Set_cs_intros arr_Set_id_SetI
        )
  qed

qed (auto simp: cat_Set_components)

lemma (in \<Z>) category_cat_Set':
  assumes "\<beta> = \<alpha>"
  shows "category \<beta> (cat_Set \<alpha>)"
  unfolding assms by (rule category_cat_Set)

lemmas [cat_cs_intros] = \<Z>.category_cat_Set'


subsubsection\<open>\<open>Set\<close> is a wide replete subcategory of \<open>Par\<close>\<close>

lemma (in \<Z>) wide_replete_subcategory_cat_Set_cat_Par: 
  "cat_Set \<alpha> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>r\<^bsub>\<alpha>\<^esub> cat_Par \<alpha>"
proof(intro wide_replete_subcategoryI)
  show wide_subcategory_cat_Set_cat_Par: "cat_Set \<alpha> \<subseteq>\<^sub>C\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> cat_Par \<alpha>"
  proof(intro wide_subcategoryI, unfold cat_smc_cat_Par cat_smc_cat_Set)
    interpret Par: category \<alpha> \<open>cat_Par \<alpha>\<close> by (rule category_cat_Par)
    interpret Set: category \<alpha> \<open>cat_Set \<alpha>\<close> by (rule category_cat_Set)
    interpret wide_subsemicategory \<alpha> \<open>smc_Set \<alpha>\<close> \<open>smc_Par \<alpha>\<close>
      by (simp add: wide_subsemicategory_smc_Set_smc_Par)
    show "cat_Set \<alpha> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Par \<alpha>"
    proof(intro subcategoryI, unfold cat_smc_cat_Par cat_smc_cat_Set)
      show "smc_Set \<alpha> \<subseteq>\<^sub>S\<^sub>M\<^sub>C\<^bsub>\<alpha>\<^esub> smc_Par \<alpha>" by (simp add: subsemicategory_axioms)
      fix A assume "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
      then show "cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> = cat_Par \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>"
        unfolding cat_Set_components cat_Par_components by simp
    qed 
      (
        auto simp: 
          subsemicategory_axioms Par.category_axioms Set.category_axioms
      )
  qed (rule wide_subsemicategory_smc_Set_smc_Par)
  show "cat_Set \<alpha> \<subseteq>\<^sub>C\<^sub>.\<^sub>r\<^sub>e\<^sub>p\<^bsub>\<alpha>\<^esub> cat_Par \<alpha>"
  proof(intro replete_subcategoryI)
    interpret wide_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close>
      by (rule wide_subcategory_cat_Set_cat_Par)
    show "cat_Set \<alpha> \<subseteq>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Par \<alpha>" by (rule subcategory_axioms)    
    fix A B F assume "F : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
    note arr_Par = cat_Par_is_arr_isomorphismD[OF this]
    from arr_Par show "F : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B"
      by (intro cat_Set_is_arrI arr_Set_arr_ParI cat_Par_is_arrD[OF arr_Par(1)])
        (auto simp: cat_Par_is_arrD(2))
  qed
qed


subsubsection\<open>\<open>Set\<close> is a subcategory of \<open>Set\<close>\<close>

lemma (in \<Z>) subcategory_cat_Set_cat_Set:(*TODO: generalize*)
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "cat_Set \<alpha> \<subseteq>\<^sub>C\<^bsub>\<beta>\<^esub> cat_Set \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show ?thesis  
  proof(intro subcategoryI')
    show "category \<beta> (cat_Set \<alpha>)"
      by (rule category.cat_category_if_ge_Limit, insert assms(2))
        (cs_concl cs_intro: cat_cs_intros cat_Rel_cs_intros)+
    show "A \<in>\<^sub>\<circ> cat_Set \<beta>\<lparr>Obj\<rparr>" if "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" for A 
      using that 
      unfolding cat_Set_components(1)
      by (meson assms(2) Vset_in_mono \<beta>.Axiom_of_Extensionality(3))
    show is_arr_if_is_arr: 
      "F : A \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> B" if "F : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" for A B F
    proof-
      note f = cat_Set_is_arrD[OF that]
      interpret f: arr_Set \<alpha> F by (rule f(1))
      show ?thesis
      proof(intro cat_Set_is_arrI arr_SetI)
        show "\<R>\<^sub>\<circ> (F\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> F\<lparr>ArrCod\<rparr>"  
           by (auto simp: f.arr_Set_ArrVal_vrange)
        show "F\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
          by (auto intro!: f.arr_Set_ArrDom_in_Vset Vset_in_mono assms(2))
        show "F\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
          by (auto intro!: f.arr_Set_ArrCod_in_Vset Vset_in_mono assms(2))
      qed 
        (
          auto simp: 
            f f.arr_Set_ArrVal_vdomain f.vfsequence_axioms f.arr_Set_length
        )
    qed
    show "G \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F = G \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> F"
      if "G : B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> C" and "F : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" for B C G A F
    proof-
      note g = cat_Set_is_arrD[OF that(1)] and f = cat_Set_is_arrD[OF that(2)]      
      from that have \<alpha>_gf_is_arr: "G \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F : A \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> C"
        by (cs_concl cs_intro: cat_cs_intros is_arr_if_is_arr)
      from that have \<beta>_gf_is_arr: "G \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> F : A \<mapsto>\<^bsub>cat_Set \<beta>\<^esub> C"
        by (cs_concl cs_intro: cat_cs_intros is_arr_if_is_arr)
      note \<alpha>_gf = cat_Set_is_arrD[OF \<alpha>_gf_is_arr]
        and \<beta>_gf = cat_Set_is_arrD[OF \<beta>_gf_is_arr]
      show ?thesis
      proof(rule arr_Set_eqI)
        show "arr_Set \<beta> (G \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)" by (rule \<alpha>_gf(1))
        then interpret arr_Set_\<alpha>_gf: arr_Set \<beta> \<open>(G \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<close> by simp
        from \<alpha>_gf_is_arr have dom_lhs: "\<D>\<^sub>\<circ> ((G \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>) = A"
          by (cs_concl cs_simp: cat_cs_simps)
        show "arr_Set \<beta> (G \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> F)" by (rule \<beta>_gf(1))
        then interpret arr_Set_\<beta>_gf: arr_Set \<beta> \<open>(G \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> F)\<close> by simp
        from \<beta>_gf_is_arr have dom_rhs: "\<D>\<^sub>\<circ> ((G \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> F)\<lparr>ArrVal\<rparr>) = A"
          by (cs_concl cs_simp: cat_cs_simps)
        show "(G \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr> = (G \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> F)\<lparr>ArrVal\<rparr>"
        proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
          fix a assume "a \<in>\<^sub>\<circ> A"
          from that this show 
            "(G \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = (G \<circ>\<^sub>A\<^bsub>cat_Set \<beta>\<^esub> F)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
            by 
              (
                cs_concl 
                  cs_simp: cat_cs_simps cs_intro: cat_cs_intros is_arr_if_is_arr
              )
        qed auto
      qed (use \<alpha>_gf_is_arr \<beta>_gf_is_arr in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+
    qed
  qed 
    (
      auto simp: 
        assms(2) cat_Set_components Vset_trans Vset_in_mono cat_cs_intros
    )
qed



subsection\<open>Isomorphism\<close>

lemma cat_Set_is_arr_isomorphismI[intro]:
  \<comment>\<open>
  See \cite{noauthor_nlab_nodate}\footnote{\url{
  https://ncatlab.org/nlab/show/isomorphism
  }}).
  \<close>
  assumes "T : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" 
    and "v11 (T\<lparr>ArrVal\<rparr>)"
    and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  shows "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B"
proof-
  interpret arr_Set \<alpha> T by (rule cat_Set_is_arrD(1)[OF assms(1)])
  note [cat_cs_intros] = cat_Par_is_arr_isomorphismI
  from wide_replete_subcategory_cat_Set_cat_Par assms have 
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
    by (cs_concl cs_intro: cat_cs_intros cat_sub_cs_intros cat_sub_fw_cs_intros)
  with wide_replete_subcategory_cat_Set_cat_Par assms show 
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B"
    by (cs_concl cs_simp: cat_sub_bw_cs_simps)
qed

lemma cat_Set_is_arr_isomorphismD[dest]:
  assumes "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B"
  shows "T : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B"
    and "v11 (T\<lparr>ArrVal\<rparr>)"
    and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
proof-
  from assms have T: "T : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" by auto
  interpret arr_Set \<alpha> T by (rule cat_Set_is_arrD(1)[OF T])
  from wide_replete_subcategory_cat_Set_cat_Par assms have T: 
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
    by (cs_concl cs_intro: cat_sub_cs_intros cat_sub_fw_cs_intros)
  show "v11 (T\<lparr>ArrVal\<rparr>)" "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A" "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
    by (intro cat_Par_is_arr_isomorphismD[OF T])+
qed (rule is_arr_isomorphismD(1)[OF assms])

lemma cat_Set_is_arr_isomorphism:
  "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B \<longleftrightarrow> 
    T : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B \<and>
    v11 (T\<lparr>ArrVal\<rparr>) \<and> 
    \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A \<and> 
    \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = B"
  by auto



subsection\<open>The inverse arrow\<close>

lemma cat_Set_ArrVal_app_is_arr[cat_cs_intros]:
  assumes "f : a \<mapsto>\<^bsub>\<AA>\<^esub> b" 
    and "category \<alpha> \<AA>" (*the order of premises is important*)
    and "F : Hom \<AA> a b \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c d"
  shows "F\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> : c \<mapsto>\<^bsub>\<BB>\<^esub> d"
proof-
  interpret \<AA>: category \<alpha> \<AA> by (rule assms(2))
  interpret F: arr_Set \<alpha> F by (rule cat_Set_is_arrD[OF assms(3)])  
  from assms have "F\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> Hom \<BB> c d"
    by (cs_concl cs_intro: cat_cs_intros cat_Set_cs_intros)
  then show ?thesis unfolding in_Hom_iff by simp
qed

abbreviation (input) converse_Set :: "V \<Rightarrow> V" ("(_\<inverse>\<^sub>S\<^sub>e\<^sub>t)" [1000] 999)
  where "a\<inverse>\<^sub>S\<^sub>e\<^sub>t \<equiv> a\<inverse>\<^sub>R\<^sub>e\<^sub>l"

lemma cat_Set_the_inverse[cat_Set_cs_simps]:
  assumes "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B"
  shows "T\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub> = T\<inverse>\<^sub>S\<^sub>e\<^sub>t"
proof-
  from assms have T: "T : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" by auto
  interpret arr_Set \<alpha> T by (rule cat_Set_is_arrD(1)[OF T])
  from wide_replete_subcategory_cat_Set_cat_Par assms have T:
    "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
    by (cs_concl cs_intro: cat_sub_cs_intros cat_sub_fw_cs_intros)
  from wide_replete_subcategory_cat_Set_cat_Par assms have [cat_cs_simps]:
    "T\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub> = T\<inverse>\<^sub>C\<^bsub>cat_Par \<alpha>\<^esub>"
    by 
      (
        cs_concl cs_full 
          cs_simp: cat_sub_bw_cs_simps cs_intro: cat_sub_cs_intros
      )
  from T show "T\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub> = T\<inverse>\<^sub>R\<^sub>e\<^sub>l"
    by (cs_concl cs_simp: cat_Par_cs_simps cat_cs_simps cs_intro: \<Z>_\<beta>)
qed

lemma cat_Set_the_inverse_app[cat_cs_intros]:
  assumes "T : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B"
    and "a \<in>\<^sub>\<circ> A"
    and [cat_cs_simps]: "T\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = b"
  shows "(T\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>)\<lparr>ArrVal\<rparr>\<lparr>b\<rparr> = a"
proof-
  from assms have T: "T : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" by auto
  interpret arr_Set \<alpha> T by (rule cat_Set_is_arrD(1)[OF T])
  note T = cat_Set_is_arr_isomorphismD[OF assms(1)]
  interpret T: v11 \<open>T\<lparr>ArrVal\<rparr>\<close> by (rule T(2))
  from T.v11_axioms assms(1,2) show "T\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>b\<rparr> = a"
    by
      (
        cs_concl 
          cs_simp: 
            converse_Rel_components V_cs_simps cat_Set_cs_simps cat_cs_simps 
          cs_intro: cat_arrow_cs_intros cat_cs_intros
      )
qed
                                                          
lemma cat_Set_ArrVal_app_the_inverse_is_arr[cat_cs_intros]:
  assumes "f : c \<mapsto>\<^bsub>\<BB>\<^esub> d" 
    and "category \<alpha> \<BB>" (*the order of premises is important*)
    and "F : Hom \<AA> a b \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> Hom \<BB> c d"
  shows "F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> : a \<mapsto>\<^bsub>\<AA>\<^esub> b"
proof-
  interpret \<BB>: category \<alpha> \<BB> by (rule assms(2))
  from cat_Set_is_arr_isomorphismD[OF assms(3)] interpret F: arr_Set \<alpha> F 
    by (simp add: cat_Set_is_arrD)  
  from assms have "F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> Hom \<AA> a b"
    by (cs_concl cs_intro: cat_cs_intros cat_arrow_cs_intros)
  then show ?thesis unfolding in_Hom_iff by simp
qed

lemma cat_Set_app_the_inverse_app[cat_cs_simps]:
  assumes "F : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B" and "b \<in>\<^sub>\<circ> B"
  shows "F\<lparr>ArrVal\<rparr>\<lparr>F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>b\<rparr>\<rparr> = b"
proof-
  note F = cat_Set_is_arr_isomorphismD[OF assms(1)]
  note F = F cat_Set_is_arrD[OF F(1)]
  interpret F: arr_Set \<alpha> F by (rule cat_Set_is_arrD[OF F(1)])  
  from assms have [cat_cs_simps]: 
    "F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub> = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms have [cat_cs_simps]: 
    "F\<lparr>ArrVal\<rparr>\<lparr>F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>b\<rparr>\<rparr> = 
      (F \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>)\<lparr>ArrVal\<rparr>\<lparr>b\<rparr>"
    by
      (
        cs_concl
          cs_simp: cat_cs_simps cs_intro: cat_arrow_cs_intros cat_cs_intros
      )
  from assms F.arr_Par_ArrCod_in_Vset[unfolded F] show ?thesis
    by (cs_concl cs_simp: cat_cs_simps)
qed

lemma cat_Set_the_inverse_app_app[cat_cs_simps]:
  assumes "F : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B" and "a \<in>\<^sub>\<circ> A"
  shows "F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<rparr> = a"
proof-
  note F = cat_Set_is_arr_isomorphismD[OF assms(1)]
  note F = F cat_Set_is_arrD[OF F(1)]
  interpret F: arr_Set \<alpha> F by (rule cat_Set_is_arrD[OF F(1)])  
  from assms have [cat_cs_simps]:
    "F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F = cat_Set \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms have [cat_cs_simps]: 
    "F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub>\<lparr>ArrVal\<rparr>\<lparr>F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<rparr> =
      (F\<inverse>\<^sub>C\<^bsub>cat_Set \<alpha>\<^esub> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
    by
      (
        cs_concl 
          cs_simp: cat_cs_simps cs_intro: cat_arrow_cs_intros cat_cs_intros
      )
  from assms F.arr_Par_ArrDom_in_Vset[unfolded F] show ?thesis
    by (cs_concl cs_simp: cat_cs_simps)
qed



subsection\<open>Projection arrows for \<open>vtimes\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition vfst_arrow :: "V \<Rightarrow> V \<Rightarrow> V"
  where "vfst_arrow A B = [(\<lambda>ab\<in>\<^sub>\<circ>A \<times>\<^sub>\<circ> B. vfst ab), A \<times>\<^sub>\<circ> B, A]\<^sub>\<circ>"

definition vsnd_arrow :: "V \<Rightarrow> V \<Rightarrow> V"
  where "vsnd_arrow A B = [(\<lambda>ab\<in>\<^sub>\<circ>A \<times>\<^sub>\<circ> B. vsnd ab), A \<times>\<^sub>\<circ> B, B]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma vfst_arrow_components: 
  shows "vfst_arrow A B\<lparr>ArrVal\<rparr> = (\<lambda>ab\<in>\<^sub>\<circ>A \<times>\<^sub>\<circ> B. vfst ab)"
    and [cat_cs_simps]: "vfst_arrow A B\<lparr>ArrDom\<rparr> = A \<times>\<^sub>\<circ> B"
    and [cat_cs_simps]: "vfst_arrow A B\<lparr>ArrCod\<rparr> = A"
  unfolding vfst_arrow_def arr_field_simps by (simp_all add: nat_omega_simps)

lemma vsnd_arrow_components: 
  shows "vsnd_arrow A B\<lparr>ArrVal\<rparr> = (\<lambda>ab\<in>\<^sub>\<circ>A \<times>\<^sub>\<circ> B. vsnd ab)"
    and [cat_cs_simps]: "vsnd_arrow A B\<lparr>ArrDom\<rparr> = A \<times>\<^sub>\<circ> B"
    and [cat_cs_simps]: "vsnd_arrow A B\<lparr>ArrCod\<rparr> = B"
  unfolding vsnd_arrow_def arr_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Arrow value\<close>

mk_VLambda vfst_arrow_components(1)
  |vsv vfst_arrow_ArrVal_vsv[cat_cs_intros]|
  |vdomain vfst_arrow_ArrVal_vdomain[cat_cs_simps]|
  |app vfst_arrow_ArrVal_app'|

mk_VLambda vsnd_arrow_components(1)
  |vsv vsnd_arrow_ArrVal_vsv[cat_cs_intros]|
  |vdomain vsnd_arrow_ArrVal_vdomain[cat_cs_simps]|
  |app vsnd_arrow_ArrVal_app'|

lemma vfst_arrow_ArrVal_app[cat_cs_simps]:
  assumes "ab = \<langle>a, b\<rangle>" and "ab \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
  shows "vfst_arrow A B\<lparr>ArrVal\<rparr>\<lparr>ab\<rparr> = a"
  using assms(2) unfolding assms(1) by (simp add: vfst_arrow_ArrVal_app')

lemma vfst_arrow_vrange: "\<R>\<^sub>\<circ> (vfst_arrow A B\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> A"
  unfolding vfst_arrow_components
proof(intro vrange_VLambda_vsubset)
  fix ab assume "ab \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
  then obtain a b where ab_def: "ab = \<langle>a, b\<rangle>" and a: "a \<in>\<^sub>\<circ> A" by clarsimp
  from a show "vfst ab \<in>\<^sub>\<circ> A" unfolding ab_def by simp
qed

lemma vsnd_arrow_ArrVal_app[cat_cs_simps]:
  assumes "ab = \<langle>a, b\<rangle>" and "ab \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
  shows "vsnd_arrow A B\<lparr>ArrVal\<rparr>\<lparr>ab\<rparr> = b"
  using assms(2) unfolding assms(1) by (simp add: vsnd_arrow_ArrVal_app')

lemma vsnd_arrow_vrange: "\<R>\<^sub>\<circ> (vsnd_arrow A B\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> B"
  unfolding vsnd_arrow_components
proof(intro vrange_VLambda_vsubset)
  fix ab assume "ab \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
  then obtain a b where ab_def: "ab = \<langle>a, b\<rangle>" and b: "b \<in>\<^sub>\<circ> B" by clarsimp
  from b show "vsnd ab \<in>\<^sub>\<circ> B" unfolding ab_def by simp
qed


subsubsection\<open>Projection arrows are arrows in the category \<open>Set\<close>\<close>

lemma (in \<Z>) vfst_arrow_is_cat_Set_arr_Vset:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vfst_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A"
proof(intro cat_Set_is_arrI arr_SetI, unfold cat_cs_simps)
  show "vfsequence (vfst_arrow A B)" unfolding vfst_arrow_def by simp
  show "vcard (vfst_arrow A B) = 3\<^sub>\<nat>"
    unfolding vfst_arrow_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (vfst_arrow A B\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> A" by (rule vfst_arrow_vrange)
qed (use assms in \<open>cs_concl cs_intro: V_cs_intros cat_cs_intros\<close>)+

lemma (in \<Z>) vfst_arrow_is_cat_Set_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "vfst_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A"
  using assms 
  unfolding cat_Set_components 
  by (rule vfst_arrow_is_cat_Set_arr_Vset)

lemma (in \<Z>) vfst_arrow_is_cat_Set_arr'[cat_rel_par_Set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> B"
    and "A' = A"
    and "\<CC>' = cat_Set \<alpha>"
  shows "vfst_arrow A B : AB \<mapsto>\<^bsub>\<CC>'\<^esub> A'"
  using assms(1-2) unfolding assms(3-5) by (rule vfst_arrow_is_cat_Set_arr)

lemmas [cat_rel_par_Set_cs_intros] = \<Z>.vfst_arrow_is_cat_Set_arr'

lemma (in \<Z>) vsnd_arrow_is_cat_Set_arr_Vset:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vsnd_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B"
proof(intro cat_Set_is_arrI arr_SetI , unfold cat_cs_simps)
  show "vfsequence (vsnd_arrow A B)" unfolding vsnd_arrow_def by simp
  show "vcard (vsnd_arrow A B) = 3\<^sub>\<nat>"
    unfolding vsnd_arrow_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (vsnd_arrow A B\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> B" by (rule vsnd_arrow_vrange)
qed (use assms in \<open>cs_concl cs_intro: V_cs_intros cat_cs_intros\<close>)+

lemma (in \<Z>) vsnd_arrow_is_cat_Set_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "vsnd_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B"
  using assms 
  unfolding cat_Set_components 
  by (rule vsnd_arrow_is_cat_Set_arr_Vset)

lemma (in \<Z>) vsnd_arrow_is_cat_Set_arr'[cat_rel_par_Set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> B"
    and "B' = B"
    and "\<CC>' = cat_Set \<alpha>"
  shows "vsnd_arrow A B : AB \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-2) unfolding assms(3-5) by (rule vsnd_arrow_is_cat_Set_arr)

lemmas [cat_rel_par_Set_cs_intros] = \<Z>.vsnd_arrow_is_cat_Set_arr'


subsubsection\<open>Projection arrows are arrows in the category \<open>Par\<close>\<close>

lemma (in \<Z>) vfst_arrow_is_cat_Par_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
  shows "vfst_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> A"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  from assms show ?thesis
    unfolding cat_Par_components(1)
    by (intro Set_Par.subcat_is_arrD vfst_arrow_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) vfst_arrow_is_cat_Par_arr'[cat_rel_Par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> B"
    and "A' = A"
    and "\<CC>' = cat_Par \<alpha>"
  shows "vfst_arrow A B : AB \<mapsto>\<^bsub>\<CC>'\<^esub> A'"
  using assms(1-2) unfolding assms(3-5) by (rule vfst_arrow_is_cat_Par_arr)

lemmas [cat_rel_Par_set_cs_intros] = \<Z>.vfst_arrow_is_cat_Par_arr'

lemma (in \<Z>) vsnd_arrow_is_cat_Par_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
  shows "vsnd_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Par \<alpha>\<^esub> B"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  from assms show ?thesis
    unfolding cat_Par_components(1)
    by (intro Set_Par.subcat_is_arrD vsnd_arrow_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) vsnd_arrow_is_cat_Par_arr'[cat_rel_Par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> B"
    and "B' = B"
    and "\<CC>' = cat_Par \<alpha>"
  shows "vsnd_arrow A B : AB \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-2) unfolding assms(3-5) by (rule vsnd_arrow_is_cat_Par_arr)

lemmas [cat_rel_Par_set_cs_intros] = \<Z>.vsnd_arrow_is_cat_Par_arr'


subsubsection\<open>Projection arrows are arrows in the category \<open>Rel\<close>\<close>

lemma (in \<Z>) vfst_arrow_is_cat_Rel_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "vfst_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A"
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
    by (intro Set_Rel.subcat_is_arrD vfst_arrow_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) vfst_arrow_is_cat_Rel_arr'[cat_Rel_par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> B"
    and "A' = A"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "vfst_arrow A B : AB \<mapsto>\<^bsub>\<CC>'\<^esub> A'"
  using assms(1-2) unfolding assms(3-5) by (rule vfst_arrow_is_cat_Rel_arr)

lemmas [cat_Rel_par_set_cs_intros] = \<Z>.vfst_arrow_is_cat_Rel_arr'

lemma (in \<Z>) vsnd_arrow_is_cat_Rel_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "vsnd_arrow A B : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B"
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
    by (intro Set_Rel.subcat_is_arrD vsnd_arrow_is_cat_Set_arr_Vset) auto
qed

lemma (in \<Z>) vsnd_arrow_is_cat_Rel_arr'[cat_Rel_par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> B"
    and "B' = B"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "vsnd_arrow A B : AB \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1-2) unfolding assms(3-5) by (rule vsnd_arrow_is_cat_Rel_arr)

lemmas [cat_Rel_par_set_cs_intros] = \<Z>.vsnd_arrow_is_cat_Rel_arr'


subsubsection\<open>Projection arrows are isomorphisms in the category \<open>Set\<close>\<close>

lemma (in \<Z>) vfst_arrow_is_cat_Set_arr_isomorphism_Vset:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vfst_arrow A (set {b}) : A \<times>\<^sub>\<circ> set {b} \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> A"
proof
  (
    intro 
      cat_Set_is_arr_isomorphismI 
      arr_SetI 
      vfst_arrow_is_cat_Set_arr_Vset 
      assms,
    unfold cat_cs_simps
  )
  show "v11 (vfst_arrow A (set {b})\<lparr>ArrVal\<rparr>)"
  proof(rule vsv.vsv_valeq_v11I, unfold cat_cs_simps)
    fix ab ab' assume prems:
      "ab \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> set {b}"
      "ab' \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> set {b}"
      "vfst_arrow A (set {b})\<lparr>ArrVal\<rparr>\<lparr>ab\<rparr> = vfst_arrow A (set {b})\<lparr>ArrVal\<rparr>\<lparr>ab'\<rparr>"
    from prems obtain a where ab_def: "ab = \<langle>a, b\<rangle>" and a: "a \<in>\<^sub>\<circ> A" 
      by clarsimp
    from prems obtain a' where ab'_def: "ab' = \<langle>a', b\<rangle>" and a': "a' \<in>\<^sub>\<circ> A" 
      by clarsimp
    from prems(3) a a' have "a = a'"
      unfolding ab_def ab'_def
      by (cs_prems cs_simp: cat_cs_simps cs_intro: V_cs_intros)
    then show "ab = ab'"  unfolding ab_def ab'_def by simp
  qed (cs_concl cs_intro: cat_cs_intros)
  show "\<R>\<^sub>\<circ> (vfst_arrow A (set {b})\<lparr>ArrVal\<rparr>) = A"
  proof(intro vsubset_antisym)
    show "A \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (vfst_arrow A (set {b})\<lparr>ArrVal\<rparr>)"
    proof(intro vsubsetI)
      fix a assume a: "a \<in>\<^sub>\<circ> A"
      then have a_def: "a = vfst_arrow A (set {b})\<lparr>ArrVal\<rparr>\<lparr>\<langle>a, b\<rangle>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
      from a assms show "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (vfst_arrow A (set {b})\<lparr>ArrVal\<rparr>)"
        by (subst a_def, use nothing in \<open>intro vsv.vsv_vimageI2\<close>) 
          (auto simp: cat_cs_simps cat_cs_intros)
    qed
  qed (rule vfst_arrow_vrange)
qed (use assms in auto)

lemma (in \<Z>) vfst_arrow_is_cat_Set_arr_isomorphism:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "vfst_arrow A (set {b}) : A \<times>\<^sub>\<circ> set {b} \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> A"
  using assms 
  unfolding cat_Set_components 
  by (rule vfst_arrow_is_cat_Set_arr_isomorphism_Vset)

lemma (in \<Z>) vfst_arrow_is_cat_Set_arr_isomorphism'[cat_rel_par_Set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> set {b}"
    and "A' = A"
    and "\<CC>' = cat_Set \<alpha>"
  shows "vfst_arrow A (set {b}) : AB \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> A"
  using assms(1-2) 
  unfolding assms(3-5)
  by (rule vfst_arrow_is_cat_Set_arr_isomorphism)

lemmas [cat_rel_par_Set_cs_intros] = \<Z>.vfst_arrow_is_cat_Set_arr_isomorphism'

lemma (in \<Z>) vsnd_arrow_is_cat_Set_arr_isomorphism_Vset:
  assumes "a \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vsnd_arrow (set {a}) B : set {a} \<times>\<^sub>\<circ> B \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B"
proof
  (
    intro 
      cat_Set_is_arr_isomorphismI 
      arr_SetI 
      vsnd_arrow_is_cat_Set_arr_Vset 
      assms,
    unfold cat_cs_simps
  )
  show "v11 (vsnd_arrow (set {a}) B\<lparr>ArrVal\<rparr>)"
  proof(rule vsv.vsv_valeq_v11I, unfold cat_cs_simps)
    fix ab ab' assume prems:
      "ab \<in>\<^sub>\<circ> set {a} \<times>\<^sub>\<circ> B"
      "ab' \<in>\<^sub>\<circ> set {a} \<times>\<^sub>\<circ> B"
      "vsnd_arrow (set {a}) B\<lparr>ArrVal\<rparr>\<lparr>ab\<rparr> = vsnd_arrow (set {a}) B\<lparr>ArrVal\<rparr>\<lparr>ab'\<rparr>"
    from prems obtain b where ab_def: "ab = \<langle>a, b\<rangle>" and b: "b \<in>\<^sub>\<circ> B" 
      by clarsimp
    from prems obtain b' where ab'_def: "ab' = \<langle>a, b'\<rangle>" and b': "b' \<in>\<^sub>\<circ> B" 
      by clarsimp
    from prems(3) b b' have "b = b'"
      unfolding ab_def ab'_def
      by (cs_prems cs_simp: cat_cs_simps cs_intro: V_cs_intros)
    then show "ab = ab'"  unfolding ab_def ab'_def by simp
  qed (cs_concl cs_intro: cat_cs_intros)
  show "\<R>\<^sub>\<circ> (vsnd_arrow (set {a}) B\<lparr>ArrVal\<rparr>) = B"
  proof(intro vsubset_antisym)
    show "B \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (vsnd_arrow (set {a}) B\<lparr>ArrVal\<rparr>)"
    proof(intro vsubsetI)
      fix b assume b: "b \<in>\<^sub>\<circ> B"
      then have b_def: "b = vsnd_arrow (set {a}) B\<lparr>ArrVal\<rparr>\<lparr>\<langle>a, b\<rangle>\<rparr>"
        by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
      from b assms show "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (vsnd_arrow (set {a}) B\<lparr>ArrVal\<rparr>)"
        by (subst b_def, use nothing in \<open>intro vsv.vsv_vimageI2\<close>) 
          (auto simp: cat_cs_simps cat_cs_intros)
    qed
  qed (rule vsnd_arrow_vrange)
qed (use assms in auto)

lemma (in \<Z>) vsnd_arrow_is_cat_Set_arr_isomorphism:
  assumes "a \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
  shows "vsnd_arrow (set {a}) B : set {a} \<times>\<^sub>\<circ> B \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B"
  using assms 
  unfolding cat_Set_components 
  by (rule vsnd_arrow_is_cat_Set_arr_isomorphism_Vset)

lemma (in \<Z>) vsnd_arrow_is_cat_Set_arr_isomorphism'[cat_rel_par_Set_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Set \<alpha>\<lparr>Obj\<rparr>"
    and "AB = set {a} \<times>\<^sub>\<circ> B"
    and "A' = A"
    and "\<CC>' = cat_Set \<alpha>"
  shows "vsnd_arrow (set {a}) B : AB \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B"
  using assms(1-2) 
  unfolding assms(3-5)
  by (rule vsnd_arrow_is_cat_Set_arr_isomorphism)

lemmas [cat_rel_par_Set_cs_intros] = \<Z>.vsnd_arrow_is_cat_Set_arr_isomorphism'


subsubsection\<open>Projection arrows are isomorphisms in the category \<open>Par\<close>\<close>

lemma (in \<Z>) vfst_arrow_is_cat_Par_arr_isomorphism:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
  shows "vfst_arrow A (set {b}) : A \<times>\<^sub>\<circ> set {b} \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> A"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  show "vfst_arrow A (set {b}) : A \<times>\<^sub>\<circ> set {b} \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> A"
    by 
      (
        rule Set_Par.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF vfst_arrow_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Par_components]
              ]
          ]
      )
qed

lemma (in \<Z>) vfst_arrow_is_cat_Par_arr_isomorphism'[cat_rel_Par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> set {b}"
    and "A' = A"
    and "\<CC>' = cat_Par \<alpha>"
  shows "vfst_arrow A (set {b}) : AB \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> A"
  using assms(1-2) 
  unfolding assms(3-5)
  by (rule vfst_arrow_is_cat_Par_arr_isomorphism)

lemmas [cat_rel_Par_set_cs_intros] = \<Z>.vfst_arrow_is_cat_Par_arr_isomorphism'

lemma (in \<Z>) vsnd_arrow_is_cat_Par_arr_isomorphism:
  assumes "a \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
  shows "vsnd_arrow (set {a}) B : set {a} \<times>\<^sub>\<circ> B \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
proof-
  interpret Set_Par: wide_replete_subcategory \<alpha> \<open>cat_Set \<alpha>\<close> \<open>cat_Par \<alpha>\<close> 
    by (rule wide_replete_subcategory_cat_Set_cat_Par)
  show "vsnd_arrow (set {a}) B : set {a} \<times>\<^sub>\<circ> B \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Par \<alpha>\<^esub> B"
    by 
      (
        rule Set_Par.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF vsnd_arrow_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Par_components]
              ]
          ]
      )
qed

lemma (in \<Z>) vsnd_arrow_is_cat_Par_arr_isomorphism'[cat_rel_Par_set_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Par \<alpha>\<lparr>Obj\<rparr>"
    and "AB = set {a} \<times>\<^sub>\<circ> B"
    and "A' = A"
    and "\<CC>' = cat_Par \<alpha>"
  shows "vsnd_arrow (set {a}) B : AB \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B"
  using assms(1-2) 
  unfolding assms(3-5)
  by (rule vsnd_arrow_is_cat_Par_arr_isomorphism)

lemmas [cat_rel_Par_set_cs_intros] = \<Z>.vsnd_arrow_is_cat_Par_arr_isomorphism'


subsubsection\<open>Projection arrows are isomorphisms in the category \<open>Rel\<close>\<close>

lemma (in \<Z>) vfst_arrow_is_cat_Rel_arr_isomorphism:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "vfst_arrow A (set {b}) : A \<times>\<^sub>\<circ> set {b} \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> A"
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
    by 
      (
        rule Set_Rel.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF vfst_arrow_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Rel_components]
              ]
          ]
      )
qed

lemma (in \<Z>) vfst_arrow_is_cat_Rel_arr_isomorphism'[cat_Rel_par_set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "AB = A \<times>\<^sub>\<circ> set {b}"
    and "A' = A"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "vfst_arrow A (set {b}) : AB \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> A"
  using assms(1-2) 
  unfolding assms(3-5)
  by (rule vfst_arrow_is_cat_Rel_arr_isomorphism)

lemmas [cat_Rel_par_set_cs_intros] = \<Z>.vfst_arrow_is_cat_Rel_arr_isomorphism'

lemma (in \<Z>) vsnd_arrow_is_cat_Rel_arr_isomorphism:
  assumes "a \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "vsnd_arrow (set {a}) B : set {a} \<times>\<^sub>\<circ> B \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Rel \<alpha>\<^esub> B"
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
    by 
      (
        rule Set_Rel.wr_subcat_is_arr_isomorphism_is_arr_isomorphism
          [
            THEN iffD1, 
            OF vsnd_arrow_is_cat_Set_arr_isomorphism_Vset[
              OF assms[unfolded cat_Rel_components]
              ]
          ]
      )
qed

lemma (in \<Z>) vsnd_arrow_is_cat_Rel_arr_isomorphism'[cat_Rel_par_set_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
    and "AB = set {a} \<times>\<^sub>\<circ> B"
    and "A' = A"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "vsnd_arrow (set {a}) B : AB \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> B"
  using assms(1-2) 
  unfolding assms(3-5)
  by (rule vsnd_arrow_is_cat_Rel_arr_isomorphism)

lemmas [cat_Rel_par_set_cs_intros] = \<Z>.vsnd_arrow_is_cat_Rel_arr_isomorphism'



subsection\<open>Projection arrow for \<open>vproduct\<close>\<close>

definition vprojection_arrow :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> V"
  where "vprojection_arrow I A i = [vprojection I A i, (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i), A i]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma vprojection_arrow_components:
  shows "vprojection_arrow I A i\<lparr>ArrVal\<rparr> = vprojection I A i"
    and "vprojection_arrow I A i\<lparr>ArrDom\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i)"
    and "vprojection_arrow I A i\<lparr>ArrCod\<rparr> = A i"
  unfolding vprojection_arrow_def arr_field_simps
  by (simp_all add: nat_omega_simps)


subsubsection\<open>Projection arrow value\<close>

mk_VLambda vprojection_arrow_components(1)[unfolded vprojection_def]
  |vsv vprojection_arrow_vsv[cat_Set_cs_intros]|
  |vdomain vprojection_arrow_vdomain[cat_Set_cs_simps]|
  |app vprojection_arrow_app[cat_Set_cs_simps]|


subsubsection\<open>Projection arrow is an arrow in the category \<open>Set\<close>\<close>

lemma (in \<Z>) arr_Set_vprojection_arrow:
  assumes "i \<in>\<^sub>\<circ> I" and "VLambda I A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Set \<alpha> (vprojection_arrow I A i)"
proof(intro arr_SetI)
  show "vfsequence (vprojection_arrow I A i)"
    unfolding vprojection_arrow_def by auto
  show "vcard (vprojection_arrow I A i) = 3\<^sub>\<nat>"
    unfolding vprojection_arrow_def by (simp add: nat_omega_simps)
  show "vprojection_arrow I A i\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding vprojection_arrow_components
  proof-
    from assms(1) have "i \<in>\<^sub>\<circ> I" by simp
    then have "A i \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (VLambda I A)" by auto
    moreover from assms(2) have "\<R>\<^sub>\<circ> (VLambda I A) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (meson vrange_in_VsetI)
    ultimately show "A i \<in>\<^sub>\<circ> Vset \<alpha>" by auto   
  qed
qed 
  (
    auto 
      simp: vprojection_arrow_components 
      intro!: 
        assms 
        vprojection_vrange_vsubset 
        Limit_vproduct_in_Vset_if_VLambda_in_VsetI
  )

lemma (in \<Z>) vprojection_arrow_is_arr:
  assumes "i \<in>\<^sub>\<circ> I" and "VLambda I A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vprojection_arrow I A i : (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. A i) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A i"
proof(intro cat_Set_is_arrI)
  from assms show "arr_Set \<alpha> (vprojection_arrow I A i)"
    by (rule arr_Set_vprojection_arrow)
qed (simp_all add: vprojection_arrow_components)



subsection\<open>Product arrow value for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition prod_2_Rel_ArrVal :: "V \<Rightarrow> V \<Rightarrow> V"
  where "prod_2_Rel_ArrVal S T =
    set {\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> | a b c d. \<langle>a, c\<rangle> \<in>\<^sub>\<circ> S \<and> \<langle>b, d\<rangle> \<in>\<^sub>\<circ> T}"

lemma small_prod_2_Rel_ArrVal[simp]:
  "small {\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> | a b c d. \<langle>a, c\<rangle> \<in>\<^sub>\<circ> S \<and> \<langle>b, d\<rangle> \<in>\<^sub>\<circ> T}"
  (is \<open>small ?S\<close>)
proof(rule down)
  show "?S \<subseteq> elts ((\<D>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> T) \<times>\<^sub>\<circ> (\<R>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> T))" by auto
qed


text\<open>Rules.\<close>

lemma prod_2_Rel_ArrValI:
  assumes "ab_cd = \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>"
    and "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S"
    and "\<langle>b, d\<rangle> \<in>\<^sub>\<circ> T"
  shows "ab_cd \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
  using assms unfolding prod_2_Rel_ArrVal_def by simp

lemma prod_2_Rel_ArrValD[dest]:
  assumes "\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
  shows "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S" and "\<langle>b, d\<rangle> \<in>\<^sub>\<circ> T"
  using assms unfolding prod_2_Rel_ArrVal_def by auto

lemma prod_2_Rel_ArrValE[elim]:
  assumes "ab_cd \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
  obtains a b c d where "ab_cd = \<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle>" 
    and "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S"
    and "\<langle>b, d\<rangle> \<in>\<^sub>\<circ> T"
  using assms unfolding prod_2_Rel_ArrVal_def by auto


text\<open>Elementary properties\<close>

lemma prod_2_Rel_ArrVal_vsubset_vprod:
  "prod_2_Rel_ArrVal S T \<subseteq>\<^sub>\<circ> ((\<D>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> T) \<times>\<^sub>\<circ> (\<R>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> T))"
  by auto

lemma prod_2_Rel_ArrVal_vbrelation: "vbrelation (prod_2_Rel_ArrVal S T)"
  using prod_2_Rel_ArrVal_vsubset_vprod by auto

lemma prod_2_Rel_ArrVal_vdomain: "\<D>\<^sub>\<circ> (prod_2_Rel_ArrVal S T) = \<D>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> T"
proof(intro vsubset_antisym)
  show "\<D>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> T \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (prod_2_Rel_ArrVal S T)"
  proof(intro vsubsetI)
    fix ab assume "ab \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> T"
    then obtain a b
      where ab_def: "ab = \<langle>a, b\<rangle>" 
        and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> S"
        and "b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> T"
      by auto
    then obtain c d where "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S" and "\<langle>b, d\<rangle> \<in>\<^sub>\<circ> T" by force
    then have "\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
      by (intro prod_2_Rel_ArrValI) auto
    then show "ab \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (prod_2_Rel_ArrVal S T)"
      unfolding ab_def by auto
  qed
qed (use prod_2_Rel_ArrVal_vsubset_vprod in blast)

lemma prod_2_Rel_ArrVal_vrange: "\<R>\<^sub>\<circ> (prod_2_Rel_ArrVal S T) = \<R>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> T"
proof(intro vsubset_antisym)
  show "\<R>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> T \<subseteq>\<^sub>\<circ> \<R>\<^sub>\<circ> (prod_2_Rel_ArrVal S T)"
  proof(intro vsubsetI)
    fix cd assume "cd \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> S \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> T"
    then obtain c d
      where cd_def: "cd = \<langle>c, d\<rangle>" 
        and "c \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> S"
        and "d \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> T"
      by auto
    then obtain a b where "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S" and "\<langle>b, d\<rangle> \<in>\<^sub>\<circ> T" by force
    then have "\<langle>\<langle>a, b\<rangle>, \<langle>c, d\<rangle>\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
      by (intro prod_2_Rel_ArrValI) auto
    then show "cd \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (prod_2_Rel_ArrVal S T)"
      unfolding cd_def by auto
  qed
qed (use prod_2_Rel_ArrVal_vsubset_vprod in blast)


subsubsection\<open>Further properties\<close>

lemma 
  assumes "vsv g" and "vsv f"
  shows prod_2_Rel_ArrVal_vsv: "vsv (prod_2_Rel_ArrVal g f)"
    and prod_2_Rel_ArrVal_app: 
      "\<And>a b. \<lbrakk> a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> g; b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f \<rbrakk> \<Longrightarrow> 
        prod_2_Rel_ArrVal g f\<lparr>\<langle>a,b\<rangle>\<rparr> = \<langle>g\<lparr>a\<rparr>, f\<lparr>b\<rparr>\<rangle>"
proof-
  interpret g: vsv g by (rule assms(1))
  interpret f: vsv f by (rule assms(2))
  show vsv_gf: "vsv (prod_2_Rel_ArrVal g f)"
    by (intro vsvI; (elim prod_2_Rel_ArrValE)?; (unfold prod_2_Rel_ArrVal_def)?)
      (auto simp: g.vsv f.vsv)
  fix a b assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> g" "b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f"
  then have a_ga: "\<langle>a, g\<lparr>a\<rparr>\<rangle> \<in>\<^sub>\<circ> g" and b_fb: "\<langle>b, f\<lparr>b\<rparr>\<rangle> \<in>\<^sub>\<circ> f" by auto
  from a_ga b_fb show "prod_2_Rel_ArrVal g f\<lparr>\<langle>a, b\<rangle>\<rparr> = \<langle>g\<lparr>a\<rparr>, f\<lparr>b\<rparr>\<rangle>"
    by (cs_concl cs_simp: vsv.vsv_appI[OF vsv_gf] cs_intro: prod_2_Rel_ArrValI)
qed

lemma prod_2_Rel_ArrVal_v11:
  assumes "v11 g" and "v11 f"
  shows "v11 (prod_2_Rel_ArrVal g f)"
proof-
  interpret g: v11 g by (rule assms(1))
  interpret f: v11 f by (rule assms(2))
  show ?thesis
  proof
    (
      intro vsv.vsv_valeq_v11I prod_2_Rel_ArrVal_vsv g.vsv_axioms f.vsv_axioms, 
      unfold prod_2_Rel_ArrVal_vdomain
    )
    fix ab cd
    assume prems:
      "ab \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> g \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> f"  
      "cd \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> g \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> f"
      "prod_2_Rel_ArrVal g f\<lparr>ab\<rparr> = prod_2_Rel_ArrVal g f\<lparr>cd\<rparr>"
    from prems(1) obtain a b
      where ab_def: "ab = \<langle>a, b\<rangle>" and a: "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> g" and b: "b \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f"
      by auto
    from prems(2) obtain c d
      where cd_def: "cd = \<langle>c, d\<rangle>" and c: "c \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> g" and d: "d \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> f"
      by auto
    from prems(3) a b c d have "\<langle>g\<lparr>a\<rparr>, f\<lparr>b\<rparr>\<rangle> = \<langle>g\<lparr>c\<rparr>, f\<lparr>d\<rparr>\<rangle>"
      unfolding ab_def cd_def
      by (cs_prems cs_simp: prod_2_Rel_ArrVal_app cs_intro: V_cs_intros)    
    then have "g\<lparr>a\<rparr> = g\<lparr>c\<rparr>" and "f\<lparr>b\<rparr> = f\<lparr>d\<rparr>" by simp_all
    then show "ab = cd"
      by (auto simp: ab_def cd_def a b c d f.v11_injective g.v11_injective)
  qed
qed

lemma prod_2_Rel_ArrVal_vcomp:
  "prod_2_Rel_ArrVal S' T' \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal S T =
    prod_2_Rel_ArrVal (S' \<circ>\<^sub>\<circ> S) (T' \<circ>\<^sub>\<circ> T)"
proof-
  interpret ST': vbrelation \<open>prod_2_Rel_ArrVal S' T'\<close>
    by (rule prod_2_Rel_ArrVal_vbrelation)
  interpret ST: vbrelation \<open>prod_2_Rel_ArrVal S T\<close>
    by (rule prod_2_Rel_ArrVal_vbrelation)
  show ?thesis (*TODO: simplify proof*)
  proof(intro vsubset_antisym vsubsetI)
    fix aa'_cc' assume 
      "aa'_cc' \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S' T' \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
    then obtain aa' bb' cc' where ac_def: "aa'_cc' = \<langle>aa', cc'\<rangle>" 
      and bc: "\<langle>bb', cc'\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S' T'"
      and ab: "\<langle>aa', bb'\<rangle> \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
      by auto
    from bc obtain b b' c c' 
      where bb'_cc'_def: "\<langle>bb', cc'\<rangle> = \<langle>\<langle>b, b'\<rangle>, \<langle>c, c'\<rangle>\<rangle>"
        and bc: "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> S'"
        and bc': "\<langle>b', c'\<rangle> \<in>\<^sub>\<circ> T'"
      by auto
    with ab obtain a a' 
      where aa'_bb'_def: "\<langle>aa', bb'\<rangle> = \<langle>\<langle>a, a'\<rangle>, \<langle>b, b'\<rangle>\<rangle>"
        and ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> S"
        and ab': "\<langle>a', b'\<rangle> \<in>\<^sub>\<circ> T"
      by auto
    from bb'_cc'_def have bb'_def: "bb' = \<langle>b, b'\<rangle>" and cc'_def: "cc' = \<langle>c, c'\<rangle>"
      by simp_all
    from aa'_bb'_def have aa'_def: "aa' = \<langle>a, a'\<rangle>" and bb'_def: "bb' = \<langle>b, b'\<rangle>"
      by simp_all
    from bc bc' ab ab' show "aa'_cc' \<in>\<^sub>\<circ> prod_2_Rel_ArrVal (S' \<circ>\<^sub>\<circ> S) (T' \<circ>\<^sub>\<circ> T)"
      unfolding ac_def aa'_def cc'_def
      by (intro prod_2_Rel_ArrValI)
        (cs_concl cs_intro: prod_2_Rel_ArrValI vcompI)+
  next
    fix aa'_cc' assume "aa'_cc' \<in>\<^sub>\<circ> prod_2_Rel_ArrVal (S' \<circ>\<^sub>\<circ> S) (T' \<circ>\<^sub>\<circ> T)"
    then obtain a a' c c'
      where aa'_cc'_def: "aa'_cc' = \<langle>\<langle>a, a'\<rangle>, \<langle>c, c'\<rangle>\<rangle>"
        and ac: "\<langle>a, c\<rangle> \<in>\<^sub>\<circ> S' \<circ>\<^sub>\<circ> S"
        and ac': "\<langle>a', c'\<rangle> \<in>\<^sub>\<circ> T' \<circ>\<^sub>\<circ> T"
      by blast
    from ac obtain b where ab: "\<langle>a, b\<rangle> \<in>\<^sub>\<circ> S" and bc: "\<langle>b, c\<rangle> \<in>\<^sub>\<circ> S'" 
      by auto
    from ac' obtain b' where ab': "\<langle>a', b'\<rangle> \<in>\<^sub>\<circ> T" and bc': "\<langle>b', c'\<rangle> \<in>\<^sub>\<circ> T'" 
      by auto
    from ab bc ab' bc' show 
      "aa'_cc' \<in>\<^sub>\<circ> prod_2_Rel_ArrVal S' T' \<circ>\<^sub>\<circ> prod_2_Rel_ArrVal S T"
      unfolding aa'_cc'_def by (cs_concl cs_intro: vcompI prod_2_Rel_ArrValI)
  qed
qed

lemma prod_2_Rel_ArrVal_vid_on[cat_cs_simps]:
  "prod_2_Rel_ArrVal (vid_on A) (vid_on B) = vid_on (A \<times>\<^sub>\<circ> B)"
  unfolding prod_2_Rel_ArrVal_def by auto



subsection\<open>Product arrow for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition prod_2_Rel :: "V \<Rightarrow> V \<Rightarrow> V"
  where "prod_2_Rel S T =
    [
      prod_2_Rel_ArrVal (S\<lparr>ArrVal\<rparr>) (T\<lparr>ArrVal\<rparr>),
      S\<lparr>ArrDom\<rparr> \<times>\<^sub>\<circ> T\<lparr>ArrDom\<rparr>,
      S\<lparr>ArrCod\<rparr> \<times>\<^sub>\<circ> T\<lparr>ArrCod\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma prod_2_Rel_components: 
  shows "prod_2_Rel S T\<lparr>ArrVal\<rparr> = prod_2_Rel_ArrVal (S\<lparr>ArrVal\<rparr>) (T\<lparr>ArrVal\<rparr>)"
    and [cat_cs_simps]: "prod_2_Rel S T\<lparr>ArrDom\<rparr> = S\<lparr>ArrDom\<rparr> \<times>\<^sub>\<circ> T\<lparr>ArrDom\<rparr>"
    and [cat_cs_simps]: "prod_2_Rel S T\<lparr>ArrCod\<rparr> = S\<lparr>ArrCod\<rparr> \<times>\<^sub>\<circ> T\<lparr>ArrCod\<rparr>"
  unfolding prod_2_Rel_def arr_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Product arrow for \<open>Rel\<close> is an arrow in \<open>Rel\<close>\<close>

lemma prod_2_Rel_is_cat_Rel_arr:
  assumes "S : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B" and "T : C \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> D"    
  shows "prod_2_Rel S T : A \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B \<times>\<^sub>\<circ> D"
proof-
  note S = cat_Rel_is_arrD[OF assms(1)]
  note T = cat_Rel_is_arrD[OF assms(2)]
  interpret S: arr_Rel \<alpha> S 
    rewrites [simp]: "S\<lparr>ArrDom\<rparr> = A" and [simp]: "S\<lparr>ArrCod\<rparr> = B"
    by (simp_all add: S)
  interpret T: arr_Rel \<alpha> T 
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = C" and [simp]: "T\<lparr>ArrCod\<rparr> = D"
    by (simp_all add: T)
  show ?thesis
  proof(intro cat_Rel_is_arrI arr_RelI)
    show "vfsequence (prod_2_Rel S T)"
      unfolding prod_2_Rel_def by simp
    show "vcard (prod_2_Rel S T) = 3\<^sub>\<nat>"
      unfolding prod_2_Rel_def by (simp add: nat_omega_simps)
    from S have "\<D>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> A" and "\<R>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> B" by auto
    moreover from T have "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> C" and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> D" 
      by auto
    ultimately have 
      "\<D>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>) \<times>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> C"
      "\<R>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>) \<times>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> B \<times>\<^sub>\<circ> D"
      by auto
    then show 
      "\<D>\<^sub>\<circ> (prod_2_Rel S T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> prod_2_Rel S T\<lparr>ArrDom\<rparr>"
      "\<R>\<^sub>\<circ> (prod_2_Rel S T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> prod_2_Rel S T\<lparr>ArrCod\<rparr>"
      unfolding 
        prod_2_Rel_components prod_2_Rel_ArrVal_vdomain prod_2_Rel_ArrVal_vrange
      by (force simp: prod_2_Rel_components)+
    from 
      S.arr_Rel_ArrDom_in_Vset T.arr_Rel_ArrDom_in_Vset
      S.arr_Rel_ArrCod_in_Vset T.arr_Rel_ArrCod_in_Vset
    show "prod_2_Rel S T\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" "prod_2_Rel S T\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      unfolding prod_2_Rel_components 
      by (all\<open>intro Limit_vtimes_in_VsetI\<close>) auto
  qed (auto simp: prod_2_Rel_components intro: prod_2_Rel_ArrVal_vbrelation)
qed

lemma prod_2_Rel_is_cat_Rel_arr'[cat_Rel_par_set_cs_intros]:
  assumes "S : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B"
    and "T : C \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> D"
    and "A' = A \<times>\<^sub>\<circ> C"
    and "B' = B \<times>\<^sub>\<circ> D"
    and "\<CC>' = cat_Rel \<alpha>"
  shows "prod_2_Rel S T : A' \<mapsto>\<^bsub>\<CC>'\<^esub> B'"
  using assms(1,2) unfolding assms(3-5) by (rule prod_2_Rel_is_cat_Rel_arr)


subsubsection\<open>Product arrow for \<open>Rel\<close> is an arrow in \<open>Set\<close>\<close>

lemma prod_2_Rel_app[cat_rel_par_Set_cs_simps]:
  assumes "S : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" 
    and "T : C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> D"    
    and "a \<in>\<^sub>\<circ> A"
    and "c \<in>\<^sub>\<circ> C"
    and "ac = \<langle>a, c\<rangle>"
  shows "prod_2_Rel S T\<lparr>ArrVal\<rparr>\<lparr>ac\<rparr> = \<langle>S\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>, T\<lparr>ArrVal\<rparr>\<lparr>c\<rparr>\<rangle>"
proof-
  note S = cat_Set_is_arrD[OF assms(1)]
  note T = cat_Set_is_arrD[OF assms(2)]
  interpret S: arr_Set \<alpha> S 
    rewrites [simp]: "S\<lparr>ArrDom\<rparr> = A" and [simp]: "S\<lparr>ArrCod\<rparr> = B"
    by (simp_all add: S)
  interpret T: arr_Set \<alpha> T 
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = C" and [simp]: "T\<lparr>ArrCod\<rparr> = D"
    by (simp_all add: T)
  from assms(3,4) show ?thesis
    unfolding prod_2_Rel_components(1) assms(5)
    by 
      (
        cs_concl 
          cs_simp: 
            S.arr_Set_ArrVal_vdomain 
            T.arr_Set_ArrVal_vdomain 
            prod_2_Rel_ArrVal_app 
          cs_intro: V_cs_intros
      )
qed

lemma prod_2_Rel_is_cat_Set_arr:
  assumes "S : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" and "T : C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> D"    
  shows "prod_2_Rel S T : A \<times>\<^sub>\<circ> C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B \<times>\<^sub>\<circ> D"
proof-

  note S = cat_Set_is_arrD[OF assms(1)]
  note T = cat_Set_is_arrD[OF assms(2)]

  interpret S: arr_Set \<alpha> S 
    rewrites [simp]: "S\<lparr>ArrDom\<rparr> = A" and [simp]: "S\<lparr>ArrCod\<rparr> = B"
    by (simp_all add: S)
  interpret T: arr_Set \<alpha> T 
    rewrites [simp]: "T\<lparr>ArrDom\<rparr> = C" and [simp]: "T\<lparr>ArrCod\<rparr> = D"
    by (simp_all add: T)

  show ?thesis
  proof(intro cat_Set_is_arrI arr_SetI)
    show "vfsequence (prod_2_Rel S T)"
      unfolding prod_2_Rel_def by simp
    show "vcard (prod_2_Rel S T) = 3\<^sub>\<nat>"
      unfolding prod_2_Rel_def by (simp add: nat_omega_simps)
    from S.arr_Set_ArrVal_vrange T.arr_Set_ArrVal_vrange show 
      "\<R>\<^sub>\<circ> (prod_2_Rel S T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> prod_2_Rel S T\<lparr>ArrCod\<rparr>"
      unfolding 
        prod_2_Rel_components prod_2_Rel_ArrVal_vdomain prod_2_Rel_ArrVal_vrange
      by auto
    from assms S.arr_Par_ArrDom_in_Vset T.arr_Par_ArrDom_in_Vset show 
      "prod_2_Rel S T\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
    from assms S.arr_Par_ArrCod_in_Vset T.arr_Par_ArrCod_in_Vset show 
      "prod_2_Rel S T\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: V_cs_intros)
    from assms show "prod_2_Rel S T\<lparr>ArrDom\<rparr> = A \<times>\<^sub>\<circ> C"
      by (cs_concl cs_simp: cat_cs_simps)
    from assms show "prod_2_Rel S T\<lparr>ArrCod\<rparr> = B \<times>\<^sub>\<circ> D"
      by (cs_concl cs_simp: cat_cs_simps)
    show "vsv (prod_2_Rel S T\<lparr>ArrVal\<rparr>)"
      unfolding prod_2_Rel_components
      by (intro prod_2_Rel_ArrVal_vsv S.ArrVal.vsv_axioms T.ArrVal.vsv_axioms)
  qed 
    (
      auto simp: 
        cat_cs_simps cat_Set_cs_simps 
        prod_2_Rel_ArrVal_vdomain prod_2_Rel_components(1)
    )

qed

lemma prod_2_Rel_is_cat_Set_arr'[cat_rel_par_Set_cs_intros]:
  assumes "S : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> B" 
    and "T : C \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> D"
    and "AC = A \<times>\<^sub>\<circ> C"
    and "BD = B \<times>\<^sub>\<circ> D"
    and "\<CC>' = cat_Set \<alpha>"
  shows "prod_2_Rel S T : AC \<mapsto>\<^bsub>\<CC>'\<^esub> BD"
  using assms(1,2) unfolding assms(3-5) by (rule prod_2_Rel_is_cat_Set_arr)


subsubsection\<open>Product arrow for \<open>Rel\<close> is an isomorphism in \<open>Set\<close>\<close>

lemma prod_2_Rel_is_cat_Set_arr_isomorphism:
  assumes "S : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B" and "T : C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> D"    
  shows "prod_2_Rel S T : A \<times>\<^sub>\<circ> C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B \<times>\<^sub>\<circ> D"
proof-
  note S = cat_Set_is_arr_isomorphismD[OF assms(1)]
  note T = cat_Set_is_arr_isomorphismD[OF assms(2)]
  show ?thesis
  proof
    (
      intro cat_Set_is_arr_isomorphismI prod_2_Rel_is_cat_Set_arr[OF S(1) T(1)], 
      unfold prod_2_Rel_components
    )
    show "\<D>\<^sub>\<circ> (prod_2_Rel_ArrVal (S\<lparr>ArrVal\<rparr>) (T\<lparr>ArrVal\<rparr>)) = A \<times>\<^sub>\<circ> C"
      unfolding prod_2_Rel_ArrVal_vdomain
      by (cs_concl cs_simp: S(3) T(3) cs_intro: cat_cs_intros)
    show "\<R>\<^sub>\<circ> (prod_2_Rel_ArrVal (S\<lparr>ArrVal\<rparr>) (T\<lparr>ArrVal\<rparr>)) = B \<times>\<^sub>\<circ> D"
      unfolding prod_2_Rel_ArrVal_vrange
      by (cs_concl cs_simp: S(4) T(4) cs_intro: cat_cs_intros)
  qed (use S(2) T(2) in \<open>cs_concl cs_intro: prod_2_Rel_ArrVal_v11\<close>)
qed

lemma prod_2_Rel_is_cat_Set_arr_isomorphism'[cat_rel_par_Set_cs_intros]:
  assumes "S : A \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> B" 
    and "T : C \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>cat_Set \<alpha>\<^esub> D"    
    and "AC = A \<times>\<^sub>\<circ> C"
    and "BD = B \<times>\<^sub>\<circ> D"
    and "\<CC>' = cat_Set \<alpha>"
  shows "prod_2_Rel S T : AC \<mapsto>\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<CC>'\<^esub> BD"
  using assms(1,2) 
  unfolding assms(3-5) 
  by (rule prod_2_Rel_is_cat_Set_arr_isomorphism)


subsubsection\<open>Further elementary properties\<close>

lemma prod_2_Rel_Comp:
  assumes "G' : B' \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B''" 
    and "F' : A' \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A''" 
    and "G : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B'"
    and "F : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A'"
  shows
    "prod_2_Rel G' F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel G F =
      prod_2_Rel (G' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> G) (F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> F)"
proof-

  from cat_Rel_is_arrD(1)[OF assms(1)] interpret \<Z> \<alpha> by auto

  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
  note (*prefer cat_Rel*)[cat_cs_simps] = cat_Rel_is_arrD(2,3)

  from assms have GF'_GF: 
    "prod_2_Rel G' F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel G F :
      B \<times>\<^sub>\<circ> A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B'' \<times>\<^sub>\<circ> A''"
    by (cs_concl cs_intro: cat_Rel_par_set_cs_intros cat_cs_intros)
  from assms Rel.category_axioms have GG'_FF':
    "prod_2_Rel (G' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> G) (F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> F) : 
      B \<times>\<^sub>\<circ> A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B'' \<times>\<^sub>\<circ> A''"
    by (cs_concl cs_intro: cat_Rel_par_set_cs_intros cat_cs_intros)

  show ?thesis
  proof(rule arr_Rel_eqI[of \<alpha>])
    from GF'_GF show arr_Rel_GF'_GF:
      "arr_Rel \<alpha> (prod_2_Rel G' F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel G F)"
      by (auto dest: cat_Rel_is_arrD(1))
    from GG'_FF' show arr_Rel_GG'_FF':
      "arr_Rel \<alpha> (prod_2_Rel (G' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> G) (F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> F))"
      by (auto dest: cat_Rel_is_arrD(1))
    show "(prod_2_Rel G' F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel G F)\<lparr>ArrVal\<rparr> = 
      prod_2_Rel (G' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> G) (F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>"
    proof(intro vsubset_antisym vsubsetI)
      fix R assume
        "R \<in>\<^sub>\<circ> (prod_2_Rel G' F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel G F)\<lparr>ArrVal\<rparr>"
      from this assms have "R \<in>\<^sub>\<circ>
        prod_2_Rel_ArrVal (G'\<lparr>ArrVal\<rparr>) (F'\<lparr>ArrVal\<rparr>) \<circ>\<^sub>\<circ>
        prod_2_Rel_ArrVal (G\<lparr>ArrVal\<rparr>) (F\<lparr>ArrVal\<rparr>)"
        by 
          (
            cs_prems 
              cs_simp: 
                prod_2_Rel_components(1) 
                comp_Rel_components(1)
                cat_Rel_cs_simps 
              cs_intro: cat_Rel_par_set_cs_intros
          )
      from this[unfolded prod_2_Rel_ArrVal_vcomp] assms show 
        "R \<in>\<^sub>\<circ> prod_2_Rel (G' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> G) (F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>"
        by 
          (
            cs_concl cs_simp: 
              prod_2_Rel_components comp_Rel_components(1) cat_Rel_cs_simps 
          )
    next
      fix R assume
        "R \<in>\<^sub>\<circ> prod_2_Rel (G' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> G) (F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> F)\<lparr>ArrVal\<rparr>"
      from this assms have 
        "R \<in>\<^sub>\<circ> prod_2_Rel_ArrVal (G'\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> G\<lparr>ArrVal\<rparr>) (F'\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> F\<lparr>ArrVal\<rparr>)"
        by 
          (
            cs_prems cs_simp:
              comp_Rel_components prod_2_Rel_components cat_Rel_cs_simps
          )
      from this[folded prod_2_Rel_ArrVal_vcomp] assms show
        "R \<in>\<^sub>\<circ> (prod_2_Rel G' F' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub> prod_2_Rel G F)\<lparr>ArrVal\<rparr>"
        by
          (
            cs_concl 
              cs_simp:
                prod_2_Rel_components comp_Rel_components(1) cat_Rel_cs_simps 
              cs_intro: cat_Rel_par_set_cs_intros
          )
    qed

  qed
    (
      use GF'_GF assms in (*slow*)
        \<open>
          cs_concl
            cs_simp: cat_cs_simps
            cs_intro: cat_cs_intros cat_Rel_cs_intros
        \<close>
    )+

qed

lemma (in \<Z>) prod_2_Rel_CId[cat_cs_simps]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" and "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows 
    "prod_2_Rel (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>) (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>) = cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> B\<rparr>"
proof-
  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close> by (rule category_cat_Rel)
  from assms have A_B: 
    "prod_2_Rel (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>) (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>) :
      A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A \<times>\<^sub>\<circ> B"
    by (cs_concl cs_intro: cat_Rel_par_set_cs_intros cat_cs_intros)
  from assms Rel.category_axioms have AB:
    "cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> B\<rparr> : A \<times>\<^sub>\<circ> B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A \<times>\<^sub>\<circ> B"
    by 
      (
        cs_concl 
          cs_simp: cat_Rel_components(1) cs_intro: V_cs_intros cat_cs_intros
      )
  show ?thesis
  proof(rule arr_Rel_eqI)
    from A_B show arr_Rel_GF'_GF:
      "arr_Rel \<alpha> (prod_2_Rel (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>) (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>))"
      by (auto dest: cat_Rel_is_arrD(1))
    from AB show arr_Rel_GG'_FF': "arr_Rel \<alpha> (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> B\<rparr>)"
      by (auto dest: cat_Rel_is_arrD(1))
    from assms show 
      "prod_2_Rel (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr>) (cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>B\<rparr>)\<lparr>ArrVal\<rparr> =
        cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A \<times>\<^sub>\<circ> B\<rparr>\<lparr>ArrVal\<rparr>"
      by
        (
          cs_concl
            cs_simp:
              id_Rel_components prod_2_Rel_components
              cat_cs_simps cat_Rel_cs_simps 
            cs_intro: V_cs_intros  cat_cs_intros 
        )
  qed 
    (
      use A_B assms in 
        \<open>
          cs_concl
            cs_simp: prod_2_Rel_components cat_Rel_cs_simps 
            cs_intro: cat_cs_intros 
        \<close>
    )+
qed



subsection\<open>Product functor for \<open>Rel\<close>\<close>

definition cf_prod_2_Rel :: "V \<Rightarrow> V"
  where "cf_prod_2_Rel \<AA> =
    [
      (\<lambda>AB\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>. AB\<lparr>0\<rparr> \<times>\<^sub>\<circ> AB\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>ST\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>. prod_2_Rel (ST\<lparr>0\<rparr>) (ST\<lparr>1\<^sub>\<nat>\<rparr>)),
      \<AA> \<times>\<^sub>C \<AA>,
      \<AA>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_prod_2_Rel_components: 
  shows "cf_prod_2_Rel \<AA>\<lparr>ObjMap\<rparr> = (\<lambda>AB\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>. AB\<lparr>0\<rparr> \<times>\<^sub>\<circ> AB\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "cf_prod_2_Rel \<AA>\<lparr>ArrMap\<rparr> =
      (\<lambda>ST\<in>\<^sub>\<circ>(\<AA> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>. prod_2_Rel (ST\<lparr>0\<rparr>) (ST\<lparr>1\<^sub>\<nat>\<rparr>))"
    and [cat_cs_simps]: "cf_prod_2_Rel \<AA>\<lparr>HomDom\<rparr> = \<AA> \<times>\<^sub>C \<AA>"
    and [cat_cs_simps]: "cf_prod_2_Rel \<AA>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding cf_prod_2_Rel_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda cf_prod_2_Rel_components(1)
  |vsv cf_prod_2_Rel_ObjMap_vsv[cat_cs_intros]|
  |vdomain cf_prod_2_Rel_ObjMap_vdomain[cat_cs_simps]|

lemma cf_prod_2_Rel_ObjMap_app[cat_cs_simps]: 
  assumes "AB = [A, B]\<^sub>\<circ>" and "AB \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<AA>)\<lparr>Obj\<rparr>"
  shows "A \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>O\<^bsub>cf_prod_2_Rel \<AA>\<^esub> B = A \<times>\<^sub>\<circ> B"
  using assms(2) 
  unfolding assms(1) cf_prod_2_Rel_components 
  by (simp add: nat_omega_simps)

lemma (in \<Z>) cf_prod_2_Rel_ObjMap_vrange: 
  "\<R>\<^sub>\<circ> (cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
proof-
  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_Rel_cs_intros)
  show ?thesis
  proof(rule vsv.vsv_vrange_vsubset, unfold cat_cs_simps)
    fix AB assume prems: "AB \<in>\<^sub>\<circ> (cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>)\<lparr>Obj\<rparr>"
    with Rel.category_axioms obtain A B where AB_def: "AB = [A, B]\<^sub>\<circ>"
      and A: "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
      and B: "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
      by (elim cat_prod_2_ObjE[rotated 2])
    from prems A B show "cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>AB\<rparr> \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
      unfolding AB_def cat_Rel_components(1)
      by (cs_concl cs_simp: cat_cs_simps cat_Rel_cs_simps cs_intro: V_cs_intros)
  qed (cs_concl cs_intro: cat_cs_intros)
qed


subsubsection\<open>Arrow map\<close>

mk_VLambda cf_prod_2_Rel_components(2)
  |vsv cf_prod_2_Rel_ArrMap_vsv[cat_cs_intros]|
  |vdomain cf_prod_2_Rel_ArrMap_vdomain[cat_cs_simps]|

lemma cf_prod_2_Rel_ArrMap_app[cat_cs_simps]: 
  assumes "GF = [G, F]\<^sub>\<circ>" and "GF \<in>\<^sub>\<circ> (\<AA> \<times>\<^sub>C \<AA>)\<lparr>Arr\<rparr>"
  shows "G \<otimes>\<^sub>H\<^sub>M\<^sub>.\<^sub>A\<^bsub>cf_prod_2_Rel \<AA>\<^esub> F = prod_2_Rel G F"
  using assms(2) 
  unfolding assms(1) cf_prod_2_Rel_components 
  by (simp add: nat_omega_simps)


subsubsection\<open>Product functor for \<open>Rel\<close> is a functor\<close>

lemma (in \<Z>) cf_prod_2_Rel_is_functor:
  "cf_prod_2_Rel (cat_Rel \<alpha>) : cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> cat_Rel \<alpha>"
proof-

  interpret Rel: category \<alpha> \<open>cat_Rel \<alpha>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_Rel_cs_intros)

  show ?thesis
  proof(rule is_functorI')
   show "vfsequence (cf_prod_2_Rel (cat_Rel \<alpha>))"
      unfolding cf_prod_2_Rel_def by auto
    show "vcard (cf_prod_2_Rel (cat_Rel \<alpha>)) = 4\<^sub>\<nat>"
      unfolding cf_prod_2_Rel_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
      by (rule cf_prod_2_Rel_ObjMap_vrange)
    show "cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>GF\<rparr> :
      cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>AB\<rparr> \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub>
      cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>CD\<rparr>"
      if "GF : AB \<mapsto>\<^bsub>cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>\<^esub> CD" for AB CD GF
    proof-
      from that obtain G F A B C D
        where GF_def: "GF = [G, F]\<^sub>\<circ>"
          and AB_def: "AB = [A, B]\<^sub>\<circ>"
          and CD_def: "CD = [C, D]\<^sub>\<circ>"
          and G: "G : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> C"
          and F: "F : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> D"
        by (elim cat_prod_2_is_arrE[OF Rel.category_axioms Rel.category_axioms])
      from that G F show ?thesis
        unfolding GF_def AB_def CD_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps 
              cs_intro: 
                cat_Rel_par_set_cs_intros cat_cs_intros cat_prod_cs_intros
          )
    qed

    show 
      "cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>GF' \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>\<^esub> GF\<rparr> =
        cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>GF'\<rparr> \<circ>\<^sub>A\<^bsub>cat_Rel \<alpha>\<^esub>
          cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>GF\<rparr>"
      if "GF' : AB' \<mapsto>\<^bsub>cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>\<^esub> AB''"
        and "GF : AB \<mapsto>\<^bsub>cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>\<^esub> AB'"
      for AB' AB'' GF' AB GF
    proof-
      from that(2) obtain G F A A' B B' 
        where GF_def: "GF = [G, F]\<^sub>\<circ>"
          and AB_def: "AB = [A, B]\<^sub>\<circ>"
          and AB'_def: "AB' = [A', B']\<^sub>\<circ>"
          and G: "G : A \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A'"
          and F: "F : B \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B'"
        by (elim cat_prod_2_is_arrE[OF Rel.category_axioms Rel.category_axioms])
      with that(1) obtain G' F' A'' B''
        where GF'_def: "GF' = [G', F']\<^sub>\<circ>"
          and AB''_def: "AB'' = [A'', B'']\<^sub>\<circ>"
          and G': "G' : A' \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> A''"
          and F': "F' : B' \<mapsto>\<^bsub>cat_Rel \<alpha>\<^esub> B''"
        by 
          (
            auto elim: 
              cat_prod_2_is_arrE[OF Rel.category_axioms Rel.category_axioms]
          )
      from that G F G' F' show ?thesis
        unfolding GF_def AB_def AB'_def GF'_def AB''_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_prod_cs_simps prod_2_Rel_Comp
              cs_intro: cat_cs_intros cat_prod_cs_intros
          )
    qed

    show 
      "cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>(cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>)\<lparr>CId\<rparr>\<lparr>AB\<rparr>\<rparr> =
        cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>cf_prod_2_Rel (cat_Rel \<alpha>)\<lparr>ObjMap\<rparr>\<lparr>AB\<rparr>\<rparr>"
      if "AB \<in>\<^sub>\<circ> (cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>)\<lparr>Obj\<rparr>" for AB 
    proof-
      from that obtain A B 
        where AB_def: "AB = [A, B]\<^sub>\<circ>"
          and A: "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
          and B: "B \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
        by (elim cat_prod_2_ObjE[OF Rel.category_axioms Rel.category_axioms])
      from A B show ?thesis
        unfolding AB_def     
        by
          (
            cs_concl
              cs_simp:
                cf_prod_2_Rel_ObjMap_app cf_prod_2_Rel_ArrMap_app
                cat_cs_simps cat_prod_cs_simps
              cs_intro:
                V_cs_intros cat_cs_intros cat_Rel_cs_intros cat_prod_cs_intros
          )
    qed

  qed
    (
      cs_concl
        cs_simp: cat_cs_simps 
        cs_intro: cat_cs_intros cat_cs_intros cat_Rel_cs_intros
    )+

qed

lemma (in \<Z>) cf_prod_2_Rel_is_functor'[cat_cs_intros]:
  assumes "\<AA>' = cat_Rel \<alpha> \<times>\<^sub>C cat_Rel \<alpha>"
    and "\<BB>' = cat_Rel \<alpha>"
    and "\<alpha>' = \<alpha>"
  shows "cf_prod_2_Rel (cat_Rel \<alpha>) : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>'\<^esub> \<BB>'"
  unfolding assms by (rule cf_prod_2_Rel_is_functor)

lemmas [cat_cs_intros] = \<Z>.cf_prod_2_Rel_is_functor'



subsection\<open>Product universal property arrow for \<open>Set\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition cat_Set_obj_prod_up :: "V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V \<Rightarrow> (V \<Rightarrow> V) \<Rightarrow> V"
  where "cat_Set_obj_prod_up I F A \<phi> =
    [(\<lambda>a\<in>\<^sub>\<circ>A. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)), A, (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_Set_obj_prod_up_components: 
  shows "cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr> = 
    (\<lambda>a\<in>\<^sub>\<circ>A. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>))"
    and [cat_Set_cs_simps]: 
      "cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrDom\<rparr> = A"
    and [cat_Set_cs_simps]: 
      "cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrCod\<rparr> = (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
  unfolding cat_Set_obj_prod_up_def arr_field_simps 
  by (simp_all add: nat_omega_simps)


text\<open>Arrow value.\<close>

mk_VLambda cat_Set_obj_prod_up_components(1)
  |vsv cat_Set_obj_prod_up_ArrVal_vsv[cat_Set_cs_intros]|
  |vdomain cat_Set_obj_prod_up_ArrVal_vdomain[cat_Set_cs_simps]|
  |app cat_Set_obj_prod_up_ArrVal_app|

lemma cat_Set_obj_prod_up_ArrVal_vrange: 
  assumes "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i"
  shows "\<R>\<^sub>\<circ> (cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
  unfolding cat_Set_obj_prod_up_components 
proof(intro vrange_VLambda_vsubset vproductI)
  fix a assume prems: "a \<in>\<^sub>\<circ> A"
  show "\<forall>i\<in>\<^sub>\<circ>I. (\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> F i"
  proof(intro ballI)
    fix i assume "i \<in>\<^sub>\<circ> I"
    with assms prems show "(\<lambda>i\<in>\<^sub>\<circ>I. \<phi> i\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)\<lparr>i\<rparr> \<in>\<^sub>\<circ> F i"
      by (cs_concl cs_simp: V_cs_simps cs_intro: cat_Set_cs_intros)
  qed
qed auto

lemma cat_Set_obj_prod_up_ArrVal_app_vdomain[cat_Set_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> A"
  shows "\<D>\<^sub>\<circ> (cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>) = I"
  unfolding cat_Set_obj_prod_up_ArrVal_app[OF assms] by simp

lemma cat_Set_obj_prod_up_ArrVal_app_component[cat_Set_cs_simps]: 
  assumes "a \<in>\<^sub>\<circ> A" and "i \<in>\<^sub>\<circ> I"
  shows "cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr> = \<phi> i\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
  using assms 
  by (cs_concl cs_simp: cat_Set_obj_prod_up_ArrVal_app V_cs_simps)

lemma cat_Set_obj_prod_up_ArrVal_app_vrange: 
  assumes "a \<in>\<^sub>\<circ> A" and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i"
  shows "\<R>\<^sub>\<circ> (cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>) \<subseteq>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
proof(intro vsubsetI)
  fix b assume prems: "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)"
  from assms(1) have "vsv (cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>)"
    by (auto simp: cat_Set_obj_prod_up_components)
  with prems obtain i 
    where b_def: "b = cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>\<lparr>i\<rparr>" 
      and i: "i \<in>\<^sub>\<circ> I"
    by 
      ( 
        auto 
          elim: vsv.vrange_atE 
          simp: cat_Set_obj_prod_up_ArrVal_app[OF assms(1)]
      )
  from cat_Set_obj_prod_up_ArrVal_app_component[OF assms(1) i] b_def have b_def':
    "b = \<phi> i\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
    by simp
  from assms(1) assms(2)[OF i] have "b \<in>\<^sub>\<circ> F i" 
    unfolding b_def' by (cs_concl cs_intro: cat_Set_cs_intros)
  with i show "b \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)" by force
qed


subsubsection\<open>Product universal property arrow for \<open>Set\<close> is an arrow in \<open>Set\<close>\<close>

lemma (in \<Z>) cat_Set_obj_prod_up_cat_Set_is_arr:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "VLambda I F \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i"
  shows "cat_Set_obj_prod_up I F A \<phi> : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
proof(intro cat_Set_is_arrI arr_SetI)
  show "vfsequence (cat_Set_obj_prod_up I F A \<phi>)"
    unfolding cat_Set_obj_prod_up_def by auto
  show "vcard (cat_Set_obj_prod_up I F A \<phi>) = 3\<^sub>\<nat>"
    unfolding cat_Set_obj_prod_up_def by (auto simp: nat_omega_simps)
  show 
    "\<R>\<^sub>\<circ> (cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ>
      cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrCod\<rparr>"
    unfolding cat_Set_obj_prod_up_components(3)
    by (rule cat_Set_obj_prod_up_ArrVal_vrange[OF assms(3)])
  show "cat_Set_obj_prod_up I F A \<phi>\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding cat_Set_cs_simps
    by (rule Limit_vproduct_in_Vset_if_VLambda_in_VsetI)
      (simp_all add: cat_Set_cs_simps assms)
qed (auto simp: assms cat_Set_cs_simps intro: cat_Set_cs_intros)

lemma (in \<Z>) pdg_dghm_comp_dghm_proj_dghm_up: 
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "VLambda I F \<in>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>i. i \<in>\<^sub>\<circ> I \<Longrightarrow> \<phi> i : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i" 
    and "i \<in>\<^sub>\<circ> I"
  shows 
    "\<phi> i = vprojection_arrow I F i \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> cat_Set_obj_prod_up I F A \<phi>"
    (is \<open>\<phi> i = ?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>\<close>)
proof(rule arr_Set_eqI[of \<alpha>])
  note \<phi>i = assms(3)[OF assms(4)]
  note \<phi>i = cat_Set_is_arrD[OF \<phi>i] \<phi>i
  have Fi: "?Fi : (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i) \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i"
    by (rule vprojection_arrow_is_arr[OF assms(4,2)])
  from cat_Set_obj_prod_up_cat_Set_is_arr[OF assms(1,2,3)] have \<phi>:
    "cat_Set_obj_prod_up I F A \<phi> : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ>I. F i)"
    by simp
  show "arr_Set \<alpha> (\<phi> i)" by (rule \<phi>i(1))
  interpret \<phi>i: arr_Set \<alpha> \<open>\<phi> i\<close> by (rule \<phi>i(1))
  from Fi \<phi> have Fi_\<phi>: "?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi> : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> F i"
    by (cs_concl cs_intro: cat_cs_intros)
  then show arr_Set_Fi_\<phi>: "arr_Set \<alpha> (?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>)"
    by (auto simp: cat_Set_is_arrD(1))
  interpret arr_Set \<alpha> \<open>?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>\<close> by (rule arr_Set_Fi_\<phi>)
  from \<phi>i have dom_lhs: "\<D>\<^sub>\<circ> (\<phi> i\<lparr>ArrVal\<rparr>) = A"
    by (cs_concl cs_simp: cat_cs_simps)
  from Fi_\<phi> have dom_rhs: "\<D>\<^sub>\<circ> ((?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>)\<lparr>ArrVal\<rparr>) = A"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  show "\<phi> i\<lparr>ArrVal\<rparr> = (?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>)\<lparr>ArrVal\<rparr>"
  proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
    fix a assume prems: "a \<in>\<^sub>\<circ> A"
    from assms(4) prems \<phi>i(4) \<phi> Fi show 
      "\<phi> i\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = (?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
      by 
        ( 
          cs_concl 
            cs_simp: cat_Set_cs_simps cat_cs_simps 
            cs_intro: cat_Set_cs_intros cat_cs_intros
        )
  qed auto
  from Fi \<phi> show "\<phi> i\<lparr>ArrDom\<rparr> = (?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>)\<lparr>ArrDom\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cat_Set_cs_simps \<phi>i(2))
  from Fi \<phi> show "\<phi> i\<lparr>ArrCod\<rparr> = (?Fi \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?\<phi>)\<lparr>ArrCod\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cat_Set_cs_simps \<phi>i(3))
qed



subsection\<open>Equalizer object for the category \<open>Set\<close>\<close>


text\<open>
The definition of the (non-categorical concept of an) equalizer can be 
found in \cite{noauthor_wikipedia_2001}\footnote{
\url{https://en.wikipedia.org/wiki/Equaliser_(mathematics)}
}\<close>

definition vequalizer :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "vequalizer X f g = set {x. x \<in>\<^sub>\<circ> X \<and> f\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = g\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>}"

lemma small_vequalizer[simp]: 
  "small {x. x \<in>\<^sub>\<circ> X \<and> f\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = g\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>}"
  by auto


text\<open>Rules.\<close>

lemma vequalizerI:
  assumes "x \<in>\<^sub>\<circ> X" and "f\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = g\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>"
  shows "x \<in>\<^sub>\<circ> vequalizer X f g"
  using assms unfolding vequalizer_def by auto

lemma vequalizerD[dest]:
  assumes "x \<in>\<^sub>\<circ> vequalizer X f g"
  shows "x \<in>\<^sub>\<circ> X" and "f\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = g\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>"
  using assms unfolding vequalizer_def by auto

lemma vequalizerE[elim]:
  assumes "x \<in>\<^sub>\<circ> vequalizer X f g"
  obtains "x \<in>\<^sub>\<circ> X" and "f\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = g\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>"
  using assms unfolding vequalizer_def by auto


text\<open>Elementary results.\<close>

lemma vequalizer_vsubset_vdomain[cat_Set_cs_intros]: "vequalizer a g f \<subseteq>\<^sub>\<circ> a" 
  by auto
  
lemma Limit_vequalizer_in_Vset[cat_Set_cs_intros]:
  assumes "Limit \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "vequalizer a g f \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms by auto

lemma vequalizer_flip: "vequalizer a f g = vequalizer a g f"
  unfolding vequalizer_def by auto

lemma (in \<Z>) cat_Set_incl_Set_commute:
  assumes "\<gg> : \<aa> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>" and "\<ff> : \<aa> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>" 
  shows 
    "\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> incl_Set (vequalizer \<aa> \<ff> \<gg>) \<aa> =
      \<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> incl_Set (vequalizer \<aa> \<ff> \<gg>) \<aa>"
  (is \<open>\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl = \<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl\<close>)
proof-

  note \<gg> = cat_Set_is_arrD[OF assms(1)]
  interpret \<gg>: arr_Set \<alpha> \<gg> 
    rewrites "\<gg>\<lparr>ArrDom\<rparr> = \<aa>" and "\<gg>\<lparr>ArrCod\<rparr> = \<bb>"
    by (rule \<gg>(1)) (simp_all add: \<gg>)
  note \<ff> = cat_Set_is_arrD[OF assms(2)]
  interpret \<ff>: arr_Set \<alpha> \<ff> 
    rewrites "\<ff>\<lparr>ArrDom\<rparr> = \<aa>" and "\<ff>\<lparr>ArrCod\<rparr> = \<bb>"
    by (rule \<ff>(1)) (simp_all add: \<ff>)

  note [cat_Set_cs_intros] = \<gg>.arr_Set_ArrDom_in_Vset \<ff>.arr_Set_ArrCod_in_Vset

  from assms have \<gg>_incl: 
    "\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl : vequalizer \<aa> \<ff> \<gg> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>"
    by (cs_concl cs_intro: V_cs_intros cat_Set_cs_intros cat_cs_intros)
  then have dom_lhs: "\<D>\<^sub>\<circ> ((\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)\<lparr>ArrVal\<rparr>) = vequalizer \<aa> \<ff> \<gg>"
    by (cs_concl cs_simp: cat_cs_simps)+
  from assms have \<ff>_incl: 
    "\<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl : vequalizer \<aa> \<ff> \<gg> \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> \<bb>"
    by (cs_concl cs_intro: V_cs_intros cat_Set_cs_intros cat_cs_intros)
  then have dom_rhs: "\<D>\<^sub>\<circ> ((\<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)\<lparr>ArrVal\<rparr>) = vequalizer \<aa> \<ff> \<gg>"
    by (cs_concl cs_simp: cat_cs_simps)+

  show ?thesis
  proof(rule arr_Set_eqI)
    from \<gg>_incl show arr_Set_\<gg>_incl: "arr_Set \<alpha> (\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)"
      by (auto dest: cat_Set_is_arrD(1))
    interpret arr_Set_\<gg>_incl: arr_Set \<alpha> \<open>\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl\<close>
      by (rule arr_Set_\<gg>_incl)
    from \<ff>_incl show arr_Set_\<ff>_incl: "arr_Set \<alpha> (\<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)"
      by (auto dest: cat_Set_is_arrD(1))
    interpret arr_Set_\<ff>_incl: arr_Set \<alpha> \<open>\<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl\<close>
      by (rule arr_Set_\<ff>_incl)
    show "(\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)\<lparr>ArrVal\<rparr> = (\<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)\<lparr>ArrVal\<rparr>"
    proof(rule vsv_eqI, unfold dom_lhs dom_rhs)
      fix a assume "a \<in>\<^sub>\<circ> vequalizer \<aa> \<ff> \<gg>"
      with assms show 
        "(\<gg> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = (\<ff> \<circ>\<^sub>A\<^bsub>cat_Set \<alpha>\<^esub> ?incl)\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
        by
          (
            cs_concl
              cs_simp: vequalizerD(2) cat_Set_cs_simps cat_cs_simps
              cs_intro: V_cs_intros cat_Set_cs_intros cat_cs_intros
          )
    qed auto
  qed (use \<gg>_incl \<ff>_incl in \<open>cs_concl cs_simp: cat_cs_simps\<close>)+

qed



subsection\<open>Auxiliary\<close>


text\<open>
This subsection is reserved for insignificant helper lemmas 
and rules that are used in applied formalization elsewhere.
\<close>

lemma (in \<Z>) cat_Rel_CId_is_cat_Set_arr:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>"
  shows "cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> : A \<mapsto>\<^bsub>cat_Set \<alpha>\<^esub> A"
proof-
  from assms show ?thesis
    unfolding cat_Rel_components cat_Set_components(6)[symmetric]
    by (cs_concl cs_simp: cat_Set_components(1) cs_intro: cat_cs_intros)
qed

lemma (in \<Z>) cat_Rel_CId_is_cat_Set_arr'[cat_rel_par_Set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> cat_Rel \<alpha>\<lparr>Obj\<rparr>" 
    and "B' = A"
    and "C' = A"
    and "\<CC>' = cat_Set \<alpha>"
  shows "cat_Rel \<alpha>\<lparr>CId\<rparr>\<lparr>A\<rparr> : B' \<mapsto>\<^bsub>\<CC>'\<^esub> C'"
  using assms(1) unfolding assms(2-4) by (rule cat_Rel_CId_is_cat_Set_arr)

text\<open>\newpage\<close>

end