(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Set\<close> as a digraph\<close>
theory CZH_DG_Set
  imports CZH_DG_Par
begin



subsection\<open>Background\<close>


text\<open>
\<open>Set\<close> is usually defined as a category of sets and total functions
(see Chapter I-2 in \cite{mac_lane_categories_2010}). However, there
is little that can prevent one from exposing \<open>Set\<close> as a digraph and
provide additional structure gradually in subsequent installments of this 
work. Thus, in this section, \<open>\<alpha>\<close>-\<open>Set\<close> is defined as a digraph of sets 
and binary relations in the set \<open>V\<^sub>\<alpha>\<close>. 
\<close>

named_theorems dg_Set_cs_simps
named_theorems dg_Set_cs_intros

lemmas [dg_Set_cs_simps] = dg_Rel_shared_cs_simps
lemmas [dg_Set_cs_intros] = dg_Rel_shared_cs_intros



subsection\<open>Arrow for \<open>Set\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale arr_Set = \<Z> \<alpha> + vfsequence T + ArrVal: vsv \<open>T\<lparr>ArrVal\<rparr>\<close> for \<alpha> T +
  assumes arr_Set_length[dg_Rel_shared_cs_simps, dg_Set_cs_simps]: 
      "vcard T = 3\<^sub>\<nat>" 
    and arr_Set_ArrVal_vdomain[dg_Rel_shared_cs_simps, dg_Set_cs_simps]: 
      "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = T\<lparr>ArrDom\<rparr>"
    and arr_Set_ArrVal_vrange: "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> T\<lparr>ArrCod\<rparr>"
    and arr_Set_ArrDom_in_Vset: "T\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and arr_Set_ArrCod_in_Vset: "T\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"

lemmas [dg_Set_cs_simps] = arr_Set.arr_Set_ArrVal_vdomain


text\<open>Elementary properties.\<close>

sublocale arr_Set \<subseteq> arr_Par
  by unfold_locales 
    (
      simp_all add:
        dg_Set_cs_simps
        arr_Set_ArrVal_vrange arr_Set_ArrDom_in_Vset arr_Set_ArrCod_in_Vset
    )


text\<open>Rules.\<close>

mk_ide rf arr_Set_def[unfolded arr_Set_axioms_def]
  |intro arr_SetI|
  |dest arr_SetD[dest]|
  |elim arr_SetE[elim!]|

lemma (in \<Z>) arr_Set_vfsequenceI: 
  assumes "vsv r" 
    and "\<D>\<^sub>\<circ> r = a"
    and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> b"
    and "a \<in>\<^sub>\<circ> Vset \<alpha>"
    and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Set \<alpha> [r, a, b]\<^sub>\<circ>"
  by (intro arr_SetI) 
    (insert assms, auto simp: arr_Rel_components nat_omega_simps)

lemma arr_Set_arr_ParI:
  assumes "arr_Par \<alpha> T" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = T\<lparr>ArrDom\<rparr>"
  shows "arr_Set \<alpha> T"
proof-
  interpret arr_Par \<alpha> T by (rule assms(1))
  show ?thesis
    by (intro arr_SetI)
      (
        auto simp: 
          dg_Par_cs_simps
          assms(2) 
          vfsequence_axioms 
          arr_Rel_ArrVal_vrange 
          arr_Rel_ArrDom_in_Vset 
          arr_Rel_ArrCod_in_Vset
      )
qed 

lemma arr_Set_arr_ParD:
  assumes "arr_Set \<alpha> T"
  shows "arr_Par \<alpha> T" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = T\<lparr>ArrDom\<rparr>"
proof-
  interpret arr_Set \<alpha> T by (rule assms)
  show "arr_Par \<alpha> T" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = T\<lparr>ArrDom\<rparr>"
    by (rule arr_Par_axioms) (auto simp: dg_Set_cs_simps)
qed

lemma arr_Set_arr_ParE:
  assumes "arr_Set \<alpha> T"
  obtains "arr_Par \<alpha> T" and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = T\<lparr>ArrDom\<rparr>"
  using assms by (auto simp: arr_Set_arr_ParD)


text\<open>Further elementary properties.\<close>

lemma arr_Set_eqI:
  assumes "arr_Set \<alpha> S" 
    and "arr_Set \<alpha> T"
    and "S\<lparr>ArrVal\<rparr> = T\<lparr>ArrVal\<rparr>"
    and "S\<lparr>ArrDom\<rparr> = T\<lparr>ArrDom\<rparr>"
    and "S\<lparr>ArrCod\<rparr> = T\<lparr>ArrCod\<rparr>"
  shows "S = T"
proof-
  interpret S: arr_Set \<alpha> S by (rule assms(1))
  interpret T: arr_Set \<alpha> T by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom: "\<D>\<^sub>\<circ> S = 3\<^sub>\<nat>" by (simp add: S.vfsequence_vdomain dg_Set_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> S \<Longrightarrow> S\<lparr>a\<rparr> = T\<lparr>a\<rparr>" for a
      by (unfold dom, elim_in_numeral, insert assms)
        (auto simp: arr_field_simps)
  qed (auto simp: S.vfsequence_vdomain T.vfsequence_vdomain dg_Set_cs_simps) 
qed

lemma small_arr_Set[simp]: "small {T. arr_Set \<alpha> T}"
proof(rule smaller_than_small)
  show "{T. arr_Set \<alpha> T} \<subseteq> {T. arr_Par \<alpha> T}" 
    by (simp add: Collect_mono arr_Set_arr_ParD(1))
qed simp

lemma set_Collect_arr_Set[simp]: 
  "T \<in>\<^sub>\<circ> set (Collect (arr_Set \<alpha>)) \<longleftrightarrow> arr_Set \<alpha> T" 
  by auto


subsubsection\<open>Composition\<close>


text\<open>See \cite{mac_lane_categories_2010}).\<close>

abbreviation (input) comp_Set :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>S\<^sub>e\<^sub>t\<close> 55)
  where "comp_Set \<equiv> comp_Rel"

lemma arr_Set_comp_Set[dg_Set_cs_intros]:
  assumes "arr_Set \<alpha> S" and "arr_Set \<alpha> T" and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> \<D>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>)"
  shows "arr_Set \<alpha> (S \<circ>\<^sub>S\<^sub>e\<^sub>t T)"
proof(intro arr_Set_arr_ParI)
  interpret S: arr_Set \<alpha> S by (rule assms(1))
  interpret T: arr_Set \<alpha> T by (rule assms(2))
  show "arr_Par \<alpha> (S \<circ>\<^sub>S\<^sub>e\<^sub>t T)"
    by (auto simp: S.arr_Par_axioms T.arr_Par_axioms arr_Par_comp_Par)
  show "\<D>\<^sub>\<circ> ((S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrVal\<rparr>) = (S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrDom\<rparr>"
    unfolding comp_Rel_components vdomain_vcomp_vsubset[OF assms(3)] 
    by (simp add: dg_Set_cs_simps)
qed


subsubsection\<open>Inclusion\<close>

abbreviation (input) incl_Set :: "V \<Rightarrow> V \<Rightarrow> V"
  where "incl_Set \<equiv> incl_Rel"

lemma (in \<Z>) arr_Set_incl_SetI:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "A \<subseteq>\<^sub>\<circ> B"
  shows "arr_Set \<alpha> (incl_Set A B)"
proof(intro arr_Set_arr_ParI)
  from assms show "arr_Par \<alpha> (incl_Set A B)" 
    by (force intro: arr_Par_incl_ParI)
qed (simp add: incl_Rel_components)


subsubsection\<open>Identity\<close>

abbreviation (input) id_Set :: "V \<Rightarrow> V"
  where "id_Set \<equiv> id_Rel"

lemma (in \<Z>) arr_Set_id_SetI:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Set \<alpha> (id_Set A)"
proof(intro arr_Set_arr_ParI)
  from assms show "arr_Par \<alpha> (id_Par A)" 
    by (force intro: arr_Par_id_ParI)
qed (simp add: id_Rel_components)

lemma arr_Set_comp_Set_id_Set_left[dg_Set_cs_simps]:
  assumes "arr_Set \<alpha> F" and "F\<lparr>ArrCod\<rparr> = A"
  shows "id_Set A \<circ>\<^sub>R\<^sub>e\<^sub>l F = F"
proof-
  interpret F: arr_Set \<alpha> F by (rule assms(1))
  have "arr_Rel \<alpha> F" by (simp add: F.arr_Rel_axioms)
  from arr_Rel_comp_Rel_id_Rel_left[OF this assms(2)] show ?thesis.
qed

lemma arr_Set_comp_Set_id_Set_right[dg_Set_cs_simps]:
  assumes "arr_Set \<alpha> F" and "F\<lparr>ArrDom\<rparr> = A"
  shows "F \<circ>\<^sub>R\<^sub>e\<^sub>l id_Set A = F"
proof-
  interpret F: arr_Set \<alpha> F by (rule assms(1))
  have "arr_Rel \<alpha> F" by (simp add: F.arr_Rel_axioms)
  from arr_Rel_comp_Rel_id_Rel_right[OF this assms(2)] show ?thesis.
qed

lemma arr_Set_comp_Set_ArrVal:
  assumes "arr_Set \<alpha> S" 
    and "arr_Set \<alpha> T" 
    and "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
    and "T\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>)"
  shows "(S \<circ>\<^sub>S\<^sub>e\<^sub>t T)\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = S\<lparr>ArrVal\<rparr>\<lparr>T\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>\<rparr>"
proof-
  interpret S: arr_Set \<alpha> S + T: arr_Set \<alpha> T by (simp_all add: assms(1,2))  
  from assms show ?thesis 
    unfolding comp_Rel_components by (intro vcomp_atI) auto
qed



subsection\<open>\<open>Set\<close> as a digraph\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_Set :: "V \<Rightarrow> V"
  where "dg_Set \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Set \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_Set_components:
  shows "dg_Set \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "dg_Set \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Set \<alpha> T}"
    and "dg_Set \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "dg_Set \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Set \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
  unfolding dg_Set_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object\<close>

lemma dg_Set_Obj_iff: "x \<in>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr> \<longleftrightarrow> x \<in>\<^sub>\<circ> Vset \<alpha>" 
  unfolding dg_Set_components by auto


subsubsection\<open>Arrow\<close>

lemma dg_Set_Arr_iff[dg_Set_cs_simps]: "x \<in>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Arr\<rparr> \<longleftrightarrow> arr_Set \<alpha> x" 
  unfolding dg_Set_components by auto


subsubsection\<open>Domain\<close>

mk_VLambda dg_Set_components(3)
  |vsv dg_Set_Dom_vsv[dg_Set_cs_intros]|
  |vdomain dg_Set_Dom_vdomain[dg_Set_cs_simps]|
  |app dg_Set_Dom_app[unfolded set_Collect_arr_Set, dg_Set_cs_simps]|

lemma dg_Set_Dom_vrange: "\<R>\<^sub>\<circ> (dg_Set \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_Set_components
  by (rule vrange_VLambda_vsubset, unfold set_Collect_arr_Set) auto


subsubsection\<open>Codomain\<close>

mk_VLambda dg_Set_components(4)
  |vsv dg_Set_Cod_vsv[dg_Set_cs_intros]|
  |vdomain dg_Set_Cod_vdomain[dg_Set_cs_simps]|
  |app dg_Set_Cod_app[unfolded set_Collect_arr_Set, dg_Set_cs_simps]|

lemma dg_Set_Cod_vrange: "\<R>\<^sub>\<circ> (dg_Set \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_Set_components
  by (rule vrange_VLambda_vsubset, unfold set_Collect_arr_Set) auto


subsubsection\<open>Arrow with a domain and a codomain\<close>


text\<open>Rules.\<close>

lemma dg_Set_is_arrI[dg_Set_cs_intros]:
  assumes "arr_Set \<alpha> S" and "S\<lparr>ArrDom\<rparr> = A" and "S\<lparr>ArrCod\<rparr> = B"
  shows "S : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B"
  using assms by (intro is_arrI, unfold dg_Set_components) simp_all

lemma dg_Set_is_arrD:
  assumes "S : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B"
  shows "arr_Set \<alpha> S" 
    and [dg_cs_simps]: "S\<lparr>ArrDom\<rparr> = A" 
    and [dg_cs_simps]: "S\<lparr>ArrCod\<rparr> = B"
  using is_arrD[OF assms] unfolding dg_Set_components by simp_all

lemma dg_Set_is_arrE:
  assumes "S : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B"
  obtains "arr_Set \<alpha> S" and "S\<lparr>ArrDom\<rparr> = A" and "S\<lparr>ArrCod\<rparr> = B"
  using is_arrD[OF assms] unfolding dg_Set_components by simp_all

lemma dg_Set_ArrVal_vdomain[dg_Set_cs_simps, dg_cs_simps]:
  assumes "T : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B"
  shows "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
proof-
  interpret T: arr_Set \<alpha> T using assms by (auto simp: dg_Set_is_arrD)
  from assms show ?thesis by (auto simp: dg_Set_is_arrD dg_Set_cs_simps)
qed


text\<open>Elementary properties.\<close>

lemma dg_Set_ArrVal_app_vrange[dg_Set_cs_intros]:
  assumes "F : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B" and "a \<in>\<^sub>\<circ> A"
  shows "F\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> \<in>\<^sub>\<circ> B"
proof-
  interpret F: arr_Set \<alpha> F 
    rewrites "F\<lparr>ArrDom\<rparr> = A" and "F\<lparr>ArrCod\<rparr> = B"
    by (intro dg_Set_is_arrD[OF assms(1)])+
  from assms F.arr_Par_ArrVal_vrange show ?thesis
    by (auto simp: F.ArrVal.vsv_vimageI2 vsubset_iff dg_Set_cs_simps)
qed

lemma dg_Set_is_arr_dg_Par_is_arr:
  assumes "T : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B" 
  shows "T : A \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B"
  using assms arr_Set_arr_ParD(1) 
  by (intro dg_Par_is_arrI; elim dg_Set_is_arrE) auto

lemma dg_Set_Hom_vsubset_dg_Par_Hom:
  assumes "a \<in>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>" 
  shows "Hom (dg_Set \<alpha>) a b \<subseteq>\<^sub>\<circ> Hom (dg_Par \<alpha>) a b"
  by (rule vsubsetI) (simp add: dg_Set_is_arr_dg_Par_is_arr)

lemma (in \<Z>) dg_Set_incl_Set_is_arr:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "A \<subseteq>\<^sub>\<circ> B"
  shows "incl_Set A B : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B"
proof(rule dg_Set_is_arrI)
  show "arr_Set \<alpha> (incl_Set A B)" by (intro arr_Set_incl_SetI assms)
qed (simp_all add: incl_Rel_components)

lemma (in \<Z>) dg_Set_incl_Set_is_arr'[dg_Set_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "B \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "A \<subseteq>\<^sub>\<circ> B"
    and "A' = A"
    and "B' = B"
  shows "incl_Set A B : A' \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B'"
  using assms(1-3) unfolding assms(4,5) by (rule dg_Set_incl_Set_is_arr)

lemmas [dg_Set_cs_intros] = \<Z>.dg_Set_incl_Set_is_arr'


subsubsection\<open>\<open>Set\<close> is a digraph\<close>

lemma (in \<Z>) dg_Set_Hom_vifunion_in_Vset:
  assumes "X \<in>\<^sub>\<circ> Vset \<alpha>" and "Y \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Set \<alpha>) A B) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have 
    "(\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Set \<alpha>) A B) \<subseteq>\<^sub>\<circ>
      (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Par \<alpha>) A B)"
  proof
    fix F assume "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Set \<alpha>) A B)"
    then obtain B where B: "B \<in>\<^sub>\<circ> Y" and F_b: 
      "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. Hom (dg_Set \<alpha>) A B)" 
      by fast
    then obtain A where A: "A \<in>\<^sub>\<circ> X" and F_AB: "F \<in>\<^sub>\<circ> Hom (dg_Set \<alpha>) A B"
      by fast
    from A B assms have "A \<in>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>" "B \<in>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>"
      unfolding dg_Set_components by auto
    from F_AB A B dg_Set_Hom_vsubset_dg_Par_Hom[OF this] show 
      "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Par \<alpha>) A B)"
      by (intro vifunionI) (auto elim!: vsubsetE simp: in_Hom_iff) 
  qed
  with dg_Par_Hom_vifunion_in_Vset[OF assms] show ?thesis by blast
qed

lemma (in \<Z>) digraph_dg_Set: "digraph \<alpha> (dg_Set \<alpha>)"
proof(intro digraphI)
  show "vfsequence (dg_Set \<alpha>)" unfolding dg_Set_def by simp
  show "vcard (dg_Set \<alpha>) = 4\<^sub>\<nat>"
    unfolding dg_Set_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dg_Set \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_Set_Dom_vrange)
  show "\<R>\<^sub>\<circ> (dg_Set \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Set \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_Set_Cod_vrange)
qed (auto simp: dg_Set_components dg_Set_Hom_vifunion_in_Vset)


subsubsection\<open>\<open>Set\<close> is a wide subdigraph of \<open>Par\<close>\<close>

lemma (in \<Z>) wide_subdigraph_dg_Set_dg_Par: "dg_Set \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> dg_Par \<alpha>"
proof(intro wide_subdigraphI)
  interpret Set: digraph \<alpha> \<open>dg_Set \<alpha>\<close> by (rule digraph_dg_Set)
  interpret Par: digraph \<alpha> \<open>dg_Par \<alpha>\<close> by (rule digraph_dg_Par)
  show "dg_Set \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_Par \<alpha>"
  proof(intro subdigraphI, unfold dg_Set_components)
    show "F : A \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B" if "F : A \<mapsto>\<^bsub>dg_Set \<alpha>\<^esub> B" for F A B
      using that by (rule dg_Set_is_arr_dg_Par_is_arr)
  qed (auto simp: dg_Par_components digraph_dg_Set digraph_dg_Par)
qed (simp_all add: dg_Par_components dg_Set_components)

text\<open>\newpage\<close>

end