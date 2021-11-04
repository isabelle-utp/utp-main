(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Par\<close> as a digraph\<close>
theory CZH_DG_Par
  imports
    CZH_DG_Rel
    CZH_DG_Subdigraph
begin



subsection\<open>Background\<close>


text\<open>
\<open>Par\<close> is usually defined as a category of sets and partial functions
(see nLab \cite{noauthor_nlab_nodate}\footnote{
\url{https://ncatlab.org/nlab/show/partial+function}
}).
However, there is little that can prevent one from exposing \<open>Par\<close> 
as a digraph and provide additional structure gradually in subsequent
installments of this work. Thus, in this section, \<open>\<alpha>\<close>-\<open>Par\<close> is defined as a
digraph of sets and partial functions in \<open>V\<^sub>\<alpha>\<close> 
\<close>

named_theorems dg_Par_cs_simps
named_theorems dg_Par_cs_intros

lemmas [dg_Par_cs_simps] = dg_Rel_shared_cs_simps
lemmas [dg_Par_cs_intros] = dg_Rel_shared_cs_intros



subsection\<open>Arrow for \<open>Par\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale arr_Par = \<Z> \<alpha> + vfsequence T + ArrVal: vsv \<open>T\<lparr>ArrVal\<rparr>\<close> for \<alpha> T +
  assumes arr_Par_length[dg_Rel_shared_cs_simps, dg_Par_cs_simps]: 
    "vcard T = 3\<^sub>\<nat>" 
    and arr_Par_ArrVal_vdomain: "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> T\<lparr>ArrDom\<rparr>"
    and arr_Par_ArrVal_vrange: "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> T\<lparr>ArrCod\<rparr>"
    and arr_Par_ArrDom_in_Vset: "T\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and arr_Par_ArrCod_in_Vset: "T\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"


text\<open>Elementary properties.\<close>

sublocale arr_Par \<subseteq> arr_Rel
  by unfold_locales 
    (
      simp_all add: 
        dg_Par_cs_simps
        arr_Par_ArrVal_vdomain 
        arr_Par_ArrVal_vrange
        arr_Par_ArrDom_in_Vset 
        arr_Par_ArrCod_in_Vset
    )

lemmas (in arr_Par) [dg_Par_cs_simps] = dg_Rel_shared_cs_simps


text\<open>Rules.\<close>

mk_ide rf arr_Par_def[unfolded arr_Par_axioms_def]
  |intro arr_ParI|
  |dest arr_ParD[dest]|
  |elim arr_ParE[elim!]|

lemma (in \<Z>) arr_Par_vfsequenceI: 
  assumes "vsv r" 
    and "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> a"
    and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> b"
    and "a \<in>\<^sub>\<circ> Vset \<alpha>"
    and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Par \<alpha> [r, a, b]\<^sub>\<circ>"
  by (intro arr_ParI) 
    (insert assms, auto simp: arr_Rel_components nat_omega_simps)

lemma arr_Par_arr_RelI:
  assumes "arr_Rel \<alpha> T" and "vsv (T\<lparr>ArrVal\<rparr>)"
  shows "arr_Par \<alpha> T"
proof-
  interpret arr_Rel \<alpha> T by (rule assms(1))
  show ?thesis
    by (intro arr_ParI)
      (
        auto simp: 
          dg_Rel_cs_simps
          assms(2)
          vfsequence_axioms 
          arr_Rel_ArrVal_vdomain 
          arr_Rel_ArrVal_vrange 
          arr_Rel_ArrDom_in_Vset 
          arr_Rel_ArrCod_in_Vset
      )
qed 

lemma arr_Par_arr_RelD:
  assumes "arr_Par \<alpha> T"
  shows "arr_Rel \<alpha> T" and "vsv (T\<lparr>ArrVal\<rparr>)"
proof-
  interpret arr_Par \<alpha> T by (rule assms)
  show "arr_Rel \<alpha> T" and "vsv (T\<lparr>ArrVal\<rparr>)"
    by (rule arr_Rel_axioms) auto
qed

lemma arr_Par_arr_RelE:
  assumes "arr_Par \<alpha> T"
  obtains "arr_Rel \<alpha> T" and "vsv (T\<lparr>ArrVal\<rparr>)"
  using assms by (auto simp: arr_Par_arr_RelD)


text\<open>Further elementary properties.\<close>

lemma arr_Par_eqI:
  assumes "arr_Par \<alpha> S" 
    and "arr_Par \<alpha> T"
    and "S\<lparr>ArrVal\<rparr> = T\<lparr>ArrVal\<rparr>"
    and "S\<lparr>ArrDom\<rparr> = T\<lparr>ArrDom\<rparr>"
    and "S\<lparr>ArrCod\<rparr> = T\<lparr>ArrCod\<rparr>"
  shows "S = T"
proof(rule vsv_eqI)
  interpret S: arr_Par \<alpha> S by (rule assms(1))
  interpret T: arr_Par \<alpha> T by (rule assms(2))
  show "vsv S" by (rule S.vsv_axioms)
  show "vsv T" by (rule T.vsv_axioms)
  show "\<D>\<^sub>\<circ> S = \<D>\<^sub>\<circ> T" 
    by (simp add: S.vfsequence_vdomain T.vfsequence_vdomain dg_Par_cs_simps) 
  have dom: "\<D>\<^sub>\<circ> S = 3\<^sub>\<nat>" by (simp add: S.vfsequence_vdomain dg_Par_cs_simps)
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> S \<Longrightarrow> S\<lparr>a\<rparr> = T\<lparr>a\<rparr>" for a 
    by (unfold dom, elim_in_numeral, insert assms) 
      (auto simp: arr_field_simps)
qed

lemma small_arr_Par[simp]: "small {T. arr_Par \<alpha> T}"
proof(rule smaller_than_small)
  show "{T. arr_Par \<alpha> T} \<subseteq> {T. arr_Rel \<alpha> T}" 
    by (simp add: Collect_mono arr_Par_arr_RelD(1))
qed simp

lemma set_Collect_arr_Par[simp]: 
  "T \<in>\<^sub>\<circ> set (Collect (arr_Par \<alpha>)) \<longleftrightarrow> arr_Par \<alpha> T" 
  by auto


subsubsection\<open>Composition\<close>

abbreviation (input) comp_Par :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>P\<^sub>a\<^sub>r\<close> 55)
  where "comp_Par \<equiv> comp_Rel"

lemma arr_Par_comp_Par[dg_Par_cs_intros]:
  assumes "arr_Par \<alpha> S" and "arr_Par \<alpha> T"
  shows "arr_Par \<alpha> (S \<circ>\<^sub>P\<^sub>a\<^sub>r T)"
proof(intro arr_Par_arr_RelI)
  interpret S: arr_Par \<alpha> S by (rule assms(1))
  interpret T: arr_Par \<alpha> T by (rule assms(2))
  show "arr_Rel \<alpha> (S \<circ>\<^sub>P\<^sub>a\<^sub>r T)"
    by (auto simp: S.arr_Rel_axioms T.arr_Rel_axioms arr_Rel_comp_Rel)
  show "vsv ((S \<circ>\<^sub>P\<^sub>a\<^sub>r T)\<lparr>ArrVal\<rparr>)"
    unfolding comp_Rel_components
    by (simp add: S.ArrVal.vsv_axioms T.ArrVal.vsv_axioms vsv_vcomp)
qed


subsubsection\<open>Inclusion\<close>

abbreviation (input) incl_Par :: "V \<Rightarrow> V \<Rightarrow> V"
  where "incl_Par \<equiv> incl_Rel"

lemma (in \<Z>) arr_Par_incl_ParI:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "A \<subseteq>\<^sub>\<circ> B"
  shows "arr_Par \<alpha> (incl_Par A B)"
proof(intro arr_Par_arr_RelI)
  from assms show "arr_Rel \<alpha> (incl_Par A B)" 
    by (force intro: arr_Rel_incl_RelI)
qed (simp add: incl_Rel_components)


subsubsection\<open>Identity\<close>

abbreviation (input) id_Par :: "V \<Rightarrow> V"
  where "id_Par \<equiv> id_Rel"

lemma (in \<Z>) arr_Par_id_ParI:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Par \<alpha> (id_Par A)"
  using assms
  by (intro arr_Par_arr_RelI) 
    (auto intro: arr_Rel_id_RelI simp: id_Rel_components)

lemma arr_Par_comp_Par_id_Par_left[dg_Par_cs_simps]:
  assumes "arr_Par \<alpha> f" and "f\<lparr>ArrCod\<rparr> = A"
  shows "id_Par A \<circ>\<^sub>R\<^sub>e\<^sub>l f = f"
proof-
  interpret f: arr_Par \<alpha> f by (rule assms(1))
  have "arr_Rel \<alpha> f" by (simp add: f.arr_Rel_axioms)
  from arr_Rel_comp_Rel_id_Rel_left[OF this assms(2)] show ?thesis .
qed

lemma arr_Par_comp_Par_id_Par_right[dg_Par_cs_simps]:
  assumes "arr_Par \<alpha> f" and "f\<lparr>ArrDom\<rparr> = A"
  shows "f \<circ>\<^sub>R\<^sub>e\<^sub>l id_Par A = f"
proof-
  interpret f: arr_Par \<alpha> f by (rule assms(1))
  have "arr_Rel \<alpha> f" by (simp add: f.arr_Rel_axioms)
  from arr_Rel_comp_Rel_id_Rel_right[OF this assms(2)] show ?thesis.
qed

lemma arr_Par_comp_Par_ArrVal:
  assumes "arr_Par \<alpha> S" 
    and "arr_Par \<alpha> T" 
    and "x \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)"
    and "T\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr>)"
  shows "(S \<circ>\<^sub>P\<^sub>a\<^sub>r T)\<lparr>ArrVal\<rparr>\<lparr>x\<rparr> = S\<lparr>ArrVal\<rparr>\<lparr>T\<lparr>ArrVal\<rparr>\<lparr>x\<rparr>\<rparr>"
  using assms 
  unfolding comp_Rel_components 
  by (intro vcomp_atI) auto



subsection\<open>\<open>Par\<close> as a digraph\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_Par :: "V \<Rightarrow> V"
  where "dg_Par \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Par \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_Par_components:
  shows "dg_Par \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "dg_Par \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Par \<alpha> T}"
    and "dg_Par \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "dg_Par \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Par \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
  unfolding dg_Par_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object\<close>

lemma dg_Par_Obj_iff: "x \<in>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr> \<longleftrightarrow> x \<in>\<^sub>\<circ> Vset \<alpha>" 
  unfolding dg_Par_components by auto


subsubsection\<open>Arrow\<close>

lemma dg_Par_Arr_iff[dg_Par_cs_simps]: "x \<in>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Arr\<rparr> \<longleftrightarrow> arr_Par \<alpha> x" 
  unfolding dg_Par_components by auto


subsubsection\<open>Domain\<close>

mk_VLambda dg_Par_components(3)
  |vsv dg_Par_Dom_vsv[dg_Par_cs_intros]|
  |vdomain dg_Par_Dom_vdomain[dg_Par_cs_simps]|
  |app dg_Par_Dom_app[unfolded set_Collect_arr_Par, dg_Par_cs_simps]|

lemma dg_Par_Dom_vrange: "\<R>\<^sub>\<circ> (dg_Par \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_Par_components
  by (rule vrange_VLambda_vsubset, unfold set_Collect_arr_Par) auto


subsubsection\<open>Codomain\<close>

mk_VLambda dg_Par_components(4)
  |vsv dg_Par_Cod_vsv[dg_Par_cs_intros]|
  |vdomain dg_Par_Cod_vdomain[dg_Par_cs_simps]|
  |app dg_Par_Cod_app[unfolded set_Collect_arr_Par, dg_Par_cs_simps]|

lemma dg_Par_Cod_vrange: "\<R>\<^sub>\<circ> (dg_Par \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_Par_components
  by (rule vrange_VLambda_vsubset, unfold set_Collect_arr_Par) auto


subsubsection\<open>Arrow with a domain and a codomain\<close>


text\<open>Rules.\<close>

lemma dg_Par_is_arrI:
  assumes "arr_Par \<alpha> S" and "S\<lparr>ArrDom\<rparr> = A" and "S\<lparr>ArrCod\<rparr> = B"
  shows "S : A \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B"
  using assms by (intro is_arrI, unfold dg_Par_components) simp_all

lemmas [dg_Par_cs_intros] = dg_Par_is_arrI

lemma dg_Par_is_arrD:
  assumes "S : A \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B"
  shows "arr_Par \<alpha> S" 
    and [dg_cs_simps]: "S\<lparr>ArrDom\<rparr> = A" 
    and [dg_cs_simps]: "S\<lparr>ArrCod\<rparr> = B"
  using is_arrD[OF assms] unfolding dg_Par_components by simp_all

lemma dg_Par_is_arrE:
  assumes "S : A \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B"
  obtains "arr_Par \<alpha> S" and "S\<lparr>ArrDom\<rparr> = A" and "S\<lparr>ArrCod\<rparr> = B"
  using is_arrD[OF assms] unfolding dg_Par_components by simp_all


text\<open>Elementary properties.\<close>

lemma dg_Par_is_arr_dg_Rel_is_arr:
  assumes "r : a \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> b" 
  shows "r : a \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> b"
  using assms arr_Par_arr_RelD(1) 
  by (intro dg_Rel_is_arrI; elim dg_Par_is_arrE) auto

lemma dg_Par_Hom_vsubset_dg_Rel_Hom:
  assumes "a \<in>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>" 
  shows "Hom (dg_Par \<alpha>) a b \<subseteq>\<^sub>\<circ> Hom (dg_Rel \<alpha>) a b"
  by (rule vsubsetI) (simp add: dg_Par_is_arr_dg_Rel_is_arr)

lemma (in \<Z>) dg_Par_incl_Par_is_arr:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "A \<subseteq>\<^sub>\<circ> B"
  shows "incl_Par A B : A \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B"
  by (rule dg_Par_is_arrI)
    (auto simp: incl_Rel_components intro!: arr_Par_incl_ParI assms)

lemma (in \<Z>) dg_Par_incl_Par_is_arr'[dg_Par_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "B \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "A \<subseteq>\<^sub>\<circ> B"
    and "A' = A"
    and "B' = B"
  shows "incl_Par A B : A' \<mapsto>\<^bsub>dg_Par \<alpha>\<^esub> B'"
  using assms(1-3) unfolding assms(4,5) by (rule dg_Par_incl_Par_is_arr)

lemmas [dg_Par_cs_intros] = \<Z>.dg_Par_incl_Par_is_arr'


subsubsection\<open>\<open>Par\<close> is a digraph\<close>

lemma (in \<Z>) dg_Par_Hom_vifunion_in_Vset:
  assumes "X \<in>\<^sub>\<circ> Vset \<alpha>" and "Y \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Par \<alpha>) A B) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  have 
    "(\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Par \<alpha>) A B) \<subseteq>\<^sub>\<circ>
      (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Rel \<alpha>) A B)"
  proof(intro vsubsetI)
    fix F assume "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Par \<alpha>) A B)"
    then obtain B where B: "B \<in>\<^sub>\<circ> Y" and "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. Hom (dg_Par \<alpha>) A B)" 
      by fast
    then obtain A where A: "A \<in>\<^sub>\<circ> X" and F_AB: "F \<in>\<^sub>\<circ> Hom (dg_Par \<alpha>) A B" by fast
    from A B assms have "A \<in>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>" "B \<in>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>"
      unfolding dg_Par_components by auto
    from F_AB A B dg_Par_Hom_vsubset_dg_Rel_Hom[OF this] show 
      "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Rel \<alpha>) A B)"
      by (intro vifunionI) (auto elim!: vsubsetE simp: in_Hom_iff) 
  qed
  with dg_Rel_Hom_vifunion_in_Vset[OF assms] show ?thesis by blast
qed

lemma (in \<Z>) digraph_dg_Par: "digraph \<alpha> (dg_Par \<alpha>)"
proof(intro digraphI)
  show "vfsequence (dg_Par \<alpha>)" unfolding dg_Par_def by simp
  show "vcard (dg_Par \<alpha>) = 4\<^sub>\<nat>" 
    unfolding dg_Par_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dg_Par \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_Par_Dom_vrange)
  show "\<R>\<^sub>\<circ> (dg_Par \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Par \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_Par_Cod_vrange)
qed (auto simp: dg_Par_components dg_Par_Hom_vifunion_in_Vset)


subsubsection\<open>\<open>Par\<close> is a wide subdigraph of \<open>Rel\<close>\<close>

lemma (in \<Z>) wide_subdigraph_dg_Par_dg_Rel: "dg_Par \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^sub>.\<^sub>w\<^sub>i\<^sub>d\<^sub>e\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>"
proof(intro wide_subdigraphI)
  show "dg_Par \<alpha> \<subseteq>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>"
    by (intro subdigraphI, unfold dg_Par_components)
      (
        auto simp: 
          dg_Rel_components 
          digraph_dg_Par 
          digraph_dg_Rel 
          dg_Par_is_arr_dg_Rel_is_arr
      )
qed (simp_all add: dg_Rel_components dg_Par_components)

text\<open>\newpage\<close>

end