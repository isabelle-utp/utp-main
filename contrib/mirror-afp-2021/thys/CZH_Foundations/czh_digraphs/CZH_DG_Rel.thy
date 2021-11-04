(* Copyright 2021 (C) Mihails Milehins *)

section\<open>\<open>Rel\<close> as a digraph\<close>
theory CZH_DG_Rel
  imports CZH_DG_Small_DGHM
begin



subsection\<open>Background\<close>


text\<open>
\<open>Rel\<close> is usually defined as a category of sets and binary relations
(e.g., see Chapter I-7 in \cite{mac_lane_categories_2010}). However, there
is little that can prevent one from exposing \<open>Rel\<close> as a digraph and
provide additional structure gradually in subsequent installments of this 
work. Thus, in this section, \<open>\<alpha>\<close>-\<open>Rel\<close> is defined as a digraph of sets 
and binary relations in \<open>V\<^sub>\<alpha>\<close>.
\<close>

named_theorems dg_Rel_shared_cs_simps
named_theorems dg_Rel_shared_cs_intros

named_theorems dg_Rel_cs_simps
named_theorems dg_Rel_cs_intros



subsection\<open>Canonical arrow for \<^typ>\<open>V\<close>\<close>

named_theorems arr_field_simps

definition ArrVal :: V where [arr_field_simps]: "ArrVal = 0"
definition ArrDom :: V where [arr_field_simps]: "ArrDom = 1\<^sub>\<nat>"
definition ArrCod :: V where [arr_field_simps]: "ArrCod = 2\<^sub>\<nat>"

lemma ArrVal_eq_helper:
  assumes "f = g"
  shows "f\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = g\<lparr>ArrVal\<rparr>\<lparr>a\<rparr>"
  using assms by simp



subsection\<open>Arrow for \<open>Rel\<close>\<close>


subsubsection\<open>Definition and elementary properties\<close>

locale arr_Rel = \<Z> \<alpha> + vfsequence T + ArrVal: vbrelation \<open>T\<lparr>ArrVal\<rparr>\<close> for \<alpha> T +
  assumes arr_Rel_length[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: 
    "vcard T = 3\<^sub>\<nat>" 
    and arr_Rel_ArrVal_vdomain: "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> T\<lparr>ArrDom\<rparr>"
    and arr_Rel_ArrVal_vrange: "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> T\<lparr>ArrCod\<rparr>"
    and arr_Rel_ArrDom_in_Vset: "T\<lparr>ArrDom\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
    and arr_Rel_ArrCod_in_Vset: "T\<lparr>ArrCod\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"

lemmas [dg_Rel_cs_simps] = arr_Rel.arr_Rel_length


text\<open>Components.\<close>

lemma arr_Rel_components[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]:
  shows "[f, A, B]\<^sub>\<circ>\<lparr>ArrVal\<rparr> = f"
    and "[f, A, B]\<^sub>\<circ>\<lparr>ArrDom\<rparr> = A"
    and "[f, A, B]\<^sub>\<circ>\<lparr>ArrCod\<rparr> = B"
  unfolding arr_field_simps by (simp_all add: nat_omega_simps)


text\<open>Rules.\<close>

mk_ide rf arr_Rel_def[unfolded arr_Rel_axioms_def]
  |intro arr_RelI|
  |dest arr_RelD[dest]|
  |elim arr_RelE[elim!]|

lemma (in \<Z>) arr_Rel_vfsequenceI: 
  assumes "vbrelation r" 
    and "\<D>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> a"
    and "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> b"
    and "a \<in>\<^sub>\<circ> Vset \<alpha>"
    and "b \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Rel \<alpha> [r, a, b]\<^sub>\<circ>"
  by (intro arr_RelI) 
    (insert assms, auto simp: nat_omega_simps arr_Rel_components)


text\<open>Elementary properties.\<close>

lemma arr_Rel_eqI:
  assumes "arr_Rel \<alpha> S" 
    and "arr_Rel \<alpha> T"
    and "S\<lparr>ArrVal\<rparr> = T\<lparr>ArrVal\<rparr>"
    and "S\<lparr>ArrDom\<rparr> = T\<lparr>ArrDom\<rparr>"
    and "S\<lparr>ArrCod\<rparr> = T\<lparr>ArrCod\<rparr>"
  shows "S = T"
proof-
  interpret S: arr_Rel \<alpha> S by (rule assms(1))
  interpret T: arr_Rel \<alpha> T by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    show "\<D>\<^sub>\<circ> S = \<D>\<^sub>\<circ> T" 
      by (simp add: S.vfsequence_vdomain T.vfsequence_vdomain dg_Rel_cs_simps) 
    have dom_lhs: "\<D>\<^sub>\<circ> S = 3\<^sub>\<nat>" 
      by (simp add: S.vfsequence_vdomain dg_Rel_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> S \<Longrightarrow> S\<lparr>a\<rparr> = T\<lparr>a\<rparr>" for a 
      by (unfold dom_lhs, elim_in_numeral, insert assms)
        (auto simp: arr_field_simps)
  qed auto
qed

lemma (in arr_Rel) arr_Rel_def: "T = [T\<lparr>ArrVal\<rparr>, T\<lparr>ArrDom\<rparr>, T\<lparr>ArrCod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> T = 3\<^sub>\<nat>" by (simp add: vfsequence_vdomain dg_Rel_cs_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> [T\<lparr>ArrVal\<rparr>, T\<lparr>ArrDom\<rparr>, T\<lparr>ArrCod\<rparr>]\<^sub>\<circ> = 3\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> T = \<D>\<^sub>\<circ> [T\<lparr>ArrVal\<rparr>, T\<lparr>ArrDom\<rparr>, T\<lparr>ArrCod\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> T \<Longrightarrow> T\<lparr>a\<rparr> = [T\<lparr>ArrVal\<rparr>, T\<lparr>ArrDom\<rparr>, T\<lparr>ArrCod\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" for a
    unfolding dom_lhs
    by elim_in_numeral (simp_all add: arr_field_simps nat_omega_simps)
qed (auto simp: vsv_axioms)


text\<open>Size.\<close>

lemma (in arr_Rel) arr_Rel_ArrVal_in_Vset: "T\<lparr>ArrVal\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  from arr_Rel_ArrVal_vdomain arr_Rel_ArrDom_in_Vset have 
    "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    by auto
  moreover from arr_Rel_ArrVal_vrange arr_Rel_ArrCod_in_Vset have 
    "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    by auto
  ultimately show "T\<lparr>ArrVal\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (simp add: ArrVal.vbrelation_Limit_in_VsetI)
qed

lemma (in arr_Rel) arr_Rel_in_Vset: "T \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  note [dg_Rel_cs_intros] = 
    arr_Rel_ArrVal_in_Vset arr_Rel_ArrDom_in_Vset arr_Rel_ArrCod_in_Vset
  show ?thesis
    by (subst arr_Rel_def)
      (cs_concl cs_intro: dg_Rel_cs_intros V_cs_intros) 
qed

lemma small_arr_Rel[simp]: "small {T. arr_Rel \<alpha> T}"
  by (rule down[of _ \<open>Vset \<alpha>\<close>]) (auto intro!: arr_Rel.arr_Rel_in_Vset)


text\<open>Other elementary properties.\<close>

lemma set_Collect_arr_Rel[simp]: 
  "x \<in>\<^sub>\<circ> set (Collect (arr_Rel \<alpha>)) \<longleftrightarrow> arr_Rel \<alpha> x" 
  by auto

lemma (in arr_Rel) arr_Rel_ArrVal_vsubset_ArrDom_ArrCod:
  "T\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> T\<lparr>ArrDom\<rparr> \<times>\<^sub>\<circ> T\<lparr>ArrCod\<rparr>"
proof
  fix ab assume "ab \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
  then obtain a b where "ab = \<langle>a, b\<rangle>" 
    and "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)" 
    and "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>)" 
    by (blast elim: ArrVal.vbrelation_vinE)
  with arr_Rel_ArrVal_vdomain arr_Rel_ArrVal_vrange show 
    "ab \<in>\<^sub>\<circ> T\<lparr>ArrDom\<rparr> \<times>\<^sub>\<circ> T\<lparr>ArrCod\<rparr>"
    by auto
qed


subsubsection\<open>Composition\<close>


text\<open>See Chapter I-7 in \cite{mac_lane_categories_2010}.\<close>

definition comp_Rel :: "V \<Rightarrow> V \<Rightarrow> V" (infixl \<open>\<circ>\<^sub>R\<^sub>e\<^sub>l\<close> 55)
  where "comp_Rel S T = [S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>, T\<lparr>ArrDom\<rparr>, S\<lparr>ArrCod\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma comp_Rel_components:
  shows "(S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrVal\<rparr> = S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: 
      "(S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrDom\<rparr> = T\<lparr>ArrDom\<rparr>"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]:
      "(S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrCod\<rparr> = S\<lparr>ArrCod\<rparr>"
  unfolding comp_Rel_def arr_field_simps by (simp_all add: nat_omega_simps)


text\<open>Elementary properties.\<close>

lemma comp_Rel_vsv[dg_Rel_shared_cs_intros, dg_Rel_cs_intros]: 
  "vsv (S \<circ>\<^sub>R\<^sub>e\<^sub>l T)"
  unfolding comp_Rel_def by auto

lemma arr_Rel_comp_Rel[dg_Rel_cs_intros]:
  assumes "arr_Rel \<alpha> S" and "arr_Rel \<alpha> T"
  shows "arr_Rel \<alpha> (S \<circ>\<^sub>R\<^sub>e\<^sub>l T)"
proof-
  interpret S: arr_Rel \<alpha> S by (rule assms(1))
  interpret T: arr_Rel \<alpha> T by (rule assms(2))
  show ?thesis
  proof(intro arr_RelI)
    show "vfsequence (S \<circ>\<^sub>R\<^sub>e\<^sub>l T)" unfolding comp_Rel_def by simp
    show "vcard (S \<circ>\<^sub>R\<^sub>e\<^sub>l T) = 3\<^sub>\<nat>"
      unfolding comp_Rel_def by (simp add: nat_omega_simps)
    from T.arr_Rel_ArrVal_vdomain show 
      "\<D>\<^sub>\<circ> ((S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> (S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrDom\<rparr>"
      unfolding comp_Rel_components by auto
    show "\<R>\<^sub>\<circ> ((S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrVal\<rparr>) \<subseteq>\<^sub>\<circ> (S \<circ>\<^sub>R\<^sub>e\<^sub>l T)\<lparr>ArrCod\<rparr>"
      unfolding comp_Rel_components 
    proof(intro vsubsetI)
      fix z assume "z \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (S\<lparr>ArrVal\<rparr> \<circ>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>)"
      then obtain x y where "\<langle>y, z\<rangle> \<in>\<^sub>\<circ> S\<lparr>ArrVal\<rparr>" and "\<langle>x, y\<rangle> \<in>\<^sub>\<circ> T\<lparr>ArrVal\<rparr>"
        by (meson vcomp_obtain_middle vrange_iff_vdomain)
      with S.arr_Rel_ArrVal_vrange show "z \<in>\<^sub>\<circ> S\<lparr>ArrCod\<rparr>" by auto
    qed
  qed 
    (
      auto simp: 
        comp_Rel_components T.arr_Rel_ArrDom_in_Vset S.arr_Rel_ArrCod_in_Vset
    ) 
qed

lemma arr_Rel_comp_Rel_assoc[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]:
  "(H \<circ>\<^sub>R\<^sub>e\<^sub>l G) \<circ>\<^sub>R\<^sub>e\<^sub>l F = H \<circ>\<^sub>R\<^sub>e\<^sub>l (G \<circ>\<^sub>R\<^sub>e\<^sub>l F)" 
  by (simp add: comp_Rel_def vcomp_assoc arr_field_simps nat_omega_simps)


subsubsection\<open>Inclusion arrow\<close>


text\<open>
The definition of the inclusion arrow is based on the concept of the 
inclusion map, e.g., see \cite{noauthor_wikipedia_2001}\footnote{
\url{https://en.wikipedia.org/wiki/Inclusion_map}
}\<close>

definition "incl_Rel A B = [vid_on A, A, B]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma incl_Rel_components:
  shows "incl_Rel A B\<lparr>ArrVal\<rparr> = vid_on A"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: "incl_Rel A B\<lparr>ArrDom\<rparr> = A"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: "incl_Rel A B\<lparr>ArrCod\<rparr> = B"
  unfolding incl_Rel_def arr_field_simps by (simp_all add: nat_omega_simps)


text\<open>Arrow value.\<close>

lemma incl_Rel_ArrVal_vsv[dg_Rel_shared_cs_intros, dg_Rel_cs_intros]: 
  "vsv (incl_Rel A B\<lparr>ArrVal\<rparr>)"
  unfolding incl_Rel_components by simp

lemma incl_Rel_ArrVal_vdomain[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]:
  "\<D>\<^sub>\<circ> (incl_Rel A B\<lparr>ArrVal\<rparr>) = A"
  unfolding incl_Rel_components by simp

lemma incl_Rel_ArrVal_app[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> A"
  shows "incl_Rel A B\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = a"
  using assms unfolding incl_Rel_components by simp


text\<open>Elementary properties.\<close>

lemma incl_Rel_vfsequence[dg_Rel_shared_cs_intros, dg_Rel_cs_intros]: 
  "vfsequence (incl_Rel A B)" 
  unfolding incl_Rel_def by simp

lemma incl_Rel_vcard[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: 
  "vcard (incl_Rel A B) = 3\<^sub>\<nat>" 
  unfolding incl_Rel_def incl_Rel_def by (simp add: nat_omega_simps)

lemma (in \<Z>) arr_Rel_incl_RelI:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "A \<subseteq>\<^sub>\<circ> B"
  shows "arr_Rel \<alpha> (incl_Rel A B)"
proof(intro arr_RelI)
  show "vfsequence (incl_Rel A B)" unfolding incl_Rel_def by simp
  show "vcard (incl_Rel A B) = 3\<^sub>\<nat>" 
    unfolding incl_Rel_def by (simp add: nat_omega_simps)
qed (auto simp: incl_Rel_components assms)


subsubsection\<open>Identity\<close>


text\<open>See Chapter I-7 in \cite{mac_lane_categories_2010}.\<close>

definition id_Rel :: "V \<Rightarrow> V"
  where "id_Rel A = incl_Rel A A"


text\<open>Components.\<close>

lemma id_Rel_components:
  shows "id_Rel A\<lparr>ArrVal\<rparr> = vid_on A"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: "id_Rel A\<lparr>ArrDom\<rparr> = A"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: "id_Rel A\<lparr>ArrCod\<rparr> = A"
  unfolding id_Rel_def incl_Rel_components by simp_all


text\<open>Elementary properties.\<close>

lemma id_Rel_vfsequence[dg_Rel_shared_cs_intros, dg_Rel_cs_intros]: 
  "vfsequence (id_Rel A)" 
  unfolding id_Rel_def by (simp add: dg_Rel_cs_intros)

lemma id_Rel_vcard[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: 
  "vcard (id_Rel A) = 3\<^sub>\<nat>" 
  unfolding id_Rel_def by (simp add: dg_Rel_cs_simps)

lemma (in \<Z>) arr_Rel_id_RelI:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Rel \<alpha> (id_Rel A)"
  by (intro arr_RelI)
    (auto simp: id_Rel_components(1) assms dg_Rel_cs_intros dg_Rel_cs_simps)

lemma id_Rel_ArrVal_app[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]:
  assumes "a \<in>\<^sub>\<circ> A"
  shows "id_Rel A\<lparr>ArrVal\<rparr>\<lparr>a\<rparr> = a"
  using assms unfolding id_Rel_components by simp

lemma arr_Rel_comp_Rel_id_Rel_left[dg_Rel_cs_simps]:
  assumes "arr_Rel \<alpha> F" and "F\<lparr>ArrCod\<rparr> = A"
  shows "id_Rel A \<circ>\<^sub>R\<^sub>e\<^sub>l F = F"
proof(rule arr_Rel_eqI [of \<alpha>])
  interpret F: arr_Rel \<alpha> F by (rule assms(1))
  from assms(2) have "A \<in>\<^sub>\<circ> Vset \<alpha>" by (auto intro: F.arr_Rel_ArrCod_in_Vset)
  with assms(1) show "arr_Rel \<alpha> (id_Rel A \<circ>\<^sub>R\<^sub>e\<^sub>l F)" 
    by (blast intro: F.arr_Rel_id_RelI intro!: arr_Rel_comp_Rel)
  from assms(2) F.arr_Rel_ArrVal_vrange show  
    "(id_Rel A \<circ>\<^sub>R\<^sub>e\<^sub>l F)\<lparr>ArrVal\<rparr> = F\<lparr>ArrVal\<rparr>"
    unfolding comp_Rel_components id_Rel_components by auto
qed 
  (
    use assms(2) in 
      \<open>auto simp: assms(1) comp_Rel_components id_Rel_components\<close>
  )

lemma arr_Rel_comp_Rel_id_Rel_right[dg_Rel_cs_simps]:
  assumes "arr_Rel \<alpha> F" and "F\<lparr>ArrDom\<rparr> = A"
  shows "F \<circ>\<^sub>R\<^sub>e\<^sub>l id_Rel A = F"
proof(rule arr_Rel_eqI[of \<alpha>])
  interpret F: arr_Rel \<alpha> F by (rule assms(1))
  from assms(2) have "A \<in>\<^sub>\<circ> Vset \<alpha>" by (auto intro: F.arr_Rel_ArrDom_in_Vset)
  with assms(1) show "arr_Rel \<alpha> (F \<circ>\<^sub>R\<^sub>e\<^sub>l id_Rel A)"
    by (blast intro: F.arr_Rel_id_RelI intro!: arr_Rel_comp_Rel)
  show "arr_Rel \<alpha> F" by (simp add: assms(1))
  from assms(2) F.arr_Rel_ArrVal_vdomain show  
    "(F \<circ>\<^sub>R\<^sub>e\<^sub>l id_Rel A)\<lparr>ArrVal\<rparr> = F\<lparr>ArrVal\<rparr>"
    unfolding comp_Rel_components id_Rel_components by auto
qed (use assms(2) in \<open>auto simp: comp_Rel_components id_Rel_components\<close>)


subsubsection\<open>Converse\<close>


text\<open>
As mentioned in Chapter I-7 in \cite{mac_lane_categories_2010}, the 
category \<open>Rel\<close> is usually equipped with an additional structure that is
the operation of taking a converse of a relation.
The operation is meant to be used almost exclusively as part of 
the dagger functor for \<open>Rel\<close>.
\<close>

definition converse_Rel :: "V \<Rightarrow> V" ("(_\<inverse>\<^sub>R\<^sub>e\<^sub>l)" [1000] 999)
  where "converse_Rel T = [(T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>, T\<lparr>ArrCod\<rparr>, T\<lparr>ArrDom\<rparr>]\<^sub>\<circ>"

lemma converse_Rel_components:
  shows "T\<inverse>\<^sub>R\<^sub>e\<^sub>l\<lparr>ArrVal\<rparr> = (T\<lparr>ArrVal\<rparr>)\<inverse>\<^sub>\<circ>"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: "T\<inverse>\<^sub>R\<^sub>e\<^sub>l\<lparr>ArrDom\<rparr> = T\<lparr>ArrCod\<rparr>"
    and [dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: "T\<inverse>\<^sub>R\<^sub>e\<^sub>l\<lparr>ArrCod\<rparr> = T\<lparr>ArrDom\<rparr>"
  unfolding converse_Rel_def arr_field_simps by (simp_all add: nat_omega_simps)


text\<open>Elementary properties.\<close>

lemma (in arr_Rel) arr_Rel_converse_Rel: "arr_Rel \<alpha> (T\<inverse>\<^sub>R\<^sub>e\<^sub>l)"
proof(rule arr_RelI, unfold converse_Rel_components)
  show "vfsequence (T\<inverse>\<^sub>R\<^sub>e\<^sub>l)" unfolding converse_Rel_def by simp
  show "vcard (T\<inverse>\<^sub>R\<^sub>e\<^sub>l) = 3\<^sub>\<nat>"
    unfolding converse_Rel_def by (simp add: nat_omega_simps)
qed 
  (
    auto simp: 
      converse_Rel_components(1)   
      arr_Rel_ArrDom_in_Vset 
      arr_Rel_ArrCod_in_Vset
      arr_Rel_ArrVal_vdomain
      arr_Rel_ArrVal_vrange
  )

lemmas [dg_Rel_cs_intros] = 
  arr_Rel.arr_Rel_converse_Rel

lemma (in arr_Rel) 
  arr_Rel_converse_Rel_converse_Rel[dg_Rel_shared_cs_simps, dg_Rel_cs_simps]: 
  "(T\<inverse>\<^sub>R\<^sub>e\<^sub>l)\<inverse>\<^sub>R\<^sub>e\<^sub>l = T"
proof(rule arr_Rel_eqI)
  from arr_Rel_axioms show "arr_Rel \<alpha> ((T\<inverse>\<^sub>R\<^sub>e\<^sub>l)\<inverse>\<^sub>R\<^sub>e\<^sub>l)"
    by (cs_intro_step dg_Rel_cs_intros)+
qed (simp_all add: arr_Rel_axioms converse_Rel_components)

lemmas [dg_Rel_cs_simps] = 
  arr_Rel.arr_Rel_converse_Rel_converse_Rel

lemma arr_Rel_converse_Rel_eq_iff[dg_Rel_cs_simps]:
  assumes "arr_Rel \<alpha> F" and "arr_Rel \<alpha> G"
  shows "F\<inverse>\<^sub>R\<^sub>e\<^sub>l = G\<inverse>\<^sub>R\<^sub>e\<^sub>l \<longleftrightarrow> F = G"
proof(rule iffI)
  show "F\<inverse>\<^sub>R\<^sub>e\<^sub>l = G\<inverse>\<^sub>R\<^sub>e\<^sub>l \<Longrightarrow> F = G"
    by (metis arr_Rel.arr_Rel_converse_Rel_converse_Rel assms)
qed simp

lemma arr_Rel_converse_Rel_comp_Rel[dg_Rel_cs_simps]:
  assumes "arr_Rel \<alpha> G" and "arr_Rel \<alpha> F"
  shows "(F \<circ>\<^sub>R\<^sub>e\<^sub>l G)\<inverse>\<^sub>R\<^sub>e\<^sub>l = G\<inverse>\<^sub>R\<^sub>e\<^sub>l \<circ>\<^sub>R\<^sub>e\<^sub>l F\<inverse>\<^sub>R\<^sub>e\<^sub>l"
proof(rule arr_Rel_eqI, unfold converse_Rel_components comp_Rel_components)
  from assms show "arr_Rel \<alpha> (G\<inverse>\<^sub>R\<^sub>e\<^sub>l \<circ>\<^sub>R\<^sub>e\<^sub>l F\<inverse>\<^sub>R\<^sub>e\<^sub>l)"
    by (cs_concl cs_intro: dg_Rel_cs_intros)
  from assms show "arr_Rel \<alpha> ((F \<circ>\<^sub>R\<^sub>e\<^sub>l G)\<inverse>\<^sub>R\<^sub>e\<^sub>l)"
    by (cs_intro_step dg_Rel_cs_intros)+
qed (simp_all add: vconverse_vcomp)

lemma (in \<Z>) arr_Rel_converse_Rel_id_Rel: 
  assumes "c \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "arr_Rel \<alpha> ((id_Rel c)\<inverse>\<^sub>R\<^sub>e\<^sub>l)"
  using assms \<Z>_axioms 
  by (cs_concl cs_intro: dg_Rel_cs_intros arr_Rel_id_RelI)+

lemma (in \<Z>) arr_Rel_converse_Rel_id_Rel_eq_id_Rel[
    dg_Rel_shared_cs_simps, dg_Rel_cs_simps
    ]: 
  assumes "c \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(id_Rel c)\<inverse>\<^sub>R\<^sub>e\<^sub>l = id_Rel c"
  by (rule arr_Rel_eqI[of \<alpha>], unfold converse_Rel_components id_Rel_components)
    (simp_all add: assms arr_Rel_id_RelI arr_Rel_converse_Rel_id_Rel)

lemmas [dg_Rel_shared_cs_simps, dg_Rel_cs_simps] = 
  \<Z>.arr_Rel_converse_Rel_id_Rel_eq_id_Rel

lemma arr_Rel_comp_Rel_converse_Rel_left_if_v11[dg_Rel_cs_simps]:
  assumes "arr_Rel \<alpha> T" 
    and "\<D>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "T\<lparr>ArrDom\<rparr> = A"
    and "v11 (T\<lparr>ArrVal\<rparr>)" 
    and "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "T\<inverse>\<^sub>R\<^sub>e\<^sub>l \<circ>\<^sub>R\<^sub>e\<^sub>l T = id_Rel A"
proof-
  interpret T: arr_Rel \<alpha> T by (rule assms(1))
  interpret v11: v11 \<open>T\<lparr>ArrVal\<rparr>\<close> by (rule assms(4))
  show ?thesis
    by (rule arr_Rel_eqI[of \<alpha>])
      (
        auto simp: 
          converse_Rel_components 
          comp_Rel_components 
          id_Rel_components 
          assms(1,3,5)
          arr_Rel.arr_Rel_converse_Rel 
          arr_Rel_comp_Rel  
          T.arr_Rel_id_RelI
          v11.v11_vcomp_vconverse[unfolded assms(2)] 
      )
qed

lemma arr_Rel_comp_Rel_converse_Rel_right_if_v11[dg_Rel_cs_simps]:
  assumes "arr_Rel \<alpha> T" 
    and "\<R>\<^sub>\<circ> (T\<lparr>ArrVal\<rparr>) = A"
    and "T\<lparr>ArrCod\<rparr> = A"
    and "v11 (T\<lparr>ArrVal\<rparr>)" 
    and "A \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "T \<circ>\<^sub>R\<^sub>e\<^sub>l T\<inverse>\<^sub>R\<^sub>e\<^sub>l = id_Rel A"
proof-
  interpret T: arr_Rel \<alpha> T by (rule assms(1))
  interpret v11: v11 \<open>T\<lparr>ArrVal\<rparr>\<close> by (rule assms(4))
  show ?thesis
    by (rule arr_Rel_eqI[of \<alpha>])
      (
        auto simp: 
          assms(1,3,5)
          comp_Rel_components 
          converse_Rel_components 
          id_Rel_components 
          v11.v11_vcomp_vconverse'[unfolded assms(2)] 
          T.arr_Rel_id_RelI 
          arr_Rel.arr_Rel_converse_Rel
          arr_Rel_comp_Rel 
      )
qed



subsection\<open>\<open>Rel\<close> as a digraph\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dg_Rel :: "V \<Rightarrow> V"
  where "dg_Rel \<alpha> =
    [
      Vset \<alpha>,
      set {T. arr_Rel \<alpha> T},
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrDom\<rparr>),
      (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrCod\<rparr>)
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dg_Rel_components:
  shows "dg_Rel \<alpha>\<lparr>Obj\<rparr> = Vset \<alpha>"
    and "dg_Rel \<alpha>\<lparr>Arr\<rparr> = set {T. arr_Rel \<alpha> T}"
    and "dg_Rel \<alpha>\<lparr>Dom\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrDom\<rparr>)"
    and "dg_Rel \<alpha>\<lparr>Cod\<rparr> = (\<lambda>T\<in>\<^sub>\<circ>set {T. arr_Rel \<alpha> T}. T\<lparr>ArrCod\<rparr>)"
  unfolding dg_Rel_def dg_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object\<close>

lemma dg_Rel_Obj_iff: "x \<in>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Obj\<rparr> \<longleftrightarrow> x \<in>\<^sub>\<circ> Vset \<alpha>" 
  unfolding dg_Rel_components by auto


subsubsection\<open>Arrow\<close>

lemma dg_Rel_Arr_iff[dg_Rel_cs_simps]: "x \<in>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Arr\<rparr> \<longleftrightarrow> arr_Rel \<alpha> x" 
  unfolding dg_Rel_components by auto


subsubsection\<open>Domain\<close>

mk_VLambda dg_Rel_components(3)
  |vsv dg_Rel_Dom_vsv[dg_Rel_cs_intros]|
  |vdomain dg_Rel_Dom_vdomain[dg_Rel_cs_simps]|
  |app dg_Rel_Dom_app[unfolded set_Collect_arr_Rel, dg_Rel_cs_simps]|

lemma dg_Rel_Dom_vrange: "\<R>\<^sub>\<circ> (dg_Rel \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_Rel_components
  by (rule vrange_VLambda_vsubset, unfold set_Collect_arr_Rel) auto


subsubsection\<open>Codomain\<close>

mk_VLambda dg_Rel_components(4)
  |vsv dg_Rel_Cod_vsv[dg_Rel_cs_intros]|
  |vdomain dg_Rel_Cod_vdomain[dg_Rel_cs_simps]|
  |app dg_Rel_Cod_app[unfolded set_Collect_arr_Rel, dg_Rel_cs_simps]|

lemma dg_Rel_Cod_vrange: "\<R>\<^sub>\<circ> (dg_Rel \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Obj\<rparr>"
  unfolding dg_Rel_components
  by (rule vrange_VLambda_vsubset, unfold set_Collect_arr_Rel) auto


subsubsection\<open>Arrow with a domain and a codomain\<close>


text\<open>Rules.\<close>

lemma dg_Rel_is_arrI[dg_Rel_cs_intros]:
  assumes "arr_Rel \<alpha> S" and "S\<lparr>ArrDom\<rparr> = A" and "S\<lparr>ArrCod\<rparr> = B"
  shows "S : A \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> B"
  using assms by (intro is_arrI, unfold dg_Rel_components) simp_all

lemma dg_Rel_is_arrD:
  assumes "S : A \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> B"
  shows "arr_Rel \<alpha> S" 
    and [dg_cs_simps]: "S\<lparr>ArrDom\<rparr> = A" 
    and [dg_cs_simps]: "S\<lparr>ArrCod\<rparr> = B"
  using is_arrD[OF assms] unfolding dg_Rel_components by simp_all

lemma dg_Rel_is_arrE:
  assumes "S : A \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> B"
  obtains "arr_Rel \<alpha> S" and "S\<lparr>ArrDom\<rparr> = A" and "S\<lparr>ArrCod\<rparr> = B"
  using is_arrD[OF assms] unfolding dg_Rel_components by simp_all


text\<open>Elementary properties.\<close>

lemma (in \<Z>) dg_Rel_incl_Rel_is_arr:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" and "B \<in>\<^sub>\<circ> Vset \<alpha>" and "A \<subseteq>\<^sub>\<circ> B"
  shows "incl_Rel A B : A \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> B"
proof(rule dg_Rel_is_arrI)
  show "arr_Rel \<alpha> (incl_Rel A B)" by (intro arr_Rel_incl_RelI assms)
qed (simp_all add: incl_Rel_components)

lemma (in \<Z>) dg_Rel_incl_Rel_is_arr'[dg_Rel_cs_intros]:
  assumes "A \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "B \<in>\<^sub>\<circ> Vset \<alpha>" 
    and "A \<subseteq>\<^sub>\<circ> B"
    and "A' = A"
    and "B' = B"
  shows "incl_Rel A B : A' \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> B'"
  using assms(1-3) unfolding assms(4,5) by (rule dg_Rel_incl_Rel_is_arr)

lemmas [dg_Rel_cs_intros] = \<Z>.dg_Rel_incl_Rel_is_arr'


subsubsection\<open>\<open>Rel\<close> is a digraph\<close>

lemma (in \<Z>) dg_Rel_Hom_vifunion_in_Vset:
  assumes "X \<in>\<^sub>\<circ> Vset \<alpha>" and "Y \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "(\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Rel \<alpha>) A B) \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  define Q where
    "Q i = (if i = 0 then VPow (\<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y) else if i = 1\<^sub>\<nat> then X else Y)" 
    for i
  have 
    "{[r, A, B]\<^sub>\<circ> |r A B. r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y \<and> A \<in>\<^sub>\<circ> X \<and> B \<in>\<^sub>\<circ> Y} \<subseteq>
      elts (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
  proof(intro subsetI, unfold mem_Collect_eq, elim exE conjE)
    fix F r A B assume prems: 
      "F = [r, A, B]\<^sub>\<circ>" 
      "r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y"
      "A \<in>\<^sub>\<circ> X"
      "B \<in>\<^sub>\<circ> Y"
    show "F \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    proof(intro vproductI, unfold Ball_def; (intro allI impI)?)
      show "\<D>\<^sub>\<circ> F = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" 
        by (simp add: three prems(1) nat_omega_simps)
      fix i assume "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
      then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> by auto
      then show "F\<lparr>i\<rparr> \<in>\<^sub>\<circ> Q i" by cases (auto simp: Q_def prems nat_omega_simps)
    qed (auto simp: prems(1))
  qed
  moreover then have small[simp]: 
    "small {[r, A, B]\<^sub>\<circ> | r A B. r \<subseteq>\<^sub>\<circ>\<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y \<and> A \<in>\<^sub>\<circ> X \<and> B \<in>\<^sub>\<circ> Y}"
    by (rule down)
  ultimately have
    "set {[r, A, B]\<^sub>\<circ> |r A B. r \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y \<and> A \<in>\<^sub>\<circ> X \<and> B \<in>\<^sub>\<circ> Y} \<subseteq>\<^sub>\<circ>
      (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    by auto
  moreover have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i) \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule Limit_vproduct_in_VsetI)
    show "set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>} \<in>\<^sub>\<circ> Vset \<alpha>"
      by (auto simp: three[symmetric] intro!: Axiom_of_Infinity)
    from assms(1,2) have "VPow (\<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (intro Limit_VPow_in_VsetI Limit_vtimes_in_VsetI) auto
    then show "Q i \<in>\<^sub>\<circ> Vset \<alpha>" if "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" for i
      using that assms(1,2) unfolding Q_def by (auto simp: nat_omega_simps)
  qed auto
  moreover have
    "(\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Rel \<alpha>) A B) \<subseteq>\<^sub>\<circ>
      set {[r, A, B]\<^sub>\<circ> | r A B. r \<subseteq>\<^sub>\<circ>\<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y \<and> A \<in>\<^sub>\<circ> X \<and> B \<in>\<^sub>\<circ> Y}"
  proof(rule vsubsetI)
    fix F assume prems: "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Rel \<alpha>) A B)"
    then obtain A where A: "A \<in>\<^sub>\<circ> X" and F_b: "F \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Rel \<alpha>) A B)" 
      unfolding vifunion_iff by auto
    then obtain B where B: "B \<in>\<^sub>\<circ> Y" and F_fba: "F \<in>\<^sub>\<circ> Hom (dg_Rel \<alpha>) A B" 
      by fastforce
    then have "F : A \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> B" by simp
    note F = dg_Rel_is_arrD[OF this]
    interpret F: arr_Rel \<alpha> F rewrites "F\<lparr>ArrDom\<rparr> = A" and "F\<lparr>ArrCod\<rparr> = B"
      by (intro F)+
    show "F \<in>\<^sub>\<circ> set {[r, A, B]\<^sub>\<circ> | r A B. r \<subseteq>\<^sub>\<circ>\<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y \<and> A \<in>\<^sub>\<circ> X \<and> B \<in>\<^sub>\<circ> Y}"
    proof(intro in_set_CollectI small exI conjI)
      from F.arr_Rel_def show "F = [F\<lparr>ArrVal\<rparr>, A, B]\<^sub>\<circ>" unfolding F(2,3) by simp
      from A B have "A \<times>\<^sub>\<circ> B \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y" by auto
      moreover then have "F\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
        by (auto simp: F.arr_Rel_ArrVal_vsubset_ArrDom_ArrCod)
      ultimately show "F\<lparr>ArrVal\<rparr> \<subseteq>\<^sub>\<circ> \<Union>\<^sub>\<circ>X \<times>\<^sub>\<circ> \<Union>\<^sub>\<circ>Y" by auto
    qed (intro A B)+
  qed
  ultimately show "(\<Union>\<^sub>\<circ>A\<in>\<^sub>\<circ>X. \<Union>\<^sub>\<circ>B\<in>\<^sub>\<circ>Y. Hom (dg_Rel \<alpha>) A B) \<in>\<^sub>\<circ> Vset \<alpha>" by blast
qed

lemma (in \<Z>) digraph_dg_Rel: "digraph \<alpha> (dg_Rel \<alpha>)"
proof(intro digraphI)
  show "vfsequence (dg_Rel \<alpha>)" unfolding dg_Rel_def by clarsimp
  show "vcard (dg_Rel \<alpha>) = 4\<^sub>\<nat>" 
    unfolding dg_Rel_def by (simp add: nat_omega_simps)
  show "\<R>\<^sub>\<circ> (dg_Rel \<alpha>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_Rel_Dom_vrange)
  show "\<R>\<^sub>\<circ> (dg_Rel \<alpha>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Obj\<rparr>" by (simp add: dg_Rel_Cod_vrange)
qed (auto simp: dg_Rel_components dg_Rel_Hom_vifunion_in_Vset dg_Rel_Dom_vrange)



subsection\<open>Canonical dagger for \<open>Rel\<close>\<close>


text\<open>
Dagger categories are exposed explicitly later. 
In the context of this section, the ``dagger'' is viewed merely as 
an explicitly defined homomorphism. A definition of a dagger functor, upon
which the definition presented in this section is based, can be found in nLab 
\cite{noauthor_nlab_nodate}\footnote{\url{https://ncatlab.org/nlab/show/Rel})}.
This reference also contains the majority of the results that are presented
in this subsection.
\<close>


subsubsection\<open>Definition and elementary properties\<close>

definition dghm_dag_Rel :: "V \<Rightarrow> V" (\<open>\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l\<close>)
  where "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> = 
    [
      vid_on (dg_Rel \<alpha>\<lparr>Obj\<rparr>), 
      VLambda (dg_Rel \<alpha>\<lparr>Arr\<rparr>) converse_Rel, 
      op_dg (dg_Rel \<alpha>), 
      dg_Rel \<alpha>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma dghm_dag_Rel_components:
  shows "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr> = vid_on (dg_Rel \<alpha>\<lparr>Obj\<rparr>)"
    and "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr> = VLambda (dg_Rel \<alpha>\<lparr>Arr\<rparr>) converse_Rel"
    and "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>HomDom\<rparr> = op_dg (dg_Rel \<alpha>)"
    and "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>HomCod\<rparr> = dg_Rel \<alpha>"
  unfolding dghm_dag_Rel_def dghm_field_simps by (simp_all add: nat_omega_simps)


subsubsection\<open>Object map\<close>

mk_VLambda dghm_dag_Rel_components(1)[folded VLambda_vid_on]
  |vsv dghm_dag_Rel_ObjMap_vsv[dg_Rel_cs_intros]|
  |vdomain 
    dghm_dag_Rel_ObjMap_vdomain[unfolded dg_Rel_components, dg_Rel_cs_simps]
  |
  |app dghm_dag_Rel_ObjMap_app[unfolded dg_Rel_components, dg_Rel_cs_simps]|

lemma dghm_dag_Rel_ObjMap_vrange[dg_cs_simps]: "\<R>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>) = Vset \<alpha>"
  unfolding dghm_dag_Rel_components dg_Rel_components by simp


subsubsection\<open>Arrow map\<close>

mk_VLambda dghm_dag_Rel_components(2)
  |vsv dghm_dag_Rel_ArrMap_vsv[dg_Rel_cs_intros]|
  |vdomain dghm_dag_Rel_ArrMap_vdomain[dg_Rel_cs_simps]|
  |app dghm_dag_Rel_ArrMap_app[unfolded dg_Rel_cs_simps, dg_Rel_cs_simps]|


subsubsection\<open>Further properties\<close>

lemma dghm_dag_Rel_ArrMap_vrange[dg_Rel_cs_simps]: 
  "\<R>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>) = dg_Rel \<alpha>\<lparr>Arr\<rparr>"
proof(intro vsubset_antisym vsubsetI)
  interpret ArrMap: vsv \<open>\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<close> 
    unfolding dghm_dag_Rel_components by simp
  fix T assume "T \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>)"
  then obtain S where T_def: "T = \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>S\<rparr>" 
    and S: "S \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>)"
    by (blast dest: ArrMap.vrange_atD)
  from S show "T \<in>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Arr\<rparr>" 
    by 
      (
        simp add:
          T_def 
          dghm_dag_Rel_components 
          dg_Rel_components 
          arr_Rel.arr_Rel_converse_Rel
      )
next
  interpret ArrMap: vsv \<open>\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<close> 
    unfolding dghm_dag_Rel_components by simp
  fix T assume "T \<in>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Arr\<rparr>"
  then have "arr_Rel \<alpha> T" by (simp add: dg_Rel_components)
  then have "(T\<inverse>\<^sub>R\<^sub>e\<^sub>l)\<inverse>\<^sub>R\<^sub>e\<^sub>l = T" and "arr_Rel \<alpha> (T\<inverse>\<^sub>R\<^sub>e\<^sub>l)"
    by 
      (
        auto simp: 
          arr_Rel.arr_Rel_converse_Rel_converse_Rel arr_Rel.arr_Rel_converse_Rel
      )
  then have "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<inverse>\<^sub>R\<^sub>e\<^sub>l\<rparr> = T" "T\<inverse>\<^sub>R\<^sub>e\<^sub>l \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>)"
    by (simp_all add: dg_Rel_components(2) dghm_dag_Rel_components(2))
  then show "T \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>)" by blast
qed

lemma dghm_dag_Rel_ArrMap_app_is_arr:
  assumes "T : b \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> a"
  shows 
    "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
proof(intro is_arrI)
  from assms have a: "a \<in>\<^sub>\<circ> Vset \<alpha>" and b: "b \<in>\<^sub>\<circ> Vset \<alpha>"
    unfolding dg_Rel_components by (fastforce simp: dg_Rel_components)+
  from assms have T: "arr_Rel \<alpha> T" by (auto simp: dg_Rel_is_arrD(1))
  then show dag_T: "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> \<in>\<^sub>\<circ> dg_Rel \<alpha>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: dg_Rel_cs_simps cs_intro: dg_Rel_cs_intros)
  from a assms T show "dg_Rel \<alpha>\<lparr>Dom\<rparr>\<lparr>\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<rparr> = \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps dg_Rel_cs_simps cs_intro: dg_Rel_cs_intros)
  from b assms T show "dg_Rel \<alpha>\<lparr>Cod\<rparr>\<lparr>\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>\<rparr> = \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    by (cs_concl cs_simp: dg_cs_simps dg_Rel_cs_simps cs_intro: dg_Rel_cs_intros)
qed


subsubsection\<open>Canonical dagger for \<open>Rel\<close> is a digraph isomorphism\<close>

lemma (in \<Z>) dghm_dag_Rel_is_iso_dghm: 
  "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_dg (dg_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^sub>.\<^sub>i\<^sub>s\<^sub>o\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>"
proof(rule is_iso_dghmI)
  interpret digraph \<alpha> \<open>dg_Rel \<alpha>\<close> by (simp add: digraph_dg_Rel)
  show "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : op_dg (dg_Rel \<alpha>) \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>"
  proof(rule is_dghmI, unfold dg_op_simps dghm_dag_Rel_components(3,4))
    show "vfsequence (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)"
      unfolding dghm_dag_Rel_def by (simp add: nat_omega_simps)
    show "vcard (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>) = 4\<^sub>\<nat>"
      unfolding dghm_dag_Rel_def by (simp add: nat_omega_simps)
    fix T a b assume "T : b \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> a" 
    then show
      "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr> : \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>dg_Rel \<alpha>\<^esub> \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      by (rule dghm_dag_Rel_ArrMap_app_is_arr)
  qed (auto simp: dghm_dag_Rel_components intro: dg_cs_intros dg_op_intros)
  show "v11 (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>)"
  proof
    (
      intro vsv.vsv_valeq_v11I,
      unfold dghm_dag_Rel_ArrMap_vdomain dg_Rel_Arr_iff
    )
    fix S T assume prems: 
      "arr_Rel \<alpha> S" 
      "arr_Rel \<alpha> T" 
      "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>S\<rparr> = \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>\<lparr>T\<rparr>" 
    from prems show "S = T"
      by 
        (
          auto simp: 
            dg_Rel_components 
            dg_Rel_cs_simps
            dghm_dag_Rel_ArrMap_app[OF prems(1)] 
            dghm_dag_Rel_ArrMap_app[OF prems(2)]
        )
  qed (auto intro: dg_Rel_cs_intros)
  show "\<R>\<^sub>\<circ> (\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>\<lparr>ArrMap\<rparr>) = dg_Rel \<alpha>\<lparr>Arr\<rparr>" by (simp add: dg_Rel_cs_simps)
qed (simp_all add: dghm_dag_Rel_components)


subsubsection\<open>Further properties of the canonical dagger\<close>

lemma (in \<Z>) dghm_cn_comp_dghm_dag_Rel_dghm_dag_Rel: 
  "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> = dghm_id (dg_Rel \<alpha>)"
proof-
  interpret digraph \<alpha> \<open>dg_Rel \<alpha>\<close> by (simp add: digraph_dg_Rel)
  from dghm_dag_Rel_is_iso_dghm have dag: 
    "\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> : dg_Rel \<alpha> \<^sub>D\<^sub>G\<mapsto>\<mapsto>\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>"
    by (simp add: is_iso_dghm_def)
  show ?thesis
  proof(rule dghm_eqI)
    show "(\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>ArrMap\<rparr> = dghm_id (dg_Rel \<alpha>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI)
      show "vsv ((\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>ArrMap\<rparr>)"
        by (auto simp: dghm_cn_comp_components dghm_dag_Rel_components)
      fix a assume "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> ((\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>ArrMap\<rparr>)"
      then have a: "arr_Rel \<alpha> a" 
        unfolding dg_Rel_cs_simps dghm_cn_comp_ArrMap_vdomain[OF dag dag] by simp
      from a dghm_dag_Rel_is_iso_dghm show 
        "(\<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha> \<^sub>D\<^sub>G\<^sub>H\<^sub>M\<circ> \<dagger>\<^sub>D\<^sub>G\<^sub>.\<^sub>R\<^sub>e\<^sub>l \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr> = dghm_id (dg_Rel \<alpha>)\<lparr>ArrMap\<rparr>\<lparr>a\<rparr>"
        by
          (
            cs_concl
              cs_simp: dg_Rel_cs_simps dg_cs_simps dg_cn_cs_simps 
              cs_intro: dg_Rel_cs_intros dghm_cs_intros 
          )
    qed (simp_all add: dghm_cn_comp_components dghm_id_components dg_Rel_cs_simps)
    show "dghm_id (dg_Rel \<alpha>) : dg_Rel \<alpha> \<mapsto>\<mapsto>\<^sub>D\<^sub>G\<^bsub>\<alpha>\<^esub> dg_Rel \<alpha>"
      by (simp_all add: digraph.dg_dghm_id_is_dghm digraph_axioms)
  qed 
    (
      auto simp: 
        dghm_cn_comp_is_dghm[OF digraph_axioms dag dag] 
        dghm_cn_comp_components 
        dghm_dag_Rel_components 
        dghm_id_components
    )
qed

text\<open>\newpage\<close>

end