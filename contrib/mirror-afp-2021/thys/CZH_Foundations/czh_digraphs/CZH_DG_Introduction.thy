(* Copyright 2021 (C) Mihails Milehins *)

chapter\<open>Digraphs\<close>

section\<open>Introduction\<close>
theory CZH_DG_Introduction
  imports
    "HOL-Library.Rewrite"
    CZH_Sets_NOP
    CZH_Sets_VNHS
begin



subsection\<open>Background\<close>


text\<open>
Many concepts that are normally associated with category theory can be
generalized to directed graphs. It is the goal of
this chapter to expose these generalized concepts and provide the
relevant foundations for the development of the notion of a semicategory
in the next chapter.
It is important to note, however, that it is not the goal of this chapter 
to present a comprehensive canonical theory of directed graphs. 
Nonetheless, there is little that could prevent one from extending this 
body of work by providing canonical results from the theory of directed 
graphs.
\<close>



subsection\<open>Preliminaries\<close>

declare One_nat_def[simp del]

named_theorems slicing_simps
named_theorems slicing_commute
named_theorems slicing_intros

named_theorems dg_op_simps
named_theorems dg_op_intros

named_theorems dg_cs_simps
named_theorems dg_cs_intros

named_theorems dg_shared_cs_simps
named_theorems dg_shared_cs_intros



subsection\<open>CS setup for foundations\<close>

named_theorems V_cs_simps
named_theorems V_cs_intros

named_theorems Ord_cs_simps
named_theorems Ord_cs_intros


subsubsection\<open>\<open>HOL\<close>\<close>

lemma (in semilattice_sup) sup_commute':
  shows "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a \<squnion> b = b' \<squnion> a'"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a \<squnion> b' = b \<squnion> a'"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a' \<squnion> b = b' \<squnion> a"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a \<squnion> b' = b \<squnion> a'"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a' \<squnion> b' = b \<squnion> a"
  by (auto simp: sup.commute)

lemma (in semilattice_inf) inf_commute':
  shows "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a \<sqinter> b = b' \<sqinter> a'"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a \<sqinter> b' = b \<sqinter> a'"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a' \<sqinter> b = b' \<sqinter> a"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a \<sqinter> b' = b \<sqinter> a'"
    and "b' = b \<Longrightarrow> a' = a \<Longrightarrow> a' \<sqinter> b' = b \<sqinter> a"
  by (auto simp: inf.commute)

lemmas [V_cs_simps] =
  if_P 
  if_not_P
  inf.absorb1
  inf.absorb2
  sup.absorb1
  sup.absorb2
  add_0_right 
  add_0

lemmas [V_cs_intros] = 
  sup_commute' 
  inf_commute' 
  sup.commute
  inf.commute


subsubsection\<open>Foundations\<close>

abbreviation (input) if3 :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "if3 a b c \<equiv>
    (
      \<lambda>i. if i = 0 \<Rightarrow> a
           | i = 1\<^sub>\<nat> \<Rightarrow> b
           | otherwise \<Rightarrow> c
    )"
lemma if3_0[V_cs_simps]: "if3 a b c 0 = a" by auto
lemma if3_1[V_cs_simps]: "if3 a b c (1\<^sub>\<nat>) = b" by auto
lemma if3_2[V_cs_simps]: "if3 a b c (2\<^sub>\<nat>) = c" by auto

lemma vinsertI1':
  assumes "x' = x"
  shows "x \<in>\<^sub>\<circ> vinsert x' A"
  unfolding assms by (rule vinsertI1)

lemma in_vsingleton[V_cs_intros]:
  assumes "f = a"
  shows "f \<in>\<^sub>\<circ> set {a}"
  unfolding assms by simp

lemma a_in_succ_a: "a \<in>\<^sub>\<circ> succ a" by simp

lemma a_in_succ_xI:
  assumes "a \<in>\<^sub>\<circ> x"
  shows "a \<in>\<^sub>\<circ> succ x"
  using assms by simp

lemma vone_ne[V_cs_intros]: "1\<^sub>\<nat> \<noteq> 0" by clarsimp

lemmas [V_cs_simps] =
  vinsert_set_insert_eq
  beta 
  set_empty
  vcard_0
   
lemmas [V_cs_intros] = 
  mem_not_refl 
  succ_notin_self
  vset_neq_1  
  vset_neq_2 
  nin_vinsertI
  vinsertI1'
  vinsertI2
  vfinite_vinsert
  vfinite_vsingleton
  vdisjnt_nin_right
  vdisjnt_nin_left
  vunionI1 
  vunionI2
  vunion_in_VsetI
  vintersection_in_VsetI
  vsubset_reflexive
  vsingletonI
  small_insert small_empty
  Limit_vtimes_in_VsetI 
  Limit_VPow_in_VsetI
  a_in_succ_a
  vsubset_vempty


subsubsection\<open>Binary relations\<close>

lemma vtimesI'[V_cs_intros]:
  assumes "ab = \<langle>a, b\<rangle>" and "a \<in>\<^sub>\<circ> A" and "b \<in>\<^sub>\<circ> B" 
  shows "ab \<in>\<^sub>\<circ> A \<times>\<^sub>\<circ> B"
  using assms by simp

lemma vrange_vcomp_vsubset[V_cs_intros]:
  assumes "\<R>\<^sub>\<circ> r \<subseteq>\<^sub>\<circ> B"
  shows "\<R>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) \<subseteq>\<^sub>\<circ> B"
  using assms by auto

lemma vrange_vconst_on_vsubset[V_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> R"
  shows "\<R>\<^sub>\<circ> (vconst_on A a) \<subseteq>\<^sub>\<circ> R"
  using assms by auto

lemma vrange_vcomp_eq_vrange[V_cs_simps]:
  assumes "\<D>\<^sub>\<circ> r = \<R>\<^sub>\<circ> s"
  shows "\<R>\<^sub>\<circ> (r \<circ>\<^sub>\<circ> s) = \<R>\<^sub>\<circ> r"
  using assms by (metis vimage_vdomain vrange_vcomp)

lemmas [V_cs_simps] =
  vdomain_vsingleton
  vdomain_vlrestriction
  vdomain_vcomp_vsubset
  vdomain_vconverse
  vrange_vconverse
  vdomain_vconst_on
  vconverse_vtimes
  vdomain_VLambda


subsubsection\<open>Single-valued functions\<close>

lemmas (in vsv) [V_cs_intros] = vsv_axioms

lemma vpair_app:
  assumes "j = a"
  shows "set {\<langle>a, b\<rangle>}\<lparr>j\<rparr> = b"
  unfolding assms by simp

lemmas [V_cs_simps] =
  vpair_app
  vsv.vlrestriction_app
  vsv_vcomp_at

lemmas (in vsv) [V_cs_intros] = vsv_vimageI2'

lemmas [V_cs_intros] =
  vsv_vsingleton
  vsv.vsv_vimageI2'
  vsv_vcomp


subsubsection\<open>Injective single-valued functions\<close>

lemmas (in v11) [V_cs_intros] = v11_axioms

lemma (in v11) v11_vconverse_app_in_vdomain':
  assumes "y \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> r" and "A = \<D>\<^sub>\<circ> r"
  shows "r\<inverse>\<^sub>\<circ>\<lparr>y\<rparr> \<in>\<^sub>\<circ> A"
  using assms(1) unfolding assms(2) by (rule v11_vconverse_app_in_vdomain)

lemmas (in v11) [V_cs_intros] = v11_vconverse_app_in_vdomain'
lemmas [V_cs_intros] = v11.v11_vconverse_app_in_vdomain'

lemmas (in v11) [V_cs_simps] = (*only in the context of v11*)
  v11_app_if_vconverse_app[rotated -2]
  v11_app_vconverse_app 
  v11_vconverse_app_app

lemmas [V_cs_simps] = 
  v11.v11_vconverse_app[rotated -1]
  v11.v11_app_vconverse_app 
  v11.v11_vconverse_app_app

lemmas [V_cs_intros] =
  v11D(1)
  v11.v11_vconverse
  v11_vcomp


subsubsection\<open>Operations on indexed families of sets\<close>

lemmas [V_cs_simps] = 
  vprojection_app 
  vprojection_vdomain

lemmas [V_cs_intros] = vprojection_vsv


subsubsection\<open>Finite sequences\<close>

lemmas (in vfsequence) [V_cs_intros] = vfsequence_axioms

lemmas (in vfsequence) [V_cs_simps] = vfsequence_vdomain
lemmas [V_cs_simps] = vfsequence.vfsequence_vdomain

lemmas [V_cs_intros] = 
  vfsequence.vfsequence_vcons
  vfsequence_vempty

lemmas [V_cs_simps] = 
  vfinite_0_left 
  vfinite_0_right


subsubsection\<open>Binary relation as a finite sequence\<close>

lemmas [V_cs_simps] = 
  fconverse_vunion
  fconverse_ftimes
  vdomain_fflip


subsubsection\<open>Ordinals\<close>

lemmas [Ord_cs_intros] = 
  Limit_right_Limit_mult
  Limit_left_Limit_mult
  Ord_succ_mono
  Limit_plus_omega_vsubset_Limit
  Limit_plus_nat_in_Limit
 

subsubsection\<open>von Neumann hierarchy\<close>

lemma (in \<Z>) omega_in_any[V_cs_intros]:
  assumes "\<alpha> \<subseteq>\<^sub>\<circ> \<beta>"
  shows "\<omega> \<in>\<^sub>\<circ> \<beta>" 
  using assms by auto

lemma Ord_vsubset_succ[V_cs_intros]:
  assumes "Ord \<alpha>" and "Ord \<beta>" and "\<alpha> \<subseteq>\<^sub>\<circ> \<beta>"
  shows "\<alpha> \<subseteq>\<^sub>\<circ> succ \<beta>" 
  by (metis Ord_linear_le Ord_succ assms(1) assms(2) assms(3) leD succ_le_iff)

lemma Ord_in_Vset_succ[V_cs_intros]:
  assumes "Ord \<alpha>" and "a \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "a \<in>\<^sub>\<circ> Vset (succ \<alpha>)"
  using assms by (auto simp: Ord_Vset_in_Vset_succI)

lemma Ord_vsubset_Vset_succ[V_cs_intros]:
  assumes "Ord \<alpha>" and "B \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  shows "B \<subseteq>\<^sub>\<circ> Vset (succ \<alpha>)"
  by (intro vsubsetI) 
    (auto simp: assms Vset_trans Ord_vsubset_in_Vset_succI)

lemmas (in \<Z>) [V_cs_intros] = 
  omega_in_\<alpha>
  Ord_\<alpha>
  Limit_\<alpha>

lemmas [V_cs_intros] =
  vempty_in_Vset_succ
  \<Z>.ord_of_nat_in_Vset
  Vset_in_mono
  Limit_vpair_in_VsetI
  Vset_vsubset_mono 
  Ord_succ
  Limit_vempty_in_VsetI
  Limit_insert_in_VsetI
  vfsequence.vfsequence_Limit_vcons_in_VsetI
  vfsequence.vfsequence_Ord_vcons_in_Vset_succI
  Limit_vdoubleton_in_VsetI
  Limit_omega_in_VsetI
  Limit_ftimes_in_VsetI


subsubsection\<open>\<open>n\<close>-ary operations\<close>

lemmas [V_cs_simps] =
  fflip_app
  vdomain_fflip


subsubsection\<open>Countable ordinals as a set\<close>

named_theorems omega_of_set
named_theorems nat_omega_simps_extra

lemmas [nat_omega_simps_extra] = 
  add_num_simps 
  Suc_numeral 
  Suc_1 
  le_num_simps
  less_numeral_simps(1,2)
  less_num_simps 
  less_one
  nat_omega_simps

lemmas [omega_of_set] = nat_omega_simps_extra

lemma set_insert_succ[omega_of_set]:
  assumes [simp]: "small b" and "set b = a\<^sub>\<nat>"
  shows "set (insert (a\<^sub>\<nat>) b) = succ (a\<^sub>\<nat>)"
  unfolding assms(2)[symmetric] by auto

lemma set_0[omega_of_set]: "set {0} = succ 0" by auto


subsubsection\<open>Sequences\<close>

named_theorems vfsequence_simps
named_theorems vfsequence_intros

lemmas [vfsequence_simps] =
  vfsequence.vfsequence_at_last[rotated]
  vfsequence.vfsequence_vcard_vcons[rotated]
  vfsequence.vfsequence_at_not_last[rotated]

lemmas [vfsequence_intros] = 
  vfsequence.vfsequence_vcons
  vfsequence_vempty


subsubsection\<open>Further numerals\<close>

named_theorems nat_omega_intros

lemma [nat_omega_intros]:
  assumes "a < b"
  shows "a\<^sub>\<nat> \<in>\<^sub>\<circ> b\<^sub>\<nat>"
  using assms by simp

lemma [nat_omega_intros]: 
  assumes "0 < b"
  shows "0 \<in>\<^sub>\<circ> b\<^sub>\<nat>" 
  using assms by auto

lemma [nat_omega_intros]:
  assumes "a = numeral b"
  shows "(0::nat) < a"
  using assms by auto

lemma nat_le_if_in[nat_omega_intros]:
  assumes "x\<^sub>\<nat> \<in>\<^sub>\<circ> y\<^sub>\<nat>"
  shows "x\<^sub>\<nat> \<le> y\<^sub>\<nat>"
  using assms by auto

lemma vempty_le_nat[nat_omega_intros]: "0 \<le> y\<^sub>\<nat>" by auto

lemmas [nat_omega_intros] = 
  preorder_class.order_refl
  preorder_class.eq_refl


subsubsection\<open>Generally available foundational results\<close>

lemma (in \<Z>) \<Z>_\<beta>:
  assumes "\<beta> = \<alpha>"
  shows "\<Z> \<beta>"
  unfolding assms by auto

lemmas (in \<Z>) [dg_cs_intros] = \<Z>_\<beta> 

text\<open>\newpage\<close>

end