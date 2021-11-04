(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Comma categories\<close>
theory CZH_ECAT_Comma
  imports 
    CZH_ECAT_NTCF
    CZH_ECAT_Simple
begin



subsection\<open>Background\<close>

named_theorems cat_comma_cs_simps
named_theorems cat_comma_cs_intros



subsection\<open>Comma category\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>
See Exercise 1.3.vi in \cite{riehl_category_2016} or 
Chapter II-6 in \cite{mac_lane_categories_2010}.
\<close>

definition cat_comma_Obj :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cat_comma_Obj \<GG> \<HH> \<equiv> set
    {
      [a, b, f]\<^sub>\<circ> | a b f.
        a \<in>\<^sub>\<circ> \<GG>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr> \<and>
        b \<in>\<^sub>\<circ> \<HH>\<lparr>HomDom\<rparr>\<lparr>Obj\<rparr> \<and>
        f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<GG>\<lparr>HomCod\<rparr>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>
    }"

lemma small_cat_comma_Obj[simp]: 
  "small
    {
      [a, b, f]\<^sub>\<circ> | a b f.
        a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<and> b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<and> f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>
    }"
  (is \<open>small ?abfs\<close>)
proof-
  define Q where
    "Q i = (if i = 0 then \<AA>\<lparr>Obj\<rparr> else if i = 1\<^sub>\<nat> then \<BB>\<lparr>Obj\<rparr> else \<CC>\<lparr>Arr\<rparr>)" 
    for i
  have "?abfs \<subseteq> elts (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    unfolding Q_def
  proof
    (
      intro subsetI, 
      unfold mem_Collect_eq, 
      elim exE conjE, 
      intro vproductI; 
      simp only:
    )
    fix a b f show "\<D>\<^sub>\<circ> [a, b, f]\<^sub>\<circ> = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
      by (simp add: three nat_omega_simps)
  qed (force simp: nat_omega_simps)+
  then show "small ?abfs" by (rule down)
qed

definition cat_comma_Hom :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V"
  where "cat_comma_Hom \<GG> \<HH> abf a'b'f' \<equiv> set
    {
      [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ> | g h.
        abf \<in>\<^sub>\<circ> cat_comma_Obj \<GG> \<HH> \<and>
        a'b'f' \<in>\<^sub>\<circ> cat_comma_Obj \<GG> \<HH> \<and>
        g : abf\<lparr>0\<rparr> \<mapsto>\<^bsub>\<GG>\<lparr>HomDom\<rparr>\<^esub> a'b'f'\<lparr>0\<rparr> \<and>
        h : abf\<lparr>1\<^sub>\<nat>\<rparr> \<mapsto>\<^bsub>\<HH>\<lparr>HomDom\<rparr>\<^esub> a'b'f'\<lparr>1\<^sub>\<nat>\<rparr> \<and>
        a'b'f'\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<GG>\<lparr>HomCod\<rparr>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> =
         \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<GG>\<lparr>HomCod\<rparr>\<^esub> abf\<lparr>2\<^sub>\<nat>\<rparr>
    }"

lemma small_cat_comma_Hom[simp]: "small
  {
    [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ> | g h.
      abf \<in>\<^sub>\<circ> cat_comma_Obj \<GG> \<HH> \<and>
      a'b'f' \<in>\<^sub>\<circ> cat_comma_Obj \<GG> \<HH> \<and>
      g : abf\<lparr>0\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> a'b'f'\<lparr>0\<rparr> \<and>
      h : abf\<lparr>1\<^sub>\<nat>\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> a'b'f'\<lparr>1\<^sub>\<nat>\<rparr> \<and>
      a'b'f'\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> abf\<lparr>2\<^sub>\<nat>\<rparr>
  }"
  (is \<open>small ?abf_a'b'f'_gh\<close>)
proof-
  define Q where
    "Q i =
      (
        if i = 0
        then cat_comma_Obj \<GG> \<HH> 
        else if i = 1\<^sub>\<nat> then cat_comma_Obj \<GG> \<HH> else \<AA>\<lparr>Arr\<rparr> \<times>\<^sub>\<bullet> \<BB>\<lparr>Arr\<rparr>
      )"
    for i
  have "?abf_a'b'f'_gh \<subseteq> elts (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    unfolding Q_def
  proof
    (
      intro subsetI, 
      unfold mem_Collect_eq, 
      elim exE conjE,
      intro vproductI; 
      simp only:
    )
    fix a b f show "\<D>\<^sub>\<circ> [a, b, f]\<^sub>\<circ> = ZFC_in_HOL.set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
      by (simp add: three nat_omega_simps)
  qed (force simp : nat_omega_simps)+
  then show "small ?abf_a'b'f'_gh" by (rule down)
qed

definition cat_comma_Arr :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cat_comma_Arr \<GG> \<HH> \<equiv>
    (
      \<Union>\<^sub>\<circ>abf\<in>\<^sub>\<circ>cat_comma_Obj \<GG> \<HH>. \<Union>\<^sub>\<circ>a'b'f'\<in>\<^sub>\<circ>cat_comma_Obj \<GG> \<HH>.
        cat_comma_Hom \<GG> \<HH> abf a'b'f'
    )"

definition cat_comma_composable :: "V \<Rightarrow> V \<Rightarrow> V"
  where "cat_comma_composable \<GG> \<HH> \<equiv> set
    {
      [[a'b'f', a''b''f'', g'h']\<^sub>\<circ>, [abf, a'b'f', gh]\<^sub>\<circ>]\<^sub>\<circ> |
        abf a'b'f' a''b''f'' g'h' gh.
          [a'b'f', a''b''f'', g'h']\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Arr \<GG> \<HH> \<and>
          [abf, a'b'f', gh]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Arr \<GG> \<HH>
    }"

lemma small_cat_comma_composable[simp]:
  shows "small
    {
      [[a'b'f', a''b''f'', g'h']\<^sub>\<circ>, [abf, a'b'f', gh]\<^sub>\<circ>]\<^sub>\<circ> |
        abf a'b'f' a''b''f'' g'h' gh.
          [a'b'f', a''b''f'', g'h']\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Arr \<GG> \<HH> \<and>
          [abf, a'b'f', gh]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Arr \<GG> \<HH>
    }"
  (is \<open>small ?S\<close>)
proof(rule down)
  show "?S \<subseteq> elts (cat_comma_Arr \<GG> \<HH> \<times>\<^sub>\<bullet> cat_comma_Arr \<GG> \<HH>)" by auto
qed

definition cat_comma :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_ \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F _)\<close> [1000, 1000] 999)
  where "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH> =
    [
      cat_comma_Obj \<GG> \<HH>,
      cat_comma_Arr \<GG> \<HH>,
      (\<lambda>F\<in>\<^sub>\<circ>cat_comma_Arr \<GG> \<HH>. F\<lparr>0\<rparr>),
      (\<lambda>F\<in>\<^sub>\<circ>cat_comma_Arr \<GG> \<HH>. F\<lparr>1\<^sub>\<nat>\<rparr>),
      (
        \<lambda>GF\<in>\<^sub>\<circ>cat_comma_composable \<GG> \<HH>.
          [
            GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>,
            GF\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>,
            [
              GF\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr> \<circ>\<^sub>A\<^bsub>\<GG>\<lparr>HomDom\<rparr>\<^esub> GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>,
              GF\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<HH>\<lparr>HomDom\<rparr>\<^esub> GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
            ]\<^sub>\<circ>
          ]\<^sub>\<circ>
      ),
      (
        \<lambda>abf\<in>\<^sub>\<circ>cat_comma_Obj \<GG> \<HH>.
          [abf, abf, [\<GG>\<lparr>HomDom\<rparr>\<lparr>CId\<rparr>\<lparr>abf\<lparr>0\<rparr>\<rparr>, \<HH>\<lparr>HomDom\<rparr>\<lparr>CId\<rparr>\<lparr>abf\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>
      )
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cat_comma_components:
  shows "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr> = cat_comma_Obj \<GG> \<HH>"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr> = cat_comma_Arr \<GG> \<HH>"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr> = (\<lambda>F\<in>\<^sub>\<circ>cat_comma_Arr \<GG> \<HH>. F\<lparr>0\<rparr>)"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr> = (\<lambda>F\<in>\<^sub>\<circ>cat_comma_Arr \<GG> \<HH>. F\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Comp\<rparr> =
      (
        \<lambda>GF\<in>\<^sub>\<circ>cat_comma_composable \<GG> \<HH>.
          [
            GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>,
            GF\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>,
            [
              GF\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr> \<circ>\<^sub>A\<^bsub>\<GG>\<lparr>HomDom\<rparr>\<^esub> GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>,
              GF\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<HH>\<lparr>HomDom\<rparr>\<^esub> GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
            ]\<^sub>\<circ>
          ]\<^sub>\<circ>
      )"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr> =
      (
        \<lambda>abf\<in>\<^sub>\<circ>cat_comma_Obj \<GG> \<HH>.
          [abf, abf, [\<GG>\<lparr>HomDom\<rparr>\<lparr>CId\<rparr>\<lparr>abf\<lparr>0\<rparr>\<rparr>, \<HH>\<lparr>HomDom\<rparr>\<lparr>CId\<rparr>\<lparr>abf\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>
      )"
  unfolding cat_comma_def dg_field_simps by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<AA> \<BB> \<CC> \<GG> \<HH>
  assumes \<GG>: "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<HH>: "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<GG>: is_functor \<alpha> \<AA> \<CC> \<GG> by (rule \<GG>)
interpretation \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule \<HH>)

lemma cat_comma_Obj_def':
  "cat_comma_Obj \<GG> \<HH> \<equiv> set
    {
      [a, b, f]\<^sub>\<circ> | a b f.
        a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr> \<and> b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr> \<and> f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>
    }"
  unfolding cat_comma_Obj_def cat_cs_simps by simp

lemma cat_comma_Hom_def':
  "cat_comma_Hom \<GG> \<HH> abf a'b'f' \<equiv> set
    {
      [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ> | g h.
        abf \<in>\<^sub>\<circ> cat_comma_Obj \<GG> \<HH> \<and>
        a'b'f' \<in>\<^sub>\<circ> cat_comma_Obj \<GG> \<HH> \<and>
        g : abf\<lparr>0\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> a'b'f'\<lparr>0\<rparr> \<and>
        h : abf\<lparr>1\<^sub>\<nat>\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> a'b'f'\<lparr>1\<^sub>\<nat>\<rparr> \<and>
        a'b'f'\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> abf\<lparr>2\<^sub>\<nat>\<rparr>
    }"
  unfolding cat_comma_Hom_def cat_cs_simps by simp

lemma cat_comma_components':
  shows "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr> = cat_comma_Obj \<GG> \<HH>"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr> = cat_comma_Arr \<GG> \<HH>"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr> = (\<lambda>F\<in>\<^sub>\<circ>cat_comma_Arr \<GG> \<HH>. F\<lparr>0\<rparr>)"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr> = (\<lambda>F\<in>\<^sub>\<circ>cat_comma_Arr \<GG> \<HH>. F\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Comp\<rparr> =
      (
        \<lambda>GF\<in>\<^sub>\<circ>cat_comma_composable \<GG> \<HH>.
          [
            GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>,
            GF\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>,
            [
              GF\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>,
              GF\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> GF\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>
            ]\<^sub>\<circ>
          ]\<^sub>\<circ>
      )"
    and "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr> =
      (\<lambda>abf\<in>\<^sub>\<circ>cat_comma_Obj \<GG> \<HH>. [abf, abf, [\<AA>\<lparr>CId\<rparr>\<lparr>abf\<lparr>0\<rparr>\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>abf\<lparr>1\<^sub>\<nat>\<rparr>\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>)"
  unfolding cat_comma_components cat_cs_simps by simp_all

end


subsubsection\<open>Objects\<close>

lemma cat_comma_ObjI[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "A = [a, b, f]\<^sub>\<circ>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  shows "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  using assms(4-6) 
  unfolding cat_comma_Obj_def'[OF assms(1,2)] assms(3) cat_comma_components 
  by simp

lemma cat_comma_ObjD[dest]:
  assumes "[a, b, f]\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  using assms
  unfolding 
    cat_comma_components'[OF assms(2,3)] cat_comma_Obj_def'[OF assms(2,3)] 
  by auto

lemma cat_comma_ObjE[elim]:
  assumes "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains a b f where "A = [a, b, f]\<^sub>\<circ>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
  using assms
  unfolding 
    cat_comma_components'[OF assms(2,3)] cat_comma_Obj_def'[OF assms(2,3)] 
  by auto


subsubsection\<open>Arrows\<close>

lemma cat_comma_HomI[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
    and "abf = [a, b, f]\<^sub>\<circ>"
    and "a'b'f' = [a', b', f']\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
    and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  shows "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
  using assms(1,2,6-10)
  unfolding cat_comma_Hom_def'[OF assms(1,2)] assms(3-5)
  by 
    (
      intro in_set_CollectI exI conjI small_cat_comma_Hom, 
      unfold cat_comma_components'(1,2)[OF assms(1,2), symmetric],
      (
        cs_concl 
          cs_simp: cat_comma_cs_simps 
          cs_intro: cat_cs_intros cat_comma_cs_intros
      )+
    )
    (clarsimp simp: nat_omega_simps)+

lemma cat_comma_HomE[elim]:
  assumes "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains a b f a' b' f' g h
    where "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and "abf = [a, b, f]\<^sub>\<circ>"
      and "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  using assms(1) 
  by 
    (
      unfold
        cat_comma_components'[OF assms(2,3)] cat_comma_Hom_def'[OF assms(2,3)],
      elim in_small_setE; 
      (unfold mem_Collect_eq, elim exE conjE cat_comma_ObjE[OF _ assms(2,3)])?,
      insert that,
      all\<open>
        (unfold cat_comma_components'(1,2)[OF assms(2,3), symmetric],
        elim cat_comma_ObjE[OF _ assms(2,3)]) | -
        \<close>
    )
    (auto simp: nat_omega_simps)

lemma cat_comma_HomD[dest]:
  assumes "[[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
    and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  using assms(1) by (force elim!: cat_comma_HomE[OF _ assms(2,3)])+

lemma cat_comma_ArrI[cat_comma_cs_intros]: 
  assumes "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
    and "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    and "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  shows "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  using assms 
  unfolding cat_comma_components cat_comma_Arr_def 
  by (intro vifunionI)

lemma cat_comma_ArrE[elim]:
  assumes "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  obtains abf a'b'f' 
    where "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
      and "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      and "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  using assms unfolding cat_comma_components cat_comma_Arr_def by auto

lemma cat_comma_ArrD[dest]: 
  assumes "[abf, a'b'f', gh]\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "[abf, a'b'f', gh]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
    and "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    and "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
proof-
  from assms obtain abf' a'b'f'' 
    where "[abf, a'b'f', gh]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf' a'b'f''"
      and "abf' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      and "a'b'f'' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    by (elim cat_comma_ArrE)
  moreover from cat_comma_HomE[OF this(1) assms(2,3)] have 
    "abf = abf'" and "a'b'f' = a'b'f''"
    by auto
  ultimately show "[abf, a'b'f', gh]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
    and "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    and "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    by auto
qed


subsubsection\<open>Domain\<close>

lemma cat_comma_Dom_vsv[cat_comma_cs_intros]: "vsv (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>)"
  unfolding cat_comma_components by simp

lemma cat_comma_Dom_vdomain[cat_comma_cs_simps]:
  "\<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>) = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  unfolding cat_comma_components by simp

lemma cat_comma_Dom_app[cat_comma_cs_simps]:
  assumes "F = [abf, a'b'f', gh]\<^sub>\<circ>" and "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  shows "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>\<lparr>F\<rparr> = abf"
  using assms(2) unfolding assms(1) cat_comma_components by simp

lemma cat_comma_Dom_vrange:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset)
  fix F assume "F \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>)"
  then have "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>" by (cs_prems cs_simp: cat_comma_cs_simps)
  then obtain abf a'b'f' 
    where F: "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
      and abf: "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      and a'b'f': "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    by auto
  from this(1) obtain a b f a' b' f' g h
    where "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and "abf = [a, b, f]\<^sub>\<circ>"
      and "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by (elim cat_comma_HomE[OF _ assms(1,2)])
  from F this abf a'b'f' show "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>\<lparr>F\<rparr> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_comma_cs_intros)
qed (auto intro: cat_comma_cs_intros)


subsubsection\<open>Codomain\<close>

lemma cat_comma_Cod_vsv[cat_comma_cs_intros]: "vsv (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>)"
  unfolding cat_comma_components by simp

lemma cat_comma_Cod_vdomain[cat_comma_cs_simps]:
  "\<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>) = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  unfolding cat_comma_components by simp

lemma cat_comma_Cod_app[cat_comma_cs_simps]:
  assumes "F = [abf, a'b'f', gh]\<^sub>\<circ>" and "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  shows "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>\<lparr>F\<rparr> = a'b'f'"
  using assms(2)
  unfolding assms(1) cat_comma_components
  by (simp add: nat_omega_simps)

lemma cat_comma_Cod_vrange:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset)
  fix F assume "F \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>)"
  then have "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>" by (cs_prems cs_simp: cat_comma_cs_simps)
  then obtain abf a'b'f' 
    where F: "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
      and abf: "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      and a'b'f': "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    by auto
  from this(1) obtain a b f a' b' f' g h
    where "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and "abf = [a, b, f]\<^sub>\<circ>"
      and "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by (elim cat_comma_HomE[OF _ assms(1,2)])
  from F this abf a'b'f' show "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>\<lparr>F\<rparr> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_comma_cs_intros)
qed (auto intro: cat_comma_cs_intros)


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma cat_comma_is_arrI[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "F = [abf, a'b'f', gh]\<^sub>\<circ>"
    and "abf = [a, b, f]\<^sub>\<circ>"
    and "a'b'f' = [a', b', f']\<^sub>\<circ>"
    and "gh = [g, h]\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
    and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
  shows "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
proof(intro is_arrI)
  interpret \<GG>: is_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))
  from assms(7-11) show "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
    unfolding assms(3-6)
    by 
      (
        cs_concl 
          cs_simp: cat_comma_cs_simps 
          cs_intro: cat_cs_intros cat_comma_cs_intros
      )
  with assms(7-11) show 
    "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>\<lparr>F\<rparr> = abf" "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>\<lparr>F\<rparr> = a'b'f'"
    unfolding assms(3-6) by (cs_concl cs_simp: cat_comma_cs_simps)+
qed

lemma cat_comma_is_arrD[dest]:
  assumes "[[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ> :
    [a, b, f]\<^sub>\<circ> \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> [a', b', f']\<^sub>\<circ>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
    and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  note F_is_arrD = is_arrD[OF assms(1)]
  note F_cat_comma_ArrD = cat_comma_ArrD[OF F_is_arrD(1) assms(2,3)]
  show "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
    and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
    and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
    and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by (intro cat_comma_HomD[OF F_cat_comma_ArrD(1) assms(2,3)])+    
qed

lemma cat_comma_is_arrE[elim]:
  assumes "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains a b f a' b' f' g h
    where "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and "abf = [a, b, f]\<^sub>\<circ>"
      and "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
proof-
  note F_is_arrD = is_arrD[OF assms(1)]
  from F_is_arrD(1) obtain abf a'b'f' 
    where "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
      and "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" 
      and "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    by auto
  from this(1) obtain a b f a' b' f' g h
    where F_def: "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and "abf = [a, b, f]\<^sub>\<circ>"
      and "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
     by (elim cat_comma_HomE[OF _ assms(2,3)])
  with that show ?thesis 
    by (metis F_is_arrD(1,2,3) cat_comma_Cod_app cat_comma_Dom_app)
qed


subsubsection\<open>Composition\<close>

lemma cat_comma_composableI:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "GF = [G, F]\<^sub>\<circ>"
    and "G : a'b'f' \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a''b''f''"
    and "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
  shows "GF \<in>\<^sub>\<circ> cat_comma_composable \<GG> \<HH>"
proof-
  from assms(1,2,5) obtain a b f a' b' f' gh 
    where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, gh]\<^sub>\<circ>"
      and "abf = [a, b, f]\<^sub>\<circ>"
      and  "a'b'f' = [a', b', f']\<^sub>\<circ>"
    by auto
  with assms(1,2,4) obtain a'' b'' f'' g'h' 
    where G_def: "G = [[a', b', f']\<^sub>\<circ>, [a'', b'', f'']\<^sub>\<circ>, g'h']\<^sub>\<circ>"
      and "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and "a''b''f'' = [a'', b'', f'']\<^sub>\<circ>"
    by auto
  from is_arrD(1)[OF assms(4)] have "G \<in>\<^sub>\<circ> cat_comma_Arr \<GG> \<HH>"
    unfolding cat_comma_components'(2)[OF assms(1,2)].
  moreover from is_arrD(1)[OF assms(5)] have "F \<in>\<^sub>\<circ> cat_comma_Arr \<GG> \<HH>"
    unfolding cat_comma_components'(2)[OF assms(1,2)].
  ultimately show ?thesis 
    unfolding assms(3) F_def G_def cat_comma_composable_def 
    by simp
qed

lemma cat_comma_composableE[elim]:
  assumes "GF \<in>\<^sub>\<circ> cat_comma_composable \<GG> \<HH>"
    and "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  obtains G F abf a'b'f' a''b''f'' 
    where "GF = [G, F]\<^sub>\<circ>"
      and "G : a'b'f' \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a''b''f''"
      and "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
proof-
  from assms(1) obtain abf a'b'f' a''b''f'' g'h' gh 
    where GF_def: "GF = [[a'b'f', a''b''f'', g'h']\<^sub>\<circ>, [abf, a'b'f', gh]\<^sub>\<circ>]\<^sub>\<circ>"
      and g'h': "[a'b'f', a''b''f'', g'h']\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
      and gh: "[abf, a'b'f', gh]\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
    unfolding cat_comma_composable_def
    by (auto simp: cat_comma_components'[OF assms(2,3)])  
  note g'h' = cat_comma_ArrD[OF g'h' assms(2,3)]
    and gh = cat_comma_ArrD[OF gh assms(2,3)]
  from gh(1) assms(2,3) obtain a b f a' b' f' g h
    where "[abf, a'b'f', gh]\<^sub>\<circ> = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and abf_def: "abf = [a, b, f]\<^sub>\<circ>"
      and a'b'f'_def: "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and gh_def: "gh = [g, h]\<^sub>\<circ>"
      and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and f: "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and f': "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and [cat_comma_cs_simps]: 
        "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by auto
  with g'h'(1) assms(2,3) obtain a'' b'' f'' g' h'
    where g'h'_def: "[a'b'f', a''b''f'', g'h']\<^sub>\<circ> = [a'b'f', a''b''f'', [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
      and a''b''f''_def: "a''b''f'' = [a'', b'', f'']\<^sub>\<circ>"
      and g'h'_def: "g'h' = [g', h']\<^sub>\<circ>"
      and g': "g' : a' \<mapsto>\<^bsub>\<AA>\<^esub> a''"
      and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
      and f'': "f'' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
      and [cat_comma_cs_simps]: 
        "f'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
    by auto  
  from gh_def have "gh = [g, h]\<^sub>\<circ>" by simp
  from assms(2,3) GF_def g h f f' g' h' f'' have 
    "[a'b'f', a''b''f'', g'h']\<^sub>\<circ> : a'b'f' \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a''b''f''"
    unfolding GF_def gh_def g'h'_def abf_def a'b'f'_def a''b''f''_def
    by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_comma_is_arrI)+
  moreover from assms(2,3) GF_def g h f f' g' h' f'' have 
    "[abf, a'b'f', gh]\<^sub>\<circ> : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
    unfolding GF_def gh_def g'h'_def abf_def a'b'f'_def a''b''f''_def
    by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_comma_is_arrI)+
  ultimately show ?thesis using that GF_def by auto
qed

lemma cat_comma_Comp_vsv[cat_comma_cs_intros]: "vsv (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Comp\<rparr>)"
  unfolding cat_comma_components by auto

lemma cat_comma_Comp_vdomain[cat_comma_cs_simps]: 
  "\<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Comp\<rparr>) = cat_comma_composable \<GG> \<HH>"
  unfolding cat_comma_components by auto

lemma cat_comma_Comp_app[cat_comma_cs_simps]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "G = [a'b'f', a''b''f'', [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
    and "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
    and "G : a'b'f' \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a''b''f''" 
    and "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
  shows "G \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> F = [abf, a''b''f'', [g' \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g, h' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> h]\<^sub>\<circ>]\<^sub>\<circ>"
  using assms(1,2,5,6)
  unfolding cat_comma_components'[OF assms(1,2)] assms(3,4)
  by (*slow*)
    (
      cs_concl
        cs_simp: omega_of_set V_cs_simps vfsequence_simps
        cs_intro: nat_omega_intros V_cs_intros cat_comma_composableI TrueI
    )

lemma cat_comma_Comp_is_arr[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "G : a'b'f' \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a''b''f''" 
    and "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
  shows "G \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a''b''f''"
proof-
  interpret \<GG>: is_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))
  from assms(1,2,4) obtain a b f a' b' f' g h
    where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and abf_def: "abf = [a, b, f]\<^sub>\<circ>"
      and a'b'f'_def: "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
      and f: "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      and f': "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and [symmetric, cat_cs_simps]: 
        "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
    by auto
  with assms(1,2,3) obtain a'' b'' f'' g' h'
    where G_def: "G = [[a', b', f']\<^sub>\<circ>, [a'', b'', f'']\<^sub>\<circ>, [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
      and a''b''f''_def: "a''b''f'' = [a'', b'', f'']\<^sub>\<circ>"
      and g': "g' : a' \<mapsto>\<^bsub>\<AA>\<^esub> a''"
      and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
      and f': "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and f'': "f'' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
      and [cat_cs_simps]: "f'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
    by auto (*slow*)
  from g' have \<GG>g': "\<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  note [cat_cs_simps] = 
    category.cat_assoc_helper[
      where \<CC>=\<CC> and h=f'' and g=\<open>\<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr>\<close> and q=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<close>
      ]
    category.cat_assoc_helper[
      where \<CC>=\<CC> and h=f and g=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<close> and q=\<open>f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<close>
      ]
  from assms(1,2,3,4) g h f f' g' h' f'' show ?thesis
    unfolding F_def G_def abf_def a'b'f'_def a''b''f''_def
    by (intro cat_comma_is_arrI[OF assms(1,2)])
      (
        cs_concl 
          cs_simp: cat_cs_simps cat_comma_cs_simps cs_intro: cat_cs_intros
      )+
qed


subsubsection\<open>Identity\<close>

lemma cat_comma_CId_vsv[cat_comma_cs_intros]: "vsv (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>)"
  unfolding cat_comma_components by simp

lemma cat_comma_CId_vdomain[cat_comma_cs_simps]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>) = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  unfolding cat_comma_components'[OF assms(1,2)] by simp

lemma cat_comma_CId_app[cat_comma_cs_simps]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "A = [a, b ,f]\<^sub>\<circ>"
    and "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  shows "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>\<lparr>A\<rparr> = [A, A, [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, \<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>"
proof-
  from assms(4)[unfolded assms(3), unfolded cat_comma_components'[OF assms(1,2)]]
  have "[a, b, f]\<^sub>\<circ> \<in>\<^sub>\<circ> cat_comma_Obj \<GG> \<HH>".
  then show ?thesis
    unfolding cat_comma_components'(6)[OF assms(1,2)] assms(3)
    by (simp add: nat_omega_simps)
qed


subsubsection\<open>\<open>Hom\<close>-set\<close>

lemma cat_comma_Hom:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "abf \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
    and "a'b'f' \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  shows "Hom (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>) abf a'b'f' = cat_comma_Hom \<GG> \<HH> abf a'b'f'"
proof(intro vsubset_antisym vsubsetI, unfold in_Hom_iff)
  fix F assume "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
  with assms(1,2) show "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
    by (elim cat_comma_is_arrE[OF _ assms(1,2)], intro cat_comma_HomI) force+
next
  fix F assume "F \<in>\<^sub>\<circ> cat_comma_Hom \<GG> \<HH> abf a'b'f'"
  with assms(1,2) show "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
    by (elim cat_comma_HomE[OF _ assms(1,2)], intro cat_comma_is_arrI) force+
qed


subsubsection\<open>Comma category is a category\<close>

lemma category_cat_comma[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "category \<alpha> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>)"
proof-

  interpret \<GG>: is_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<FF>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))

  show ?thesis
  proof(rule categoryI')

    show "vfsequence (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>)" unfolding cat_comma_def by auto
    show "vcard (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>) = 6\<^sub>\<nat>"
      unfolding cat_comma_def by (simp add: nat_omega_simps)
    show "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      by (rule cat_comma_Dom_vrange[OF assms])
    show "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      by (rule cat_comma_Cod_vrange[OF assms])
    show "(GF \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Comp\<rparr>)) \<longleftrightarrow>
      (\<exists>g f b c a. GF = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> b)"
      for GF
    proof(intro iffI; (elim exE conjE)?; (simp only: cat_comma_Comp_vdomain)?)
      assume prems: "GF \<in>\<^sub>\<circ> cat_comma_composable \<GG> \<HH>"
      with assms obtain G F abf a'b'f' a''b''f'' 
        where "GF = [G, F]\<^sub>\<circ>"
          and "G : a'b'f' \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a''b''f''"
          and "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
        by auto
      with assms show "\<exists>g f b c a.
        GF = [g, f]\<^sub>\<circ> \<and> g : b \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> c \<and> f : a \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> b"
        by auto
    qed (use assms in \<open>cs_concl cs_intro: cat_comma_composableI\<close>)
    from assms show "\<D>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>) = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_comma_cs_simps)
    from assms show "g \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> f : a \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> c"
      if "g : b \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> c" and "f : a \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> b"
      for b c g a f
      using that by (cs_concl cs_intro: cat_comma_cs_intros)
    from assms show 
      "H \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> G \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> F =
        H \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> (G \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> F)"
      if "H : C \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> D"
        and "G : B \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> C"
        and "F : A \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> B"
      for C D H B G A F
      using assms that
    proof-
      from that(3) assms obtain a b f a' b' f' g h
        where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [a, b, f]\<^sub>\<circ>"
          and B_def: "B = [a', b', f']\<^sub>\<circ>"
          and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
          and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f: "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and f': "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and [cat_cs_simps]: "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
        by auto
      with that(2) assms obtain a'' b'' f'' g' h'
        where G_def: "G = [[a', b', f']\<^sub>\<circ>, [a'', b'', f'']\<^sub>\<circ>, [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
          and C_def: "C = [a'', b'', f'']\<^sub>\<circ>"
          and g': "g' : a' \<mapsto>\<^bsub>\<AA>\<^esub> a''"
          and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
          and f'': "f'' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
          and [cat_cs_simps]: 
            "f'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
        by auto (*slow*)
      with that(1) assms obtain a''' b''' f''' g'' h''
        where H_def: "H = [[a'', b'', f'']\<^sub>\<circ>, [a''', b''', f''']\<^sub>\<circ>, [g'', h'']\<^sub>\<circ>]\<^sub>\<circ>"
          and D_def: "D = [a''', b''', f''']\<^sub>\<circ>"
          and g'': "g'' : a'' \<mapsto>\<^bsub>\<AA>\<^esub> a'''"
          and h'': "h'' : b'' \<mapsto>\<^bsub>\<BB>\<^esub> b'''"
          and f''': "f''' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'''\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'''\<rparr>"
          and [cat_cs_simps]: 
            "f''' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g''\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h''\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''"
        by auto (*slow*)      
      note [cat_cs_simps] = 
        category.cat_assoc_helper[
          where \<CC>=\<CC> 
            and h=f'' 
            and g=\<open>\<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr>\<close> 
            and q=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<close>
          ]
        category.cat_assoc_helper[
          where \<CC>=\<CC> 
            and h=f'' 
            and g=\<open>\<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr>\<close> 
            and q=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<close>
          ]
        category.cat_assoc_helper[
          where \<CC>=\<CC> 
            and h=f''' 
            and g=\<open>\<GG>\<lparr>ArrMap\<rparr>\<lparr>g''\<rparr>\<close> 
            and q=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h''\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f''\<close>
          ]
      from assms that g h f f' g' h' f'' g'' h''  f''' show ?thesis
        unfolding F_def G_def H_def A_def B_def C_def D_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps 
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed

    show "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>\<lparr>a\<rparr> : a \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a"
      if "a \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" for a
      using that
      by (elim cat_comma_ObjE[OF _ assms(1)]; (simp only:)?) 
        (
          cs_concl
            cs_simp: cat_cs_simps cat_comma_cs_simps 
            cs_intro: cat_cs_intros cat_comma_cs_intros
        )+

    show "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>\<lparr>b\<rparr> \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> f = f"
      if "f : a \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> b" for a b f
      using that 
      by (elim cat_comma_is_arrE[OF _ assms]; (simp only:)?)
        (
          cs_concl 
            cs_simp: cat_cs_simps cat_comma_cs_simps 
            cs_intro: cat_cs_intros cat_comma_cs_intros
        )+

    show "f \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>\<lparr>b\<rparr> = f"
      if "f : b \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> c" for b c f
      using that 
      by (elim cat_comma_is_arrE[OF _ assms]; (simp only:)?)
        (
          cs_concl
            cs_simp: cat_cs_simps cat_comma_cs_simps 
            cs_intro: cat_cs_intros cat_comma_cs_intros
        )+

    show "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    proof(intro vsubsetI, elim cat_comma_ObjE[OF _ assms])
      fix F a b f assume prems: 
        "F = [a, b, f]\<^sub>\<circ>" 
        "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
        "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
        "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
      from prems(2-4) show "F \<in>\<^sub>\<circ> Vset \<alpha>"
        unfolding prems(1) by (cs_concl cs_intro: cat_cs_intros V_cs_intros) 
    qed

    show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>) a b) \<in>\<^sub>\<circ> Vset \<alpha>"
      if "A \<subseteq>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
        and "B \<subseteq>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
        and "A \<in>\<^sub>\<circ> Vset \<alpha>"
        and "B \<in>\<^sub>\<circ> Vset \<alpha>"
      for A B
    proof-

      define A0 where "A0 = \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>A. F\<lparr>0\<rparr>)"
      define A1 where "A1 = \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>A. F\<lparr>1\<^sub>\<nat>\<rparr>)"
      define B0 where "B0 = \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>B. F\<lparr>0\<rparr>)"
      define B1 where "B1 = \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>B. F\<lparr>1\<^sub>\<nat>\<rparr>)"

      define A0B0 where "A0B0 = (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A0. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B0. Hom \<AA> a b)"
      define A1B1 where "A1B1 = (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A1. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B1. Hom \<BB> a b)"

      have A0B0: "A0B0 \<in>\<^sub>\<circ> Vset \<alpha>"
        unfolding A0B0_def
      proof(rule \<GG>.HomDom.cat_Hom_vifunion_in_Vset; (intro vsubsetI)?)
        show "A0 \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding A0_def
        proof(intro vrange_vprojection_in_VsetI that(3))
          fix F assume "F \<in>\<^sub>\<circ> A"
          with that(1) have "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" by auto
          with assms obtain a b f where F_def: "F = [a, b, f]\<^sub>\<circ>" by auto
          show "vsv F" unfolding F_def by auto
          show "0 \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> F" unfolding F_def by simp
        qed auto
        show "B0 \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding B0_def
        proof(intro vrange_vprojection_in_VsetI that(4))
          fix F assume "F \<in>\<^sub>\<circ> B"
          with that(2) have "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" by auto
          with assms obtain a b f where F_def: "F = [a, b, f]\<^sub>\<circ>" by auto
          show "vsv F" unfolding F_def by auto
          show "0 \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> F" unfolding F_def by simp
        qed auto
      next
        fix a assume "a \<in>\<^sub>\<circ> A0"
        with that(1) obtain F 
          where a_def: "a = F\<lparr>0\<rparr>" and "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" 
          unfolding A0_def by force
        with assms obtain b f where "F = [a, b, f]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by auto
        then show "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" unfolding a_def by simp
      next
        fix a assume "a \<in>\<^sub>\<circ> B0"
        with that(2) obtain F 
          where a_def: "a = F\<lparr>0\<rparr>" and "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" 
          unfolding B0_def by force
        with assms obtain b f where "F = [a, b, f]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" by auto
        then show "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" unfolding a_def by simp
      qed

      have A1B1: "A1B1 \<in>\<^sub>\<circ> Vset \<alpha>"
        unfolding A1B1_def
      proof(rule \<FF>.HomDom.cat_Hom_vifunion_in_Vset; (intro vsubsetI)?)
        show "A1 \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding A1_def
        proof(intro vrange_vprojection_in_VsetI that(3))
          fix F assume "F \<in>\<^sub>\<circ> A"
          with that(1) have "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" by auto
          with assms obtain a b f where F_def: "F = [a, b, f]\<^sub>\<circ>" by auto
          show "vsv F" unfolding F_def by auto
          show "1\<^sub>\<nat> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> F" unfolding F_def by (simp add: nat_omega_simps)
        qed auto
        show "B1 \<in>\<^sub>\<circ> Vset \<alpha>"
          unfolding B1_def
        proof(intro vrange_vprojection_in_VsetI that(4))
          fix F assume "F \<in>\<^sub>\<circ> B"
          with that(2) have "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" by auto
          with assms obtain a b f where F_def: "F = [a, b, f]\<^sub>\<circ>" by auto
          show "vsv F" unfolding F_def by auto
          show "1\<^sub>\<nat> \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> F" unfolding F_def by (simp add: nat_omega_simps)
        qed auto
      next
        fix b assume "b \<in>\<^sub>\<circ> A1"
        with that(1) obtain F 
          where b_def: "b = F\<lparr>1\<^sub>\<nat>\<rparr>" and "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" 
          unfolding A1_def by force
        with assms obtain a f where "F = [a, b, f]\<^sub>\<circ>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          by (auto simp: nat_omega_simps)
        then show "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" unfolding b_def by simp
      next
        fix b assume "b \<in>\<^sub>\<circ> B1"
        with that(2) obtain F 
          where b_def: "b = F\<lparr>1\<^sub>\<nat>\<rparr>" and "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" 
          unfolding B1_def by force
        with assms obtain a f where "F = [a, b, f]\<^sub>\<circ>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          by (auto simp: nat_omega_simps)
        then show "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" unfolding b_def by simp
      qed
      
      define Q where 
        "Q i = (if i = 0 then A else if i = 1\<^sub>\<nat> then B else (A0B0 \<times>\<^sub>\<bullet> A1B1))" 
        for i
      have 
        "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B.
          Hom (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>) a b) \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
      proof
        (
          intro vsubsetI,
          elim vifunionE,
          unfold in_Hom_iff,
          intro vproductI ballI
        )
        fix abf a'b'f' F assume prems: 
          "abf \<in>\<^sub>\<circ> A" "a'b'f' \<in>\<^sub>\<circ> B" "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
        from prems(3) assms obtain a b f a' b' f' g h
          where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
            and abf_def: "abf = [a, b, f]\<^sub>\<circ>"
            and a'b'f'_def: "a'b'f' = [a', b', f']\<^sub>\<circ>"
            and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
            and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
            and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
            and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
            and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
          by auto
        have gh: "[g, h]\<^sub>\<circ> \<in>\<^sub>\<circ> A0B0 \<times>\<^sub>\<bullet> A1B1"
          unfolding A0B0_def A1B1_def 
        proof
          (
            intro ftimesI2 vifunionI, 
            unfold in_Hom_iff A0_def B0_def A1_def B1_def
          )
          from prems(1) show "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>A. F\<lparr>0\<rparr>)"
            by (intro vsv.vsv_vimageI2'[where a=abf]) (simp_all add: abf_def)
          from prems(2) show "a' \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>B. F\<lparr>0\<rparr>)"
            by (intro vsv.vsv_vimageI2'[where a=a'b'f']) 
              (simp_all add: a'b'f'_def)
          from prems(1) show "b \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>A. F\<lparr>1\<^sub>\<nat>\<rparr>)"
            by (intro vsv.vsv_vimageI2'[where a=abf]) 
              (simp_all add: nat_omega_simps abf_def)
          from prems(2) show "b' \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<lambda>F\<in>\<^sub>\<circ>B. F\<lparr>1\<^sub>\<nat>\<rparr>)"
            by (intro vsv.vsv_vimageI2'[where a=a'b'f']) 
              (simp_all add: nat_omega_simps a'b'f'_def)
        qed (intro g h)+
        show "vsv F" unfolding F_def by auto
        show "\<D>\<^sub>\<circ> F = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
          by (simp add: F_def three nat_omega_simps)
        fix i assume "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
        then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> by auto
        from this prems show "F\<lparr>i\<rparr> \<in>\<^sub>\<circ> Q i" 
          by cases
            (simp_all add: F_def Q_def gh abf_def a'b'f'_def nat_omega_simps)
      qed
      moreover have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i) \<in>\<^sub>\<circ> Vset \<alpha>"
      proof(rule Limit_vproduct_in_VsetI)
        show "set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>} \<in>\<^sub>\<circ> Vset \<alpha>" by (cs_concl cs_intro: V_cs_intros)
        from A0B0 A1B1 assms(1,2) that(3,4) show 
          "Q i \<in>\<^sub>\<circ> Vset \<alpha>" if "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" 
          for i 
          by (simp_all add: Q_def Limit_ftimes_in_VsetI nat_omega_simps)
      qed auto
      ultimately show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>) a b) \<in>\<^sub>\<circ> Vset \<alpha>" by auto
    qed
  qed (auto simp: cat_comma_cs_simps intro: cat_comma_cs_intros)

qed


subsubsection\<open>Tiny comma category\<close>

lemma tiny_category_cat_comma[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "tiny_category \<alpha> (\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>)"
proof-

  interpret \<GG>: is_tm_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<HH>: is_tm_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))
  note \<GG> = \<GG>.is_functor_axioms 
    and \<HH> = \<HH>.is_functor_axioms
  interpret category \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close>
    by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)

  show ?thesis
  proof(intro tiny_categoryI' category_cat_comma)
    have vrange_\<GG>: "\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (simp add: vrange_in_VsetI \<GG>.tm_cf_ObjMap_in_Vset)
    moreover have vrange_\<HH>: "\<R>\<^sub>\<circ> (\<HH>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
      by (simp add: vrange_in_VsetI \<HH>.tm_cf_ObjMap_in_Vset)
    ultimately have UU_Hom_in_Vset:
      "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>). \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<HH>\<lparr>ObjMap\<rparr>). Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
      using \<GG>.cf_ObjMap_vrange \<HH>.cf_ObjMap_vrange 
      by (auto intro: \<GG>.HomCod.cat_Hom_vifunion_in_Vset) 
    define Q where
      "Q i =
        (
          if i = 0
          then \<AA>\<lparr>Obj\<rparr>
          else
            if i = 1\<^sub>\<nat>
            then \<BB>\<lparr>Obj\<rparr>
            else (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>). \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<HH>\<lparr>ObjMap\<rparr>). Hom \<CC> a b)
        )" 
      for i
    have "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    proof(intro vsubsetI)
      fix A assume "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
      then obtain a b f
        where A_def: "A = [a, b, f]\<^sub>\<circ>"
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
          and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
          and f: "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by (elim cat_comma_ObjE[OF _ \<GG> \<HH>])
      from f have f:
        "f \<in>\<^sub>\<circ> (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<GG>\<lparr>ObjMap\<rparr>). \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>\<R>\<^sub>\<circ> (\<HH>\<lparr>ObjMap\<rparr>). Hom \<CC> a b)"
        by (intro vifunionI, unfold in_Hom_iff)
          (
            simp_all add: 
              a b 
              \<HH>.ObjMap.vsv_vimageI2 
              \<HH>.cf_ObjMap_vdomain 
              \<GG>.ObjMap.vsv_vimageI2 
              \<GG>.cf_ObjMap_vdomain
          )
      show "A \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
      proof(intro vproductI, unfold Ball_def; (intro allI impI)?)
        show "\<D>\<^sub>\<circ> A = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
          unfolding A_def by (simp add: three nat_omega_simps)
        fix i assume "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
        then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> by auto
        from this a b f show "A\<lparr>i\<rparr> \<in>\<^sub>\<circ> Q i"
          unfolding A_def Q_def by cases (simp_all add: nat_omega_simps)
      qed (auto simp: A_def)
    qed
    moreover have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule Limit_vproduct_in_VsetI)
      show "set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>} \<in>\<^sub>\<circ> Vset \<alpha>"
        unfolding three[symmetric] by simp
      from this show "Q i \<in>\<^sub>\<circ> Vset \<alpha>" if "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" for i
        using that assms(1,2) UU_Hom_in_Vset  
        by 
          (
            simp_all add:
              Q_def 
              \<GG>.HomDom.tiny_cat_Obj_in_Vset 
              \<HH>.HomDom.tiny_cat_Obj_in_Vset 
              nat_omega_simps
          )
    qed auto
    ultimately show [simp]: "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by auto 
    define Q where
      "Q i =
        (
          if i = 0
          then \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>
          else
            if i = 1\<^sub>\<nat>
            then \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>
            else \<AA>\<lparr>Arr\<rparr> \<times>\<^sub>\<bullet> \<BB>\<lparr>Arr\<rparr>
        )" 
    for i
    have "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
    proof(intro vsubsetI)
      fix F assume "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
      then obtain abf a'b'f' where F: "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'"
        by (auto intro: is_arrI)
      with assms obtain a b f a' b' f' g h
        where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and abf_def: "abf = [a, b, f]\<^sub>\<circ>"
          and a'b'f'_def: "a'b'f' = [a', b', f']\<^sub>\<circ>"
          and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
          and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
        by auto
      from g h have "[g, h]\<^sub>\<circ> \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr> \<times>\<^sub>\<bullet> \<BB>\<lparr>Arr\<rparr>" by auto      
      show "F \<in>\<^sub>\<circ> (\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i)"
      proof(intro vproductI, unfold Ball_def; (intro allI impI)?)
        show "\<D>\<^sub>\<circ> F = set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
          by (simp add: F_def three nat_omega_simps)
        fix i assume "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}"
        then consider \<open>i = 0\<close> | \<open>i = 1\<^sub>\<nat>\<close> | \<open>i = 2\<^sub>\<nat>\<close> by auto
        from this F g h show "F\<lparr>i\<rparr> \<in>\<^sub>\<circ> Q i"
          unfolding Q_def F_def abf_def[symmetric] a'b'f'_def[symmetric]
          by cases (auto simp: nat_omega_simps)
      qed (auto simp: F_def)
    qed
    moreover have "(\<Prod>\<^sub>\<circ>i\<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}. Q i) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof(rule Limit_vproduct_in_VsetI)
      show "set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>} \<in>\<^sub>\<circ> Vset \<alpha>"
        by (simp add: three[symmetric] nat_omega_simps)
      moreover have "\<AA>\<lparr>Arr\<rparr> \<times>\<^sub>\<bullet> \<BB>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
        by 
          (
            auto intro!: 
              Limit_ftimes_in_VsetI 
              \<GG>.\<Z>_\<beta> \<Z>_def 
              \<GG>.HomDom.tiny_cat_Arr_in_Vset 
              \<HH>.HomDom.tiny_cat_Arr_in_Vset
          )
      ultimately show "Q i \<in>\<^sub>\<circ> Vset \<alpha>" if "i \<in>\<^sub>\<circ> set {0, 1\<^sub>\<nat>, 2\<^sub>\<nat>}" for i
        using that assms(1,2) UU_Hom_in_Vset  
        by 
          (
            simp_all add:
              Q_def
              \<GG>.HomDom.tiny_cat_Obj_in_Vset 
              \<HH>.HomDom.tiny_cat_Obj_in_Vset 
              nat_omega_simps
          )
    qed auto
    ultimately show "\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  qed (rule \<GG>, rule \<HH>)

qed



subsection\<open>Projections for a comma category\<close>


subsubsection\<open>Definitions and elementary properties\<close>


text\<open>See Chapter II-6 in \cite{mac_lane_categories_2010}.\<close>

definition cf_comma_proj_left :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_ \<^sub>C\<^sub>F\<Sqinter> _)\<close> [1000, 1000] 999)
  where "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>. a\<lparr>0\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>. f\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>),
      \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>,
      \<GG>\<lparr>HomDom\<rparr>
    ]\<^sub>\<circ>"

definition cf_comma_proj_right :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_ \<Sqinter>\<^sub>C\<^sub>F _)\<close> [1000, 1000] 999)
  where "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH> =
    [
      (\<lambda>a\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>. a\<lparr>1\<^sub>\<nat>\<rparr>),
      (\<lambda>f\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>. f\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>),
      \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>,
      \<HH>\<lparr>HomDom\<rparr>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_comma_proj_left_components:
  shows "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>. a\<lparr>0\<rparr>)"
    and "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>. f\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>0\<rparr>)"
    and "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>HomDom\<rparr> = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>"
    and "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>HomCod\<rparr> = \<GG>\<lparr>HomDom\<rparr>"
  unfolding cf_comma_proj_left_def dghm_field_simps
  by (simp_all add: nat_omega_simps)

lemma cf_comma_proj_right_components:
  shows "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr> = (\<lambda>a\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>. a\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr> = (\<lambda>f\<in>\<^sub>\<circ>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>. f\<lparr>2\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>)"
    and "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>HomDom\<rparr> = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>"
    and "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>HomCod\<rparr> = \<HH>\<lparr>HomDom\<rparr>"
  unfolding cf_comma_proj_right_def dghm_field_simps
  by (simp_all add: nat_omega_simps)

context
  fixes \<alpha> \<AA> \<BB> \<CC> \<GG> \<HH>
  assumes \<GG>: "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and \<HH>: "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
begin

interpretation \<GG>: is_functor \<alpha> \<AA> \<CC> \<GG> by (rule \<GG>)
interpretation \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule \<HH>)

lemmas cf_comma_proj_left_components' = 
  cf_comma_proj_left_components[of \<GG> \<HH>, unfolded \<GG>.cf_HomDom]

lemmas cf_comma_proj_right_components' = 
  cf_comma_proj_right_components[of \<GG> \<HH>, unfolded \<HH>.cf_HomDom]

lemmas [cat_comma_cs_simps] = 
  cf_comma_proj_left_components'(3,4)
  cf_comma_proj_right_components'(3,4)

end


subsubsection\<open>Object map\<close>

mk_VLambda cf_comma_proj_left_components(1)
  |vsv cf_comma_proj_left_ObjMap_vsv[cat_comma_cs_intros]|
  |vdomain cf_comma_proj_left_ObjMap_vdomain[cat_comma_cs_simps]|

mk_VLambda cf_comma_proj_right_components(1)
  |vsv cf_comma_proj_right_ObjMap_vsv[cat_comma_cs_intros]|
  |vdomain cf_comma_proj_right_ObjMap_vdomain[cat_comma_cs_simps]|

lemma cf_comma_proj_left_ObjMap_app[cat_comma_cs_simps]:
  assumes "A = [a, b, f]\<^sub>\<circ>" and "[a, b, f]\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  shows "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = a"
  using assms(2) unfolding assms(1) cf_comma_proj_left_components by simp

lemma cf_comma_proj_right_ObjMap_app[cat_comma_cs_simps]:
  assumes "A = [a, b, f]\<^sub>\<circ>" and "[a, b, f]\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  shows "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = b"
  using assms(2)
  unfolding assms(1) cf_comma_proj_right_components 
  by (simp add: nat_omega_simps)

lemma cf_comma_proj_left_ObjMap_vrange:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cat_comma_cs_simps)
  fix A assume prems: "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  with assms obtain a b f where A_def: "A = [a, b, f]\<^sub>\<circ>" and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    by auto
  from assms prems a show "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    unfolding A_def by (cs_concl cs_simp: cat_comma_cs_simps)
qed (auto intro: cat_comma_cs_intros)  

lemma cf_comma_proj_right_ObjMap_vrange:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cat_comma_cs_simps)
  fix A assume prems: "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>"
  with assms obtain a b f where A_def: "A = [a, b, f]\<^sub>\<circ>" and b: "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    by auto
  from assms prems b show "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    unfolding A_def by (cs_concl cs_simp: cat_comma_cs_simps)
qed (auto intro: cat_comma_cs_intros)  


subsubsection\<open>Arrow map\<close>

mk_VLambda cf_comma_proj_left_components(2)
  |vsv cf_comma_proj_left_ArrMap_vsv[cat_comma_cs_intros]|
  |vdomain cf_comma_proj_left_ArrMap_vdomain[cat_comma_cs_simps]|

mk_VLambda cf_comma_proj_right_components(2)
  |vsv cf_comma_proj_right_ArrMap_vsv[cat_comma_cs_intros]|
  |vdomain cf_comma_proj_right_ArrMap_vdomain[cat_comma_cs_simps]|

lemma cf_comma_proj_left_ArrMap_app[cat_comma_cs_simps]:
  assumes "A = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>" 
    and "[abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  shows "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>A\<rparr> = g"
  using assms(2)
  unfolding assms(1) cf_comma_proj_left_components 
  by (simp add: nat_omega_simps)

lemma cf_comma_proj_right_ArrMap_app[cat_comma_cs_simps]:
  assumes "A = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>" 
    and "[abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  shows "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>A\<rparr> = h"
  using assms(2)
  unfolding assms(1) cf_comma_proj_right_components 
  by (simp add: nat_omega_simps)

lemma cf_comma_proj_left_ArrMap_vrange:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cat_comma_cs_simps)
  from assms interpret category \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  fix F assume prems: "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  then obtain abf a'b'f' where "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'" by auto
  with assms obtain a b f a' b' f' g h
    where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    by auto
  from assms prems g show "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<in>\<^sub>\<circ> \<AA>\<lparr>Arr\<rparr>"
    unfolding F_def 
    by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_cs_intros)
qed (auto intro: cat_comma_cs_intros)  

lemma cf_comma_proj_right_ArrMap_vrange:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<R>\<^sub>\<circ> (\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
proof(rule vsv.vsv_vrange_vsubset, unfold cat_comma_cs_simps)
  from assms interpret category \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  fix F assume prems: "F \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Arr\<rparr>"
  then obtain abf a'b'f' where F: "F : abf \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> a'b'f'" by auto
  with assms obtain a b f a' b' f' g h
    where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
    by auto
  from assms prems h show "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> \<in>\<^sub>\<circ> \<BB>\<lparr>Arr\<rparr>"
    unfolding F_def 
    by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_cs_intros)
qed (auto intro: cat_comma_cs_intros)  


subsubsection\<open>Projections for a comma category are functors\<close>

lemma cf_comma_proj_left_is_functor:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH> : \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  interpret \<GG>: is_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))
  from assms interpret \<GG>\<HH>: category \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  show ?thesis
  proof(rule is_functorI')
    show "vfsequence (\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>)"
      unfolding cf_comma_proj_left_def by auto
    show "vcard (\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>) = 4\<^sub>\<nat>"
      unfolding cf_comma_proj_left_def by (simp add: nat_omega_simps)
    from assms show "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      by (rule cf_comma_proj_left_ObjMap_vrange)
    show "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> : \<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "F : A \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> B" for A B F
    proof-
      from assms that obtain a b f a' b' f' g h
        where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [a, b, f]\<^sub>\<circ>"
          and B_def: "B = [a', b', f']\<^sub>\<circ>"
          and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
        by auto
      from that g show 
        "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> : \<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>\<AA>\<^esub> \<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
        unfolding F_def A_def B_def
        by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_cs_intros)
    qed
    show 
      "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>G \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> F\<rparr> =
        \<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>G\<rparr> \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> \<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
      if "G : B \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> C" and "F : A \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> B" for B C G A F
    proof-
      from assms that(2) obtain a b f a' b' f' g h
        where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [a, b, f]\<^sub>\<circ>"
          and B_def: "B = [a', b', f']\<^sub>\<circ>"
          and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
          and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f: "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and f': "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and [cat_cs_simps]: "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
        by auto
      with that(1) assms obtain a'' b'' f'' g' h'
        where G_def: "G = [[a', b', f']\<^sub>\<circ>, [a'', b'', f'']\<^sub>\<circ>, [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
          and C_def: "C = [a'', b'', f'']\<^sub>\<circ>"
          and g': "g' : a' \<mapsto>\<^bsub>\<AA>\<^esub> a''"
          and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
          and f'': "f'' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
          and [cat_cs_simps]: "f'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
        by auto (*slow*)
      note [cat_cs_simps] = 
        category.cat_assoc_helper
          [
            where \<CC>=\<CC> 
              and h=f'' 
              and g=\<open>\<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr>\<close> 
              and q=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<close>
          ]
        category.cat_assoc_helper
          [
            where \<CC>=\<CC> 
              and h=f 
              and g=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<close> 
              and q=\<open>f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<close>
          ]
      from assms that g g' h h' f f' f'' show ?thesis
        unfolding F_def G_def A_def B_def C_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps
              cs_intro: cat_comma_cs_intros cat_cs_intros
          )
    qed
    show "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>\<lparr>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>\<lparr>A\<rparr>\<rparr> = \<AA>\<lparr>CId\<rparr>\<lparr>\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>\<rparr>"
      if "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" for A
    proof-
      from assms that obtain a b f 
        where A_def: "A = [a, b, f]\<^sub>\<circ>"
          and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by auto
      from assms that this(2-4) show ?thesis
        unfolding A_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps 
              cs_intro: cat_comma_cs_intros cat_cs_intros
          )
    qed
  qed 
    (
      use assms in 
        \<open>
          cs_concl
            cs_simp: cat_comma_cs_simps
            cs_intro: cat_cs_intros cat_comma_cs_intros
        \<close>
    )+
qed

lemma cf_comma_proj_left_is_functor'[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<AA>' = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>"
  shows "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1,2) unfolding assms(3) by (rule cf_comma_proj_left_is_functor)

lemma cf_comma_proj_right_is_functor:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH> : \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
proof-
  interpret \<GG>: is_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<HH>: is_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))
  from assms interpret \<GG>\<HH>: category \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close>
    by (cs_concl cs_intro: cat_comma_cs_intros)
  show ?thesis
  proof(rule is_functorI')
    show "vfsequence (\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>)"
      unfolding cf_comma_proj_right_def by auto
    show "vcard (\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>) = 4\<^sub>\<nat>"
      unfolding cf_comma_proj_right_def by (simp add: nat_omega_simps)
    from assms show "\<R>\<^sub>\<circ> (\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
      by (rule cf_comma_proj_right_ObjMap_vrange)
    show "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> : \<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "F : A \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> B" for A B F
    proof-
      from assms that obtain a b f a' b' f' g h
        where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [a, b, f]\<^sub>\<circ>"
          and B_def: "B = [a', b', f']\<^sub>\<circ>"
          and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
        by auto
      from that h show 
        "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> : \<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
        unfolding F_def A_def B_def
        by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_cs_intros)
    qed
    show 
      "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>G \<circ>\<^sub>A\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> F\<rparr> =
        \<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>G\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
      if "G : B \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> C" and "F : A \<mapsto>\<^bsub>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<^esub> B" for B C G A F
    proof-
      from assms that(2) obtain a b f a' b' f' g h
        where F_def: "F = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [a, b, f]\<^sub>\<circ>"
          and B_def: "B = [a', b', f']\<^sub>\<circ>"
          and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
          and h: "h : b \<mapsto>\<^bsub>\<BB>\<^esub> b'"
          and f: "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and f': "f' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and [cat_cs_simps]: "f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f"
        by auto
      with that(1) assms obtain a'' b'' f'' g' h'
        where G_def: "G = [[a', b', f']\<^sub>\<circ>, [a'', b'', f'']\<^sub>\<circ>, [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
          and C_def: "C = [a'', b'', f'']\<^sub>\<circ>"
          and g': "g' : a' \<mapsto>\<^bsub>\<AA>\<^esub> a''"
          and h': "h' : b' \<mapsto>\<^bsub>\<BB>\<^esub> b''"
          and f'': "f'' : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a''\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
          and [cat_cs_simps]: "f'' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr> = \<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'"
        by auto (*slow*)
      note [cat_cs_simps] = 
        category.cat_assoc_helper
          [
            where \<CC>=\<CC> 
              and h=f'' 
              and g=\<open>\<GG>\<lparr>ArrMap\<rparr>\<lparr>g'\<rparr>\<close> 
              and q=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h'\<rparr> \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> f'\<close>
          ]
        category.cat_assoc_helper
          [
            where \<CC>=\<CC> 
              and h=f 
              and g=\<open>\<HH>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr>\<close> 
              and q=\<open>f' \<circ>\<^sub>A\<^bsub>\<CC>\<^esub> \<GG>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr>\<close>
          ]
      from assms that g g' h h' f f' f'' show ?thesis
        unfolding F_def G_def A_def B_def C_def
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps 
              cs_intro: cat_comma_cs_intros cat_cs_intros
          )
    qed
    show "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>\<lparr>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>CId\<rparr>\<lparr>A\<rparr>\<rparr> = \<BB>\<lparr>CId\<rparr>\<lparr>\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>\<rparr>"
      if "A \<in>\<^sub>\<circ> \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<lparr>Obj\<rparr>" for A
    proof-
      from assms that obtain a b f 
        where A_def: "A = [a, b, f]\<^sub>\<circ>"
          and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
          and "f : \<GG>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<CC>\<^esub> \<HH>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
        by auto
      from assms that this(2-4) show ?thesis
        unfolding A_def
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps
              cs_intro: cat_comma_cs_intros cat_cs_intros
          )
    qed
  qed 
    (
      use assms in
        \<open>
          cs_concl
            cs_simp: cat_comma_cs_simps
            cs_intro: cat_cs_intros cat_comma_cs_intros
        \<close>
    )+
qed

lemma cf_comma_proj_right_is_functor'[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<AA>' = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>"
  shows "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1,2) unfolding assms(3) by (rule cf_comma_proj_right_is_functor)


subsubsection\<open>Projections for a tiny comma category\<close>

lemma cf_comma_proj_left_is_tm_functor:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH> : \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
proof(intro is_tm_functorI')

  interpret \<GG>: is_tm_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<HH>: is_tm_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))

  show \<Pi>_\<GG>\<HH>: "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH> : \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
    by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)

  interpret \<Pi>_\<GG>\<HH>: is_functor \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close> \<AA> \<open>\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<close>
    by (rule \<Pi>_\<GG>\<HH>)
  interpret \<GG>\<HH>: tiny_category \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close> 
    by (cs_concl cs_intro: cat_small_cs_intros cat_comma_cs_intros)

  show "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    show "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof-
      note \<Pi>_\<GG>\<HH>.cf_ObjMap_vrange
      moreover have "\<AA>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (intro cat_small_cs_intros)
      ultimately show ?thesis by auto
    qed
  qed (auto simp: cf_comma_proj_left_components intro: cat_small_cs_intros)

  show "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    show "\<R>\<^sub>\<circ> (\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof-
      note \<Pi>_\<GG>\<HH>.cf_ArrMap_vrange
      moreover have "\<AA>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (intro cat_small_cs_intros)
      ultimately show ?thesis by auto
    qed
  qed (auto simp: cf_comma_proj_left_components intro: cat_small_cs_intros)

qed

lemma cf_comma_proj_left_is_tm_functor'[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG>\<HH> = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>"
  shows "\<GG> \<^sub>C\<^sub>F\<Sqinter> \<HH> : \<GG>\<HH> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1,2) unfolding assms(3) by (rule cf_comma_proj_left_is_tm_functor)

lemma cf_comma_proj_right_is_tm_functor:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
  shows "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH> : \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
proof(intro is_tm_functorI')

  interpret \<GG>: is_tm_functor \<alpha> \<AA> \<CC> \<GG> by (rule assms(1))
  interpret \<HH>: is_tm_functor \<alpha> \<BB> \<CC> \<HH> by (rule assms(2))

  show \<Pi>_\<GG>\<HH>: "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH> : \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)

  interpret \<Pi>_\<GG>\<HH>: is_functor \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close> \<BB> \<open>\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<close>
    by (rule \<Pi>_\<GG>\<HH>)
  interpret \<GG>\<HH>: tiny_category \<alpha> \<open>\<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>\<close> 
    by (cs_concl cs_intro: cat_small_cs_intros cat_comma_cs_intros)

  show "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    show "\<R>\<^sub>\<circ> (\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ObjMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof-
      note \<Pi>_\<GG>\<HH>.cf_ObjMap_vrange
      moreover have "\<BB>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (intro cat_small_cs_intros)
      ultimately show ?thesis by auto
    qed
  qed (auto simp: cf_comma_proj_right_components intro: cat_small_cs_intros)

  show "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>"
  proof(rule vbrelation.vbrelation_Limit_in_VsetI)
    show "\<R>\<^sub>\<circ> (\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH>\<lparr>ArrMap\<rparr>) \<in>\<^sub>\<circ> Vset \<alpha>"
    proof-
      note \<Pi>_\<GG>\<HH>.cf_ArrMap_vrange
      moreover have "\<BB>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<alpha>" by (intro cat_small_cs_intros)
      ultimately show ?thesis by auto
    qed
  qed (auto simp: cf_comma_proj_right_components intro: cat_small_cs_intros)

qed

lemma cf_comma_proj_right_is_tm_functor'[cat_comma_cs_intros]:
  assumes "\<GG> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>" 
    and "\<HH> : \<BB> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<CC>"
    and "\<GG>\<HH> = \<GG> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<HH>"
  shows "\<GG> \<Sqinter>\<^sub>C\<^sub>F \<HH> : \<GG>\<HH> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
  using assms(1,2) unfolding assms(3) by (rule cf_comma_proj_right_is_tm_functor)



subsection\<open>Comma categories constructed from a functor and an object\<close>


subsubsection\<open>Definitions and elementary properties\<close>


text\<open>See Chapter II-6 in \cite{mac_lane_categories_2010}.\<close>

definition cat_cf_obj_comma :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_ \<^sub>C\<^sub>F\<down> _)\<close> [1000, 1000] 999)
  where "\<FF> \<^sub>C\<^sub>F\<down> b \<equiv> \<FF> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F (cf_const (cat_1 0 0) (\<FF>\<lparr>HomCod\<rparr>) b)"

definition cat_obj_cf_comma :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_ \<down>\<^sub>C\<^sub>F _)\<close> [1000, 1000] 999)
  where "b \<down>\<^sub>C\<^sub>F \<FF> \<equiv> (cf_const (cat_1 0 0) (\<FF>\<lparr>HomCod\<rparr>) b) \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<FF>"


text\<open>Alternative forms of the definitions.\<close>

lemma (in is_functor) cat_cf_obj_comma_def:
  "\<FF> \<^sub>C\<^sub>F\<down> b = \<FF> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F (cf_const (cat_1 0 0) \<BB> b)" 
  unfolding cat_cf_obj_comma_def cf_HomCod ..

lemma (in is_functor) cat_obj_cf_comma_def:
  "b \<down>\<^sub>C\<^sub>F \<FF> = (cf_const (cat_1 0 0) \<BB> b) \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<FF>" 
  unfolding cat_obj_cf_comma_def cf_HomCod ..


subsubsection\<open>Objects\<close>

lemma (in is_functor) cat_cf_obj_comma_ObjI[cat_comma_cs_intros]:
  assumes "A = [a, 0, f]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "A \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
  using assms(2,3)
  unfolding assms(1)
  by
    (
      cs_concl 
        cs_simp: cat_cs_simps cat_cf_obj_comma_def 
        cs_intro: cat_cs_intros vempty_is_zet cat_comma_ObjI
    )

lemmas [cat_comma_cs_intros] = is_functor.cat_cf_obj_comma_ObjI

lemma (in is_functor) cat_obj_cf_comma_ObjI[cat_comma_cs_intros]:
  assumes "A = [0, a, f]\<^sub>\<circ>" and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
  shows "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
  using assms(2,3)
  unfolding assms(1)
  by
    (
      cs_concl 
        cs_simp: cat_cs_simps cat_obj_cf_comma_def 
        cs_intro: vempty_is_zet cat_cs_intros cat_comma_ObjI
    )

lemmas [cat_comma_cs_intros] = is_functor.cat_obj_cf_comma_ObjI

lemma (in is_functor) cat_cf_obj_comma_ObjD[dest]:
  assumes "[a, b', f]\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "b' = 0" 
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
proof-
  from assms(2) have "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  note obj = cat_comma_ObjD[
      OF assms(1)[unfolded cat_cf_obj_comma_def] is_functor_axioms this
      ]
  from obj[unfolded cat_1_components] have [cat_cs_simps]: "b' = 0" by simp
  moreover have "cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr> = b"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  ultimately show "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b' = 0" "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    using obj by auto
qed

lemmas [dest] = is_functor.cat_cf_obj_comma_ObjD[rotated 1]

lemma (in is_functor) cat_obj_cf_comma_ObjD[dest]:
  assumes "[b', a, f]\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "b' = 0" 
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
proof-
  from assms(2) have "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  note obj = cat_comma_ObjD[
      OF assms(1)[unfolded cat_obj_cf_comma_def] this is_functor_axioms
      ]
  from obj[unfolded cat_1_components] have [cat_cs_simps]: "b' = 0" by simp
  moreover have "cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr> = b"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  ultimately show "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" "b' = 0" "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    using obj by auto
qed

lemmas [dest] = is_functor.cat_obj_cf_comma_ObjD[rotated 1]

lemma (in is_functor) cat_cf_obj_comma_ObjE[elim]:
  assumes "A \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  obtains a f where "A = [a, 0, f]\<^sub>\<circ>" 
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
proof-
  from assms(2) have "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from assms(1)[unfolded cat_cf_obj_comma_def] is_functor_axioms this 
  obtain a b' f 
    where "A = [a, b', f]\<^sub>\<circ>"
      and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      and b': "b' \<in>\<^sub>\<circ> cat_1 0 0\<lparr>Obj\<rparr>" 
      and f: "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
    by auto
  moreover from b' have [cat_cs_simps]: "b' = 0"
    unfolding cat_1_components by auto
  moreover have "cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr> = b"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  ultimately show ?thesis using that by auto
qed

lemmas [elim] = is_functor.cat_cf_obj_comma_ObjE[rotated 1]

lemma (in is_functor) cat_obj_cf_comma_ObjE[elim]:
  assumes "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  obtains a f where "A = [0, a, f]\<^sub>\<circ>"
    and "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
proof-
  from assms(2) have "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from assms(1)[unfolded cat_obj_cf_comma_def] is_functor_axioms this 
  obtain a b' f 
    where A_def: "A = [b', a, f]\<^sub>\<circ>"
      and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      and b': "b' \<in>\<^sub>\<circ> cat_1 0 0\<lparr>Obj\<rparr>" 
      and f: "f : cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    by auto
  moreover from b' have [cat_cs_simps]: "b' = 0" 
    unfolding cat_1_components by auto
  moreover have "cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr> = b"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  ultimately show ?thesis using that by auto
qed

lemmas [elim] = is_functor.cat_obj_cf_comma_ObjE[rotated 1]


subsubsection\<open>Arrows\<close>

lemma (in is_functor) cat_cf_obj_comma_ArrI[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "F = [abf, a'b'f', [g, 0]\<^sub>\<circ>]\<^sub>\<circ>"
    and "abf = [a, 0, f]\<^sub>\<circ>"
    and "a'b'f' = [a', 0, f']\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f"
  shows "F \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
  unfolding cat_cf_obj_comma_def
proof(intro cat_comma_ArrI cat_comma_HomI)
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (cs_concl cs_intro: cat_cs_intros)
  from assms(1) show const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from vempty_is_zet show 0: "0 : 0 \<mapsto>\<^bsub>cat_1 0 0\<^esub> 0"
    by (cs_concl cs_simp: cat_cs_simps cat_1_CId_app cs_intro: cat_cs_intros)
  from assms(6) show 
    "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(7) show 
    "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>0\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from 0 assms(6) show 
    "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = cf_const (cat_1 0 0) \<BB> b\<lparr>ArrMap\<rparr>\<lparr>0\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f"
    by (cs_concl cs_simp: cat_cs_simps assms(8) cs_intro: cat_cs_intros)
  from const assms(5,6) show 
    "abf \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F (dghm_const (cat_1 []\<^sub>\<circ> []\<^sub>\<circ>) \<BB> b (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>))\<lparr>Obj\<rparr>"
    by (fold cat_cf_obj_comma_def)
      (cs_concl cs_simp: assms(3) cs_intro: cat_cs_intros cat_comma_cs_intros)
  from const assms(5,7) show 
    "a'b'f' \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F (dghm_const (cat_1 []\<^sub>\<circ> []\<^sub>\<circ>) \<BB> b (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>))\<lparr>Obj\<rparr>"
    by (fold cat_cf_obj_comma_def)
      (cs_concl cs_simp: assms(4) cs_intro: cat_cs_intros cat_comma_cs_intros)
qed (intro assms)+

lemmas [cat_comma_cs_intros] = is_functor.cat_cf_obj_comma_ArrI

lemma (in is_functor) cat_obj_cf_comma_ArrI[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "F = [abf, a'b'f', [0, g]\<^sub>\<circ>]\<^sub>\<circ>"
    and "abf = [0, a, f]\<^sub>\<circ>"
    and "a'b'f' = [0, a', f']\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> "
    and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
  shows "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
  unfolding cat_obj_cf_comma_def
proof(intro cat_comma_ArrI cat_comma_HomI)
  show "\<FF> : \<AA> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>" by (cs_concl cs_intro: cat_cs_intros)
  from assms(1) show const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from vempty_is_zet show 0: "0 : 0 \<mapsto>\<^bsub>cat_1 0 0\<^esub> 0"
    by (cs_concl cs_simp: cat_1_CId_app cs_intro: cat_cs_intros)
  from assms(6) show 
    "f : cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>0\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from assms(7) show 
    "f' : cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>0\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
    by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from 0 assms(7) show 
    "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> cf_const (cat_1 0 0) \<BB> b\<lparr>ArrMap\<rparr>\<lparr>0\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f"
    by (cs_concl cs_simp: cat_cs_simps assms(8) cs_intro: cat_cs_intros)
  from const assms(5,6) show 
    "abf \<in>\<^sub>\<circ> (dghm_const (cat_1 0 0) \<BB> b (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>)) \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    by (fold cat_obj_cf_comma_def)
      (cs_concl cs_simp: assms(3) cs_intro: cat_cs_intros cat_comma_cs_intros)
  from const assms(5,7) show 
    "a'b'f' \<in>\<^sub>\<circ> (dghm_const (cat_1 []\<^sub>\<circ> []\<^sub>\<circ>) \<BB> b (\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>)) \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    by (fold cat_obj_cf_comma_def)
      (cs_concl cs_simp: assms(4) cs_intro: cat_cs_intros cat_comma_cs_intros)
qed (intro assms)+

lemmas [cat_comma_cs_intros] = is_functor.cat_obj_cf_comma_ArrI

lemma (in is_functor) cat_cf_obj_comma_ArrE[elim]:
  assumes "F \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  obtains abf a'b'f' a f a' f' g
    where "F = [abf, a'b'f', [g, 0]\<^sub>\<circ>]\<^sub>\<circ>"
      and "abf = [a, 0, f]\<^sub>\<circ>"
      and "a'b'f' = [a', 0, f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
      and "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
      and "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f"
      and "abf \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
      and "a'b'f' \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
proof-
  from cat_comma_ArrE[OF assms(1)[unfolded cat_cf_obj_comma_def]] 
  obtain abf a'b'f' 
    where F: "F \<in>\<^sub>\<circ> cat_comma_Hom \<FF> (cf_const (cat_1 0 0) \<BB> b) abf a'b'f'"
      and abf: "abf \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F (cf_const (cat_1 0 0) \<BB> b)\<lparr>Obj\<rparr>"
      and a'b'f': "a'b'f' \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F (cf_const (cat_1 0 0) \<BB> b)\<lparr>Obj\<rparr>"
    by auto
  from assms(2) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from F obtain a b'' f a' b' f' g h
    where F_def: "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
      and abf_def: "abf = [a, b'', f]\<^sub>\<circ>"
      and a'b'f'_def: "a'b'f' = [a', b', f']\<^sub>\<circ>"
      and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and h: "h : b'' \<mapsto>\<^bsub>cat_1 0 0\<^esub> b'"
      and f: "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
      and f': "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
      and f_def: 
        "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = cf_const (cat_1 0 0) \<BB> b\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f"
    by (elim cat_comma_HomE[OF _ is_functor_axioms const]) blast
  note hb'b'' = cat_1_is_arrD[OF h]
  from F_def have F_def: "F = [abf, a'b'f', [g, 0]\<^sub>\<circ>]\<^sub>\<circ>" 
    unfolding hb'b'' by simp
  from abf_def have abf_def: "abf = [a, 0, f]\<^sub>\<circ>"
    unfolding hb'b'' by simp
  from a'b'f'_def have a'b'f'_def: "a'b'f' = [a', 0, f']\<^sub>\<circ>"
    unfolding hb'b'' by simp
  from f have f: "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    unfolding hb'b'' by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from f' have f': "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    unfolding hb'b'' by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from f_def f f' g h have f_def: "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f"
    unfolding hb'b'' by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from 
    that F_def abf_def a'b'f'_def g f f' f_def  
    a'b'f'[folded cat_cf_obj_comma_def] abf[folded cat_cf_obj_comma_def]
  show ?thesis
    by blast
qed

lemmas [elim] = is_functor.cat_cf_obj_comma_ArrE[rotated 1]

lemma (in is_functor) cat_obj_cf_comma_ArrE[elim]:
  assumes "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  obtains baf b'a'f' a f a' f' g
    where "F = [baf, b'a'f', [0, g]\<^sub>\<circ>]\<^sub>\<circ>"
      and "baf = [0, a, f]\<^sub>\<circ>"
      and "b'a'f' = [0, a', f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      and "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
      and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
      and "baf \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      and "b'a'f' \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
proof-
  from cat_comma_ArrE[OF assms(1)[unfolded cat_obj_cf_comma_def]] 
  obtain baf b'a'f' 
    where F: "F \<in>\<^sub>\<circ> cat_comma_Hom (cf_const (cat_1 0 0) \<BB> b) \<FF> baf b'a'f'"
      and baf: "baf \<in>\<^sub>\<circ> (cf_const (cat_1 0 0) \<BB> b) \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      and b'a'f': "b'a'f' \<in>\<^sub>\<circ> (cf_const (cat_1 0 0) \<BB> b) \<^sub>C\<^sub>F\<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    by auto
  from assms(2) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from F obtain a b'' f a' b' f' h g 
    where F_def: "F = [baf, b'a'f', [h, g]\<^sub>\<circ>]\<^sub>\<circ>"
      and baf_def: "baf = [b', a, f]\<^sub>\<circ>"
      and b'a'f'_def: "b'a'f' = [b'', a', f']\<^sub>\<circ>"
      and h: "h : b' \<mapsto>\<^bsub>cat_1 0 0\<^esub> b''"
      and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and f: "f : cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      and f': "f' : cf_const (cat_1 0 0) \<BB> b\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
      and f'_def: 
        "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> cf_const (cat_1 0 0) \<BB> b\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f"
    by (elim cat_comma_HomE[OF _ const is_functor_axioms]) blast
  note hb'b'' = cat_1_is_arrD[OF h]
  from F_def have F_def: "F = [baf, b'a'f', [0, g]\<^sub>\<circ>]\<^sub>\<circ>" 
    unfolding hb'b'' by simp
  from baf_def have baf_def: "baf = [0, a, f]\<^sub>\<circ>" 
    unfolding hb'b'' by simp
  from b'a'f'_def have b'a'f'_def: "b'a'f' = [0, a', f']\<^sub>\<circ>"
    unfolding hb'b'' by simp
  from f have f: "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    unfolding hb'b'' by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from f' have f': "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
    unfolding hb'b'' by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from f'_def f f' g h have f'_def[symmetric]: "f' = \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f"
    unfolding hb'b'' by (cs_prems cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
  from 
    that F_def baf_def b'a'f'_def g f f' f'_def  
    baf[folded cat_obj_cf_comma_def] b'a'f'[folded cat_obj_cf_comma_def] 
  show ?thesis
    by blast
qed

lemmas [elim] = is_functor.cat_obj_cf_comma_ArrE

lemma (in is_functor) cat_cf_obj_comma_ArrD[dest]: 
  assumes "[[a, b', f]\<^sub>\<circ>, [a', b'', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>" 
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "b' = 0"
    and "b'' = 0"
    and "h = 0"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f"
    and "[a, b', f]\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
    and "[a', b'', f']\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
  using cat_cf_obj_comma_ArrE[OF assms] by auto

lemmas [dest] = is_functor.cat_cf_obj_comma_ArrD[rotated 1]

lemma (in is_functor) cat_obj_cf_comma_ArrD[dest]: 
  assumes "[[b', a, f]\<^sub>\<circ>, [b'', a', f']\<^sub>\<circ>, [h, g]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "b' = 0"
    and "b'' = 0"
    and "h = 0"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
    and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
    and "[b', a, f]\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    and "[b'', a', f']\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
  using cat_obj_cf_comma_ArrE[OF assms] by auto

lemmas [dest] = is_functor.cat_obj_cf_comma_ArrD


subsubsection\<open>Domain\<close>

lemma cat_cf_obj_comma_Dom_vsv[cat_comma_cs_intros]: "vsv (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Dom\<rparr>)"
  unfolding cat_cf_obj_comma_def cat_comma_components by simp

lemma cat_cf_obj_comma_Dom_vdomain[cat_comma_cs_simps]:
  "\<D>\<^sub>\<circ> (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Dom\<rparr>) = \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
  unfolding cat_cf_obj_comma_def cat_comma_components by simp

lemma cat_cf_obj_comma_Dom_app[cat_comma_cs_simps]:
  assumes "F = [abf, a'b'f', gh]\<^sub>\<circ>" and "F \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
  shows "\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Dom\<rparr>\<lparr>F\<rparr> = abf"
  using assms(2) 
  unfolding assms(1) cat_cf_obj_comma_def cat_comma_components 
  by simp

lemma (in is_functor) cat_cf_obj_comma_Dom_vrange:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
proof-  
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule cat_comma_Dom_vrange[
          OF is_functor_axioms const, folded cat_cf_obj_comma_def
          ]
      )
qed

lemma cat_obj_cf_comma_Dom_vsv[cat_comma_cs_intros]: "vsv (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Dom\<rparr>)"
  unfolding cat_obj_cf_comma_def cat_comma_components by simp

lemma cat_obj_cf_comma_Dom_vdomain[cat_comma_cs_simps]:
  "\<D>\<^sub>\<circ> (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Dom\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
  unfolding cat_obj_cf_comma_def cat_comma_components by simp

lemma cat_obj_cf_comma_Dom_app[cat_comma_cs_simps]:
  assumes "F = [baf, b'a'f', gh]\<^sub>\<circ>" and "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
  shows "b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Dom\<rparr>\<lparr>F\<rparr> = baf"
  using assms(2)
  unfolding assms(1) cat_obj_cf_comma_def cat_comma_components 
  by simp

lemma (in is_functor) cat_obj_cf_comma_Dom_vrange:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
proof-  
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule cat_comma_Dom_vrange[
          OF const is_functor_axioms, folded cat_obj_cf_comma_def
          ]
      )
qed


subsubsection\<open>Codomain\<close>

lemma cat_cf_obj_comma_Cod_vsv[cat_comma_cs_intros]: "vsv (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Cod\<rparr>)"
  unfolding cat_cf_obj_comma_def cat_comma_components by simp

lemma cat_cf_obj_comma_Cod_vdomain[cat_comma_cs_simps]:
  "\<D>\<^sub>\<circ> (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Cod\<rparr>) = \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
  unfolding cat_cf_obj_comma_def cat_comma_components by simp

lemma cat_cf_obj_comma_Cod_app[cat_comma_cs_simps]:
  assumes "F = [abf, a'b'f', gh]\<^sub>\<circ>" and "F \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
  shows "\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Cod\<rparr>\<lparr>F\<rparr> = a'b'f'"
  using assms(2) 
  unfolding assms(1) cat_cf_obj_comma_def cat_comma_components 
  by (simp add: nat_omega_simps)

lemma (in is_functor) cat_cf_obj_comma_Cod_vrange:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
proof-  
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule cat_comma_Cod_vrange[
          OF is_functor_axioms const, folded cat_cf_obj_comma_def
          ]
      )
qed

lemma cat_obj_cf_comma_Cod_vsv[cat_comma_cs_intros]: "vsv (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Cod\<rparr>)"
  unfolding cat_obj_cf_comma_def cat_comma_components by simp

lemma cat_obj_cf_comma_Cod_vdomain[cat_comma_cs_simps]:
  "\<D>\<^sub>\<circ> (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Cod\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
  unfolding cat_obj_cf_comma_def cat_comma_components by simp

lemma cat_obj_cf_comma_Cod_app[cat_comma_cs_simps]:
  assumes "F = [baf, b'a'f', gh]\<^sub>\<circ>" and "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
  shows "b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Cod\<rparr>\<lparr>F\<rparr> = b'a'f'"
  using assms(2)
  unfolding assms(1) cat_obj_cf_comma_def cat_comma_components 
  by (simp add: nat_omega_simps)

lemma (in is_functor) cat_obj_cf_comma_Cod_vrange:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<R>\<^sub>\<circ> (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
proof-  
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule cat_comma_Dom_vrange[
          OF const is_functor_axioms, folded cat_obj_cf_comma_def
          ]
      )
qed


subsubsection\<open>Arrow with a domain and a codomain\<close>

lemma (in is_functor) cat_cf_obj_comma_is_arrI[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "F = [abf, a'b'f', gh]\<^sub>\<circ>"
    and "abf = [a, 0, f]\<^sub>\<circ>"
    and "a'b'f' = [a', 0, f']\<^sub>\<circ>"
    and "gh = [g, 0]\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f"
  shows "F : abf \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> a'b'f'"
proof(intro is_arrI)
  from assms(1,6,7,8) show "F \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: assms(2,3,4,5,9) cs_intro: cat_comma_cs_intros)
  with assms(2) show "\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Dom\<rparr>\<lparr>F\<rparr> = abf" "\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Cod\<rparr>\<lparr>F\<rparr> = a'b'f'"
    by (cs_concl cs_simp: cat_comma_cs_simps)+
qed

lemmas [cat_comma_cs_intros] = is_functor.cat_cf_obj_comma_is_arrI

lemma (in is_functor) cat_obj_cf_comma_is_arrI[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "F = [baf, b'a'f', gh]\<^sub>\<circ>"
    and "baf = [0, a, f]\<^sub>\<circ>"
    and "b'a'f' = [0, a', f']\<^sub>\<circ>"
    and "gh = [0, g]\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
    and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
  shows "F : baf \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> b'a'f'"
proof(intro is_arrI)
  from assms(1,6,7,8) show "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
    by (cs_concl cs_simp: assms(2,3,4,5,9) cs_intro: cat_comma_cs_intros)
  with assms(2) show "b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Dom\<rparr>\<lparr>F\<rparr> = baf" "b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Cod\<rparr>\<lparr>F\<rparr> = b'a'f'"
    by (cs_concl cs_simp: cat_comma_cs_simps)+
qed

lemmas [cat_comma_cs_intros] = is_functor.cat_obj_cf_comma_is_arrI

lemma (in is_functor) cat_cf_obj_comma_is_arrD[dest]:
  assumes "[[a, b', f]\<^sub>\<circ>, [a', b'', f']\<^sub>\<circ>, [g, h]\<^sub>\<circ>]\<^sub>\<circ> :
    [a, b', f]\<^sub>\<circ> \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> [a', b'', f']\<^sub>\<circ>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "b' = []\<^sub>\<circ>"
    and "b'' = []\<^sub>\<circ>"
    and "h = []\<^sub>\<circ>"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
    and "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f"
    and "[a, b', f]\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
    and "[a', b'', f']\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
  by (intro cat_cf_obj_comma_ArrD[OF is_arrD(1)[OF assms(1)] assms(2)])+

lemma (in is_functor) cat_obj_cf_comma_is_arrD[dest]:
  assumes "[[b', a, f]\<^sub>\<circ>, [b'', a', f']\<^sub>\<circ>, [h, g]\<^sub>\<circ>]\<^sub>\<circ> :
    [b', a, f]\<^sub>\<circ> \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> [b'', a', f']\<^sub>\<circ>"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "b' = 0"
    and "b'' = 0"
    and "h = 0"
    and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
    and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
    and "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
    and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
    and "[b', a, f]\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    and "[b'', a', f']\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
  by (intro cat_obj_cf_comma_ArrD[OF is_arrD(1)[OF assms(1)] assms(2)])+

lemmas [dest] = is_functor.cat_obj_cf_comma_is_arrD

lemma (in is_functor) cat_cf_obj_comma_is_arrE[elim]:
  assumes "F : abf \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> a'b'f'" and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  obtains a f a' f' g 
    where "F = [[a, 0, f]\<^sub>\<circ>, [a', 0, f']\<^sub>\<circ>, [g, 0]\<^sub>\<circ>]\<^sub>\<circ>"
      and "abf = [a, 0, f]\<^sub>\<circ>"
      and "a'b'f' = [a', 0, f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
      and "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
      and "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f"
      and "abf \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
      and "a'b'f' \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
proof-
  note F = is_arrD[OF assms(1)]
  from F(1) obtain abf' a'b'f'' a f a' f' g 
    where F_def: "F = [abf', a'b'f'', [g, 0]\<^sub>\<circ>]\<^sub>\<circ>"
      and abf'_def: "abf' = [a, 0, f]\<^sub>\<circ>"
      and a'b'f''_def: "a'b'f'' = [a', 0, f']\<^sub>\<circ>"
      and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and f: "f : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
      and f': "f' : \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr> \<mapsto>\<^bsub>\<BB>\<^esub> b"
      and f_def: "f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> = f" 
      and abf': "abf' \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>" 
      and a'b'f'': "a'b'f'' \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
    by (elim cat_cf_obj_comma_ArrE[OF _ assms(2)])
  from F(2) assms(2) abf'_def a'b'f''_def g f f' f_def have "abf' = abf"
    unfolding F_def 
    by (cs_prems cs_simp: cat_comma_cs_simps cs_intro: cat_comma_cs_intros)
  from F(3) assms(2) abf'_def a'b'f''_def g f f' f_def have "a'b'f'' = a'b'f'"
    unfolding F_def 
    by (cs_prems cs_simp: cat_comma_cs_simps cs_intro: cat_comma_cs_intros)
  from that F_def abf'_def a'b'f''_def g f f' f_def abf' a'b'f'' show ?thesis
    unfolding \<open>abf' = abf\<close> \<open>a'b'f'' = a'b'f'\<close> by auto
qed

lemmas [elim] = is_functor.cat_cf_obj_comma_is_arrE

lemma (in is_functor) cat_obj_cf_comma_is_arrE[elim]:
  assumes "F : baf \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> b'a'f'"
    and "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  obtains a f a' f' g
    where "F = [[0, a, f]\<^sub>\<circ>, [0, a', f']\<^sub>\<circ>, [0, g]\<^sub>\<circ>]\<^sub>\<circ>"
      and "baf = [0, a, f]\<^sub>\<circ>"
      and "b'a'f' = [0, a', f']\<^sub>\<circ>"
      and "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      and "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
      and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
      and "baf \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      and "b'a'f' \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
proof-
  note F = is_arrD[OF assms(1)]
  from F(1) obtain baf' b'a'f'' a f a' f' g 
    where F_def: "F = [baf', b'a'f'', [0, g]\<^sub>\<circ>]\<^sub>\<circ>"
      and baf'_def: "baf' = [0, a, f]\<^sub>\<circ>"
      and b'a'f''_def: "b'a'f'' = [0, a', f']\<^sub>\<circ>"
      and g: "g : a \<mapsto>\<^bsub>\<AA>\<^esub> a'"
      and f: "f : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
      and f': "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
      and f'_def: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>g\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'" 
      and baf': "baf' \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>" 
      and b'a'f'': "b'a'f'' \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    by (elim cat_obj_cf_comma_ArrE[OF _ assms(2)])
  from F(2) assms(2) baf'_def b'a'f''_def g f f' f'_def have "baf' = baf"
    unfolding F_def 
    by (cs_prems cs_simp: cat_comma_cs_simps cs_intro: cat_comma_cs_intros)
  from F(3) assms(2) baf'_def b'a'f''_def g f f' f'_def have "b'a'f'' = b'a'f'"
    unfolding F_def 
    by (cs_prems cs_simp: cat_comma_cs_simps cs_intro: cat_comma_cs_intros)
  from that F_def baf'_def b'a'f''_def g f f' f'_def baf' b'a'f'' show ?thesis
    unfolding \<open>baf' = baf\<close> \<open>b'a'f'' = b'a'f'\<close> by auto
qed

lemmas [elim] = is_functor.cat_obj_cf_comma_is_arrE


subsubsection\<open>Composition\<close>

lemma cat_cf_obj_comma_Comp_vsv[cat_comma_cs_intros]: "vsv (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Comp\<rparr>)"
  unfolding cat_cf_obj_comma_def by (cs_concl cs_intro: cat_comma_cs_intros)

lemma cat_obj_cf_comma_Comp_vsv[cat_comma_cs_intros]: "vsv (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Comp\<rparr>)"
  unfolding cat_obj_cf_comma_def by (cs_concl cs_intro: cat_comma_cs_intros)

lemma (in is_functor) cat_cf_obj_comma_Comp_app[cat_comma_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "G = [a'b'f', a''b''f'', [g', h']\<^sub>\<circ>]\<^sub>\<circ>"
    and "F = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>"
    and "G : a'b'f' \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> a''b''f''" 
    and "F : abf \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> a'b'f'"
  shows "G \<circ>\<^sub>A\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> F = [abf, a''b''f'', [g' \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g, 0]\<^sub>\<circ>]\<^sub>\<circ>"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from assms(4) obtain a f a' f' g
    where G_def: "G = [[a, 0, f]\<^sub>\<circ>, [a', 0, f']\<^sub>\<circ>, [g, 0]\<^sub>\<circ>]\<^sub>\<circ>"
    by (elim cat_cf_obj_comma_is_arrE[OF _ assms(1)])
  from assms(5) obtain a f a' f' g
    where F_def: "F = [[a, 0, f]\<^sub>\<circ>, [a', 0, f']\<^sub>\<circ>, [g, 0]\<^sub>\<circ>]\<^sub>\<circ>"
    by (elim cat_cf_obj_comma_is_arrE[OF _ assms(1)])
  from assms(2)[unfolded G_def] assms(3)[unfolded F_def] have [cat_cs_simps]:
    "h' = 0" "h = 0"
    by simp_all
  have "h' \<circ>\<^sub>A\<^bsub>cat_1 0 0\<^esub> h = 0" by (cs_concl cs_simp: cat_cs_simps)
  show ?thesis
    by 
      (
        rule cat_comma_Comp_app
          [
            OF 
              is_functor_axioms 
              const 
              assms(2,3) 
              assms(4)[unfolded cat_cf_obj_comma_def] 
              assms(5)[unfolded cat_cf_obj_comma_def],
            folded cat_cf_obj_comma_def,
            unfolded cat_cs_simps
          ]
      )
qed

lemma (in is_functor) cat_obj_cf_comma_Comp_app[cat_comma_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
    and "G = [b'a'f', b''a''f'', [h', g']\<^sub>\<circ>]\<^sub>\<circ>"
    and "F = [baf, b'a'f', [h, g]\<^sub>\<circ>]\<^sub>\<circ>"
    and "G : b'a'f' \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> b''a''f''" 
    and "F : baf \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> b'a'f'"
  shows "G \<circ>\<^sub>A\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> F = [baf, b''a''f'', [0, g' \<circ>\<^sub>A\<^bsub>\<AA>\<^esub> g]\<^sub>\<circ>]\<^sub>\<circ>"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_simp: cs_intro: vempty_is_zet cat_cs_intros)
  from assms(4) obtain a f a' f' g
    where G_def: "G = [[0, a, f]\<^sub>\<circ>, [0, a', f']\<^sub>\<circ>, [0, g]\<^sub>\<circ>]\<^sub>\<circ>"
    by (elim cat_obj_cf_comma_is_arrE[OF _ assms(1)])
  from assms(5) obtain a f a' f' g
    where F_def: "F = [[0, a, f]\<^sub>\<circ>, [0, a', f']\<^sub>\<circ>, [0, g]\<^sub>\<circ>]\<^sub>\<circ>"
    by (elim cat_obj_cf_comma_is_arrE[OF _ assms(1)])
  from assms(2)[unfolded G_def] assms(3)[unfolded F_def] have [cat_cs_simps]:
    "h' = 0" "h = 0"
    by simp_all
  have "h' \<circ>\<^sub>A\<^bsub>cat_1 0 0\<^esub> h = 0" by (cs_concl cs_simp: cat_cs_simps) show ?thesis
    by 
      (
        rule cat_comma_Comp_app
          [
            OF 
              const 
              is_functor_axioms
              assms(2,3) 
              assms(4)[unfolded cat_obj_cf_comma_def] 
              assms(5)[unfolded cat_obj_cf_comma_def],
            folded cat_obj_cf_comma_def,
            unfolded cat_cs_simps
          ]
      )
qed

lemma (in is_functor) cat_cf_obj_comma_Comp_is_arr[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "G : a'b'f' \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> a''b''f''" 
    and "F : abf \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> a'b'f'"
  shows "G \<circ>\<^sub>A\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> F : abf \<mapsto>\<^bsub>\<FF> \<^sub>C\<^sub>F\<down> b\<^esub> a''b''f''"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule cat_comma_Comp_is_arr
          [
            OF 
              is_functor_axioms 
              const 
              assms(2)[unfolded cat_cf_obj_comma_def]
              assms(3)[unfolded cat_cf_obj_comma_def],
            folded cat_cf_obj_comma_def
          ]
      )
qed

lemma (in is_functor) cat_obj_cf_comma_Comp_is_arr[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" 
    and "G : b'a'f' \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> b''a''f''" 
    and "F : baf \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> b'a'f'"
  shows "G \<circ>\<^sub>A\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> F : baf \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> b''a''f''"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule cat_comma_Comp_is_arr
          [
            OF 
              const 
              is_functor_axioms 
              assms(2)[unfolded cat_obj_cf_comma_def]
              assms(3)[unfolded cat_obj_cf_comma_def],
            folded cat_obj_cf_comma_def
          ]
      )
qed


subsubsection\<open>Identity\<close>

lemma cat_cf_obj_comma_CId_vsv[cat_comma_cs_intros]: "vsv (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>CId\<rparr>)"
  unfolding cat_cf_obj_comma_def by (cs_concl cs_intro: cat_comma_cs_intros)

lemma cat_obj_cf_comma_CId_vsv[cat_comma_cs_intros]: "vsv (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>)"
  unfolding cat_obj_cf_comma_def by (cs_concl cs_intro: cat_comma_cs_intros)

lemma (in is_functor) cat_cf_obj_comma_CId_vdomain[cat_comma_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>CId\<rparr>) = \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule cat_comma_CId_vdomain[
          OF is_functor_axioms const, folded cat_cf_obj_comma_def
          ]
      )
qed

lemma (in is_functor) cat_obj_cf_comma_CId_vdomain[cat_comma_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<D>\<^sub>\<circ> (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show "\<D>\<^sub>\<circ> (b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    by 
      (
        rule cat_comma_CId_vdomain[
          OF const is_functor_axioms, folded cat_obj_cf_comma_def
          ]
      )
qed

lemma (in is_functor) cat_cf_obj_comma_CId_app[cat_comma_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "A = [a, b', f]\<^sub>\<circ>" and "A \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
  shows "\<FF> \<^sub>C\<^sub>F\<down> b\<lparr>CId\<rparr>\<lparr>A\<rparr> = [A, A, [\<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>, 0]\<^sub>\<circ>]\<^sub>\<circ>"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from assms(3,2) have b'_def: "b' = 0"
    by (auto elim: cat_cf_obj_comma_ObjE[OF _ assms(1)])
  have [cat_cs_simps]: "cat_1 0 0\<lparr>CId\<rparr>\<lparr>b'\<rparr> = 0" 
    unfolding cat_1_components b'_def by simp
  show ?thesis
    by 
      ( 
        rule cat_comma_CId_app
          [
            OF 
              is_functor_axioms 
              const
              assms(2,3)[unfolded cat_cf_obj_comma_def],  
            unfolded cat_cf_obj_comma_def[symmetric] cat_cs_simps
          ]
        )
qed

lemma (in is_functor) cat_obj_cf_comma_CId_app[cat_comma_cs_simps]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "A = [b', a, f]\<^sub>\<circ>" and "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
  shows "b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>\<lparr>A\<rparr> = [A, A, [0, \<AA>\<lparr>CId\<rparr>\<lparr>a\<rparr>]\<^sub>\<circ>]\<^sub>\<circ>"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  from assms(3,2) have b'_def: "b' = 0"
    by (auto elim: cat_obj_cf_comma_ObjE[OF _ assms(1)])
  have [cat_cs_simps]: "cat_1 0 0\<lparr>CId\<rparr>\<lparr>b'\<rparr> = 0" 
    unfolding cat_1_components b'_def by simp
  show ?thesis
    by 
      ( 
        rule cat_comma_CId_app
          [
            OF 
              const
              is_functor_axioms 
              assms(2,3)[unfolded cat_obj_cf_comma_def],  
            unfolded cat_obj_cf_comma_def[symmetric] cat_cs_simps
          ]
        )
qed


subsubsection\<open>
Comma categories constructed from a functor and an object are categories
\<close>

lemma (in is_functor) category_cat_cf_obj_comma[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "category \<alpha> (\<FF> \<^sub>C\<^sub>F\<down> b)"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule category_cat_comma[
          OF is_functor_axioms const, folded cat_cf_obj_comma_def
          ]
      )
qed

lemmas [cat_comma_cs_intros] = is_functor.category_cat_cf_obj_comma

lemma (in is_functor) category_cat_obj_cf_comma[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "category \<alpha> (b \<down>\<^sub>C\<^sub>F \<FF>)"
proof-
  from assms(1) have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: vempty_is_zet cat_cs_intros)
  show ?thesis
    by 
      (
        rule category_cat_comma[
          OF const is_functor_axioms, folded cat_obj_cf_comma_def
          ]
      )
qed

lemmas [cat_comma_cs_intros] = is_functor.category_cat_obj_cf_comma


subsubsection\<open>Tiny comma categories constructed from a functor and an object\<close>

lemma (in is_tm_functor) tiny_category_cat_cf_obj_comma[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "tiny_category \<alpha> (\<FF> \<^sub>C\<^sub>F\<down> b)"
proof-
  from assms(1) have const: 
    "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by 
      (
        cs_concl cs_intro: 
          vempty_is_zet cat_small_cs_intros cat_cs_intros
      )
  show ?thesis
    by 
      (
        rule tiny_category_cat_comma[
          OF is_tm_functor_axioms const, folded cat_cf_obj_comma_def
          ]
      )
qed

lemma (in is_tm_functor) tiny_category_cat_obj_cf_comma[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "tiny_category \<alpha> (b \<down>\<^sub>C\<^sub>F \<FF>)"
proof-
  from assms(1) have const: 
    "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by 
      (
        cs_concl cs_intro: 
          vempty_is_zet cat_small_cs_intros cat_cs_intros
      )
  show ?thesis
    by 
      (
        rule tiny_category_cat_comma[
          OF const is_tm_functor_axioms, folded cat_obj_cf_comma_def
          ]
      )
qed



subsection\<open>
Projections for comma categories constructed from a functor and an object
\<close>


subsubsection\<open>Definitions and elementary properties\<close>

definition cf_cf_obj_comma_proj :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_ \<^sub>C\<^sub>F\<Sqinter>\<^sub>O _)\<close> [1000, 1000] 999)
  where "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b \<equiv> \<FF> \<^sub>C\<^sub>F\<Sqinter> (cf_const (cat_1 0 0) (\<FF>\<lparr>HomCod\<rparr>) b)"

definition cf_obj_cf_comma_proj :: "V \<Rightarrow> V \<Rightarrow> V" (\<open>(_ \<^sub>O\<Sqinter>\<^sub>C\<^sub>F _)\<close> [1000, 1000] 999)
  where "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<equiv> (cf_const (cat_1 0 0) (\<FF>\<lparr>HomCod\<rparr>) b) \<Sqinter>\<^sub>C\<^sub>F \<FF>"


text\<open>Alternative forms of the definitions.\<close>

lemma (in is_functor) cf_cf_obj_comma_proj_def:
  "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b = \<FF> \<^sub>C\<^sub>F\<Sqinter> (cf_const (cat_1 0 0) \<BB> b)" 
  unfolding cf_cf_obj_comma_proj_def cf_HomCod..

lemma (in is_functor) cf_obj_cf_comma_proj_def: 
  "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> = (cf_const (cat_1 0 0) \<BB> b) \<Sqinter>\<^sub>C\<^sub>F \<FF>" 
  unfolding cf_obj_cf_comma_proj_def cf_HomCod..


text\<open>Components.\<close>

lemma (in is_functor) cf_cf_obj_comma_proj_components[cat_comma_cs_simps]: 
  shows "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>HomDom\<rparr> = \<FF> \<^sub>C\<^sub>F\<down> b"
    and "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>HomCod\<rparr> = \<AA>"
  unfolding 
    cf_cf_obj_comma_proj_def 
    cf_comma_proj_left_components 
    cat_cf_obj_comma_def[symmetric]
    cat_cs_simps 
  by simp_all

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_obj_comma_proj_components

lemma (in is_functor) cf_obj_cf_comma_proj_components[cat_comma_cs_simps]: 
  shows "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>HomDom\<rparr> = b \<down>\<^sub>C\<^sub>F \<FF>"
    and "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>HomCod\<rparr> = \<AA>"
  unfolding 
    cf_obj_cf_comma_proj_def 
    cf_comma_proj_right_components 
    cat_obj_cf_comma_def[symmetric]
    cat_cs_simps 
  by simp_all

lemmas [cat_comma_cs_simps] = is_functor.cf_obj_cf_comma_proj_components


subsubsection\<open>Object map\<close>

lemma cf_cf_obj_comma_proj_ObjMap_vsv[cat_comma_cs_intros]: 
  "vsv (\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>ObjMap\<rparr>)"
  unfolding cf_cf_obj_comma_proj_def
  by (cs_concl cs_intro: cat_comma_cs_intros)

lemma cf_obj_cf_comma_proj_ObjMap_vsv[cat_comma_cs_intros]: 
  "vsv (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>)"
  unfolding cf_obj_cf_comma_proj_def
  by (cs_concl cs_intro: cat_comma_cs_intros)

lemma (in is_functor) cf_cf_obj_comma_proj_ObjMap_vdomain[cat_comma_cs_simps]: 
  "\<D>\<^sub>\<circ> (\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>ObjMap\<rparr>) = \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
  unfolding cf_cf_obj_comma_proj_def cf_comma_proj_left_ObjMap_vdomain
  unfolding 
    cf_cf_obj_comma_proj_def[symmetric] 
    cf_comma_proj_left_components[symmetric]
    cat_comma_cs_simps
  by simp

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_obj_comma_proj_ObjMap_vdomain

lemma (in is_functor) cf_obj_cf_comma_proj_ObjMap_vdomain[cat_comma_cs_simps]: 
  "\<D>\<^sub>\<circ> (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
  unfolding cf_obj_cf_comma_proj_def cf_comma_proj_right_ObjMap_vdomain
  unfolding 
    cf_obj_cf_comma_proj_def[symmetric] 
    cf_comma_proj_right_components[symmetric]
    cat_comma_cs_simps
  by simp

lemmas [cat_comma_cs_simps] = is_functor.cf_obj_cf_comma_proj_ObjMap_vdomain

lemma (in is_functor) cf_cf_obj_comma_proj_ObjMap_app[cat_comma_cs_simps]:
  assumes "A = [a, b', f]\<^sub>\<circ>" and "[a, b', f]\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Obj\<rparr>"
  shows "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = a"
  by 
    (
      rule cf_comma_proj_left_ObjMap_app[
        OF assms(1) assms(2)[unfolded cat_cf_obj_comma_def], 
        folded cf_cf_obj_comma_proj_def
        ]
    )

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_obj_comma_proj_ObjMap_app

lemma (in is_functor) cf_obj_cf_comma_proj_ObjMap_app[cat_comma_cs_simps]:
  assumes "A = [b', a, f]\<^sub>\<circ>" and "[b', a, f]\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
  shows "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = a"
  by 
    (
      rule cf_comma_proj_right_ObjMap_app[
        OF assms(1) assms(2)[unfolded cat_obj_cf_comma_def], 
        folded cf_obj_cf_comma_proj_def
        ]
    )

lemmas [cat_comma_cs_simps] = is_functor.cf_obj_cf_comma_proj_ObjMap_app


subsubsection\<open>Arrow map\<close>

lemma cf_cf_obj_comma_proj_ArrMap_vsv[cat_comma_cs_intros]: 
  "vsv (\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>ArrMap\<rparr>)"
  unfolding cf_cf_obj_comma_proj_def
  by (cs_concl cs_intro: cat_comma_cs_intros)

lemma cf_obj_cf_comma_proj_ArrMap_vsv[cat_comma_cs_intros]: 
  "vsv (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>)"
  unfolding cf_obj_cf_comma_proj_def
  by (cs_concl cs_intro: cat_comma_cs_intros)

lemma (in is_functor) cf_cf_obj_comma_proj_ArrMap_vdomain[cat_comma_cs_simps]: 
  "\<D>\<^sub>\<circ> (\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>ArrMap\<rparr>) = \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
  unfolding cf_cf_obj_comma_proj_def cf_comma_proj_left_ArrMap_vdomain
  unfolding 
    cf_cf_obj_comma_proj_def[symmetric] 
    cf_comma_proj_left_components[symmetric]
    cat_comma_cs_simps
  by simp

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_obj_comma_proj_ObjMap_vdomain

lemma (in is_functor) cf_obj_cf_comma_proj_ArrMap_vdomain[cat_comma_cs_simps]:
  "\<D>\<^sub>\<circ> (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
  unfolding cf_obj_cf_comma_proj_def cf_comma_proj_right_ArrMap_vdomain
  unfolding 
    cf_obj_cf_comma_proj_def[symmetric] 
    cf_comma_proj_right_components[symmetric]
    cat_comma_cs_simps
  by simp

lemmas [cat_comma_cs_simps] = is_functor.cf_obj_cf_comma_proj_ArrMap_vdomain

lemma (in is_functor) cf_cf_obj_comma_proj_ArrMap_app[cat_comma_cs_simps]:
  assumes "A = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>" 
    and "[abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> \<FF> \<^sub>C\<^sub>F\<down> b\<lparr>Arr\<rparr>"
  shows "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b\<lparr>ArrMap\<rparr>\<lparr>A\<rparr> = g"
  by 
    (
      rule cf_comma_proj_left_ArrMap_app[
        OF assms(1) assms(2)[unfolded cat_cf_obj_comma_def], 
        folded cf_cf_obj_comma_proj_def
        ]
    )

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_obj_comma_proj_ArrMap_app

lemma (in is_functor) cf_obj_cf_comma_proj_ArrMap_app[cat_comma_cs_simps]:
  assumes "A = [abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ>" 
    and "[abf, a'b'f', [g, h]\<^sub>\<circ>]\<^sub>\<circ> \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
  shows "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>A\<rparr> = h"
  by 
    (
      rule cf_comma_proj_right_ArrMap_app[
        OF assms(1) assms(2)[unfolded cat_obj_cf_comma_def], 
        folded cf_obj_cf_comma_proj_def
        ]
    )

lemmas [cat_comma_cs_simps] = is_functor.cf_obj_cf_comma_proj_ArrMap_app


subsubsection\<open>Projections for a comma category are functors\<close>

lemma (in is_functor) cf_cf_obj_comma_proj_is_functor:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b : \<FF> \<^sub>C\<^sub>F\<down> b \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: V_cs_intros cat_cs_intros)
  show ?thesis
    by 
      (
        rule cf_comma_proj_left_is_functor[
          OF is_functor_axioms const,
          folded cf_cf_obj_comma_proj_def cat_cf_obj_comma_def
          ]
      )
qed

lemma (in is_functor) cf_cf_obj_comma_proj_is_functor'[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "\<AA>' = \<FF> \<^sub>C\<^sub>F\<down> b"
  shows "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1) unfolding assms(2) by (rule cf_cf_obj_comma_proj_is_functor)

lemmas [cat_comma_cs_intros] = is_functor.cf_cf_obj_comma_proj_is_functor'

lemma (in is_functor) cf_obj_cf_comma_proj_is_functor:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> : b \<down>\<^sub>C\<^sub>F \<FF> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: V_cs_intros cat_cs_intros)
  show ?thesis
    by 
      (
        rule cf_comma_proj_right_is_functor[
          OF const is_functor_axioms,
          folded cf_obj_cf_comma_proj_def cat_obj_cf_comma_def
          ]
      )
qed

lemma (in is_functor) cf_obj_cf_comma_proj_is_functor'[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "\<AA>' = b \<down>\<^sub>C\<^sub>F \<FF>"
  shows "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1) unfolding assms(2) by (rule cf_obj_cf_comma_proj_is_functor)

lemmas [cat_comma_cs_intros] = is_functor.cf_obj_cf_comma_proj_is_functor'


subsubsection\<open>Projections for a tiny comma category\<close>

lemma (in is_tm_functor) cf_cf_obj_comma_proj_is_tm_functor:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b : \<FF> \<^sub>C\<^sub>F\<down> b \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: V_cs_intros cat_small_cs_intros cat_cs_intros)
  show ?thesis
    by 
      (
        rule cf_comma_proj_left_is_tm_functor[
          OF is_tm_functor_axioms const,
          folded cf_cf_obj_comma_proj_def cat_cf_obj_comma_def
          ]
      )
qed

lemma (in is_tm_functor) cf_cf_obj_comma_proj_is_tm_functor'[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "\<FF>b = \<FF> \<^sub>C\<^sub>F\<down> b"
  shows "\<FF> \<^sub>C\<^sub>F\<Sqinter>\<^sub>O b : \<FF>b \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1) unfolding assms(2) by (rule cf_cf_obj_comma_proj_is_tm_functor)

lemmas [cat_comma_cs_intros] = is_tm_functor.cf_cf_obj_comma_proj_is_tm_functor'

lemma (in is_tm_functor) cf_obj_cf_comma_proj_is_tm_functor:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> : b \<down>\<^sub>C\<^sub>F \<FF> \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
proof-
  from assms have const: "cf_const (cat_1 0 0) \<BB> b : cat_1 0 0 \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<BB>"
    by (cs_concl cs_intro: V_cs_intros cat_small_cs_intros cat_cs_intros)
  show ?thesis
    by 
      (
        rule cf_comma_proj_right_is_tm_functor[
          OF const is_tm_functor_axioms,
          folded cf_obj_cf_comma_proj_def cat_obj_cf_comma_def
          ]
      )
qed

lemma (in is_tm_functor) cf_obj_cf_comma_proj_is_tm_functor'[cat_comma_cs_intros]:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" and "\<AA>' = b \<down>\<^sub>C\<^sub>F \<FF>"
  shows "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^sub>.\<^sub>t\<^sub>m\<^bsub>\<alpha>\<^esub> \<AA>"
  using assms(1) unfolding assms(2) by (rule cf_obj_cf_comma_proj_is_tm_functor)

lemmas [cat_comma_cs_intros] = is_tm_functor.cf_obj_cf_comma_proj_is_tm_functor'



subsection\<open>Comma functors\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Theorem 1 in Chapter X-3 in \cite{mac_lane_categories_2010}.\<close>

definition cf_cf_arr_comma :: "V \<Rightarrow> V \<Rightarrow> V" 
  (\<open>(_ \<^sub>A\<down>\<^sub>C\<^sub>F _)\<close> [1000, 1000] 999)
  where "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF> =
    [
      (\<lambda>A\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>. [0, A\<lparr>1\<^sub>\<nat>\<rparr>, A\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> g]\<^sub>\<circ>),
      (
        \<lambda>F\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>.
          [
            [0, F\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> g]\<^sub>\<circ>,
            [0, F\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> g]\<^sub>\<circ>,
            F\<lparr>2\<^sub>\<nat>\<rparr>
          ]\<^sub>\<circ>
      ),
      (\<FF>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>,
      (\<FF>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>
    ]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma cf_cf_arr_comma_components:
  shows "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr> =
    (\<lambda>A\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>. [0, A\<lparr>1\<^sub>\<nat>\<rparr>, A\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> g]\<^sub>\<circ>)"
    and "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>F\<in>\<^sub>\<circ>(\<FF>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>.
          [
            [0, F\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> g]\<^sub>\<circ>,
            [0, F\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<FF>\<lparr>HomCod\<rparr>\<^esub> g]\<^sub>\<circ>,
            F\<lparr>2\<^sub>\<nat>\<rparr>
          ]\<^sub>\<circ>
      )"
    and "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>HomDom\<rparr> = (\<FF>\<lparr>HomCod\<rparr>\<lparr>Cod\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>"
    and "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>HomCod\<rparr> = (\<FF>\<lparr>HomCod\<rparr>\<lparr>Dom\<rparr>\<lparr>g\<rparr>) \<down>\<^sub>C\<^sub>F \<FF>"
  unfolding cf_cf_arr_comma_def dghm_field_simps 
  by (simp_all add: nat_omega_simps)

context is_functor
begin

lemma cf_cf_arr_comma_components':
  assumes "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'"
  shows "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr> = (\<lambda>A\<in>\<^sub>\<circ>c' \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>. [0, A\<lparr>1\<^sub>\<nat>\<rparr>, A\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g]\<^sub>\<circ>)"
    and "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr> =
      (
        \<lambda>F\<in>\<^sub>\<circ>c' \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>.
          [
            [0, F\<lparr>0\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>0\<rparr>\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g]\<^sub>\<circ>,
            [0, F\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>1\<^sub>\<nat>\<rparr>, F\<lparr>1\<^sub>\<nat>\<rparr>\<lparr>2\<^sub>\<nat>\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g]\<^sub>\<circ>,
            F\<lparr>2\<^sub>\<nat>\<rparr>
          ]\<^sub>\<circ>
      )"
    and [cat_comma_cs_simps]: "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>HomDom\<rparr> = c' \<down>\<^sub>C\<^sub>F \<FF>"
    and [cat_comma_cs_simps]: "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>HomCod\<rparr> = c \<down>\<^sub>C\<^sub>F \<FF>"
  using assms
  unfolding cf_cf_arr_comma_components
  by (simp_all add: cat_cs_simps)

end

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_arr_comma_components'(3,4)


subsubsection\<open>Object map\<close>

mk_VLambda cf_cf_arr_comma_components(1)[unfolded VLambda_vid_on[symmetric]]
  |vsv cf_cf_arr_comma_ObjMap_vsv[cat_comma_cs_intros]|

context is_functor
begin

context 
  fixes g c c'
  assumes g: "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'"
begin

mk_VLambda 
  cf_cf_arr_comma_components'(1)[OF g, unfolded VLambda_vid_on[symmetric]]
  |vdomain cf_cf_arr_comma_ObjMap_vdomain[cat_comma_cs_simps]|

end

end

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_arr_comma_ObjMap_vdomain

lemma (in is_functor) cf_cf_arr_comma_ObjMap_app[cat_comma_cs_simps]:
  assumes "A = [a', b', f']\<^sub>\<circ>" and "A \<in>\<^sub>\<circ> c' \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>" and "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'"
  shows "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = [a', b', f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g]\<^sub>\<circ>"
proof-
  from assms have b': "b' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
    and f: "f' : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
    and a'_def: "a' = 0"
    by auto
  from assms(2) show ?thesis
    unfolding cf_cf_arr_comma_components'[OF assms(3)] assms(1)
    by (simp add: nat_omega_simps a'_def)
qed

lemma (in is_functor) cf_cf_arr_comma_ObjMap_vrange: 
  assumes "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'"
  shows "\<R>\<^sub>\<circ> (g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
proof
  (
    rule vsv.vsv_vrange_vsubset, 
    unfold cf_cf_arr_comma_ObjMap_vdomain[OF assms]
  )
  fix A assume "A \<in>\<^sub>\<circ> c' \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
  with assms is_functor_axioms obtain a f 
    where A_def: "A = [[]\<^sub>\<circ>, a, f]\<^sub>\<circ>"
      and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>"
      and f: "f : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>" 
    by auto
  from assms a f show "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<in>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
    by 
      (
        cs_concl
          cs_simp: cat_comma_cs_simps A_def
          cs_intro: cat_cs_intros cat_comma_cs_intros
      )
qed (cs_concl cs_intro: cat_comma_cs_intros)


subsubsection\<open>Arrow map\<close>

mk_VLambda cf_cf_arr_comma_components(2)
  |vsv cf_cf_arr_comma_ArrMap_vsv[cat_comma_cs_intros]|

context is_functor
begin

context 
  fixes g c c'
  assumes g: "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'"
begin

mk_VLambda 
  cf_cf_arr_comma_components'(2)[OF g, unfolded VLambda_vid_on[symmetric]]
  |vdomain cf_cf_arr_comma_ArrMap_vdomain[cat_comma_cs_simps]|

end

end

lemmas [cat_comma_cs_simps] = is_functor.cf_cf_arr_comma_ArrMap_vdomain

lemma (in is_functor) cf_cf_arr_comma_ArrMap_app[cat_comma_cs_simps]:
  assumes "A = [[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [h, k]\<^sub>\<circ>]\<^sub>\<circ>"
    and "[[a, b, f]\<^sub>\<circ>, [a', b', f']\<^sub>\<circ>, [h, k]\<^sub>\<circ>]\<^sub>\<circ> :
    [a, b, f]\<^sub>\<circ> \<mapsto>\<^bsub>c' \<down>\<^sub>C\<^sub>F \<FF>\<^esub> [a', b', f']\<^sub>\<circ>" 
    and "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'"
  shows "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>A\<rparr> =
    [[a, b, f \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g]\<^sub>\<circ>, [a', b', f' \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> g]\<^sub>\<circ>, [h, k]\<^sub>\<circ>]\<^sub>\<circ>"
proof-
  from assms(3) have c': "c' \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>" by auto
  from 
    cat_obj_cf_comma_is_arrD(1,2)[OF assms(2)[unfolded cat_comma_cs_simps] c'] 
    is_arrD(1)[OF assms(2)] 
  show ?thesis
    unfolding assms(1) cf_cf_arr_comma_components'[OF assms(3)]
    by (simp_all add: nat_omega_simps)
qed


subsubsection\<open>Comma functors are functors\<close>

lemma (in is_functor) cf_cf_arr_comma_is_functor:
  assumes "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'"
  shows "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF> : c' \<down>\<^sub>C\<^sub>F \<FF> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> c \<down>\<^sub>C\<^sub>F \<FF>"
proof-
  show ?thesis
  proof(rule is_functorI')
    show "vfsequence (g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)" unfolding cf_cf_arr_comma_def by simp
    from assms show "category \<alpha> (c' \<down>\<^sub>C\<^sub>F \<FF>)"
      by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
    from assms show "category \<alpha> (c \<down>\<^sub>C\<^sub>F \<FF>)"
      by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
    show "vcard (g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>) = 4\<^sub>\<nat>"
      unfolding  cf_cf_arr_comma_def by (simp_all add: nat_omega_simps)
    from assms show "\<R>\<^sub>\<circ> (g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>) \<subseteq>\<^sub>\<circ> c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by (intro cf_cf_arr_comma_ObjMap_vrange)
    show "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> :
      g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> \<mapsto>\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>B\<rparr>"
      if "F : A \<mapsto>\<^bsub>c' \<down>\<^sub>C\<^sub>F \<FF>\<^esub> B" for A B F
    proof-
      from assms that obtain b f b' f' k 
        where F_def: "F = [[0, b, f]\<^sub>\<circ>, [0, b', f']\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [0, b, f]\<^sub>\<circ>"
          and B_def: "B = [0, b', f']\<^sub>\<circ>"
          and k: "k : b \<mapsto>\<^bsub>\<AA>\<^esub> b'"
          and f: "f : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and f': "f' : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and f'_def: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
        by auto
      from assms that k f f' show ?thesis
        unfolding F_def A_def B_def
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps f'_def[symmetric]
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed
    show "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>G \<circ>\<^sub>A\<^bsub>c' \<down>\<^sub>C\<^sub>F \<FF>\<^esub> F\<rparr> =
      g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>G\<rparr> \<circ>\<^sub>A\<^bsub>c \<down>\<^sub>C\<^sub>F \<FF>\<^esub> g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
      if "G : B \<mapsto>\<^bsub>c' \<down>\<^sub>C\<^sub>F \<FF>\<^esub> C" and "F : A \<mapsto>\<^bsub>c' \<down>\<^sub>C\<^sub>F \<FF>\<^esub> B" for B C G A F
    proof-
      from that(2) assms obtain b f b' f' k 
        where F_def: "F = [[0, b, f]\<^sub>\<circ>, [0, b', f']\<^sub>\<circ>, [0, k]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [0, b, f]\<^sub>\<circ>"
          and B_def: "B = [0, b', f']\<^sub>\<circ>"
          and k: "k : b \<mapsto>\<^bsub>\<AA>\<^esub> b'"
          and f: "f : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b\<rparr>"
          and f': "f' : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and f'_def: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>k\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f = f'"
        by auto
      with that(1) assms obtain b'' f'' k' 
        where G_def: "G = [[0, b', f']\<^sub>\<circ>, [0, b'', f'']\<^sub>\<circ>, [0, k']\<^sub>\<circ>]\<^sub>\<circ>"
          and C_def: "C = [0, b'', f'']\<^sub>\<circ>"
          and k': "k' : b' \<mapsto>\<^bsub>\<AA>\<^esub> b''"
          and f'': "f'' : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
          and f''_def: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>k'\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f' = f''"
        by auto (*slow*)
      from assms that k f f' f'' k' show ?thesis
        unfolding F_def G_def A_def B_def C_def 
        by (*slow*)
          (
            cs_concl
              cs_simp:
                cat_cs_simps cat_comma_cs_simps
                f''_def[symmetric] f'_def[symmetric]
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed
    show "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>c' \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>\<lparr>C\<rparr>\<rparr> = c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>\<lparr>g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>C\<rparr>\<rparr>"
      if "C \<in>\<^sub>\<circ> c' \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>" for C
    proof-
      from that assms obtain a f 
        where C_def: "C = [0, a, f]\<^sub>\<circ>"
          and a: "a \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and f: "f : c' \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a\<rparr>"
        by auto
      from a assms f show
        "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>c' \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>\<lparr>C\<rparr>\<rparr> = c \<down>\<^sub>C\<^sub>F \<FF>\<lparr>CId\<rparr>\<lparr>g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>C\<rparr>\<rparr>"
        unfolding C_def 
        by
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed
  qed
    (
      use assms in
        \<open>
          cs_concl
            cs_simp: cat_comma_cs_simps
            cs_intro: cat_cs_intros cat_comma_cs_intros
        \<close>
    )+
qed

lemma (in is_functor) cf_cf_arr_comma_is_functor'[cat_comma_cs_intros]:
  assumes "g : c \<mapsto>\<^bsub>\<BB>\<^esub> c'" and "\<AA>' = c' \<down>\<^sub>C\<^sub>F \<FF>" and "\<BB>' = c \<down>\<^sub>C\<^sub>F \<FF>"
  shows "g \<^sub>A\<down>\<^sub>C\<^sub>F \<FF> : \<AA>' \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<BB>'"
  using assms(1) unfolding assms(2,3) by (rule cf_cf_arr_comma_is_functor(1))

lemmas [cat_comma_cs_intros] = is_functor.cf_cf_arr_comma_is_functor'

lemma (in is_functor) cf_cf_arr_comma_CId:
  assumes "b \<in>\<^sub>\<circ> \<BB>\<lparr>Obj\<rparr>"
  shows "(\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF> = cf_id (b \<down>\<^sub>C\<^sub>F \<FF>)"
proof-

  show ?thesis
  proof(rule cf_eqI)
    from vempty_is_zet assms show "cf_id (b \<down>\<^sub>C\<^sub>F \<FF>) : b \<down>\<^sub>C\<^sub>F \<FF> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> b \<down>\<^sub>C\<^sub>F \<FF>"
      by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
    from vempty_is_zet assms show "(\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF> : b \<down>\<^sub>C\<^sub>F \<FF> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> b \<down>\<^sub>C\<^sub>F \<FF>"
      by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
    from assms have ObjMap_dom_lhs: 
      "\<D>\<^sub>\<circ> ((\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_cs_intros)
    from assms have ObjMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (dghm_id (b \<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)
    show "(\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr> = cf_id (b \<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
      fix A assume prems: "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      with assms obtain a' f' 
        where A_def: "A = [0, a', f']\<^sub>\<circ>"
          and a': "a' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and f': "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>a'\<rparr>"
        by auto
      from prems assms vempty_is_zet a' f' show 
        "(\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = cf_id (b \<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
        unfolding A_def
        by 
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps 
              cs_intro: cat_cs_intros
          )
    qed (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)+

    from assms have ArrMap_dom_lhs: 
      "\<D>\<^sub>\<circ> ((\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_comma_cs_simps cs_intro: cat_cs_intros)
    from assms have ArrMap_dom_rhs: 
      "\<D>\<^sub>\<circ> (dghm_id (b \<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_cs_simps cs_intro: cat_cs_intros)

    show "(\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr> = cf_id (b \<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix F assume prems: "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
      then obtain A B where F: "F : A \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> B" by (auto dest: is_arrI)
      from assms F obtain b' f' b'' f'' h
        where F_def: "F = [[0, b', f']\<^sub>\<circ>, [0, b'', f'']\<^sub>\<circ>, [0, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [0, b', f']\<^sub>\<circ>"
          and B_def: "B = [0, b'', f'']\<^sub>\<circ>"
          and h: "h : b' \<mapsto>\<^bsub>\<AA>\<^esub> b''"
          and f': "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and f'': "f'' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
          and "\<FF>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f' = f''"
        by auto
      from assms prems F h f' f'' show 
        "(\<BB>\<lparr>CId\<rparr>\<lparr>b\<rparr>) \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> = cf_id (b \<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
        unfolding F_def A_def B_def
        by 
          (
            cs_concl
              cs_simp: cat_comma_cs_simps cat_cs_simps cs_intro: cat_cs_intros
          )
    qed (cs_concl cs_intro: cat_comma_cs_intros cat_cs_intros)+

  qed simp_all

qed


subsubsection\<open>Comma functors and projections\<close>

lemma (in is_functor) 
  cf_cf_comp_cf_obj_cf_comma_proj_cf_cf_arr_comma[cat_comma_cs_simps]: 
  assumes "f : a \<mapsto>\<^bsub>\<BB>\<^esub> b"
  shows "a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF> = b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>"
proof-

  show ?thesis
  proof(rule cf_eqI)
    from assms vempty_is_zet show "b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> : b \<down>\<^sub>C\<^sub>F \<FF> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
    from assms show 
      "a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF> : b \<down>\<^sub>C\<^sub>F \<FF> \<mapsto>\<mapsto>\<^sub>C\<^bsub>\<alpha>\<^esub> \<AA>"
      by (cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros)
    from assms have ObjMap_dom_lhs:
      "\<D>\<^sub>\<circ> ((a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by 
        ( 
          cs_concl 
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_comma_cs_intros
        )
    from assms have ObjMap_dom_rhs: "\<D>\<^sub>\<circ> (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_comma_cs_simps)
    show "(a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr> = b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>"
    proof(rule vsv_eqI, unfold ObjMap_dom_lhs ObjMap_dom_rhs)
      from assms show "vsv (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>)"
        by (cs_concl cs_intro: cat_comma_cs_intros)
      fix A assume prems: "A \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      with assms obtain b' f' 
        where A_def: "A = [0, b', f']\<^sub>\<circ>"
          and b': "b' \<in>\<^sub>\<circ> \<AA>\<lparr>Obj\<rparr>" 
          and f': "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
        by auto
      from prems assms b' f' show 
        "(a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>\<lparr>A\<rparr> = b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>\<lparr>A\<rparr>"
        unfolding A_def
        by 
          (
            cs_concl 
              cs_simp: cat_cs_simps cat_comma_cs_simps 
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )
    qed
      (
        use assms vempty_is_zet in
          \<open>cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros\<close>
      )
    from assms have ArrMap_dom_lhs:
      "\<D>\<^sub>\<circ> ((a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ObjMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_comma_cs_intros
        )
    from assms vempty_is_zet have ArrMap_dom_rhs:
      "\<D>\<^sub>\<circ> (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ObjMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Obj\<rparr>"
      by (cs_concl cs_simp: cat_comma_cs_simps)
    from assms vempty_is_zet have ArrMap_dom_lhs:
      "\<D>\<^sub>\<circ> ((a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
      by
        (
          cs_concl
            cs_simp: cat_cs_simps cs_intro: cat_cs_intros cat_comma_cs_intros
        )
    from assms have ArrMap_dom_rhs:
      "\<D>\<^sub>\<circ> (b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>) = b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
      by (cs_concl cs_simp: cat_comma_cs_simps)
    show "(a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr> = b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>"
    proof(rule vsv_eqI, unfold ArrMap_dom_lhs ArrMap_dom_rhs)
      fix F assume "F \<in>\<^sub>\<circ> b \<down>\<^sub>C\<^sub>F \<FF>\<lparr>Arr\<rparr>"
      then obtain A B where F: "F : A \<mapsto>\<^bsub>b \<down>\<^sub>C\<^sub>F \<FF>\<^esub> B"
        by (auto dest: is_arrI)
      with assms obtain b' f' b'' f'' h
        where F_def: "F = [[0, b', f']\<^sub>\<circ>, [0, b'', f'']\<^sub>\<circ>, [0, h]\<^sub>\<circ>]\<^sub>\<circ>"
          and A_def: "A = [0, b', f']\<^sub>\<circ>"
          and B_def: "B = [0, b'', f'']\<^sub>\<circ>"
          and h: "h : b' \<mapsto>\<^bsub>\<AA>\<^esub> b''"
          and f': "f' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b'\<rparr>"
          and f'': "f'' : b \<mapsto>\<^bsub>\<BB>\<^esub> \<FF>\<lparr>ObjMap\<rparr>\<lparr>b''\<rparr>"
          and f''_def: "\<FF>\<lparr>ArrMap\<rparr>\<lparr>h\<rparr> \<circ>\<^sub>A\<^bsub>\<BB>\<^esub> f' = f''"
        by auto
      from vempty_is_zet h assms f' f'' F show
        "(a \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF> \<circ>\<^sub>C\<^sub>F f \<^sub>A\<down>\<^sub>C\<^sub>F \<FF>)\<lparr>ArrMap\<rparr>\<lparr>F\<rparr> = b \<^sub>O\<Sqinter>\<^sub>C\<^sub>F \<FF>\<lparr>ArrMap\<rparr>\<lparr>F\<rparr>"
        unfolding F_def A_def B_def 
        by (*slow*)
          (
            cs_concl
              cs_simp: cat_cs_simps cat_comma_cs_simps f''_def[symmetric]
              cs_intro: cat_cs_intros cat_comma_cs_intros
          )+
    qed
      (
        use assms vempty_is_zet in
          \<open>cs_concl cs_intro: cat_cs_intros cat_comma_cs_intros\<close>
      )
  qed simp_all

qed

text\<open>\newpage\<close>

end