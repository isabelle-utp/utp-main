(* Copyright 2021 (C) Mihails Milehins *)

section\<open>Digraph\label{sec:digraph}\<close>
theory CZH_DG_Digraph
  imports CZH_DG_Introduction
begin



subsection\<open>Background\<close>

named_theorems dg_field_simps

definition Obj :: V where [dg_field_simps]: "Obj = 0"
definition Arr :: V where [dg_field_simps]: "Arr = 1\<^sub>\<nat>"
definition Dom :: V where [dg_field_simps]: "Dom = 2\<^sub>\<nat>"
definition Cod :: V where [dg_field_simps]: "Cod = 3\<^sub>\<nat>"



subsection\<open>Arrow with a domain and a codomain\<close>


text\<open>
The definition of and notation for an arrow with a domain and codomain is
adapted from Chapter I-1 in \cite{mac_lane_categories_2010}.
The definition is applicable to digraphs and all other relevant derived
entities, such as semicategories and categories, that are presented in
the subsequent chapters.

In this work, by convention, the definition of an arrow with a domain and a 
codomain is nearly always preferred to the explicit use of the domain 
and codomain functions for the specification of the fundamental properties 
of arrows.
Thus, to say that \<open>f\<close> is an arrow with the domain \<open>a\<close>, it is preferable
to write \<open>f : a \<mapsto>\<^bsub>\<CC>\<^esub> b\<close> (\<open>b\<close> can be assumed to be arbitrary) instead
of \<^term>\<open>f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>\<close> and \<^term>\<open>\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a\<close>.
\<close>

definition is_arr :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool"
  where "is_arr \<CC> a b f \<longleftrightarrow> f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<and> \<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a \<and> \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b"

syntax "_is_arr" :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> bool" (\<open>_ : _ \<mapsto>\<index> _\<close> [51, 51, 51] 51)
translations "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" \<rightleftharpoons> "CONST is_arr \<CC> a b f"


text\<open>Rules.\<close>

mk_ide is_arr_def
  |intro is_arrI|
  |dest is_arrD[dest]|
  |elim is_arrE[elim]|

lemmas [dg_shared_cs_intros, dg_cs_intros] = is_arrD(1)
lemmas [dg_shared_cs_simps, dg_cs_simps] = is_arrD(2,3)



subsection\<open>\<open>Hom\<close>-set\<close>


text\<open>See Chapter I-8 in \cite{mac_lane_categories_2010}.\<close>

abbreviation Hom :: "V \<Rightarrow> V \<Rightarrow> V \<Rightarrow> V" 
  where "Hom \<CC> a b \<equiv> set {f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b}"

lemma small_Hom[simp]: "small {f. f : a \<mapsto>\<^bsub>\<CC>\<^esub> b}" unfolding is_arr_def by simp


text\<open>Rules.\<close>

lemma HomI[dg_shared_cs_intros, dg_cs_intros]:
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  shows "f \<in>\<^sub>\<circ> Hom \<CC> a b"
  using assms by auto

lemma in_Hom_iff[dg_shared_cs_simps, dg_cs_simps]: 
  "f \<in>\<^sub>\<circ> Hom \<CC> a b \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  by simp


text\<open>
The \<open>Hom\<close>-sets in a given digraph are pairwise disjoint. This property 
was exposed as Axiom (v) in an alternative definition of a category presented 
in Chapter I-8 in \cite{mac_lane_categories_2010}. Within the scope of the 
definitional framework employed in this study, this property holds 
unconditionally.
\<close>

lemma Hom_vdisjnt: 
  assumes "a \<noteq> a' \<or> b \<noteq> b'" 
    and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "a' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" 
    and "b' \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "vdisjnt (Hom \<CC> a b) (Hom \<CC> a' b')"
proof(intro vdisjntI, unfold in_Hom_iff)
  fix g f assume "g : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "f : a' \<mapsto>\<^bsub>\<CC>\<^esub> b'" 
  then have "g \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
    and "\<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> = a"
    and "\<CC>\<lparr>Cod\<rparr>\<lparr>g\<rparr> = b"
    and "\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a'"
    and "\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b'"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+
  with assms(1) have "\<CC>\<lparr>Dom\<rparr>\<lparr>g\<rparr> \<noteq> \<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> \<or> \<CC>\<lparr>Cod\<rparr>\<lparr>g\<rparr> \<noteq> \<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr>" by auto
  then show "g \<noteq> f" by clarsimp
qed



subsection\<open>Digraph: background information\<close>


text\<open>
The definition of a digraph that is employed in this work is similar
to the definition of a \<open>directed graph\<close> presented in Chapter I-2 in 
\cite{mac_lane_categories_2010}. However, there are notable differences.
More specifically, the definition is parameterized by a limit ordinal \<open>\<alpha>\<close>, 
such that \<open>\<omega> < \<alpha>\<close>; the set of objects is assumed to be a subset 
of the set \<open>V\<^sub>\<alpha>\<close> in the von Neumann hierarchy of sets (e.g., 
see \cite{takeuti_introduction_1971}). Such digraphs are called \<open>\<alpha>\<close>-\<open>digraphs\<close> 
to make the dependence on the parameter \<open>\<alpha>\<close> explicit.\footnote{
The prefix ``\<open>\<alpha>\<close>-'' may be omitted whenever it is possible to infer the value 
of \<open>\<alpha>\<close> from the context. This applies not only to the digraphs, but all 
other entities that are parameterized by a limit ordinal \<open>\<alpha>\<close> such that 
\<open>\<omega> < \<alpha>\<close>.} This definition was inspired by the ideas expressed in 
\cite{feferman_set-theoretical_1969}, \cite{sica_doing_2006} and
\cite{shulman_set_2008}.

In ZFC in HOL, the predicate \<^term>\<open>small\<close> is used for distinguishing the
terms of any type of the form \<^typ>\<open>'a set\<close> that are isomorphic to elements 
of a term of the type \<^typ>\<open>V\<close> (the elements can be exposed via the predicate
\<^const>\<open>elts\<close>). Thus, the collection of the elements associated with any term of 
the type \<^typ>\<open>V\<close> (e.g., \<^term>\<open>elts (a::V)\<close>) is always small 
(see the theorem @{thm [source] small_elts} in \cite{paulson_zermelo_2019}).
Therefore, in this study, in an attempt to avoid confusion, the term ``small''
is never used to refer to digraphs. 
Instead, a new terminology is introduced in this body of work.

Thus, in this work, an \<open>\<alpha>\<close>-digraph is a tiny \<open>\<alpha>\<close>-digraph if and only if 
the set of its objects and the set of its arrows both belong to the set \<open>V\<^sub>\<alpha>\<close>. 
This notion is similar to the notion of a small category in the sense of 
the definition employed in Chapter I-6 in \cite{mac_lane_categories_2010}, 
if it is assumed that the ``smallness'' is determined with respect to the 
set \<open>V\<^sub>\<alpha>\<close> instead of the universe \<open>U\<close>. Also, in what follows, any member of 
the set \<open>V\<^sub>\<alpha>\<close> will be referred to as an \<open>\<alpha>\<close>-tiny set.

All of the large (i.e. non-tiny) digraphs 
that are considered within the scope of this work have a slightly 
unconventional condition associated with the size of their \<open>Hom\<close>-sets. 
This condition implies that all \<open>Hom\<close>-sets of a digraph 
are tiny, but it is not equivalent to 
all \<open>Hom\<close>-sets being tiny. The condition was introduced in an attempt to
resolve some of the issues related to the lack of an analogue of the 
Axiom Schema of Replacement closed with respect to \<open>V\<^sub>\<alpha>\<close>. 
\<close>



subsection\<open>Digraph: definition and elementary properties\<close>

locale digraph = \<Z> \<alpha> + vfsequence \<CC> + Dom: vsv \<open>\<CC>\<lparr>Dom\<rparr>\<close> + Cod: vsv \<open>\<CC>\<lparr>Cod\<rparr>\<close> 
  for \<alpha> \<CC> +
  assumes dg_length[dg_cs_simps]: "vcard \<CC> = 4\<^sub>\<nat>"  
    and dg_Dom_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) = \<CC>\<lparr>Arr\<rparr>"    
    and dg_Dom_vrange: "\<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and dg_Cod_vdomain[dg_cs_simps]: "\<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) = \<CC>\<lparr>Arr\<rparr>"
    and dg_Cod_vrange: "\<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and dg_Obj_vsubset_Vset: "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and dg_Hom_vifunion_in_Vset[dg_cs_intros]: 
      "\<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow> 
        (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"

lemmas [dg_cs_simps] = 
  digraph.dg_length
  digraph.dg_Dom_vdomain
  digraph.dg_Cod_vdomain

lemmas [dg_cs_intros] = 
  digraph.dg_Hom_vifunion_in_Vset


text\<open>Rules.\<close>

lemma (in digraph) digraph_axioms'[dg_cs_intros]:
  assumes "\<alpha>' = \<alpha>"
  shows "digraph \<alpha>' \<CC>"
  unfolding assms by (rule digraph_axioms)

mk_ide rf digraph_def[unfolded digraph_axioms_def]
  |intro digraphI|
  |dest digraphD[dest]|
  |elim digraphE[elim]|


text\<open>Elementary properties.\<close>

lemma dg_eqI:
  assumes "digraph \<alpha> \<AA>" 
    and "digraph \<alpha> \<BB>"
    and "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>"
    and "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>"
    and "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>"
    and "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
  shows "\<AA> = \<BB>"
proof-
  interpret \<AA>: digraph \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: digraph \<alpha> \<BB> by (rule assms(2))
  show ?thesis
  proof(rule vsv_eqI)
    have dom_lhs: "\<D>\<^sub>\<circ> \<AA> = 4\<^sub>\<nat>" by (cs_concl cs_simp: V_cs_simps dg_cs_simps)
    show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<AA> \<Longrightarrow> \<AA>\<lparr>a\<rparr> = \<BB>\<lparr>a\<rparr>" for a 
      by (unfold dom_lhs, elim_in_numeral, insert assms)
        (auto simp: dg_field_simps)
  qed (cs_concl cs_simp: V_cs_simps dg_cs_simps cs_intro: V_cs_intros)+
qed

lemma (in digraph) dg_def: "\<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>]\<^sub>\<circ>"
proof(rule vsv_eqI)
  have dom_lhs: "\<D>\<^sub>\<circ> \<CC> = 4\<^sub>\<nat>" by (cs_concl cs_simp: V_cs_simps dg_cs_simps)
  have dom_rhs: "\<D>\<^sub>\<circ> [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>]\<^sub>\<circ> = 4\<^sub>\<nat>"
    by (simp add: nat_omega_simps)
  then show "\<D>\<^sub>\<circ> \<CC> = \<D>\<^sub>\<circ> [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>]\<^sub>\<circ>"
    unfolding dom_lhs dom_rhs by simp
  show "a \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> \<CC> \<Longrightarrow> \<CC>\<lparr>a\<rparr> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Dom\<rparr>, \<CC>\<lparr>Cod\<rparr>]\<^sub>\<circ>\<lparr>a\<rparr>" for a
    by (unfold dom_lhs, elim_in_numeral, unfold dg_field_simps)
      (simp_all add: nat_omega_simps)
qed (auto simp: vsv_axioms)

lemma (in digraph) dg_Obj_if_Dom_vrange:
  assumes "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>)"
  shows "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms dg_Dom_vrange by auto

lemma (in digraph) dg_Obj_if_Cod_vrange:
  assumes "a \<in>\<^sub>\<circ> \<R>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>)"
  shows "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms dg_Cod_vrange by auto

lemma (in digraph) dg_is_arrD:
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  shows "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a" 
    and "\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b"
proof-
  from assms show prems: "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
    and fa[symmetric]: "\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a"
    and fb[symmetric]: "\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b"
    by (cs_concl cs_simp: dg_cs_simps cs_intro: dg_cs_intros)+
  from digraph_axioms prems have "f \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Dom\<rparr>)" "f \<in>\<^sub>\<circ> \<D>\<^sub>\<circ> (\<CC>\<lparr>Cod\<rparr>)"
    by (cs_concl cs_simp: dg_cs_simps)+
  with assms show "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"  
    by 
      (
        cs_concl 
          cs_intro: dg_Obj_if_Dom_vrange dg_Obj_if_Cod_vrange V_cs_intros
          cs_simp: fa fb
      )+
qed

lemmas [dg_cs_intros] = digraph.dg_is_arrD(1-3)

lemma (in digraph) dg_is_arrE[elim]:
  assumes "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" 
  obtains "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" 
    and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    and "\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> = a" 
    and "\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr> = b"
  using assms by (blast dest: dg_is_arrD)

lemma (in digraph) dg_in_ArrE[elim]:
  assumes "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  obtains a b where "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms by (auto dest: dg_is_arrD(2,3) is_arrI)

lemma (in digraph) dg_Hom_in_Vset[dg_cs_intros]: 
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "Hom \<CC> a b \<in>\<^sub>\<circ> Vset \<alpha>"
proof-
  let ?A = \<open>set {a}\<close> and ?B = \<open>set {b}\<close>
  from assms have A: "?A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and B: "?B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" by auto
  from assms dg_Obj_vsubset_Vset have "a \<in>\<^sub>\<circ> Vset \<alpha>" and "b \<in>\<^sub>\<circ> Vset \<alpha>" by auto
  then have a: "set {a} \<in>\<^sub>\<circ> Vset \<alpha>" and b: "set {b} \<in>\<^sub>\<circ> Vset \<alpha>" 
    by (metis Axiom_of_Pairing insert_absorb2)+
  from dg_Hom_vifunion_in_Vset[OF A B a b] show "Hom \<CC> a b \<in>\<^sub>\<circ> Vset \<alpha>" by simp
qed

lemmas [dg_cs_intros] = digraph.dg_Hom_in_Vset


text\<open>Size.\<close>

lemma (in digraph) dg_Arr_vsubset_Vset: "\<CC>\<lparr>Arr\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
proof(intro vsubsetI)
  fix f assume "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  then obtain a b 
    where f: "f : a \<mapsto>\<^bsub>\<CC>\<^esub> b" and a: "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" and b: "b \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
    by blast
  show "f \<in>\<^sub>\<circ> Vset \<alpha>"
    by (rule Vset_trans, rule HomI[OF f], rule dg_Hom_in_Vset[OF a b])
qed

lemma (in digraph) dg_Dom_vsubset_Vset: "\<CC>\<lparr>Dom\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by 
    (
      rule Dom.vbrelation_Limit_vsubset_VsetI, 
      unfold dg_cs_simps, 
      insert dg_Dom_vrange dg_Obj_vsubset_Vset
    )
    (auto intro!: dg_Arr_vsubset_Vset)

lemma (in digraph) dg_Cod_vsubset_Vset: "\<CC>\<lparr>Cod\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
  by 
    (
      rule Cod.vbrelation_Limit_vsubset_VsetI, 
      unfold dg_cs_simps, 
      insert dg_Cod_vrange dg_Obj_vsubset_Vset
    )
    (auto intro!: dg_Arr_vsubset_Vset)

lemma (in digraph) dg_digraph_in_Vset_4: "\<CC> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
proof-
  note [folded VPow_iff, folded Vset_succ[OF Ord_\<alpha>], dg_cs_intros] =
    dg_Obj_vsubset_Vset
    dg_Arr_vsubset_Vset
    dg_Dom_vsubset_Vset
    dg_Cod_vsubset_Vset
  show ?thesis
    by (subst dg_def, succ_of_numeral)
      (
        cs_concl 
          cs_simp: plus_V_succ_right V_cs_simps 
          cs_intro: dg_cs_intros V_cs_intros
      )
qed

lemma (in digraph) dg_Obj_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC>\<lparr>Obj\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms dg_Obj_vsubset_Vset Vset_in_mono by auto

lemma (in digraph) dg_in_Obj_in_Vset[dg_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms dg_Obj_vsubset_Vset by auto

lemma (in digraph) dg_Arr_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC>\<lparr>Arr\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  using assms dg_Arr_vsubset_Vset Vset_in_mono by auto

lemma (in digraph) dg_in_Arr_in_Vset[dg_cs_intros]:
  assumes "a \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "a \<in>\<^sub>\<circ> Vset \<alpha>"
  using assms dg_Arr_vsubset_Vset by auto

lemma (in digraph) dg_Dom_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC>\<lparr>Dom\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  by (meson assms dg_Dom_vsubset_Vset Vset_in_mono vsubset_in_VsetI)

lemma (in digraph) dg_Cod_in_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC>\<lparr>Cod\<rparr> \<in>\<^sub>\<circ> Vset \<beta>"
  by (meson assms dg_Cod_vsubset_Vset Vset_in_mono vsubset_in_VsetI)

lemma (in digraph) dg_in_Vset:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "\<CC> \<in>\<^sub>\<circ> Vset \<beta>"
proof-
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  note [dg_cs_intros] = 
    dg_Obj_in_Vset dg_Arr_in_Vset dg_Dom_in_Vset dg_Cod_in_Vset 
  from assms(2) show ?thesis
     by (subst dg_def) (cs_concl cs_intro: dg_cs_intros V_cs_intros)
 qed

lemma (in digraph) dg_digraph_if_ge_Limit:
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "digraph \<beta> \<CC>"
proof(rule digraphI)
  show "vfsequence \<CC>" by (simp add: vfsequence_axioms)
  show "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<beta>"
    by (rule vsubsetI) 
      (meson Vset_in_mono Vset_trans assms(2) dg_Obj_vsubset_Vset vsubsetE)
  fix A B assume "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "A \<in>\<^sub>\<circ> Vset \<beta>" "B \<in>\<^sub>\<circ> Vset \<beta>"
  then have "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>" by auto
  moreover note dg_Arr_vsubset_Vset
  moreover have "Vset \<alpha> \<in>\<^sub>\<circ> Vset \<beta>" by (simp add: Vset_in_mono assms(2))
  ultimately show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<beta>" by auto
qed (auto simp: assms(1) dg_Dom_vrange dg_Cod_vrange dg_cs_simps)

lemma small_digraph[simp]: "small {\<CC>. digraph \<alpha> \<CC>}"
proof(cases \<open>\<Z> \<alpha>\<close>)
  case True
  with digraph.dg_in_Vset show ?thesis
    by (intro down[of _ \<open>Vset (\<alpha> + \<omega>)\<close>] subsetI)
      (auto simp: \<Z>.\<Z>_Limit_\<alpha>\<omega> \<Z>.\<Z>_\<omega>_\<alpha>\<omega> \<Z>.intro \<Z>.\<Z>_\<alpha>_\<alpha>\<omega>)
next
  case False
  then have "{\<CC>. digraph \<alpha> \<CC>} = {}" by auto
  then show ?thesis by simp
qed

lemma (in \<Z>) digraphs_in_Vset: 
  assumes "\<Z> \<beta>" and "\<alpha> \<in>\<^sub>\<circ> \<beta>"
  shows "set {\<CC>. digraph \<alpha> \<CC>} \<in>\<^sub>\<circ> Vset \<beta>"
proof(rule vsubset_in_VsetI)
  interpret \<beta>: \<Z> \<beta> by (rule assms(1))
  show "set {\<CC>. digraph \<alpha> \<CC>} \<subseteq>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
  proof(intro vsubsetI)
    fix \<CC> assume "\<CC> \<in>\<^sub>\<circ> set {\<CC>. digraph \<alpha> \<CC>}"
    then interpret digraph \<alpha> \<CC> by simp
    show "\<CC> \<in>\<^sub>\<circ> Vset (\<alpha> + 4\<^sub>\<nat>)"
      unfolding VPow_iff by (rule dg_digraph_in_Vset_4)
  qed
  from assms(2) show "Vset (\<alpha> + 4\<^sub>\<nat>) \<in>\<^sub>\<circ> Vset \<beta>"
    by (cs_concl cs_intro: V_cs_intros Ord_cs_intros)
qed

lemma digraph_if_digraph:
  assumes "digraph \<beta> \<CC>"
    and "\<Z> \<alpha>"
    and "\<CC>\<lparr>Obj\<rparr> \<subseteq>\<^sub>\<circ> Vset \<alpha>"
    and "\<And>A B. \<lbrakk> A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>; A \<in>\<^sub>\<circ> Vset \<alpha>; B \<in>\<^sub>\<circ> Vset \<alpha> \<rbrakk> \<Longrightarrow>
      (\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
  shows "digraph \<alpha> \<CC>"
proof-
  interpret digraph \<beta> \<CC> by (rule assms(1))
  interpret \<alpha>: \<Z> \<alpha> by (rule assms(2))
  show ?thesis
  proof(intro digraphI)
    show "vfsequence \<CC>" by (simp add: vfsequence_axioms)
    show "(\<Union>\<^sub>\<circ>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>b\<in>\<^sub>\<circ>B. Hom \<CC> a b) \<in>\<^sub>\<circ> Vset \<alpha>"
      if "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "A \<in>\<^sub>\<circ> Vset \<alpha>" "B \<in>\<^sub>\<circ> Vset \<alpha>" for A B
      by (rule assms(4)[OF that])
  qed (auto simp: assms(3) dg_Cod_vrange dg_cs_simps intro!: dg_Dom_vrange)
qed


text\<open>Further elementary properties.\<close>

lemma (in digraph) dg_Dom_app_in_Obj:
  assumes "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "\<CC>\<lparr>Dom\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms dg_Dom_vrange by (auto simp: Dom.vsv_vimageI2)

lemma (in digraph) dg_Cod_app_in_Obj:
  assumes "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr>"
  shows "\<CC>\<lparr>Cod\<rparr>\<lparr>f\<rparr> \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>"
  using assms dg_Cod_vrange by (auto simp: Cod.vsv_vimageI2)

lemma (in digraph) dg_Arr_vempty_if_Obj_vempty:
  assumes "\<CC>\<lparr>Obj\<rparr> = 0"
  shows "\<CC>\<lparr>Arr\<rparr> = 0"
  by (metis assms eq0_iff dg_Cod_app_in_Obj)

lemma (in digraph) dg_Dom_vempty_if_Arr_vempty:
  assumes "\<CC>\<lparr>Arr\<rparr> = 0"
  shows "\<CC>\<lparr>Dom\<rparr> = 0"
  using assms Dom.vdomain_vrange_is_vempty 
  by (auto intro: Dom.vsv_vrange_vempty simp: dg_cs_simps)

lemma (in digraph) dg_Cod_vempty_if_Arr_vempty:
  assumes "\<CC>\<lparr>Arr\<rparr> = 0"
  shows "\<CC>\<lparr>Cod\<rparr> = 0"
  using assms Cod.vdomain_vrange_is_vempty 
  by (auto intro: Cod.vsv_vrange_vempty simp: dg_cs_simps)



subsection\<open>Opposite digraph\<close>


subsubsection\<open>Definition and elementary properties\<close>


text\<open>See Chapter II-2 in \cite{mac_lane_categories_2010}.\<close>

definition op_dg :: "V \<Rightarrow> V"
  where "op_dg \<CC> = [\<CC>\<lparr>Obj\<rparr>, \<CC>\<lparr>Arr\<rparr>, \<CC>\<lparr>Cod\<rparr>, \<CC>\<lparr>Dom\<rparr>]\<^sub>\<circ>"


text\<open>Components.\<close>

lemma op_dg_components[dg_op_simps]:
  shows "op_dg \<CC>\<lparr>Obj\<rparr> = \<CC>\<lparr>Obj\<rparr>"
    and "op_dg \<CC>\<lparr>Arr\<rparr> = \<CC>\<lparr>Arr\<rparr>"
    and "op_dg \<CC>\<lparr>Dom\<rparr> = \<CC>\<lparr>Cod\<rparr>"
    and "op_dg \<CC>\<lparr>Cod\<rparr> = \<CC>\<lparr>Dom\<rparr>"
  unfolding op_dg_def dg_field_simps by (auto simp: nat_omega_simps)

lemma op_dg_component_intros[dg_op_intros]:
  shows "a \<in>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr> \<Longrightarrow> a \<in>\<^sub>\<circ> op_dg \<CC>\<lparr>Obj\<rparr>"
    and "f \<in>\<^sub>\<circ> \<CC>\<lparr>Arr\<rparr> \<Longrightarrow> f \<in>\<^sub>\<circ> op_dg \<CC>\<lparr>Arr\<rparr>"
  unfolding dg_op_simps by simp_all


text\<open>Elementary properties.\<close>

lemma op_dg_is_arr[dg_op_simps]: "f : b \<mapsto>\<^bsub>op_dg \<CC>\<^esub> a \<longleftrightarrow> f : a \<mapsto>\<^bsub>\<CC>\<^esub> b"
  unfolding dg_op_simps is_arr_def by auto

lemmas [dg_op_intros] = op_dg_is_arr[THEN iffD2]

lemma op_dg_Hom[dg_op_simps]: "Hom (op_dg \<CC>) a b = Hom \<CC> b a"
  unfolding dg_op_simps by simp


subsubsection\<open>Further properties\<close>

lemma (in digraph) digraph_op[dg_op_intros]: "digraph \<alpha> (op_dg \<CC>)"
proof(intro digraphI, unfold op_dg_components dg_op_simps)
  show "vfsequence (op_dg \<CC>)" unfolding op_dg_def by simp
  show "vcard (op_dg \<CC>) = 4\<^sub>\<nat>"
    unfolding op_dg_def by (simp add: nat_omega_simps)
  fix A B assume "A \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "B \<subseteq>\<^sub>\<circ> \<CC>\<lparr>Obj\<rparr>" "A \<in>\<^sub>\<circ> Vset \<alpha>" "B \<in>\<^sub>\<circ> Vset \<alpha>"
  then show "\<Union>\<^sub>\<circ>((\<lambda>a\<in>\<^sub>\<circ>A. \<Union>\<^sub>\<circ>((\<lambda>aa\<in>\<^sub>\<circ>B. Hom \<CC> aa a) `\<^sub>\<circ> B)) `\<^sub>\<circ> A) \<in>\<^sub>\<circ> Vset \<alpha>"
    by (subst vifunion_vifunion_flip) (intro dg_Hom_vifunion_in_Vset)
qed (auto simp: dg_Dom_vrange dg_Cod_vrange dg_Obj_vsubset_Vset dg_cs_simps)

lemmas digraph_op[dg_op_intros] = digraph.digraph_op

lemma (in digraph) dg_op_dg_op_dg[dg_op_simps]: "op_dg (op_dg \<CC>) = \<CC>"
  by (rule dg_eqI[of \<alpha>], unfold dg_op_simps)
    (simp_all add: digraph_axioms digraph.digraph_op digraph_op)

lemmas dg_op_dg_op_dg[dg_op_simps] = digraph.dg_op_dg_op_dg

lemma eq_op_dg_iff[dg_op_simps]: 
  assumes "digraph \<alpha> \<AA>" and "digraph \<alpha> \<BB>"
  shows "op_dg \<AA> = op_dg \<BB> \<longleftrightarrow> \<AA> = \<BB>"
proof
  interpret \<AA>: digraph \<alpha> \<AA> by (rule assms(1))
  interpret \<BB>: digraph \<alpha> \<BB> by (rule assms(2))
  assume prems: "op_dg \<AA> = op_dg \<BB>"
  show "\<AA> = \<BB>"
  proof(rule dg_eqI[of \<alpha>])
    from prems show 
      "\<AA>\<lparr>Obj\<rparr> = \<BB>\<lparr>Obj\<rparr>" "\<AA>\<lparr>Arr\<rparr> = \<BB>\<lparr>Arr\<rparr>" "\<AA>\<lparr>Dom\<rparr> = \<BB>\<lparr>Dom\<rparr>" "\<AA>\<lparr>Cod\<rparr> = \<BB>\<lparr>Cod\<rparr>"
      by (metis prems \<AA>.dg_op_dg_op_dg \<BB>.dg_op_dg_op_dg)+
  qed (simp_all add: assms)
qed auto

text\<open>\newpage\<close>

end