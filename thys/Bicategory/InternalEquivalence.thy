(*  Title:       InternalEquivalence
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Internal Equivalences"

theory InternalEquivalence
imports Bicategory
begin

  text \<open>
    An \emph{internal equivalence} in a bicategory consists of antiparallel 1-cells \<open>f\<close> and \<open>g\<close>
    together with invertible 2-cells \<open>\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>\<close> and \<open>\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> src g\<guillemotright>\<close>.
    Objects in a bicategory are said to be \emph{equivalent} if they are connected by an
    internal equivalence.
    In this section we formalize the definition of internal equivalence and the related notions
    ``equivalence map'' and ``equivalent objects'', and we establish some basic facts about
    these notions.
  \<close>

  subsection "Definition of Equivalence"

  text \<open>
    The following locale is defined to prove some basic facts about an equivalence
    (or an adjunction) in a bicategory that are ``syntactic'' in the sense that they depend
    only on the configuration (source, target, domain, codomain) of the arrows
    involved and not on further properties such as the triangle identities (for adjunctions)
    or assumptions about invertibility (for equivalences).  Proofs about adjunctions and
    equivalences become more automatic once we have introduction and simplification rules in
    place about this syntax.
  \<close>

  locale adjunction_data_in_bicategory =
     bicategory +
  fixes f :: 'a
  and g :: 'a
  and \<eta> :: 'a
  and \<epsilon> :: 'a
  assumes ide_left [simp]: "ide f"
  and ide_right [simp]: "ide g"
  and unit_in_vhom: "\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>"
  and counit_in_vhom: "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> src g\<guillemotright>"
  begin

    (*
     * TODO: It is difficult to orient the following equations to make them useful as
     * default simplifications, so they have to be cited explicitly where they are used.
     *)
    lemma antipar (*[simp]*):
    shows "trg g = src f" and "src g = trg f"
      apply (metis counit_in_vhom ideD(1) ide_right iso_is_arr not_arr_null
                   seq_if_composable src.components_are_iso trg.is_extensional trg_src
                   vconn_implies_hpar(4))
      by (metis horizontal_homs.vconn_implies_hpar(4) horizontal_homs_axioms ideD(1)
                ide_left iso_is_arr not_arr_null seq_if_composable src.components_are_iso
                trg.is_extensional trg_src unit_in_vhom)

    lemma counit_in_hom [intro]:
    shows "\<guillemotleft>\<epsilon> : trg f \<rightarrow> trg f\<guillemotright>" and "\<guillemotleft>\<epsilon> : f \<star> g \<Rightarrow> trg f\<guillemotright>"
      using counit_in_vhom vconn_implies_hpar antipar by auto

    lemma unit_in_hom [intro]:
    shows "\<guillemotleft>\<eta> : src f \<rightarrow> src f\<guillemotright>" and "\<guillemotleft>\<eta> : src f \<Rightarrow> g \<star> f\<guillemotright>"
      using unit_in_vhom vconn_implies_hpar antipar by auto

    lemma unit_simps [simp]:
    shows "arr \<eta>" and "dom \<eta> = src f" and "cod \<eta> = g \<star> f"
    and "src \<eta> = src f" and "trg \<eta> = src f"
      using unit_in_hom antipar by auto

    lemma counit_simps [simp]:
    shows "arr \<epsilon>" and "dom \<epsilon> = f \<star> g" and "cod \<epsilon> = trg f"
    and "src \<epsilon> = trg f" and "trg \<epsilon> = trg f"
      using counit_in_hom antipar by auto

    text \<open>
      The expressions found in the triangle identities for an adjunction come up
      relatively frequently, so it is useful to have established some basic facts
      about them, even if the triangle identities themselves have not actually been
      introduced as assumptions in the current context.
    \<close>

    lemma triangle_in_hom:
    shows "\<guillemotleft>(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) : f \<star> src f \<Rightarrow> trg f \<star> f\<guillemotright>"
    and "\<guillemotleft>(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) : trg g \<star> g \<Rightarrow> g \<star> src g\<guillemotright>"
    and "\<guillemotleft>\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] : f \<Rightarrow> f\<guillemotright>"
    and "\<guillemotleft>\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] : g \<Rightarrow> g\<guillemotright>"
      using antipar by auto

    lemma triangle_equiv_form:
    shows "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<longleftrightarrow>
           \<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
    and "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<longleftrightarrow>
         \<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
    proof -
      show "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] \<longleftrightarrow>
            \<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
      proof
        assume 1: "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
        have "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] =
              \<l>[f] \<cdot> ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) \<cdot> \<r>\<^sup>-\<^sup>1[f]"
          using comp_assoc by simp
        also have "... = \<l>[f] \<cdot> (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]) \<cdot> \<r>\<^sup>-\<^sup>1[f]"
          using 1 by simp
        also have "... = f"
          using comp_assoc comp_arr_inv' comp_inv_arr' iso_lunit iso_runit
                comp_arr_dom comp_cod_arr
          by simp
        finally show "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
          by simp
        next
        assume 2: "\<l>[f] \<cdot> (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) \<cdot> \<r>\<^sup>-\<^sup>1[f] = f"
        have "\<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f] = \<l>\<^sup>-\<^sup>1[f] \<cdot> f \<cdot> \<r>[f]"
          using comp_cod_arr by simp
        also have "... = (\<l>\<^sup>-\<^sup>1[f] \<cdot> \<l>[f]) \<cdot> ((\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)) \<cdot> (\<r>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f])"
          using 2 comp_assoc by (metis (no_types, lifting))
        also have "... = (\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>)"
          using comp_arr_inv' comp_inv_arr' iso_lunit iso_runit comp_arr_dom comp_cod_arr
                hseqI' antipar
          by (metis ide_left in_homE lunit_simps(4) runit_simps(4) triangle_in_hom(1))
        finally show "(\<epsilon> \<star> f) \<cdot> \<a>\<^sup>-\<^sup>1[f, g, f] \<cdot> (f \<star> \<eta>) = \<l>\<^sup>-\<^sup>1[f] \<cdot> \<r>[f]"
          by simp
      qed
      show "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] \<longleftrightarrow>
            \<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
      proof
        assume 1: "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
        have "\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] =
              \<r>[g] \<cdot> ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot> \<l>\<^sup>-\<^sup>1[g]"
          using comp_assoc by simp
        also have "... = \<r>[g] \<cdot> (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]) \<cdot> \<l>\<^sup>-\<^sup>1[g]"
          using 1 by simp
        also have "... = g"
          using comp_assoc comp_arr_inv' comp_inv_arr' iso_lunit iso_runit
                comp_arr_dom comp_cod_arr
          by simp
        finally show "\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
          by simp
        next
        assume 2: "\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] = g"
        have "\<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g] = \<r>\<^sup>-\<^sup>1[g] \<cdot> g \<cdot> \<l>[g]"
          using comp_cod_arr by simp
        also have "... = \<r>\<^sup>-\<^sup>1[g] \<cdot> (\<r>[g] \<cdot> (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g]) \<cdot> \<l>[g]"
          using 2 by simp
        also have "... = (\<r>\<^sup>-\<^sup>1[g] \<cdot> \<r>[g]) \<cdot> ((g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)) \<cdot> (\<l>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g])"
          using comp_assoc by simp
        also have "... = (g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g)"
          using comp_arr_inv' comp_inv_arr' iso_lunit iso_runit comp_arr_dom comp_cod_arr
                hseqI' antipar
          by (metis ide_right in_homE lunit_simps(4) runit_simps(4) triangle_in_hom(2))
        finally show "(g \<star> \<epsilon>) \<cdot> \<a>[g, f, g] \<cdot> (\<eta> \<star> g) = \<r>\<^sup>-\<^sup>1[g] \<cdot> \<l>[g]"
          by simp
      qed
    qed

  end

  locale equivalence_in_bicategory =
    adjunction_data_in_bicategory +
  assumes unit_is_iso [simp]: "iso \<eta>"
  and counit_is_iso [simp]: "iso \<epsilon>"
  begin

    lemma dual_equivalence:
    shows "equivalence_in_bicategory V H \<a> \<i> src trg g f (inv \<epsilon>) (inv \<eta>)"
      using antipar by unfold_locales auto

  end

  abbreviation (in bicategory) internal_equivalence
    where "internal_equivalence f g \<phi> \<psi> \<equiv> equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>"

  subsection "Quasi-Inverses and Equivalence Maps"

  text \<open>
    Antiparallel 1-cells \<open>f\<close> and \<open>g\<close> are \emph{quasi-inverses} if they can be extended to
    an internal equivalence.  We will use the term \emph{equivalence map} to refer to a 1-cell
    that has a quasi-inverse.
  \<close>

  context bicategory
  begin

    definition quasi_inverses
    where "quasi_inverses f g \<equiv> \<exists>\<phi> \<psi>. internal_equivalence f g \<phi> \<psi>"

    lemma quasi_inversesI:
    assumes "ide f" and "ide g"
    and "src f \<cong> g \<star> f" and "f \<star> g \<cong> trg f"
    shows "quasi_inverses f g"
    proof (unfold quasi_inverses_def)
      have 1: "src g = trg f"
        using assms ideD(1) isomorphic_implies_ide(2) by blast
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : src f \<Rightarrow> g \<star> f\<guillemotright> \<and> iso \<phi>"
        using assms isomorphic_def by auto
      obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : f \<star> g \<Rightarrow> trg f\<guillemotright> \<and> iso \<psi>"
        using assms isomorphic_def by auto
     have "equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>"
        using assms 1 \<phi> \<psi> by unfold_locales auto
      thus "\<exists>\<phi> \<psi>. internal_equivalence f g \<phi> \<psi>" by auto
    qed

    lemma quasi_inversesE:
    assumes "quasi_inverses f g"
    and "\<lbrakk>ide f; ide g; src f \<cong> g \<star> f; f \<star> g \<cong> trg f\<rbrakk> \<Longrightarrow> T"
    shows T
    proof -
      obtain \<phi> \<psi> where \<phi>\<psi>: "internal_equivalence f g \<phi> \<psi>"
        using assms quasi_inverses_def by auto
      interpret \<phi>\<psi>: equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>
        using \<phi>\<psi> by simp
      have "ide f \<and> ide g"
        by simp
      moreover have "src f \<cong> g \<star> f"
        using isomorphic_def \<phi>\<psi>.unit_in_hom by auto
      moreover have "f \<star> g \<cong> trg f"
        using isomorphic_def \<phi>\<psi>.counit_in_hom by auto
      ultimately show T
        using assms by blast
    qed

    lemma quasi_inverse_unique:
    assumes "quasi_inverses f g" and "quasi_inverses f g'"
    shows "isomorphic g g'"
    proof -
      obtain \<phi> \<psi> where \<phi>\<psi>: "internal_equivalence f g \<phi> \<psi>"
        using assms quasi_inverses_def by auto
      interpret \<phi>\<psi>: equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>
        using \<phi>\<psi> by simp
      obtain \<phi>' \<psi>' where \<phi>'\<psi>': "internal_equivalence f g' \<phi>' \<psi>'"
        using assms quasi_inverses_def by auto
      interpret \<phi>'\<psi>': equivalence_in_bicategory V H \<a> \<i> src trg f g' \<phi>' \<psi>'
        using \<phi>'\<psi>' by simp
      have "\<guillemotleft>\<r>[g'] \<cdot> (g' \<star> \<psi>) \<cdot> \<a>[g', f, g] \<cdot> (\<phi>' \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g] : g \<Rightarrow> g'\<guillemotright>"
        using \<phi>\<psi>.unit_in_hom \<phi>\<psi>.unit_is_iso \<phi>\<psi>.antipar \<phi>'\<psi>'.antipar
        by (intro comp_in_homI' hseqI') auto
      moreover have "iso (\<r>[g'] \<cdot> (g' \<star> \<psi>) \<cdot> \<a>[g', f, g] \<cdot> (\<phi>' \<star> g) \<cdot> \<l>\<^sup>-\<^sup>1[g])"
        using \<phi>\<psi>.unit_in_hom \<phi>\<psi>.unit_is_iso \<phi>\<psi>.antipar \<phi>'\<psi>'.antipar
        by (intro isos_compose) auto
      ultimately show ?thesis
        using isomorphic_def by auto
    qed

    lemma quasi_inverses_symmetric:
    assumes "quasi_inverses f g"
    shows "quasi_inverses g f"
      using assms quasi_inverses_def equivalence_in_bicategory.dual_equivalence by metis

    definition equivalence_map
    where "equivalence_map f \<equiv> \<exists>g \<eta> \<epsilon>. equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"

    lemma equivalence_mapI:
    assumes "quasi_inverses f g"
    shows "equivalence_map f"
      using assms quasi_inverses_def equivalence_map_def by auto

    lemma equivalence_mapE:
    assumes "equivalence_map f"
    obtains g where "quasi_inverses f g"
      using assms equivalence_map_def quasi_inverses_def by auto

    lemma equivalence_map_is_ide:
    assumes "equivalence_map f"
    shows "ide f"
      using assms adjunction_data_in_bicategory.ide_left equivalence_in_bicategory_def
            equivalence_map_def
      by fastforce

    lemma obj_is_equivalence_map:
    assumes "obj a"
    shows "equivalence_map a"
      using assms
      by (metis equivalence_mapI isomorphic_symmetric objE obj_self_composable(2) quasi_inversesI)

    lemma equivalence_respects_iso:
    assumes "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>" and "\<guillemotleft>\<psi> : g \<Rightarrow> g'\<guillemotright>" and "iso \<psi>"
    shows "internal_equivalence f' g' ((g' \<star> \<phi>) \<cdot> (\<psi> \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv \<psi>))"
    proof -
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show ?thesis
      proof
        show f': "ide f'" using assms by auto
        show g': "ide g'" using assms by auto
        show 1: "\<guillemotleft>(g' \<star> \<phi>) \<cdot> (\<psi> \<star> f) \<cdot> \<eta> : src f' \<Rightarrow> g' \<star> f'\<guillemotright>"
          using assms f' g' E.unit_in_hom E.antipar(2) vconn_implies_hpar(3)
         apply (intro comp_in_homI)
            apply auto
          by (intro hcomp_in_vhom) auto
        show "iso ((g' \<star> \<phi>) \<cdot> (\<psi> \<star> f) \<cdot> \<eta>)"
          using assms 1 g' vconn_implies_hpar(3) E.antipar(2) iso_hcomp
          by (intro isos_compose) auto
        show 1: "\<guillemotleft>\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv \<psi>) : f' \<star> g' \<Rightarrow> src g'\<guillemotright>"
          using assms f' ide_in_hom(2) vconn_implies_hpar(3-4) E.antipar(1-2)
          by (intro comp_in_homI) auto
        show "iso (\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv \<psi>))"
          using assms 1 isos_compose
          by (metis E.counit_is_iso E.ide_right arrI f' hseqE ide_is_iso iso_hcomp
              iso_inv_iso seqE)
      qed
    qed

    lemma equivalence_map_preserved_by_iso:
    assumes "equivalence_map f" and "f \<cong> f'"
    shows "equivalence_map f'"
    proof -
      obtain g \<eta> \<epsilon> where E: "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using E by auto
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright> \<and> iso \<phi>"
        using assms isomorphic_def isomorphic_symmetric by blast
      have "equivalence_in_bicategory V H \<a> \<i> src trg f' g
              ((g \<star> \<phi>) \<cdot> (g \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (inv \<phi> \<star> g) \<cdot> (f' \<star> inv g))"
        using E \<phi> equivalence_respects_iso [of f g \<eta> \<epsilon> \<phi> f' g g] by fastforce
      thus ?thesis
        using equivalence_map_def by auto
    qed

    lemma equivalence_preserved_by_iso_right:
    assumes "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : g \<Rightarrow> g'\<guillemotright>" and "iso \<phi>"
    shows "equivalence_in_bicategory V H \<a> \<i> src trg f g' ((\<phi> \<star> f) \<cdot> \<eta>) (\<epsilon> \<cdot> (f \<star> inv \<phi>))"
    proof
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show "ide f" by simp
      show "ide g'"
        using assms(2) isomorphic_def by auto
      show "\<guillemotleft>(\<phi> \<star> f) \<cdot> \<eta> : src f \<Rightarrow> g' \<star> f\<guillemotright>"
        using assms E.antipar(2) E.ide_left by blast
      show "\<guillemotleft>\<epsilon> \<cdot> (f \<star> inv \<phi>) : f \<star> g' \<Rightarrow> src g'\<guillemotright>"
        using assms vconn_implies_hpar(3-4) E.counit_in_vhom E.antipar(1) ide_in_hom(2)
        by (intro comp_in_homI, auto)
      show "iso ((\<phi> \<star> f) \<cdot> \<eta>)"
        using assms E.antipar isos_compose by auto
      show "iso (\<epsilon> \<cdot> (f \<star> inv \<phi>))"
        using assms E.antipar isos_compose by auto
    qed

    lemma equivalence_preserved_by_iso_left:
    assumes "equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>"
    and "\<guillemotleft>\<phi> : f \<Rightarrow> f'\<guillemotright>" and "iso \<phi>"
    shows "equivalence_in_bicategory V H \<a> \<i> src trg f' g ((g \<star> \<phi>) \<cdot> \<eta>) (\<epsilon> \<cdot> (inv \<phi> \<star> g))"
    proof
      interpret E: equivalence_in_bicategory V H \<a> \<i> src trg f g \<eta> \<epsilon>
        using assms by auto
      show "ide f'"
        using assms by auto
      show "ide g"
        by simp
      show "\<guillemotleft>(g \<star> \<phi>) \<cdot> \<eta> : src f' \<Rightarrow> g \<star> f'\<guillemotright>"
        using assms E.unit_in_hom E.antipar by auto
      show "\<guillemotleft>\<epsilon> \<cdot> (inv \<phi> \<star> g) : f' \<star> g \<Rightarrow> src g\<guillemotright>"
        using assms E.counit_in_hom E.antipar ide_in_hom(2) vconn_implies_hpar(3) by auto
      show "iso ((g \<star> \<phi>) \<cdot> \<eta>)"
        using assms E.antipar isos_compose by auto
      show "iso (\<epsilon> \<cdot> (inv \<phi> \<star> g))"
        using assms E.antipar isos_compose by auto
    qed

    definition some_quasi_inverse
    where "some_quasi_inverse f = (SOME g. quasi_inverses f g)"

    notation some_quasi_inverse  ("_\<^sup>~" [1000] 1000)

    lemma quasi_inverses_some_quasi_inverse:
    assumes "equivalence_map f"
    shows "quasi_inverses f f\<^sup>~"
    and "quasi_inverses f\<^sup>~ f"
      using assms some_quasi_inverse_def quasi_inverses_def equivalence_map_def
            someI_ex [of "\<lambda>g. quasi_inverses f g"] quasi_inverses_symmetric
      by auto

    lemma quasi_inverse_antipar:
    assumes "equivalence_map f"
    shows "src f\<^sup>~ = trg f" and "trg f\<^sup>~ = src f"
    proof -
      obtain \<phi> \<psi> where \<phi>\<psi>: "equivalence_in_bicategory V H \<a> \<i> src trg f f\<^sup>~ \<phi> \<psi>"
        using assms equivalence_map_def quasi_inverses_some_quasi_inverse quasi_inverses_def
        by blast
      interpret \<phi>\<psi>: equivalence_in_bicategory V H \<a> \<i> src trg f \<open>f\<^sup>~\<close> \<phi> \<psi>
        using \<phi>\<psi> by simp
      show "src f\<^sup>~ = trg f"
        using \<phi>\<psi>.antipar by simp
      show "trg f\<^sup>~ = src f"
        using \<phi>\<psi>.antipar by simp
    qed

    lemma quasi_inverse_in_hom [intro]:
    assumes "equivalence_map f"
    shows "\<guillemotleft>f\<^sup>~ : trg f \<rightarrow> src f\<guillemotright>"
    and "\<guillemotleft>f\<^sup>~ : f\<^sup>~ \<Rightarrow> f\<^sup>~\<guillemotright>"
      using assms equivalence_mapE
      apply (intro in_homI in_hhomI)
         apply (metis equivalence_map_is_ide ideD(1) not_arr_null quasi_inverse_antipar(2)
                      src.preserves_ide trg.is_extensional)
        apply (simp_all add: quasi_inverse_antipar)
      using assms quasi_inversesE quasi_inverses_some_quasi_inverse(2) by blast

    lemma quasi_inverse_simps [simp]:
    assumes "equivalence_map f"
    shows "equivalence_map f\<^sup>~" and "ide f\<^sup>~"
    and "src f\<^sup>~ = trg f" and "trg f\<^sup>~ = src f"
    and "dom f\<^sup>~ = f\<^sup>~" and "cod f\<^sup>~ = f\<^sup>~"
      using assms equivalence_mapE quasi_inverse_in_hom quasi_inverses_some_quasi_inverse equivalence_map_is_ide
           apply auto
      by (meson equivalence_mapI)

    lemma quasi_inverse_quasi_inverse:
    assumes "equivalence_map f"
    shows "(f\<^sup>~)\<^sup>~ \<cong> f"
    proof -
      have "quasi_inverses f\<^sup>~ (f\<^sup>~)\<^sup>~"
        using assms quasi_inverses_some_quasi_inverse by simp
      moreover have "quasi_inverses f\<^sup>~ f"
        using assms quasi_inverses_some_quasi_inverse quasi_inverses_symmetric by simp
      ultimately show ?thesis
        using quasi_inverse_unique by simp
    qed

    lemma comp_quasi_inverse:
    assumes "equivalence_map f"
    shows "f\<^sup>~ \<star> f \<cong> src f" and "f \<star> f\<^sup>~ \<cong> trg f"
    proof -
      obtain \<phi> \<psi> where \<phi>\<psi>: "equivalence_in_bicategory V H \<a> \<i> src trg f f\<^sup>~ \<phi> \<psi>"
        using assms equivalence_map_def quasi_inverses_some_quasi_inverse
              quasi_inverses_def
        by blast
      interpret \<phi>\<psi>: equivalence_in_bicategory V H \<a> \<i> src trg f \<open>f\<^sup>~\<close> \<phi> \<psi>
        using \<phi>\<psi> by simp
      show "f\<^sup>~ \<star> f \<cong> src f"
        using quasi_inverses_some_quasi_inverse quasi_inverses_def
              \<phi>\<psi>.unit_in_hom \<phi>\<psi>.unit_is_iso isomorphic_def
        by blast
      show "f \<star> f\<^sup>~ \<cong> trg f"
        using quasi_inverses_some_quasi_inverse quasi_inverses_def
              \<phi>\<psi>.counit_in_hom \<phi>\<psi>.counit_is_iso isomorphic_def
        by blast
    qed

    lemma quasi_inverse_transpose:
    assumes "ide f" and "ide g" and "ide h" and "f \<star> g \<cong> h"
    shows "equivalence_map g \<Longrightarrow> f \<cong> h \<star> g\<^sup>~"
    and "equivalence_map f \<Longrightarrow> g \<cong> f\<^sup>~ \<star> h"
    proof -
      have 1: "src f = trg g"
        using assms equivalence_map_is_ide by fastforce
      show "equivalence_map g \<Longrightarrow> f \<cong> h \<star> g\<^sup>~"
      proof -
        assume g: "equivalence_map g"
        have 2: "ide g\<^sup>~"
          using g by simp
        have "f \<cong> f \<star> src f"
          using assms isomorphic_unit_right isomorphic_symmetric by blast
        also have "... \<cong> f \<star> trg g"
          using assms 1 isomorphic_reflexive by auto
        also have "... \<cong> f \<star> g \<star> g\<^sup>~"
          using assms g 1 comp_quasi_inverse(2) isomorphic_symmetric hcomp_ide_isomorphic
          by simp
        also have "... \<cong> (f \<star> g) \<star> g\<^sup>~"
          using assms g 1 2 assoc'_in_hom [of f g "g\<^sup>~"] iso_assoc' isomorphic_def by auto
        also have "... \<cong> h \<star> g\<^sup>~"
          using assms g 1 2
          by (simp add: hcomp_isomorphic_ide)
        finally show ?thesis by blast
      qed
      show "equivalence_map f \<Longrightarrow> g \<cong> f\<^sup>~ \<star> h"
      proof -
        assume f: "equivalence_map f"
        have 2: "ide f\<^sup>~"
          using f by simp
        have "g \<cong> src f \<star> g"
          using assms 1 isomorphic_unit_left isomorphic_symmetric by metis
        also have "... \<cong> (f\<^sup>~ \<star> f) \<star> g"
          using assms f 1 comp_quasi_inverse(1) [of f] isomorphic_symmetric
                hcomp_isomorphic_ide
          by simp
        also have "... \<cong> f\<^sup>~ \<star> f \<star> g"
          using assms f 1 assoc_in_hom [of "f\<^sup>~" f g] iso_assoc isomorphic_def by auto
        also have "... \<cong> f\<^sup>~ \<star> h"
          using assms f 1 equivalence_map_is_ide quasi_inverses_some_quasi_inverse
                hcomp_ide_isomorphic
          by simp
        finally show ?thesis by blast
      qed
    qed

  end

  subsection "Composing Equivalences"

  locale composite_equivalence_in_bicategory =
    bicategory V H \<a> \<i> src trg +
    fg: equivalence_in_bicategory V H \<a> \<i> src trg f g \<zeta> \<xi> +
    hk: equivalence_in_bicategory V H \<a> \<i> src trg h k \<sigma> \<tau>
  for V :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"        (infixr "\<cdot>" 55)
  and H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"        (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"              ("\<i>[_]")
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a"
  and f :: "'a"
  and g :: "'a"
  and \<zeta> :: "'a"
  and \<xi> :: "'a"
  and h :: "'a"
  and k :: "'a"
  and \<sigma> :: "'a"
  and \<tau> :: "'a" +
  assumes composable: "src h = trg f"
  begin

    abbreviation \<eta>
    where "\<eta> \<equiv> \<a>\<^sup>-\<^sup>1[g, k, h \<star> f] \<cdot> (g \<star> \<a>[k, h, f]) \<cdot> (g \<star> \<sigma> \<star> f) \<cdot> (g \<star> \<l>\<^sup>-\<^sup>1[f]) \<cdot> \<zeta>"

    abbreviation \<epsilon>
    where "\<epsilon> \<equiv> \<tau> \<cdot> (h \<star> \<l>[k]) \<cdot> (h \<star> \<xi> \<star> k) \<cdot> (h \<star> \<a>\<^sup>-\<^sup>1[f, g, k]) \<cdot> \<a>[h, f, g \<star> k]"

    interpretation adjunction_data_in_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
    proof
      show "ide (h \<star> f)"
        using composable by simp
      show "ide (g \<star> k)"
        using fg.antipar hk.antipar composable by simp
      show "\<guillemotleft>\<eta> : src (h \<star> f) \<Rightarrow> (g \<star> k) \<star> h \<star> f\<guillemotright>"
        using fg.antipar hk.antipar composable by fastforce
      show "\<guillemotleft>\<epsilon> : (h \<star> f) \<star> g \<star> k \<Rightarrow> src (g \<star> k)\<guillemotright>"
        using fg.antipar hk.antipar composable by fastforce
    qed

    interpretation equivalence_in_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
    proof
      show "iso \<eta>"
        using fg.antipar hk.antipar composable fg.unit_is_iso hk.unit_is_iso iso_hcomp
              iso_lunit' hseq_char
        by (intro isos_compose, auto)
      show "iso \<epsilon>"
        using fg.antipar hk.antipar composable fg.counit_is_iso hk.counit_is_iso iso_hcomp
              iso_lunit hseq_char
        by (intro isos_compose, auto)
    qed

    lemma is_equivalence:
    shows "equivalence_in_bicategory V H \<a> \<i> src trg (h \<star> f) (g \<star> k) \<eta> \<epsilon>"
      ..

    sublocale equivalence_in_bicategory V H \<a> \<i> src trg \<open>h \<star> f\<close> \<open>g \<star> k\<close> \<eta> \<epsilon>
      using is_equivalence by simp

  end

  context bicategory
  begin

    lemma equivalence_maps_compose:
    assumes "equivalence_map f" and "equivalence_map f'" and "src f' = trg f"
    shows "equivalence_map (f' \<star> f)"
    proof -
      obtain g \<phi> \<psi> where fg: "equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>"
        using assms(1) equivalence_map_def by auto
      interpret fg: equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>
        using fg by auto
      obtain g' \<phi>' \<psi>' where f'g': "equivalence_in_bicategory V H \<a> \<i> src trg f' g' \<phi>' \<psi>'"
        using assms(2) equivalence_map_def by auto
      interpret f'g': equivalence_in_bicategory V H \<a> \<i> src trg f' g' \<phi>' \<psi>'
        using f'g' by auto
      interpret composite_equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi> f' g' \<phi>' \<psi>'
        using assms(3) by (unfold_locales, auto)
      show ?thesis
        using equivalence_map_def equivalence_in_bicategory_axioms by auto
    qed

    lemma quasi_inverse_hcomp':
    assumes "equivalence_map f" and "equivalence_map f'" and "equivalence_map (f \<star> f')"
    and "quasi_inverses f g" and "quasi_inverses f' g'"
    shows "quasi_inverses (f \<star> f') (g' \<star> g)"
    proof -
      obtain \<phi> \<psi> where g: "internal_equivalence f g \<phi> \<psi>"
        using assms quasi_inverses_def by auto
      interpret g: equivalence_in_bicategory V H \<a> \<i> src trg f g \<phi> \<psi>
        using g by simp
      obtain \<phi>' \<psi>' where g': "internal_equivalence f' g' \<phi>' \<psi>'"
        using assms quasi_inverses_def by auto
      interpret g': equivalence_in_bicategory V H \<a> \<i> src trg f' g' \<phi>' \<psi>'
        using g' by simp
      interpret gg': composite_equivalence_in_bicategory V H \<a> \<i> src trg f' g' \<phi>' \<psi>' f g \<phi> \<psi>
        using assms equivalence_map_is_ide [of "f \<star> f'"]
        apply unfold_locales
        using ideD(1) by fastforce
      show ?thesis
        unfolding quasi_inverses_def
        using gg'.equivalence_in_bicategory_axioms by auto
    qed

    lemma quasi_inverse_hcomp:
    assumes "equivalence_map f" and "equivalence_map f'" and "equivalence_map (f \<star> f')"
    shows "(f \<star> f')\<^sup>~ \<cong> f'\<^sup>~ \<star> f\<^sup>~"
      using assms quasi_inverses_some_quasi_inverse quasi_inverse_hcomp' quasi_inverse_unique
      by metis

    lemma quasi_inverse_respects_isomorphic:
    assumes "equivalence_map f" and "equivalence_map f'" and "f \<cong> f'"
    shows "f\<^sup>~ \<cong> f'\<^sup>~"
    proof -
      have hpar: "src f = src f' \<and> trg f = trg f'"
        using assms isomorphic_implies_hpar by simp
      have "f\<^sup>~ \<cong> f\<^sup>~ \<star> trg f"
        using isomorphic_unit_right
        by (metis assms(1) isomorphic_symmetric quasi_inverse_simps(2-3))
      also have "... \<cong> f\<^sup>~ \<star> f' \<star> f'\<^sup>~"
      proof -
        have "trg f \<cong> f' \<star> f'\<^sup>~"
          using assms quasi_inverse_hcomp
          by (simp add: comp_quasi_inverse(2) hpar isomorphic_symmetric)
        thus ?thesis
          using assms hpar hcomp_ide_isomorphic isomorphic_implies_hpar(2) by auto
      qed
      also have "... \<cong> (f\<^sup>~ \<star> f') \<star> f'\<^sup>~"
        using assms hcomp_assoc_isomorphic hpar isomorphic_implies_ide(2) isomorphic_symmetric
        by auto
      also have "... \<cong> (f\<^sup>~ \<star> f) \<star> f'\<^sup>~"
      proof -
        have "f\<^sup>~ \<star> f' \<cong> f\<^sup>~ \<star> f"
          using assms isomorphic_symmetric hcomp_ide_isomorphic isomorphic_implies_hpar(1)
          by auto
        thus ?thesis
          using assms hcomp_isomorphic_ide isomorphic_implies_hpar(1) by auto
      qed
      also have "... \<cong> src f \<star> f'\<^sup>~"
      proof -
        have "f\<^sup>~ \<star> f \<cong> src f"
          using assms comp_quasi_inverse by simp
        thus ?thesis
          using assms hcomp_isomorphic_ide isomorphic_implies_hpar by simp
      qed
      also have "... \<cong> f'\<^sup>~"
        using assms isomorphic_unit_left
        by (metis hpar quasi_inverse_simps(2,4))
      finally show ?thesis by blast
    qed

  end

  subsection "Equivalent Objects"

  context bicategory
  begin

    definition equivalent_objects
    where "equivalent_objects a b \<equiv> \<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> equivalence_map f"

    lemma equivalent_objects_reflexive:
    assumes "obj a"
    shows "equivalent_objects a a"
      using assms
      by (metis equivalent_objects_def ide_in_hom(1) objE obj_is_equivalence_map)

    lemma equivalent_objects_symmetric:
    assumes "equivalent_objects a b"
    shows "equivalent_objects b a"
      using assms
      by (metis equivalent_objects_def in_hhomE quasi_inverse_in_hom(1) quasi_inverse_simps(1))

    lemma equivalent_objects_transitive [trans]:
    assumes "equivalent_objects a b" and "equivalent_objects b c"
    shows "equivalent_objects a c"
    proof -
      obtain f where f: "\<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> equivalence_map f"
        using assms equivalent_objects_def by auto
      obtain g where g: "\<guillemotleft>g : b \<rightarrow> c\<guillemotright> \<and> equivalence_map g"
        using assms equivalent_objects_def by auto
      have "\<guillemotleft>g \<star> f : a \<rightarrow> c\<guillemotright> \<and> equivalence_map (g \<star> f)"
        using f g equivalence_maps_compose by auto
      thus ?thesis
        using equivalent_objects_def by auto
    qed

  end

  subsection "Transporting Arrows along Equivalences"

  text \<open>
    We show in this section that transporting the arrows of one hom-category to another
    along connecting equivalence maps yields an equivalence of categories.
    This is useful, because it seems otherwise hard to establish that the transporting
    functor is full.
  \<close>

  locale two_equivalences_in_bicategory =
    bicategory V H \<a> \<i> src trg +
    e\<^sub>0: equivalence_in_bicategory V H \<a> \<i> src trg e\<^sub>0 d\<^sub>0 \<eta>\<^sub>0 \<epsilon>\<^sub>0 +
    e\<^sub>1: equivalence_in_bicategory V H \<a> \<i> src trg e\<^sub>1 d\<^sub>1 \<eta>\<^sub>1 \<epsilon>\<^sub>1
  for V :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<cdot>" 55)
  and H :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<star>" 53)
  and \<a> :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<a>[_, _, _]")
  and \<i> :: "'a \<Rightarrow> 'a"             ("\<i>[_]")
  and src :: "'a \<Rightarrow> 'a"
  and trg :: "'a \<Rightarrow> 'a"
  and e\<^sub>0 :: "'a"
  and d\<^sub>0 :: "'a"
  and \<eta>\<^sub>0 :: "'a"
  and \<epsilon>\<^sub>0 :: "'a"
  and e\<^sub>1 :: "'a"
  and d\<^sub>1 :: "'a"
  and \<eta>\<^sub>1 :: "'a"
  and \<epsilon>\<^sub>1 :: "'a"
  begin

    interpretation hom: subcategory V \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>\<close>
      using hhom_is_subcategory by simp

    (* TODO: The preceding interpretation somehow brings in unwanted notation. *)
    no_notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    interpretation hom': subcategory V \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>\<close>
      using hhom_is_subcategory by simp

    no_notation in_hom        ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    abbreviation (input) F
    where "F \<equiv> \<lambda>\<mu>. e\<^sub>1 \<star> \<mu> \<star> d\<^sub>0"

    interpretation F: "functor" hom.comp hom'.comp F
    proof
      show 1: "\<And>f. hom.arr f \<Longrightarrow> hom'.arr (e\<^sub>1 \<star> f \<star> d\<^sub>0)"
        using hom.arr_char hom'.arr_char in_hhom_def e\<^sub>0.antipar(1-2) by simp
      show "\<And>f. \<not> hom.arr f \<Longrightarrow> e\<^sub>1 \<star> f \<star> d\<^sub>0 = hom'.null"
        using 1 hom.arr_char hom'.null_char in_hhom_def
        by (metis e\<^sub>0.antipar(1) hseqE hseq_char' hcomp_simps(2))
      show "\<And>f. hom.arr f \<Longrightarrow> hom'.dom (e\<^sub>1 \<star> f \<star> d\<^sub>0) = e\<^sub>1 \<star> hom.dom f \<star> d\<^sub>0"
        using hom.arr_char hom.dom_char hom'.arr_char hom'.dom_char
        by (metis 1 hcomp_simps(3) e\<^sub>0.ide_right e\<^sub>1.ide_left hom'.inclusion hseq_char ide_char)
      show "\<And>f. hom.arr f \<Longrightarrow> hom'.cod (e\<^sub>1 \<star> f \<star> d\<^sub>0) = e\<^sub>1 \<star> hom.cod f \<star> d\<^sub>0"
        using hom.arr_char hom.cod_char hom'.arr_char hom'.cod_char
        by (metis 1 hcomp_simps(4) e\<^sub>0.ide_right e\<^sub>1.ide_left hom'.inclusion hseq_char ide_char)
      show "\<And>g f. hom.seq g f \<Longrightarrow>
                   e\<^sub>1 \<star> hom.comp g f \<star> d\<^sub>0 = hom'.comp (e\<^sub>1 \<star> g \<star> d\<^sub>0) (e\<^sub>1 \<star> f \<star> d\<^sub>0)"
        using 1 hom.seq_char hom.arr_char hom.comp_char hom'.arr_char hom'.comp_char
              whisker_left [of e\<^sub>1] whisker_right [of d\<^sub>0]
        apply auto
         apply (metis hseq_char seqE src_vcomp)
        by (metis hseq_char hseq_char')
    qed

    abbreviation (input) G
    where "G \<equiv> \<lambda>\<mu>'. d\<^sub>1 \<star> \<mu>' \<star> e\<^sub>0"

    interpretation G: "functor" hom'.comp hom.comp G
    proof
      show 1: "\<And>f. hom'.arr f \<Longrightarrow> hom.arr (d\<^sub>1 \<star> f \<star> e\<^sub>0)"
        using hom.arr_char hom'.arr_char in_hhom_def e\<^sub>1.antipar(1) e\<^sub>1.antipar(2)
        by simp
      show "\<And>f. \<not> hom'.arr f \<Longrightarrow> d\<^sub>1 \<star> f \<star> e\<^sub>0 = hom.null"
        using 1 hom.arr_char hom'.null_char in_hhom_def
        by (metis e\<^sub>1.antipar(2) hom'.arrI hom.null_char hseqE hseq_char' hcomp_simps(2))
      show "\<And>f. hom'.arr f \<Longrightarrow> hom.dom (d\<^sub>1 \<star> f \<star> e\<^sub>0) = d\<^sub>1 \<star> hom'.dom f \<star> e\<^sub>0"
        using 1 hom.arr_char hom.dom_char hom'.arr_char hom'.dom_char
        by (metis hcomp_simps(3) e\<^sub>0.ide_left e\<^sub>1.ide_right hom.inclusion hseq_char ide_char)
      show "\<And>f. hom'.arr f \<Longrightarrow> hom.cod (d\<^sub>1 \<star> f \<star> e\<^sub>0) = d\<^sub>1 \<star> hom'.cod f \<star> e\<^sub>0"
        using 1 hom.arr_char hom.cod_char hom'.arr_char hom'.cod_char
        by (metis hcomp_simps(4) e\<^sub>0.ide_left e\<^sub>1.ide_right hom.inclusion hseq_char ide_char)
      show "\<And>g f. hom'.seq g f \<Longrightarrow>
                   d\<^sub>1 \<star> hom'.comp g f \<star> e\<^sub>0 = hom.comp (d\<^sub>1 \<star> g \<star> e\<^sub>0) (d\<^sub>1 \<star> f \<star> e\<^sub>0)"
        using 1 hom'.seq_char hom'.arr_char hom'.comp_char hom.arr_char hom.comp_char
              whisker_left [of d\<^sub>1] whisker_right [of e\<^sub>0]
        apply auto
         apply (metis hseq_char seqE src_vcomp)
        by (metis hseq_char hseq_char')
    qed

    interpretation GF: composite_functor hom.comp hom'.comp hom.comp F G ..
    interpretation FG: composite_functor hom'.comp hom.comp hom'.comp G F ..

    abbreviation (input) \<phi>\<^sub>0
    where "\<phi>\<^sub>0 f \<equiv> (d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, f \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (f \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                    ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> f \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[f \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[f]"

    lemma \<phi>\<^sub>0_in_hom:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "\<guillemotleft>\<phi>\<^sub>0 f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    and "\<guillemotleft>\<phi>\<^sub>0 f : f \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> f \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
    proof -
      show "\<guillemotleft>\<phi>\<^sub>0 f : f \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> f \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
        using assms e\<^sub>0.antipar e\<^sub>1.antipar by fastforce
      thus "\<guillemotleft>\<phi>\<^sub>0 f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
        using assms src_dom [of "\<phi>\<^sub>0 f"] trg_dom [of "\<phi>\<^sub>0 f"]
        by (metis arrI dom_comp in_hhom_def runit'_simps(4) seqE)
    qed

    lemma iso_\<phi>\<^sub>0:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "iso (\<phi>\<^sub>0 f)"
      using assms iso_lunit' iso_runit' e\<^sub>0.antipar e\<^sub>1.antipar
      by (intro isos_compose) auto

    interpretation \<phi>: transformation_by_components hom.comp hom.comp hom.map \<open>G o F\<close> \<phi>\<^sub>0
    proof
      fix f
      assume f: "hom.ide f"
      show "hom.in_hom (\<phi>\<^sub>0 f) (hom.map f) (GF.map f)"
      proof (unfold hom.in_hom_char, intro conjI)
        show "hom.arr (hom.map f)"
          using f by simp
        show "hom.arr (GF.map f)"
          using f by simp
        show "hom.arr (\<phi>\<^sub>0 f)"
          using f hom.ide_char hom.arr_char \<phi>\<^sub>0_in_hom by simp
        show "\<guillemotleft>\<phi>\<^sub>0 f : hom.map f \<Rightarrow> GF.map f\<guillemotright>"
          using f hom.ide_char hom.arr_char hom'.ide_char hom'.arr_char F.preserves_arr
                \<phi>\<^sub>0_in_hom
          by auto
      qed
      next
      fix \<mu>
      assume \<mu>: "hom.arr \<mu>"
      show "hom.comp (\<phi>\<^sub>0 (hom.cod \<mu>)) (hom.map \<mu>) =
            hom.comp (GF.map \<mu>) (\<phi>\<^sub>0 (hom.dom \<mu>))"
      proof -
        have "hom.comp (\<phi>\<^sub>0 (hom.cod \<mu>)) (hom.map \<mu>) = \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu>"
        proof -
          have "hom.map \<mu> = \<mu>"
            using \<mu> by simp
          moreover have "\<phi>\<^sub>0 (hom.cod \<mu>) = \<phi>\<^sub>0 (cod \<mu>)"
            using \<mu> hom.arr_char hom.cod_char by simp
          moreover have "hom.arr (\<phi>\<^sub>0 (cod \<mu>))"
            using \<mu> hom.arr_char \<phi>\<^sub>0_in_hom [of "cod \<mu>"]
            by (metis hom.arr_cod hom.cod_simp ide_cod in_hhom_def)
          moreover have "seq (\<phi>\<^sub>0 (cod \<mu>)) \<mu>"
          proof
            show 1: "\<guillemotleft>\<mu> : dom \<mu> \<Rightarrow> cod \<mu>\<guillemotright>"
              using \<mu> hom.arr_char by auto
            show "\<guillemotleft>\<phi>\<^sub>0 (cod \<mu>) : cod \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
              using \<mu> hom.arr_char \<phi>\<^sub>0_in_hom
              by (metis 1 arrI hom.arr_cod hom.cod_simp ide_cod)
          qed
          ultimately show ?thesis
            using \<mu> hom.comp_char by simp
        qed
        also have "... = (d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           \<l>\<^sup>-\<^sup>1[cod \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[cod \<mu>] \<cdot> \<mu>"
          using \<mu> hom.arr_char comp_assoc by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           \<l>\<^sup>-\<^sup>1[cod \<mu> \<star> src e\<^sub>0] \<cdot> (\<mu> \<star> src e\<^sub>0)) \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char runit'_naturality [of \<mu>] comp_assoc by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0]) \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char lunit'_naturality [of "\<mu> \<star> src e\<^sub>0"] by force
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> (\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot>
                           (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0)) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using comp_assoc by simp
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0)) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
        proof -
          have "(\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot> (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0) = \<eta>\<^sub>1 \<star> \<mu> \<star> \<eta>\<^sub>0"
            using \<mu> hom.arr_char comp_arr_dom comp_cod_arr
                  interchange [of \<eta>\<^sub>1 "src e\<^sub>1" "cod \<mu> \<star> \<eta>\<^sub>0" "\<mu> \<star> src e\<^sub>0"]
                  interchange [of "cod \<mu>" \<mu> \<eta>\<^sub>0 "src e\<^sub>0"]
            by (metis e\<^sub>0.unit_in_hom(1) e\<^sub>0.unit_simps(2) e\<^sub>1.unit_simps(1) e\<^sub>1.unit_simps(2)
                hseqI' in_hhom_def)
          also have "... = ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0)"
          proof -
            have "\<eta>\<^sub>1 \<star> \<mu> \<star> \<eta>\<^sub>0 = (d\<^sub>1 \<star> e\<^sub>1) \<cdot> \<eta>\<^sub>1 \<star> \<mu> \<cdot> dom \<mu> \<star> (d\<^sub>0 \<star> e\<^sub>0) \<cdot> \<eta>\<^sub>0"
              using \<mu> hom.arr_char comp_arr_dom comp_cod_arr by auto
            also have "... = (d\<^sub>1 \<star> e\<^sub>1) \<cdot> \<eta>\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (dom \<mu> \<star> \<eta>\<^sub>0)"
              using \<mu> hom.arr_char comp_cod_arr
                    interchange [of \<mu> "dom \<mu>" "d\<^sub>0 \<star> e\<^sub>0" \<eta>\<^sub>0]
              by auto
            also have "... = ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0)"
              using \<mu> hom.arr_char comp_arr_dom comp_cod_arr
                    interchange [of "d\<^sub>1 \<star> e\<^sub>1" \<eta>\<^sub>1 "\<mu> \<star> d\<^sub>0 \<star> e\<^sub>0" "dom \<mu> \<star> \<eta>\<^sub>0"]
                    interchange [of \<mu> "dom \<mu>" "d\<^sub>0 \<star> e\<^sub>0" \<eta>\<^sub>0]
              by (metis e\<^sub>0.unit_in_hom(1) e\<^sub>0.unit_simps(1) e\<^sub>0.unit_simps(3) e\<^sub>1.unit_simps(1)
                  e\<^sub>1.unit_simps(3) hom.inclusion hseqI)
            finally show ?thesis by simp
          qed
          finally have "(\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0) \<cdot> (src e\<^sub>1 \<star> \<mu> \<star> src e\<^sub>0) =
                          ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0) \<cdot> (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0)"
            by simp
          thus ?thesis
            using comp_assoc by simp
        qed
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0])) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char e\<^sub>0.antipar e\<^sub>1.antipar assoc'_naturality [of \<mu> d\<^sub>0 e\<^sub>0]
                whisker_left [of "d\<^sub>1 \<star> e\<^sub>1" "\<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0]" "\<mu> \<star> d\<^sub>0 \<star> e\<^sub>0"]
                whisker_left [of "d\<^sub>1 \<star> e\<^sub>1" "(\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0" "\<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]"]
          by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> \<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot>
                           ((d\<^sub>1 \<star> e\<^sub>1) \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0)) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using comp_assoc by simp
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> (d\<^sub>1 \<star> e\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0) \<cdot>
                           \<a>[d\<^sub>1, e\<^sub>1, (dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0]) \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char e\<^sub>0.antipar e\<^sub>1.antipar
                assoc_naturality [of d\<^sub>1 e\<^sub>1 "(\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0"] hseqI
          by auto
        also have "... = ((d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]) \<cdot> (d\<^sub>1 \<star> e\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0)) \<cdot>
                           \<a>[d\<^sub>1, e\<^sub>1, (dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using comp_assoc by simp
        also have "... = ((d\<^sub>1 \<star> (e\<^sub>1 \<star> \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0) \<cdot> (d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, dom \<mu> \<star> d\<^sub>0, e\<^sub>0])) \<cdot>
                           \<a>[d\<^sub>1, e\<^sub>1, (dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] \<cdot> ((d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[dom \<mu>, d\<^sub>0, e\<^sub>0]) \<cdot>
                           (\<eta>\<^sub>1 \<star> dom \<mu> \<star> \<eta>\<^sub>0) \<cdot> \<l>\<^sup>-\<^sup>1[dom \<mu> \<star> src e\<^sub>0] \<cdot> \<r>\<^sup>-\<^sup>1[dom \<mu>]"
          using \<mu> hom.arr_char e\<^sub>0.antipar e\<^sub>1.antipar
                assoc'_naturality [of e\<^sub>1 "\<mu> \<star> d\<^sub>0" e\<^sub>0]
                whisker_left [of d\<^sub>1 "\<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0]" "e\<^sub>1 \<star> (\<mu> \<star> d\<^sub>0) \<star> e\<^sub>0"]
                whisker_left [of d\<^sub>1 "(e\<^sub>1 \<star> \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0" "\<a>\<^sup>-\<^sup>1[e\<^sub>1, dom \<mu> \<star> d\<^sub>0, e\<^sub>0]"]
          by auto
        also have "... = hom.comp (GF.map \<mu>) (\<phi>\<^sub>0 (hom.dom \<mu>))"
        proof -
          have "hom.arr (GF.map \<mu>)"
            using \<mu> by blast
          moreover have "hom.arr (\<phi>\<^sub>0 (hom.dom \<mu>))"
            using \<mu> hom.arr_char hom.in_hom_char \<phi>\<^sub>0_in_hom(1) hom.dom_closed hom.dom_simp
                  hom.inclusion ide_dom
            by metis
          moreover have "seq (GF.map \<mu>) (\<phi>\<^sub>0 (hom.dom \<mu>))"
          proof
            show "\<guillemotleft>\<phi>\<^sub>0 (hom.dom \<mu>) : dom \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
              using \<mu> hom.arr_char hom.dom_char hom.in_hom_char \<phi>\<^sub>0_in_hom hom.dom_closed
                    hom.dom_simp hom.inclusion ide_dom
              by metis
            show "\<guillemotleft>GF.map \<mu> : d\<^sub>1 \<star> (e\<^sub>1 \<star> dom \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0 \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
              using \<mu> hom.arr_char hom'.arr_char F.preserves_arr
              apply simp
              apply (intro hcomp_in_vhom)
              by (auto simp add: e\<^sub>0.antipar e\<^sub>1.antipar in_hhom_def)
          qed
          ultimately show ?thesis
            using \<mu> hom.comp_char comp_assoc hom.dom_simp by auto
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma transformation_by_components_\<phi>\<^sub>0:
    shows "transformation_by_components hom.comp hom.comp hom.map (G o F) \<phi>\<^sub>0"
      ..

    interpretation \<phi>: natural_isomorphism hom.comp hom.comp hom.map \<open>G o F\<close> \<phi>.map
    proof
      fix f
      assume "hom.ide f"
      hence f: "ide f \<and> \<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
        using hom.ide_char hom.arr_char by simp
      show "hom.iso (\<phi>.map f)"
      proof (unfold hom.iso_char hom.arr_char, intro conjI)
        show "iso (\<phi>.map f)"
          using f iso_\<phi>\<^sub>0 \<phi>.map_simp_ide hom.ide_char hom.arr_char by simp
        moreover show "\<guillemotleft>\<phi>.map f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
          using f hom.ide_char hom.arr_char by blast
        ultimately show "\<guillemotleft>inv (\<phi>.map f) : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
          by auto
      qed
    qed

    lemma natural_isomorphism_\<phi>:
    shows "natural_isomorphism hom.comp hom.comp hom.map (G o F) \<phi>.map"
      ..

    definition \<phi>
    where "\<phi> \<equiv> \<phi>.map"

    lemma \<phi>_ide_simp:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "\<phi> f = \<phi>\<^sub>0 f"
      unfolding \<phi>_def
      using assms hom.ide_char hom.arr_char by simp

    lemma \<phi>_components_are_iso:
    assumes "\<guillemotleft>f : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>" and "ide f"
    shows "iso (\<phi> f)"
      using assms \<phi>_def \<phi>.components_are_iso hom.ide_char hom.arr_char hom.iso_char
      by simp

    lemma \<phi>_eq:
    shows "\<phi> = (\<lambda>\<mu>. if \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> then \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu> else null)"
    proof
      fix \<mu>
      have "\<not> \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> \<Longrightarrow> \<phi>.map \<mu> = null"
        using hom.comp_char hom.null_char hom.arr_char
        by (simp add: \<phi>.is_extensional)
      moreover have "\<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> \<Longrightarrow> \<phi>.map \<mu> = \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu>"
        unfolding \<phi>.map_def
        apply auto
        using hom.comp_char hom.arr_char hom.dom_simp hom.cod_simp
        apply simp
        by (metis (no_types, lifting) \<phi>\<^sub>0_in_hom(1) hom.cod_closed hom.inclusion ide_cod local.ext)
      ultimately show "\<phi> \<mu> = (if \<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright> then \<phi>\<^sub>0 (cod \<mu>) \<cdot> \<mu> else null)"
        unfolding \<phi>_def by auto
    qed

    lemma \<phi>_in_hom [intro]:
    assumes "\<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    shows "\<guillemotleft>\<phi> \<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    and "\<guillemotleft>\<phi> \<mu> : dom \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
    proof -
      show "\<guillemotleft>\<phi> \<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
        using assms \<phi>_eq \<phi>_def hom.arr_char \<phi>.preserves_reflects_arr by presburger
      show "\<guillemotleft>\<phi> \<mu> : dom \<mu> \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
        unfolding \<phi>_eq
        using assms apply simp
        apply (intro comp_in_homI)
              apply auto
      proof -
        show "\<guillemotleft>\<r>\<^sup>-\<^sup>1[cod \<mu>] : cod \<mu> \<Rightarrow> cod \<mu> \<star> src e\<^sub>0\<guillemotright>"
          using assms by auto
        show "\<guillemotleft>\<l>\<^sup>-\<^sup>1[cod \<mu> \<star> src e\<^sub>0] : cod \<mu> \<star> src e\<^sub>0 \<Rightarrow> src e\<^sub>1 \<star> cod \<mu> \<star> src e\<^sub>0\<guillemotright>"
          using assms by auto
        show "\<guillemotleft>\<eta>\<^sub>1 \<star> cod \<mu> \<star> \<eta>\<^sub>0 : src e\<^sub>1 \<star> cod \<mu> \<star> src e\<^sub>0 \<Rightarrow> (d\<^sub>1 \<star> e\<^sub>1) \<star> cod \<mu> \<star> (d\<^sub>0 \<star> e\<^sub>0)\<guillemotright>"
          using assms e\<^sub>0.unit_in_hom(2) e\<^sub>1.unit_in_hom(2)
          apply (intro hcomp_in_vhom)
              apply auto
          by fastforce
        show "\<guillemotleft>(d\<^sub>1 \<star> e\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[cod \<mu>, d\<^sub>0, e\<^sub>0] :
                 (d\<^sub>1 \<star> e\<^sub>1) \<star> cod \<mu> \<star> d\<^sub>0 \<star> e\<^sub>0 \<Rightarrow> (d\<^sub>1 \<star> e\<^sub>1) \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
          using assms assoc'_in_hom e\<^sub>0.antipar(1-2) e\<^sub>1.antipar(2)
          apply (intro hcomp_in_vhom) by auto
        show "\<guillemotleft>\<a>[d\<^sub>1, e\<^sub>1, (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0] :
                (d\<^sub>1 \<star> e\<^sub>1) \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0 \<Rightarrow> d\<^sub>1 \<star> e\<^sub>1 \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
          using assms assoc_in_hom e\<^sub>0.antipar(1-2) e\<^sub>1.antipar(2) by auto
        show "\<guillemotleft>d\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[e\<^sub>1, cod \<mu> \<star> d\<^sub>0, e\<^sub>0] :
                 d\<^sub>1 \<star> e\<^sub>1 \<star> (cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0 \<Rightarrow> d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0\<guillemotright>"
          using assms assoc'_in_hom [of "d\<^sub>1" "e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0" "e\<^sub>0"]
                e\<^sub>0.antipar(1-2) e\<^sub>1.antipar(1-2)
          apply (intro hcomp_in_vhom)
            apply auto
          by fastforce
      qed
    qed

    lemma \<phi>_simps [simp]:
    assumes "\<guillemotleft>\<mu> : src e\<^sub>0 \<rightarrow> src e\<^sub>1\<guillemotright>"
    shows "arr (\<phi> \<mu>)"
    and "src (\<phi> \<mu>) = src e\<^sub>0" and "trg (\<phi> \<mu>) = src e\<^sub>1"
    and "dom (\<phi> \<mu>) = dom \<mu>" and "cod (\<phi> \<mu>) = d\<^sub>1 \<star> (e\<^sub>1 \<star> cod \<mu> \<star> d\<^sub>0) \<star> e\<^sub>0"
      using assms \<phi>_in_hom by auto

    interpretation d\<^sub>0: equivalence_in_bicategory V H \<a> \<i> src trg d\<^sub>0 e\<^sub>0 \<open>inv \<epsilon>\<^sub>0\<close> \<open>inv \<eta>\<^sub>0\<close>
      using e\<^sub>0.dual_equivalence by simp
    interpretation d\<^sub>1: equivalence_in_bicategory V H \<a> \<i> src trg d\<^sub>1 e\<^sub>1 \<open>inv \<epsilon>\<^sub>1\<close> \<open>inv \<eta>\<^sub>1\<close>
      using e\<^sub>1.dual_equivalence by simp
    interpretation d\<^sub>0e\<^sub>0: two_equivalences_in_bicategory V H \<a> \<i> src trg
                           d\<^sub>0 e\<^sub>0 \<open>inv \<epsilon>\<^sub>0\<close> \<open>inv \<eta>\<^sub>0\<close> d\<^sub>1 e\<^sub>1 \<open>inv \<epsilon>\<^sub>1\<close> \<open>inv \<eta>\<^sub>1\<close>
      ..

    interpretation \<psi>: inverse_transformation hom'.comp hom'.comp hom'.map \<open>F o G\<close> d\<^sub>0e\<^sub>0.\<phi>
    proof -
      interpret \<psi>': natural_isomorphism hom'.comp hom'.comp hom'.map \<open>F o G\<close> d\<^sub>0e\<^sub>0.\<phi>
        using d\<^sub>0e\<^sub>0.natural_isomorphism_\<phi> e\<^sub>0.antipar e\<^sub>1.antipar d\<^sub>0e\<^sub>0.\<phi>_eq d\<^sub>0e\<^sub>0.\<phi>_def by metis
      show "inverse_transformation hom'.comp hom'.comp hom'.map (F o G) d\<^sub>0e\<^sub>0.\<phi>"
        ..
    qed

    definition \<psi>
    where "\<psi> \<equiv> \<psi>.map"

    lemma \<psi>_ide_simp:
    assumes "\<guillemotleft>f': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>" and "ide f'"
    shows "\<psi> f' = \<r>[f'] \<cdot> \<l>[f' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> f' \<star> \<epsilon>\<^sub>0) \<cdot> ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[f', e\<^sub>0, d\<^sub>0]) \<cdot>
                    \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot> (e\<^sub>1 \<star> \<a>[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
    proof -
      have "hom'.ide f'"
        using assms hom'.ide_char hom'.arr_char by simp
      hence "\<psi>.map f' = hom'.inv (d\<^sub>0e\<^sub>0.\<phi> f')"
        using assms by simp
      also have "... = inv (d\<^sub>0e\<^sub>0.\<phi> f')"
        using hom'.inv_char \<open>hom'.ide f'\<close> by simp
      also have "... = inv (d\<^sub>0e\<^sub>0.\<phi>\<^sub>0 f')"
        using assms e\<^sub>0.antipar e\<^sub>1.antipar d\<^sub>0e\<^sub>0.\<phi>_eq d\<^sub>0e\<^sub>0.\<phi>_ide_simp [of f'] by simp
      also have "... = ((((inv \<r>\<^sup>-\<^sup>1[f'] \<cdot> inv \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0]) \<cdot> inv (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0)) \<cdot>
                         inv ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0])) \<cdot> inv \<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0]) \<cdot>
                         inv (e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
      proof -
        text \<open>There has to be a better way to do this.\<close>
        have 1: "\<And>A B C D E F.
                 \<lbrakk> iso A; iso B; iso C; iso D; iso E; iso F;
                   arr (((((A \<cdot> B) \<cdot> C) \<cdot> D) \<cdot> E) \<cdot> F) \<rbrakk> \<Longrightarrow>
                 inv (((((A \<cdot> B) \<cdot> C) \<cdot> D) \<cdot> E) \<cdot> F) =
                 inv F \<cdot> inv E \<cdot> inv D \<cdot> inv C \<cdot> inv B \<cdot> inv A"
          using inv_comp isos_compose seqE by metis
        have "arr (d\<^sub>0e\<^sub>0.\<phi>\<^sub>0 f')"
          using assms e\<^sub>0.antipar(2) e\<^sub>1.antipar(2) d\<^sub>0e\<^sub>0.iso_\<phi>\<^sub>0 [of f'] iso_is_arr by simp
        moreover have "iso \<r>\<^sup>-\<^sup>1[f']"
          using assms iso_runit' by simp
        moreover have "iso \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0]"
          using assms iso_lunit' by auto
        moreover have "iso (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0)"
          using assms e\<^sub>0.antipar(2) e\<^sub>1.antipar(2) in_hhom_def by simp
        moreover have "iso ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0])"
          using assms e\<^sub>0.antipar e\<^sub>1.antipar(1) e\<^sub>1.antipar(2) in_hhom_def iso_hcomp
          by (metis calculation(1) e\<^sub>0.ide_left e\<^sub>0.ide_right e\<^sub>1.ide_left e\<^sub>1.ide_right hseqE
              ide_is_iso iso_assoc' seqE)
        moreover have "iso \<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0]"
          using assms e\<^sub>0.antipar e\<^sub>1.antipar by auto
        moreover have "iso (e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
          using assms e\<^sub>0.antipar e\<^sub>1.antipar
          by (metis calculation(1) e\<^sub>0.ide_left e\<^sub>0.ide_right e\<^sub>1.ide_left e\<^sub>1.ide_right
              iso_hcomp ide_hcomp hseqE ideD(1) ide_is_iso in_hhomE iso_assoc'
              seqE hcomp_simps(1-2))
        ultimately show ?thesis
          using 1 [of "e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0]" "\<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0]"
                      "(e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0]" "inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0" "\<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0]" "\<r>\<^sup>-\<^sup>1[f']"]
                comp_assoc
          by (metis e\<^sub>0.antipar(2))
      qed
      also have "... = inv \<r>\<^sup>-\<^sup>1[f'] \<cdot> inv \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0] \<cdot> inv (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0) \<cdot>
                         inv ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>\<^sup>-\<^sup>1[f', e\<^sub>0, d\<^sub>0]) \<cdot> inv \<a>[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                         inv (e\<^sub>1 \<star> \<a>\<^sup>-\<^sup>1[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
        using comp_assoc by simp
      also have "... = \<r>[f'] \<cdot> \<l>[f' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> f' \<star> \<epsilon>\<^sub>0) \<cdot> ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[f', e\<^sub>0, d\<^sub>0]) \<cdot>
                         \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (f' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot> (e\<^sub>1 \<star> \<a>[d\<^sub>1, f' \<star> e\<^sub>0, d\<^sub>0])"
      proof -
        have "inv \<r>\<^sup>-\<^sup>1[f'] = \<r>[f']"
          using assms inv_inv iso_runit by blast
        moreover have "inv \<l>\<^sup>-\<^sup>1[f' \<star> trg e\<^sub>0] = \<l>[f' \<star> trg e\<^sub>0]"
          using assms iso_lunit by auto
        moreover have "inv (inv \<epsilon>\<^sub>1 \<star> f' \<star> inv \<epsilon>\<^sub>0) = \<epsilon>\<^sub>1 \<star> f' \<star> \<epsilon>\<^sub>0"
        proof -
          have "src (inv \<epsilon>\<^sub>1) = trg f'"
            using assms(1) e\<^sub>1.antipar(2) by auto
          moreover have "src f' = trg (inv \<epsilon>\<^sub>0)"
            using assms(1) e\<^sub>0.antipar(2) by auto
          ultimately show ?thesis
            using assms(2) e\<^sub>0.counit_is_iso e\<^sub>1.counit_is_iso by simp
        qed
        ultimately show ?thesis
          using assms e\<^sub>0.antipar e\<^sub>1.antipar by auto
      qed
      finally show ?thesis
        using \<psi>_def by simp
    qed

    lemma \<psi>_components_are_iso:
    assumes "\<guillemotleft>f' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>" and "ide f'"
    shows "iso (\<psi> f')"
      using assms \<psi>_def \<psi>.components_are_iso hom'.ide_char hom'.arr_char hom'.iso_char
      by simp

    lemma \<psi>_eq:
    shows "\<psi> = (\<lambda>\<mu>'. if \<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> then
                          \<mu>' \<cdot> \<r>[dom \<mu>'] \<cdot> \<l>[dom \<mu>' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> dom \<mu>' \<star> \<epsilon>\<^sub>0) \<cdot>
                            ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[dom \<mu>', e\<^sub>0, d\<^sub>0]) \<cdot> \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                            (e\<^sub>1 \<star> \<a>[d\<^sub>1, dom \<mu>' \<star> e\<^sub>0, d\<^sub>0])
                     else null)"
    proof
      fix \<mu>'
      have "\<not> \<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> \<Longrightarrow> \<psi>.map \<mu>' = null"
        using \<psi>.is_extensional hom'.arr_char hom'.null_char by simp
      moreover have "\<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> \<Longrightarrow>
                     \<psi>.map \<mu>' = \<mu>' \<cdot> \<r>[dom \<mu>'] \<cdot> \<l>[dom \<mu>' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> dom \<mu>' \<star> \<epsilon>\<^sub>0) \<cdot>
                                  ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[dom \<mu>', e\<^sub>0, d\<^sub>0]) \<cdot> \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                                  (e\<^sub>1 \<star> \<a>[d\<^sub>1, dom \<mu>' \<star> e\<^sub>0, d\<^sub>0])"
      proof -
        assume \<mu>': "\<guillemotleft>\<mu>': trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
        have "\<guillemotleft>\<psi>.map (dom \<mu>') : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
          using \<mu>' hom'.arr_char hom'.dom_closed by auto
        moreover have "seq \<mu>' (\<psi>.map (dom \<mu>'))"
        proof -
          have "hom'.seq \<mu>' (\<psi>.map (dom \<mu>'))"
            using \<mu>' \<psi>.preserves_cod hom'.arrI hom'.dom_simp hom'.cod_simp
            apply (intro hom'.seqI) by auto
          thus ?thesis
            using hom'.seq_char by blast
        qed
        ultimately show ?thesis
          using \<mu>' \<psi>.is_natural_1 [of \<mu>'] hom'.comp_char hom'.arr_char hom'.dom_closed
                \<psi>_ide_simp [of "dom \<mu>'"] hom'.dom_simp hom'.cod_simp
          apply auto
          by (metis \<psi>_def hom'.inclusion ide_dom)
      qed
      ultimately show "\<psi> \<mu>' = (if \<guillemotleft>\<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright> then
                                  \<mu>' \<cdot> \<r>[dom \<mu>'] \<cdot> \<l>[dom \<mu>' \<star> trg e\<^sub>0] \<cdot> (\<epsilon>\<^sub>1 \<star> dom \<mu>' \<star> \<epsilon>\<^sub>0) \<cdot>
                                    ((e\<^sub>1 \<star> d\<^sub>1) \<star> \<a>[dom \<mu>', e\<^sub>0, d\<^sub>0]) \<cdot>
                                    \<a>\<^sup>-\<^sup>1[e\<^sub>1, d\<^sub>1, (dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0] \<cdot>
                                    (e\<^sub>1 \<star> \<a>[d\<^sub>1, dom \<mu>' \<star> e\<^sub>0, d\<^sub>0])
                               else null)"
        unfolding \<psi>_def by argo
    qed

    lemma \<psi>_in_hom [intro]:
    assumes "\<guillemotleft>\<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
    shows "\<guillemotleft>\<psi> \<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
    and "\<guillemotleft>\<psi> \<mu>' : e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0 \<Rightarrow> cod \<mu>'\<guillemotright>"
    proof -
      have 0: "\<psi> \<mu>' = \<psi>.map \<mu>'"
        using \<psi>_def by auto
      hence 1: "hom'.arr (\<psi> \<mu>')"
        using assms hom'.arr_char \<psi>.preserves_reflects_arr by auto
      show "\<guillemotleft>\<psi> \<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
        using 1 hom'.arr_char by blast
      show "\<guillemotleft>\<psi> \<mu>' : e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0 \<Rightarrow> cod \<mu>'\<guillemotright>"
        using assms 0 1 \<psi>.preserves_hom hom'.in_hom_char hom'.arr_char
              e\<^sub>0.antipar e\<^sub>1.antipar \<psi>.preserves_dom \<psi>.preserves_cod hom'.dom_char
        apply (intro in_homI)
          apply auto[1]
      proof -
        show "dom (\<psi> \<mu>') = e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0"
        proof -
          have "hom'.dom (\<psi> \<mu>') = FG.map (hom'.dom \<mu>')"
            using assms 0 \<psi>.preserves_dom hom'.arr_char
            by (metis (no_types, lifting))
          thus ?thesis
            using assms 0 1 hom.arr_char hom'.arr_char hom'.dom_char G.preserves_arr
                  hom'.dom_closed
            by auto
        qed
        show "cod (\<psi> \<mu>') = cod \<mu>'"
        proof -
          have "hom'.cod (\<psi> \<mu>') = cod \<mu>'"
            using assms 0 \<psi>.preserves_cod hom'.arr_char hom'.cod_simp by auto
          thus ?thesis
            using assms 0 1 hom'.arr_char hom'.cod_char G.preserves_arr hom'.cod_closed by auto
        qed
      qed
    qed

    lemma \<psi>_simps [simp]:
    assumes "\<guillemotleft>\<mu>' : trg e\<^sub>0 \<rightarrow> trg e\<^sub>1\<guillemotright>"
    shows "arr (\<psi> \<mu>')"
    and "src (\<psi> \<mu>') = trg e\<^sub>0" and "trg (\<psi> \<mu>') = trg e\<^sub>1"
    and "dom (\<psi> \<mu>') = e\<^sub>1 \<star> (d\<^sub>1 \<star> dom \<mu>' \<star> e\<^sub>0) \<star> d\<^sub>0" and "cod (\<psi> \<mu>') = cod \<mu>'"
      using assms \<psi>_in_hom by auto

    interpretation equivalence_of_categories hom'.comp hom.comp F G \<phi> \<psi>
    proof -
      interpret \<phi>: natural_isomorphism hom.comp hom.comp hom.map \<open>G o F\<close> \<phi>
        using \<phi>.natural_isomorphism_axioms \<phi>_def by simp
      interpret \<psi>: natural_isomorphism hom'.comp hom'.comp \<open>F o G\<close> hom'.map \<psi>
        using \<psi>.natural_isomorphism_axioms \<psi>_def by simp
      show "equivalence_of_categories hom'.comp hom.comp F G \<phi> \<psi>"
        ..
    qed

    lemma induces_equivalence_of_hom_categories:
    shows "equivalence_of_categories hom'.comp hom.comp F G \<phi> \<psi>"
      ..

    lemma equivalence_functor_F:
    shows "equivalence_functor hom.comp hom'.comp F"
    proof -
      interpret \<phi>': inverse_transformation hom.comp hom.comp hom.map \<open>G o F\<close> \<phi> ..
      interpret \<psi>': inverse_transformation hom'.comp hom'.comp \<open>F o G\<close> hom'.map \<psi> ..
      interpret E: equivalence_of_categories hom.comp hom'.comp G F \<psi>'.map \<phi>'.map ..
      show ?thesis
        using E.equivalence_functor_axioms by simp
    qed

    lemma equivalence_functor_G:
    shows "equivalence_functor hom'.comp hom.comp G"
      using equivalence_functor_axioms by simp

  end

  context bicategory
  begin

    text \<open>
      We now use the just-established equivalence of hom-categories to prove some cancellation
      laws for equivalence maps.  It is relatively straightforward to prove these results
      directly, without using the just-established equivalence, but the proofs are somewhat
      longer that way.
    \<close>

    lemma equivalence_cancel_left:
    assumes "equivalence_map e"
    and "par \<mu> \<mu>'" and "src e = trg \<mu>" and "e \<star> \<mu> = e \<star> \<mu>'"
    shows "\<mu> = \<mu>'"
    proof -
      obtain d \<eta> \<epsilon> where d\<eta>\<epsilon>: "equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret e: equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>
        using d\<eta>\<epsilon> by simp
      interpret i: equivalence_in_bicategory V H \<a> \<i> src trg
                     \<open>src \<mu>\<close> \<open>src \<mu>\<close> \<open>inv \<i>[src \<mu>]\<close> \<open>\<i>[src \<mu>]\<close>
        using assms iso_unit obj_src
        by unfold_locales simp_all
      interpret two_equivalences_in_bicategory V H \<a> \<i> src trg
                     \<open>src \<mu>\<close> \<open>src \<mu>\<close> \<open>inv \<i>[src \<mu>]\<close> \<open>\<i>[src \<mu>]\<close> e d \<eta> \<epsilon>
        ..
      interpret hom: subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (src (src \<mu>)) (src e)\<close>
        using hhom_is_subcategory by blast
      interpret hom': subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (trg (src \<mu>)) (trg e)\<close>
        using hhom_is_subcategory by blast
      interpret F: equivalence_functor hom.comp hom'.comp \<open>\<lambda>\<mu>'. e \<star> \<mu>' \<star> src \<mu>\<close>
        using equivalence_functor_F by simp
      have "F \<mu> = F \<mu>'"
        using assms hom.arr_char
        apply simp
        by (metis e.ide_left hcomp_reassoc(2) i.ide_right ideD(1) src_dom trg_dom trg_src)
      moreover have "hom.par \<mu> \<mu>'"
        using assms hom.arr_char hom.dom_char hom.cod_char
        by (metis (no_types, lifting) in_hhomI src_dom src_src trg_dom)
      ultimately show "\<mu> = \<mu>'"
        using F.is_faithful by blast
    qed

    lemma equivalence_cancel_right:
    assumes "equivalence_map e"
    and "par \<mu> \<mu>'" and "src \<mu> = trg e" and "\<mu> \<star> e = \<mu>' \<star> e"
    shows "\<mu> = \<mu>'"
    proof -
      obtain d \<eta> \<epsilon> where d\<eta>\<epsilon>: "equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret e: equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>
        using d\<eta>\<epsilon> by simp
      interpret i: equivalence_in_bicategory V H \<a> \<i> src trg
                     \<open>trg \<mu>\<close> \<open>trg \<mu>\<close> \<open>inv \<i>[trg \<mu>]\<close> \<open>\<i>[trg \<mu>]\<close>
        using assms iso_unit obj_src
        by unfold_locales simp_all
      interpret two_equivalences_in_bicategory V H \<a> \<i> src trg
                      e d \<eta> \<epsilon> \<open>trg \<mu>\<close> \<open>trg \<mu>\<close> \<open>inv \<i>[trg \<mu>]\<close> \<open>\<i>[trg \<mu>]\<close>
        ..
      interpret hom: subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (trg e) (trg (trg \<mu>))\<close>
        using hhom_is_subcategory by blast
      interpret hom': subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (src e) (src (trg \<mu>))\<close>
        using hhom_is_subcategory by blast
      interpret G: equivalence_functor hom.comp hom'.comp \<open>\<lambda>\<mu>'. trg \<mu> \<star> \<mu>' \<star> e\<close>
        using equivalence_functor_G by simp
      have "G \<mu> = G \<mu>'"
        using assms hom.arr_char by simp
      moreover have "hom.par \<mu> \<mu>'"
        using assms hom.arr_char hom.dom_char hom.cod_char
        by (metis (no_types, lifting) in_hhomI src_dom trg_dom trg_trg)
      ultimately show "\<mu> = \<mu>'"
        using G.is_faithful by blast
    qed

    lemma equivalence_isomorphic_cancel_left:
    assumes "equivalence_map e" and "ide f" and "ide f'"
    and "src f = src f'" and "src e = trg f" and "e \<star> f \<cong> e \<star> f'"
    shows "f \<cong> f'"
    proof -
      have ef': "src e = trg f'"
        using assms R.components_are_iso iso_is_arr isomorphic_implies_hpar(2) by blast
      obtain d \<eta> \<epsilon> where e: "equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret e: equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>
        using e by simp
      interpret i: equivalence_in_bicategory V H \<a> \<i> src trg
                     \<open>src f\<close> \<open>src f\<close> \<open>inv \<i>[src f]\<close> \<open>\<i>[src f]\<close>
        using assms iso_unit obj_src
        by unfold_locales auto
      interpret two_equivalences_in_bicategory V H \<a> \<i> src trg
                     \<open>src f\<close> \<open>src f\<close> \<open>inv \<i>[src f]\<close> \<open>\<i>[src f]\<close> e d \<eta> \<epsilon>
        ..
      interpret hom: subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (src (src f)) (src e)\<close>
        using hhom_is_subcategory by blast
      interpret hom': subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (trg (src f)) (trg e)\<close>
        using hhom_is_subcategory by blast
      interpret F: equivalence_functor hom.comp hom'.comp \<open>\<lambda>\<mu>'. e \<star> \<mu>' \<star> src f\<close>
        using equivalence_functor_F by simp
      have 1: "F f \<cong> F f'"
      proof -
        have "F f \<cong> (e \<star> f) \<star> src f"
          using assms hcomp_assoc_isomorphic equivalence_map_is_ide isomorphic_symmetric
          by auto
        also have "... \<cong> (e \<star> f') \<star> src f'"
          using assms ef' by (simp add: hcomp_isomorphic_ide)
        also have "... \<cong> F f'"
          using assms ef' hcomp_assoc_isomorphic equivalence_map_is_ide by auto
        finally show ?thesis by blast
      qed
      show "f \<cong> f'"
      proof -
        obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : F f \<Rightarrow> F f'\<guillemotright> \<and> iso \<psi>"
          using 1 isomorphic_def by auto
        have 2: "hom'.iso \<psi>"
          using assms \<psi> hom'.iso_char hom'.arr_char vconn_implies_hpar(1,2)
          by auto
        have 3: "hom'.in_hom \<psi> (F f) (F f')"
          using assms 2 \<psi> ef' hom'.in_hom_char hom'.arr_char
          by (metis F.preserves_reflects_arr hom'.iso_is_arr hom.arr_char i.antipar(1)
              ideD(1) ide_in_hom(1) trg_src)
        obtain \<phi> where \<phi>: "hom.in_hom \<phi> f f' \<and> F \<phi> = \<psi>"
          using assms 3 \<psi> F.is_full F.preserves_reflects_arr hom'.in_hom_char hom.ide_char
          by fastforce
        have "hom.iso \<phi>"
          using 2 \<phi> F.reflects_iso by auto
        thus ?thesis
          using \<phi> isomorphic_def hom.in_hom_char hom.arr_char hom.iso_char by auto
      qed
    qed

    lemma equivalence_isomorphic_cancel_right:
    assumes "equivalence_map e" and "ide f" and "ide f'"
    and "trg f = trg f'" and "src f = trg e" and "f \<star> e \<cong> f' \<star> e"
    shows "f \<cong> f'"
    proof -
      have f'e: "src f' = trg e"
        using assms R.components_are_iso iso_is_arr isomorphic_implies_hpar(2) by blast
      obtain d \<eta> \<epsilon> where d\<eta>\<epsilon>: "equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>"
        using assms equivalence_map_def by auto
      interpret e: equivalence_in_bicategory V H \<a> \<i> src trg e d \<eta> \<epsilon>
        using d\<eta>\<epsilon> by simp
      interpret i: equivalence_in_bicategory V H \<a> \<i> src trg
                     \<open>trg f\<close> \<open>trg f\<close> \<open>inv \<i>[trg f]\<close> \<open>\<i>[trg f]\<close>
        using assms iso_unit obj_src
        by unfold_locales auto
      interpret two_equivalences_in_bicategory V H \<a> \<i> src trg
                      e d \<eta> \<epsilon> \<open>trg f\<close> \<open>trg f\<close> \<open>inv \<i>[trg f]\<close> \<open>\<i>[trg f]\<close>
        ..
      interpret hom: subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (trg e) (trg (trg f))\<close>
        using hhom_is_subcategory by blast
      interpret hom': subcategory V \<open>\<lambda>\<mu>'. in_hhom \<mu>' (src e) (src (trg f))\<close>
        using hhom_is_subcategory by blast
      interpret G: equivalence_functor hom.comp hom'.comp \<open>\<lambda>\<mu>'. trg f \<star> \<mu>' \<star> e\<close>
        using equivalence_functor_G by simp
      have 1: "G f \<cong> G f'"
        using assms hcomp_isomorphic_ide hcomp_ide_isomorphic by simp
      show "f \<cong> f'"
      proof -
        obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : G f \<Rightarrow> G f'\<guillemotright> \<and> iso \<psi>"
          using 1 isomorphic_def by auto
        have 2: "hom'.iso \<psi>"
          using assms \<psi> hom'.iso_char hom'.arr_char vconn_implies_hpar(1-2) by auto
        have 3: "hom'.in_hom \<psi> (G f) (G f')"
          using assms 2 \<psi> f'e hom'.in_hom_char hom'.arr_char
          by (metis G.preserves_arr hom'.iso_is_arr hom.ideI hom.ide_char ideD(1)
              ide_in_hom(1) trg_trg)
        obtain \<phi> where \<phi>: "hom.in_hom \<phi> f f' \<and> G \<phi> = \<psi>"
          using assms 3 \<psi> G.is_full G.preserves_reflects_arr hom'.in_hom_char hom.ide_char
          by fastforce
        have "hom.iso \<phi>"
          using 2 \<phi> G.reflects_iso by auto
        thus ?thesis
          using \<phi> isomorphic_def hom.in_hom_char hom.arr_char hom.iso_char by auto
      qed
    qed

  end

end

