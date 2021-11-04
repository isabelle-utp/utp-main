(*  Title:       EquivalenceOfBicategories
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Equivalence of Bicategories"

text \<open>
  In this section, we define the notion ``equivalence of bicategories'', which generalizes
  the notion of equivalence of categories, and we establish various of its properties.
  In particular, we show that ``equivalent bicategories'' is an equivalence relation,
  and that a pseudofunctor is part of an equivalence of bicategories if and only if it
  is an equivalence pseudofunctor (\emph{i.e.}~it is faithful, locally full, locally
  essentially surjective, and biessentially surjective on objects).
\<close>

theory EquivalenceOfBicategories
imports InternalAdjunction PseudonaturalTransformation
begin

  subsection "Definition of Equivalence of Bicategories"

  text \<open>
    An equivalence of bicategories between bicategories \<open>C\<close> and \<open>D\<close> consists of pseudofunctors
    \<open>F : D \<rightarrow> C\<close> and \<open>G : C \<rightarrow> D\<close> and pseudonatural equivalences \<open>\<eta>: I\<^sub>D \<approx> GF\<close> and
    \<open>\<epsilon>: FG \<approx> I\<^sub>C\<close>.
  \<close>

  locale equivalence_of_bicategories =  (* 35 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F +
    G: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G +
    FG: composite_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
          V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G F \<Phi>\<^sub>F +
    GF: composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G +
    I\<^sub>C: identity_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    I\<^sub>D: identity_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    \<eta>: pseudonatural_equivalence V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
          I\<^sub>D.map I\<^sub>D.cmp GF.map GF.cmp \<eta>\<^sub>0 \<eta>\<^sub>1 +
    \<epsilon>: pseudonatural_equivalence V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
          FG.map FG.cmp I\<^sub>C.map I\<^sub>C.cmp \<epsilon>\<^sub>0 \<epsilon>\<^sub>1
  for V\<^sub>C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'d \<Rightarrow> 'c"
  and \<Phi>\<^sub>F :: "'d * 'd \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>G :: "'c * 'c \<Rightarrow> 'd"
  and \<eta>\<^sub>0 :: "'d \<Rightarrow> 'd"
  and \<eta>\<^sub>1 :: "'d \<Rightarrow> 'd"
  and \<epsilon>\<^sub>0 :: "'c \<Rightarrow> 'c"
  and \<epsilon>\<^sub>1 :: "'c \<Rightarrow> 'c"
  begin

    notation C.isomorphic (infix "\<cong>\<^sub>C" 50)
    notation D.isomorphic (infix "\<cong>\<^sub>D" 50)

    notation C.iso_in_hom ("\<guillemotleft>_ : _ \<cong>\<^sub>C _\<guillemotright>")
    notation D.iso_in_hom ("\<guillemotleft>_ : _ \<cong>\<^sub>D _\<guillemotright>")

    notation C.some_quasi_inverse  ("_\<^sup>~\<^sup>C" [1000] 1000)
    notation D.some_quasi_inverse  ("_\<^sup>~\<^sup>D" [1000] 1000)

    interpretation \<eta>': converse_pseudonatural_equivalence
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         I\<^sub>D.map I\<^sub>D.cmp GF.map GF.cmp \<eta>\<^sub>0 \<eta>\<^sub>1
      ..
    interpretation \<epsilon>': converse_pseudonatural_equivalence
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         FG.map FG.cmp I\<^sub>C.map I\<^sub>C.cmp \<epsilon>\<^sub>0 \<epsilon>\<^sub>1
      ..

    text \<open>
      Although it will be some trouble yet to prove that \<open>F\<close> is an equivalence pseudofunctor,
      it is not as difficult to prove that the composites \<open>GF\<close> and \<open>FG\<close> are equivalence
      pseudofunctors, by virtue of their being pseudonaturally equivalent to identity
      pseudofunctors.
    \<close>

    interpretation GF: equivalence_pseudofunctor
                          V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D GF.map GF.cmp
    proof -
      interpret GF: pseudofunctor_pseudonaturally_equivalent_to_equivalence_pseudofunctor
                       V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                       I\<^sub>D.map I\<^sub>D.cmp GF.map GF.cmp \<eta>\<^sub>0 \<eta>\<^sub>1
        ..
      show "equivalence_pseudofunctor
              V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D GF.map GF.cmp"
        using GF.is_equivalence_pseudofunctor by simp
    qed

    interpretation FG: equivalence_pseudofunctor
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C FG.map FG.cmp
    proof -
      interpret FG: pseudofunctor_pseudonaturally_equivalent_to_equivalence_pseudofunctor
                       V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                       I\<^sub>C.map I\<^sub>C.cmp FG.map FG.cmp \<epsilon>'.map\<^sub>0 \<epsilon>'.map\<^sub>1
        ..
      show "equivalence_pseudofunctor
              V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C FG.map FG.cmp"
        using FG.is_equivalence_pseudofunctor by simp
    qed

    text \<open>
      It is also easy to establish that \<open>F\<close> and \<open>G\<close> are faithful.
      We will use the facts, that \<open>GF\<close> is locally full and \<open>G\<close> is faithful,
      to prove that \<open>F\<close> is locally full.
    \<close>

    interpretation F: faithful_functor V\<^sub>D V\<^sub>C F
    proof
      fix \<mu> \<mu>'
      assume par: "D.par \<mu> \<mu>'" and eq: "F \<mu> = F \<mu>'"
      have hpar: "src\<^sub>D \<mu> = src\<^sub>D \<mu>' \<and> trg\<^sub>D \<mu> = trg\<^sub>D \<mu>'"
        using par D.src_dom D.trg_cod by fastforce
      have "\<eta>\<^sub>0 (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu> = \<eta>\<^sub>0 (trg\<^sub>D \<mu>) \<star>\<^sub>D \<mu>'"
        using par hpar eq \<eta>.iso_map\<^sub>1_ide D.comp_arr_inv' D.trg.preserves_dom
              D.comp_arr_dom D.comp_assoc
        by (metis GF.is_faithful o_apply)
      thus "\<mu> = \<mu>'"
        using par \<eta>.ide_map\<^sub>0_obj \<eta>.components_are_equivalences
              D.equivalence_cancel_left [of "\<eta>\<^sub>0 (trg\<^sub>D \<mu>)" \<mu> \<mu>']
        by simp
    qed

    interpretation G: faithful_functor V\<^sub>C V\<^sub>D G
    proof
      show "\<And>\<mu> \<mu>'. \<lbrakk>C.par \<mu> \<mu>'; G \<mu> = G \<mu>'\<rbrakk> \<Longrightarrow> \<mu> = \<mu>'"
      proof -
        fix \<mu> \<mu>'
        assume par: "C.par \<mu> \<mu>'" and eq: "G \<mu> = G \<mu>'"
        have hpar: "src\<^sub>C \<mu> = src\<^sub>C \<mu>' \<and> trg\<^sub>C \<mu> = trg\<^sub>C \<mu>'"
          using par C.src_dom C.trg_cod by fastforce
        have "\<mu> \<star>\<^sub>C \<epsilon>\<^sub>0 (src\<^sub>C \<mu>) = \<mu>' \<star>\<^sub>C \<epsilon>\<^sub>0 (src\<^sub>C \<mu>)"
            using par hpar eq \<epsilon>.iso_map\<^sub>1_ide C.comp_inv_arr' C.src.preserves_dom
                  C.comp_arr_dom C.comp_assoc
            by (metis FG.is_faithful o_apply)
        thus "\<mu> = \<mu>'"
          using par \<epsilon>.ide_map\<^sub>0_obj \<epsilon>.components_are_equivalences
                C.equivalence_cancel_right [of "\<epsilon>\<^sub>0 (src\<^sub>C \<mu>)" \<mu> \<mu>']
          by simp
      qed
    qed

    text \<open>
      It is perhaps not so easy to discover a proof that \<open>F\<close> is locally essentially surjective.
      Here we follow the proof of \cite{johnson-yau-2d-categories}, Lemma 6.2.13, except we
      have expressed it in a way that explicitly shows its constructive nature, given that
      we have already chosen an extension of each component of \<open>\<eta>\<close> and \<open>\<epsilon>\<close> to an adjoint
      equivalence.
    \<close>

    abbreviation \<Phi>
    where "\<Phi> \<psi> f f' \<equiv> \<r>\<^sub>C[f'] \<cdot>\<^sub>C
                       (f' \<star>\<^sub>C \<epsilon>'.counit (src\<^sub>C f)) \<cdot>\<^sub>C
                       \<a>\<^sub>C[f', \<epsilon>\<^sub>0 (src\<^sub>C f), \<epsilon>'.map\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>C
                       (C.inv (\<epsilon>\<^sub>1 f') \<star>\<^sub>C \<epsilon>'.map\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>C
                       \<a>\<^sub>C\<^sup>-\<^sup>1[\<epsilon>\<^sub>0 (trg\<^sub>C f), F (G f'), \<epsilon>'.map\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>C
                       (\<epsilon>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>C F \<psi> \<star>\<^sub>C \<epsilon>'.map\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>C
                       (\<epsilon>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>C C.inv (\<epsilon>'.map\<^sub>1 f)) \<cdot>\<^sub>C
                       \<a>\<^sub>C[\<epsilon>\<^sub>0 (trg\<^sub>C f), \<epsilon>'.map\<^sub>0 (trg\<^sub>C f), f] \<cdot>\<^sub>C
                       (C.inv (\<epsilon>'.counit (trg\<^sub>C f)) \<star>\<^sub>C f) \<cdot>\<^sub>C
                       \<l>\<^sub>C\<^sup>-\<^sup>1[f]"

    lemma G_reflects_isomorphic:
    assumes "C.ide f" and "C.ide f'" and "src\<^sub>C f = src\<^sub>C f'" and "trg\<^sub>C f = trg\<^sub>C f'"
    and "\<guillemotleft>\<psi> : G f \<cong>\<^sub>D G f'\<guillemotright>"
    shows "\<guillemotleft>\<Phi> \<psi> f f' : f \<cong>\<^sub>C f'\<guillemotright>"
    proof -
      let ?a = "src\<^sub>C f" and ?a' = "trg\<^sub>C f"
      have f: "\<guillemotleft>f : ?a \<rightarrow>\<^sub>C ?a'\<guillemotright> \<and> C.ide f"
        using assms by simp
      have f': "\<guillemotleft>f' : ?a \<rightarrow>\<^sub>C ?a'\<guillemotright> \<and> C.ide f'"
        using assms by simp
      have \<psi>: "\<guillemotleft>\<psi> : G.map\<^sub>0 ?a \<rightarrow>\<^sub>D G.map\<^sub>0 ?a'\<guillemotright>"
        using assms D.vconn_implies_hpar(1-2)
        by (elim D.iso_in_homE) auto
      hence F\<psi>: "\<guillemotleft>F \<psi> : F.map\<^sub>0 (G.map\<^sub>0 ?a) \<rightarrow>\<^sub>C F.map\<^sub>0 (G.map\<^sub>0 ?a')\<guillemotright>"
        by auto
      show "\<guillemotleft>\<Phi> \<psi> f f' : f \<cong>\<^sub>C f'\<guillemotright>"
      proof (intro C.comp_iso_in_hom)
        show "\<guillemotleft>\<l>\<^sub>C\<^sup>-\<^sup>1[f] : f \<cong>\<^sub>C ?a' \<star>\<^sub>C f\<guillemotright>"
          using f by auto
        show "\<guillemotleft>C.inv (\<epsilon>'.counit ?a') \<star>\<^sub>C f : ?a' \<star>\<^sub>C f \<cong>\<^sub>C (\<epsilon>\<^sub>0 ?a' \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a') \<star>\<^sub>C f\<guillemotright>"
          using f \<epsilon>'.counit_in_hom [of ?a'] \<epsilon>'.iso_counit [of ?a']
          by (intro C.hcomp_iso_in_hom) auto
        show "\<guillemotleft>\<a>\<^sub>C[\<epsilon>\<^sub>0 ?a', \<epsilon>'.map\<^sub>0 ?a', f] :
                 (\<epsilon>\<^sub>0 ?a' \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a') \<star>\<^sub>C f \<cong>\<^sub>C \<epsilon>\<^sub>0 ?a' \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a' \<star>\<^sub>C f\<guillemotright>"
          using f \<epsilon>'.counit_in_hom [of ?a] \<epsilon>'.ide_map\<^sub>0_obj
          by (intro C.iso_in_homI) auto
        show "\<guillemotleft>\<epsilon>\<^sub>0 ?a' \<star>\<^sub>C C.inv (\<epsilon>'.map\<^sub>1 f) :
                 \<epsilon>\<^sub>0 ?a' \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a' \<star>\<^sub>C f \<cong>\<^sub>C \<epsilon>\<^sub>0 ?a' \<star>\<^sub>C F (G f) \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a\<guillemotright>"
          using f \<epsilon>'.map\<^sub>1_in_hom [of f] \<epsilon>'.iso_map\<^sub>1_ide [of f] C.ide_iso_in_hom
          by (intro C.hcomp_iso_in_hom) auto
        show "\<guillemotleft>\<epsilon>\<^sub>0 ?a' \<star>\<^sub>C F \<psi> \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a :
                 \<epsilon>\<^sub>0 ?a' \<star>\<^sub>C F (G f) \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a \<cong>\<^sub>C \<epsilon>\<^sub>0 ?a' \<star>\<^sub>C F (G f') \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a\<guillemotright>"
          using assms f f' F\<psi> F.preserves_iso C.ide_iso_in_hom
          by (intro C.hcomp_iso_in_hom) auto
        show "\<guillemotleft>\<a>\<^sub>C\<^sup>-\<^sup>1[\<epsilon>\<^sub>0 ?a', F (G f'), \<epsilon>'.map\<^sub>0 ?a] :
                 \<epsilon>\<^sub>0 ?a' \<star>\<^sub>C F (G f') \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a \<cong>\<^sub>C (\<epsilon>\<^sub>0 ?a' \<star>\<^sub>C F (G f')) \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a\<guillemotright>"
          using assms f' \<epsilon>.map\<^sub>0_in_hom(1) [of ?a'] \<epsilon>.ide_map\<^sub>0_obj [of ?a']
                \<epsilon>'.map\<^sub>0_in_hom(1) [of ?a] \<epsilon>'.ide_map\<^sub>0_obj [of ?a]
                C.assoc'_in_hom C.iso_assoc'
          by auto
        show "\<guillemotleft>C.inv (\<epsilon>\<^sub>1 f') \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a :
                 (\<epsilon>\<^sub>0 ?a' \<star>\<^sub>C F (G f')) \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a \<cong>\<^sub>C (f' \<star>\<^sub>C \<epsilon>\<^sub>0 ?a)  \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a\<guillemotright>"
          using assms f' \<epsilon>.map\<^sub>1_in_hom \<epsilon>.iso_map\<^sub>1_ide \<epsilon>'.map\<^sub>0_in_hom(1) [of ?a]
                C.ide_iso_in_hom
          by (intro C.hcomp_iso_in_hom) auto
        show "\<guillemotleft>\<a>\<^sub>C[f', \<epsilon>\<^sub>0 ?a, \<epsilon>'.map\<^sub>0 ?a] :
                (f' \<star>\<^sub>C \<epsilon>\<^sub>0 ?a) \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a \<cong>\<^sub>C f' \<star>\<^sub>C \<epsilon>\<^sub>0 ?a \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a\<guillemotright>"
          using assms f' \<epsilon>.map\<^sub>0_in_hom(1) [of ?a] \<epsilon>'.map\<^sub>0_in_hom(1) [of ?a]
                \<epsilon>.ide_map\<^sub>0_obj \<epsilon>'.ide_map\<^sub>0_obj C.assoc_in_hom
          by auto
        show "\<guillemotleft>f' \<star>\<^sub>C \<epsilon>'.counit ?a : f' \<star>\<^sub>C \<epsilon>\<^sub>0 ?a \<star>\<^sub>C \<epsilon>'.map\<^sub>0 ?a \<cong>\<^sub>C f' \<star>\<^sub>C ?a\<guillemotright>"
          using f f' \<epsilon>'.counit_in_hom
          by (intro C.hcomp_iso_in_hom) auto
        show "\<guillemotleft>\<r>\<^sub>C[f'] : f' \<star>\<^sub>C ?a \<cong>\<^sub>C f'\<guillemotright>"
          using assms f' by auto
      qed
    qed

    abbreviation \<Psi>
    where "\<Psi> f b b' \<equiv> \<r>\<^sub>D[G (F (\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b))] \<cdot>\<^sub>D
                       (G (F (\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b)) \<star>\<^sub>D \<eta>'.\<epsilon> b) \<cdot>\<^sub>D
                       \<a>\<^sub>D[G (F (\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b)), \<eta>\<^sub>0 b, \<eta>'.map\<^sub>0 b] \<cdot>\<^sub>D
                       (D.inv (\<eta>\<^sub>1 (\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b)) \<star>\<^sub>D \<eta>'.map\<^sub>0 b) \<cdot>\<^sub>D
                       (\<a>\<^sub>D[\<eta>\<^sub>0 b', \<eta>'.map\<^sub>0 b', G f \<star>\<^sub>D \<eta>\<^sub>0 b] \<star>\<^sub>D \<eta>'.map\<^sub>0 b) \<cdot>\<^sub>D
                       \<a>\<^sub>D\<^sup>-\<^sup>1[\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b', G f \<star>\<^sub>D \<eta>\<^sub>0 b, \<eta>'.map\<^sub>0 b] \<cdot>\<^sub>D
                       ((\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<eta>\<^sub>0 b, \<eta>'.map\<^sub>0 b]) \<cdot>\<^sub>D
                       (D.inv (\<eta>'.counit b') \<star>\<^sub>D G f \<star>\<^sub>D D.inv (\<eta>'.counit b)) \<cdot>\<^sub>D
                       \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b)] \<cdot>\<^sub>D
                       \<r>\<^sub>D\<^sup>-\<^sup>1[G f]"

    lemma F_is_locally_essentially_surjective:
    assumes "D.obj b" and "D.obj b'" and "\<guillemotleft>f : F.map\<^sub>0 b \<rightarrow>\<^sub>C F.map\<^sub>0 b'\<guillemotright>" and "C.ide f"
    shows "\<guillemotleft>\<Phi> (\<Psi> f b b') f (F (\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b)) :
              f \<cong>\<^sub>C F (\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b)\<guillemotright>"
    proof -
      let ?g = "\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b"
      have g_in_hhom: "\<guillemotleft>?g : b \<rightarrow>\<^sub>D b'\<guillemotright>"
        using assms \<eta>.ide_map\<^sub>0_obj \<eta>.map\<^sub>0_in_hhom by auto
      have ide_g: "D.ide ?g"
        using assms g_in_hhom \<eta>.ide_map\<^sub>0_obj \<eta>'.ide_map\<^sub>0_obj G.preserves_ide by blast
      let ?\<psi> = "\<Psi> f b b'"
      have 1: "\<guillemotleft>?\<psi> : G f \<cong>\<^sub>D G (F ?g)\<guillemotright>"
      proof (intro D.comp_iso_in_hom)
        show 1: "\<guillemotleft>\<r>\<^sub>D\<^sup>-\<^sup>1[G f] : G f \<cong>\<^sub>D G f \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b)\<guillemotright>"
          using assms
          by (intro D.iso_in_homI) auto
        show "\<guillemotleft>\<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b)] :
                  G f \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b)
                     \<cong>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b') \<star>\<^sub>D G f \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b)\<guillemotright>"
        proof -
          have "D.ide (G f \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b))"
            using assms D.ide_hcomp [of "G f" "G.map\<^sub>0 (F.map\<^sub>0 b)"]
            by (metis D.hcomp_in_hhomE D.hseqE D.objE F.map\<^sub>0_simps(1) G.map\<^sub>0_simps(1)
                G.preserves_ide GF.map\<^sub>0_simp \<eta>.map\<^sub>0_simps(3) g_in_hhom)
          thus ?thesis
            using assms \<eta>.ide_map\<^sub>0_obj
            by (intro D.iso_in_homI) auto
        qed
        show "\<guillemotleft>D.inv (\<eta>'.counit b') \<star>\<^sub>D G f \<star>\<^sub>D D.inv (\<eta>'.counit b) :
                 G.map\<^sub>0 (F.map\<^sub>0 b') \<star>\<^sub>D G f \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b)
                   \<cong>\<^sub>D (\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D G f \<star>\<^sub>D (\<eta>\<^sub>0 b \<star>\<^sub>D \<eta>'.map\<^sub>0 b)\<guillemotright>"
          using assms 1 \<eta>'.iso_counit \<eta>'.counit_in_hom(2) D.vconn_implies_hpar(4) D.ide_iso_in_hom
          by (intro D.hcomp_iso_in_hom) auto
        show 2: "\<guillemotleft>(\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<eta>\<^sub>0 b, \<eta>'.map\<^sub>0 b] :
                    (\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D G f \<star>\<^sub>D (\<eta>\<^sub>0 b \<star>\<^sub>D \<eta>'.map\<^sub>0 b)
                      \<cong>\<^sub>D (\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D (G f \<star>\<^sub>D \<eta>\<^sub>0 b) \<star>\<^sub>D \<eta>'.map\<^sub>0 b\<guillemotright>"
        proof -
          have "\<guillemotleft>\<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<eta>\<^sub>0 b, \<eta>'.map\<^sub>0 b] :
                   G f \<star>\<^sub>D (\<eta>\<^sub>0 b \<star>\<^sub>D \<eta>'.map\<^sub>0 b) \<cong>\<^sub>D (G f \<star>\<^sub>D \<eta>\<^sub>0 b) \<star>\<^sub>D \<eta>'.map\<^sub>0 b\<guillemotright>"
            using assms \<eta>.ide_map\<^sub>0_obj \<eta>'.ide_map\<^sub>0_obj \<eta>.map\<^sub>0_in_hom \<eta>'.map\<^sub>0_in_hom
                  D.assoc'_in_hom D.iso_assoc'
            by (intro D.iso_in_homI) auto
          thus ?thesis
            using assms
            by (intro D.hcomp_iso_in_hom) auto
        qed
        show "\<guillemotleft>\<a>\<^sub>D\<^sup>-\<^sup>1[\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b', G f \<star>\<^sub>D \<eta>\<^sub>0 b, \<eta>'.map\<^sub>0 b] :
                (\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D (G f \<star>\<^sub>D \<eta>\<^sub>0 b) \<star>\<^sub>D \<eta>'.map\<^sub>0 b
                   \<cong>\<^sub>D ((\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D (G f \<star>\<^sub>D \<eta>\<^sub>0 b)) \<star>\<^sub>D \<eta>'.map\<^sub>0 b\<guillemotright>"
          using assms \<eta>.ide_map\<^sub>0_obj \<eta>'.ide_map\<^sub>0_obj \<eta>.map\<^sub>0_in_hom \<eta>'.map\<^sub>0_in_hom
                D.assoc'_in_hom D.iso_assoc'
          by (intro D.iso_in_homI) auto
        show "\<guillemotleft>\<a>\<^sub>D[\<eta>\<^sub>0 b', \<eta>'.map\<^sub>0 b', G f \<star>\<^sub>D \<eta>\<^sub>0 b] \<star>\<^sub>D \<eta>'.map\<^sub>0 b :
                 ((\<eta>\<^sub>0 b' \<star>\<^sub>D \<eta>'.map\<^sub>0 b') \<star>\<^sub>D (G f \<star>\<^sub>D \<eta>\<^sub>0 b)) \<star>\<^sub>D \<eta>'.map\<^sub>0 b
                   \<cong>\<^sub>D (\<eta>\<^sub>0 b' \<star>\<^sub>D ?g) \<star>\<^sub>D \<eta>'.map\<^sub>0 b\<guillemotright>"
          using assms \<eta>.ide_map\<^sub>0_obj \<eta>'.ide_map\<^sub>0_obj \<eta>.map\<^sub>0_in_hom \<eta>'.map\<^sub>0_in_hom
                D.assoc_in_hom D.iso_assoc
          by (intro D.hcomp_iso_in_hom D.iso_in_homI) auto
        show "\<guillemotleft>D.inv (\<eta>\<^sub>1 ?g) \<star>\<^sub>D \<eta>'.map\<^sub>0 b :
                 (\<eta>\<^sub>0 b' \<star>\<^sub>D ?g) \<star>\<^sub>D \<eta>'.map\<^sub>0 b \<cong>\<^sub>D (G (F ?g) \<star>\<^sub>D \<eta>\<^sub>0 b) \<star>\<^sub>D \<eta>'.map\<^sub>0 b\<guillemotright>"
          using assms \<eta>.map\<^sub>1_in_hom [of ?g] \<eta>.iso_map\<^sub>1_ide \<eta>'.map\<^sub>0_in_hom g_in_hhom ide_g
          by (intro D.hcomp_iso_in_hom D.iso_in_homI) auto
        show "\<guillemotleft>\<a>\<^sub>D[G (F ?g), \<eta>\<^sub>0 b, \<eta>'.map\<^sub>0 b] :
                (G (F ?g) \<star>\<^sub>D \<eta>\<^sub>0 b) \<star>\<^sub>D \<eta>'.map\<^sub>0 b \<cong>\<^sub>D G (F ?g) \<star>\<^sub>D \<eta>\<^sub>0 b \<star>\<^sub>D \<eta>'.map\<^sub>0 b\<guillemotright>"
          using assms \<eta>.ide_map\<^sub>0_obj \<eta>'.ide_map\<^sub>0_obj \<eta>.map\<^sub>0_in_hom \<eta>'.map\<^sub>0_in_hom
                D.assoc_in_hom D.iso_assoc
          by (intro D.iso_in_homI) auto
        show "\<guillemotleft>G (F ?g) \<star>\<^sub>D \<eta>'.counit b :
                 G (F ?g) \<star>\<^sub>D \<eta>\<^sub>0 b \<star>\<^sub>D \<eta>'.map\<^sub>0 b \<cong>\<^sub>D G (F ?g) \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b)\<guillemotright>"
          using assms \<eta>'.counit_in_hom D.ide_in_hom(2) ide_g
          by (intro D.hcomp_iso_in_hom) auto
        show "\<guillemotleft>\<r>\<^sub>D[G (F ?g)] : G (F ?g) \<star>\<^sub>D G.map\<^sub>0 (F.map\<^sub>0 b) \<cong>\<^sub>D G (F ?g)\<guillemotright>"
          using assms ide_g
          by (intro D.iso_in_homI) auto
      qed
      show "\<guillemotleft>\<Phi> ?\<psi> f (F ?g) : f \<cong>\<^sub>C F ?g\<guillemotright>"
        using assms 1 ide_g G_reflects_isomorphic [of f "F ?g" ?\<psi>]
        by (metis C.horizontal_homs_axioms D.in_hhomE F.preserves_ide F.preserves_src
            F.preserves_trg g_in_hhom horizontal_homs.in_hhomE)
    qed

    interpretation F: equivalence_pseudofunctor
                        V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F
    proof
      show "\<And>b. C.obj b \<Longrightarrow> \<exists>a. D.obj a \<and> C.equivalent_objects (F.map\<^sub>0 a) b"
      proof -
        fix b
        assume b: "C.obj b"
        have "D.obj (G.map\<^sub>0 b)"
          using b by simp
        moreover have "C.equivalent_objects (F.map\<^sub>0 (G.map\<^sub>0 b)) b"
          unfolding C.equivalent_objects_def
          using b \<epsilon>.components_are_equivalences
          by (metis FG.map\<^sub>0_simp I\<^sub>C.map\<^sub>0_simp \<epsilon>.map\<^sub>0_in_hom(1))
        ultimately show "\<exists>a. D.obj a \<and> C.equivalent_objects (F.map\<^sub>0 a) b"
          by auto
      qed
      show "\<And>g g' \<mu>. \<lbrakk>D.ide g; D.ide g'; src\<^sub>D g = src\<^sub>D g'; trg\<^sub>D g = trg\<^sub>D g';
                       \<guillemotleft>\<mu> : F g \<Rightarrow>\<^sub>C F g'\<guillemotright>\<rbrakk>
                         \<Longrightarrow> \<exists>\<nu>. \<guillemotleft>\<nu> : g \<Rightarrow>\<^sub>D g'\<guillemotright> \<and> F \<nu> = \<mu>"
      proof -
        fix g g' \<mu>
        assume g: "D.ide g" and g': "D.ide g'"
        assume eq_src: "src\<^sub>D g = src\<^sub>D g'" and eq_trg: "trg\<^sub>D g = trg\<^sub>D g'"
        assume \<mu>: "\<guillemotleft>\<mu> : F g \<Rightarrow>\<^sub>C F g'\<guillemotright>"
        obtain \<nu> where \<nu>: "\<guillemotleft>\<nu> : g \<Rightarrow>\<^sub>D g'\<guillemotright> \<and> G (F \<nu>) = G \<mu>"
          using g g' eq_src eq_trg \<mu> GF.locally_full [of g g' "G \<mu>"] by auto
        have "F \<nu> = \<mu>"
          using \<mu> \<nu> G.is_faithful
          by (metis (mono_tags, lifting) C.in_homE F.preserves_hom)
        thus "\<exists>\<nu>. \<guillemotleft>\<nu> : g \<Rightarrow>\<^sub>D g'\<guillemotright> \<and> F \<nu> = \<mu>"
          using \<nu> by auto
      qed
      show "\<And>b b' f. \<lbrakk>D.obj b; D.obj b'; \<guillemotleft>f : F.map\<^sub>0 b \<rightarrow>\<^sub>C F.map\<^sub>0 b'\<guillemotright>; C.ide f\<rbrakk>
                       \<Longrightarrow> \<exists>g. \<guillemotleft>g : b \<rightarrow>\<^sub>D b'\<guillemotright> \<and> D.ide g \<and> C.isomorphic (F g) f"
      proof -
        fix b b' f
        assume b: "D.obj b" and b': "D.obj b'" and f: "\<guillemotleft>f : F.map\<^sub>0 b \<rightarrow>\<^sub>C F.map\<^sub>0 b'\<guillemotright>"
        assume ide_f: "C.ide f"
        let ?g = "\<eta>'.map\<^sub>0 b' \<star>\<^sub>D G f \<star>\<^sub>D \<eta>\<^sub>0 b"
        have g_in_hhom: "\<guillemotleft>?g : b \<rightarrow>\<^sub>D b'\<guillemotright>"
          using b b' f \<eta>.ide_map\<^sub>0_obj \<eta>.map\<^sub>0_in_hhom by auto
        have ide_g: "D.ide ?g"
          using b b' f ide_f g_in_hhom \<eta>.ide_map\<^sub>0_obj \<eta>'.ide_map\<^sub>0_obj G.preserves_ide by blast
        have "f \<cong>\<^sub>C F ?g"
          using b b' f ide_f F_is_locally_essentially_surjective C.isomorphic_symmetric
          by (meson C.isomorphicI')
        thus "\<exists>g. \<guillemotleft>g : b \<rightarrow>\<^sub>D b'\<guillemotright> \<and> D.ide g \<and> F g \<cong>\<^sub>C f"
          using g_in_hhom ide_g C.isomorphic_symmetric C.isomorphic_def by blast
      qed
    qed

    lemma equivalence_pseudofunctor_left:
    shows "equivalence_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F"
      ..

  end

  subsection "Equivalences Respect Pseudonatural Equivalence"

  text \<open>
    In this section we prove that, in an equivalence of bicategories, either pseudofunctor
    may be replaced by a pseudonaturally equivalent one and still obtain an equivalence of
    bicategories.
  \<close>

  locale equivalence_of_bicategories_and_pseudonatural_equivalence_left =  (* 40 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    E: equivalence_of_bicategories +
    \<tau>: pseudonatural_equivalence
         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F F' \<Phi>\<^sub>F' \<tau>\<^sub>0 \<tau>\<^sub>1
  for F'
  and \<Phi>\<^sub>F'
  and \<tau>\<^sub>0
  and \<tau>\<^sub>1
  (*
   * TODO: If I attempt to declare these free variables with the types they are ultimately
   * inferred to have, then a disjoint set of type variables gets used, resulting in an error.
   *)
  begin

    interpretation GF': composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F' \<Phi>\<^sub>F' G \<Phi>\<^sub>G
      ..
    interpretation F'G: composite_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                           V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G F' \<Phi>\<^sub>F'
      ..
    interpretation \<tau>': converse_pseudonatural_equivalence
                          V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F F' \<Phi>\<^sub>F' \<tau>\<^sub>0 \<tau>\<^sub>1
      ..
    interpretation \<tau>'oG: pseudonatural_equivalence_whisker_right V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          F' \<Phi>\<^sub>F' F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>'.map\<^sub>0 \<tau>'.map\<^sub>1
      ..
    interpretation Go\<tau>: pseudonatural_equivalence_whisker_left V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           F \<Phi>\<^sub>F F' \<Phi>\<^sub>F' G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      ..
    sublocale unit: composite_pseudonatural_equivalence
                           V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           E.I\<^sub>D.map E.I\<^sub>D.cmp E.GF.map E.GF.cmp GF'.map GF'.cmp
                           \<eta>\<^sub>0 \<eta>\<^sub>1 Go\<tau>.map\<^sub>0 Go\<tau>.map\<^sub>1
      ..
    sublocale counit: composite_pseudonatural_equivalence
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                           F'G.map F'G.cmp E.FG.map E.FG.cmp E.I\<^sub>C.map E.I\<^sub>C.cmp
                           \<tau>'oG.map\<^sub>0 \<tau>'oG.map\<^sub>1 \<epsilon>\<^sub>0 \<epsilon>\<^sub>1
      ..
    sublocale equivalence_of_bicategories
                     V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F' \<Phi>\<^sub>F' G \<Phi>\<^sub>G
                     unit.map\<^sub>0 unit.map\<^sub>1 counit.map\<^sub>0 counit.map\<^sub>1
      ..

    abbreviation unit\<^sub>0
    where "unit\<^sub>0 \<equiv> unit.map\<^sub>0"

    abbreviation unit\<^sub>1
    where "unit\<^sub>1 \<equiv> unit.map\<^sub>1"

    abbreviation counit\<^sub>0
    where "counit\<^sub>0 \<equiv> counit.map\<^sub>0"

    abbreviation counit\<^sub>1
    where "counit\<^sub>1 \<equiv> counit.map\<^sub>1"

    lemma induces_equivalence_of_bicategories:
    shows "equivalence_of_bicategories
             V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F' \<Phi>\<^sub>F' G \<Phi>\<^sub>G
             unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1"
      ..

  end

  locale equivalence_of_bicategories_and_pseudonatural_equivalence_right =  (* 40 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    E: equivalence_of_bicategories +
    \<tau>: pseudonatural_equivalence
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G G' \<Phi>\<^sub>G' \<tau>\<^sub>0 \<tau>\<^sub>1
  for G'
  and \<Phi>\<^sub>G'
  and \<tau>\<^sub>0
  and \<tau>\<^sub>1
  begin

    interpretation G'F: composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G' \<Phi>\<^sub>G'
      ..
    interpretation FG': composite_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G' \<Phi>\<^sub>G' F \<Phi>\<^sub>F
      ..
    interpretation \<tau>': converse_pseudonatural_equivalence
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G G' \<Phi>\<^sub>G' \<tau>\<^sub>0 \<tau>\<^sub>1
      ..
    interpretation \<tau>oF: pseudonatural_equivalence_whisker_right V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          G \<Phi>\<^sub>G G' \<Phi>\<^sub>G' F \<Phi>\<^sub>F \<tau>\<^sub>0 \<tau>\<^sub>1
      ..
    interpretation Fo\<tau>': pseudonatural_equivalence_whisker_left
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          G' \<Phi>\<^sub>G' G \<Phi>\<^sub>G F \<Phi>\<^sub>F \<tau>'.map\<^sub>0 \<tau>'.map\<^sub>1
      ..
    sublocale unit: composite_pseudonatural_equivalence
                          V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          E.I\<^sub>D.map E.I\<^sub>D.cmp E.GF.map E.GF.cmp G'F.map G'F.cmp
                          \<eta>\<^sub>0 \<eta>\<^sub>1 \<tau>oF.map\<^sub>0 \<tau>oF.map\<^sub>1
      ..
    sublocale counit: composite_pseudonatural_equivalence
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          FG'.map FG'.cmp E.FG.map E.FG.cmp E.I\<^sub>C.map E.I\<^sub>C.cmp
                          Fo\<tau>'.map\<^sub>0 Fo\<tau>'.map\<^sub>1 \<epsilon>\<^sub>0 \<epsilon>\<^sub>1
      ..
    sublocale equivalence_of_bicategories
                     V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G' \<Phi>\<^sub>G'
                     unit.map\<^sub>0 unit.map\<^sub>1 counit.map\<^sub>0 counit.map\<^sub>1
      ..

    abbreviation unit\<^sub>0
    where "unit\<^sub>0 \<equiv> unit.map\<^sub>0"

    abbreviation unit\<^sub>1
    where "unit\<^sub>1 \<equiv> unit.map\<^sub>1"

    abbreviation counit\<^sub>0
    where "counit\<^sub>0 \<equiv> counit.map\<^sub>0"

    abbreviation counit\<^sub>1
    where "counit\<^sub>1 \<equiv> counit.map\<^sub>1"

    lemma induces_equivalence_of_bicategories:
    shows "equivalence_of_bicategories
             V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G' \<Phi>\<^sub>G'
             unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1"
      ..

  end

  subsection "Converse of an Equivalence"

  text \<open>
    Equivalence of bicategories is a symmetric notion, in the sense that from an equivalence
    of bicategories from \<open>C\<close> to \<open>D\<close> we may obtain an equivalence of bicategories from
    \<open>D\<close> to \<open>C\<close>.  The converse equivalence is obtained by interchanging the pseudofunctors
    \<open>F\<close> and \<open>G\<close> and replacing the pseudonatural equivalences \<open>\<eta>\<close> and \<open>\<epsilon>\<close> by converse
    equivalences.  Essentially all the work goes into proving that pseudonatural equivalences
    have pseudonatural converses, which we have already done.
  \<close>

  locale converse_equivalence_of_bicategories =  (* 35 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    I\<^sub>C: identity_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    I\<^sub>D: identity_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    E: equivalence_of_bicategories
  begin

    sublocale counit: converse_pseudonatural_equivalence
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         I\<^sub>D.map I\<^sub>D.cmp E.GF.map E.GF.cmp \<eta>\<^sub>0 \<eta>\<^sub>1
      ..
    sublocale unit: converse_pseudonatural_equivalence
                      V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                      E.FG.map E.FG.cmp I\<^sub>C.map I\<^sub>C.cmp \<epsilon>\<^sub>0 \<epsilon>\<^sub>1
      ..

    sublocale equivalence_of_bicategories
                 V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G F \<Phi>\<^sub>F
                 unit.map\<^sub>0 unit.map\<^sub>1 counit.map\<^sub>0 counit.map\<^sub>1
      ..

    abbreviation unit\<^sub>0
    where "unit\<^sub>0 \<equiv> unit.map\<^sub>0"

    abbreviation unit\<^sub>1
    where "unit\<^sub>1 \<equiv> unit.map\<^sub>1"

    abbreviation counit\<^sub>0
    where "counit\<^sub>0 \<equiv> counit.map\<^sub>0"

    abbreviation counit\<^sub>1
    where "counit\<^sub>1 \<equiv> counit.map\<^sub>1"

    lemma is_equivalence_of_bicategories:
    shows "equivalence_of_bicategories
             V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G F \<Phi>\<^sub>F
             unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1"
      ..

  end

  subsection "Composition of Equivalences"

  text \<open>
    An equivalence of bicategories from \<open>B\<close> to \<open>C\<close> and an equivalence of bicategories
    from \<open>C\<close> to \<open>D\<close> may be composed to obtain an equivalence of bicategories
    from \<open>B\<close> to \<open>D\<close>.
  \<close>

  locale composite_equivalence_of_bicategories =  (* 80 sec *)
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B +
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    I\<^sub>B: identity_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B +
    I\<^sub>C: identity_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    I\<^sub>D: identity_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F_: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B F \<Phi>\<^sub>F +
    G_: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G +
    H: pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C H \<Phi>\<^sub>H +
    K: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D K \<Phi>\<^sub>K +
    FG: equivalence_of_bicategories
          V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<rho>\<^sub>0 \<rho>\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 +
    HK: equivalence_of_bicategories
          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D H \<Phi>\<^sub>H K \<Phi>\<^sub>K \<zeta>\<^sub>0 \<zeta>\<^sub>1 \<xi>\<^sub>0 \<xi>\<^sub>1
  for V\<^sub>B :: "'b comp"                    (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'b comp"                   (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"       ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'b \<Rightarrow> 'b"                   ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'b \<Rightarrow> 'b"
  and trg\<^sub>B :: "'b \<Rightarrow> 'b"
  and V\<^sub>C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'b"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'b"
  and G :: "'b \<Rightarrow> 'c"
  and \<Phi>\<^sub>G :: "'b * 'b \<Rightarrow> 'c"
  and H :: "'d \<Rightarrow> 'c"
  and \<Phi>\<^sub>H :: "'d * 'd \<Rightarrow> 'c"
  and K :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>K :: "'c * 'c \<Rightarrow> 'd"
  and \<rho>\<^sub>0 :: "'c \<Rightarrow> 'c"
  and \<rho>\<^sub>1 :: "'c \<Rightarrow> 'c"
  and \<sigma>\<^sub>0 :: "'b \<Rightarrow> 'b"
  and \<sigma>\<^sub>1 :: "'b \<Rightarrow> 'b"
  and \<zeta>\<^sub>0 :: "'d \<Rightarrow> 'd"
  and \<zeta>\<^sub>1 :: "'d \<Rightarrow> 'd"
  and \<xi>\<^sub>0 :: "'c \<Rightarrow> 'c"
  and \<xi>\<^sub>1 :: "'c \<Rightarrow> 'c"
  begin

    notation B.\<a>'                         ("\<a>\<^sub>B\<^sup>-\<^sup>1[_, _, _]")

    text \<open>
      At this point we could make the explicit definitions:
      \begin{itemize}
      \item  \<open>\<eta>\<^sub>0 = K (\<rho>\<^sub>0 (H.map\<^sub>0 a)) \<star>\<^sub>D \<zeta>\<^sub>0 a\<close>
      \item  \<open>\<eta>\<^sub>1 = \<a>\<^sub>D\<^sup>-\<^sup>1[K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f))), \<zeta>\<^sub>0 (trg\<^sub>D f), f] \<cdot>\<^sub>D
                       (K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f))) \<star>\<^sub>D \<zeta>\<^sub>1 f) \<cdot>\<^sub>D
                       \<a>\<^sub>D[K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f))), K (H f), \<zeta>\<^sub>0 (src\<^sub>D f)] \<cdot>\<^sub>D
                       (D.inv (\<Phi>\<^sub>K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f)), H f)) \<cdot>\<^sub>D
                          K (\<rho>\<^sub>1 (H f)) \<cdot>\<^sub>D
                          \<Phi>\<^sub>K (G (F (H f)), \<rho>\<^sub>0 (H.map\<^sub>0 (src\<^sub>D f))) \<star>\<^sub>D \<zeta>\<^sub>0 (src\<^sub>D f)) \<cdot>\<^sub>D
                       \<a>\<^sub>D\<^sup>-\<^sup>1[K (G (F (H f))), K (\<rho>\<^sub>0 (H.map\<^sub>0 (src\<^sub>D f))), \<zeta>\<^sub>0 (src\<^sub>D f)]\<close>
      \item  \<open>\<epsilon>\<^sub>0 = \<sigma>\<^sub>0 a \<star>\<^sub>B F (\<xi>\<^sub>0 (G_.map\<^sub>0 a))\<close>
      \item  \<open>\<epsilon>\<^sub>1 = \<a>\<^sub>B\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>B f), F (\<xi>\<^sub>0 (G_.map\<^sub>0 (trg\<^sub>B f))), F (H (K (G f)))] \<cdot>\<^sub>B
                       (\<sigma>\<^sub>0 (trg\<^sub>B f) \<star>\<^sub>B
                          B.inv (\<Phi>\<^sub>F (\<xi>\<^sub>0 (G_.map\<^sub>0 (trg\<^sub>B f)), H (K (G f)))) \<cdot>\<^sub>B
                            F (\<xi>\<^sub>1 (G f)) \<cdot>\<^sub>B \<Phi>\<^sub>F (G f, \<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>B
                       \<a>\<^sub>B[\<sigma>\<^sub>0 (trg\<^sub>B f), F (G f), F (\<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))] \<cdot>\<^sub>B
                       (\<sigma>\<^sub>1 f \<star>\<^sub>B F (\<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[f, \<sigma>\<^sub>0 (src\<^sub>B f), F (\<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))]\<close>
      \end{itemize}
      but then it is a daunting task to establish the necessary coherence conditions.
      It is easier (and more useful) to use general results about composite pseudonatural
      equivalences, which are somewhat easier to prove, though long calculations are
      still required for those.
    \<close>

    sublocale FH: composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                    V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B H \<Phi>\<^sub>H F \<Phi>\<^sub>F
      ..
    sublocale KG: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                    V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G K \<Phi>\<^sub>K
      ..
    interpretation IG: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         G \<Phi>\<^sub>G I\<^sub>C.map I\<^sub>C.cmp
      ..
    interpretation IH: composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          H \<Phi>\<^sub>H I\<^sub>C.map I\<^sub>C.cmp
      ..
    interpretation HKG: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          G \<Phi>\<^sub>G HK.FG.map HK.FG.cmp
      ..
    interpretation GFH: composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          H \<Phi>\<^sub>H FG.GF.map FG.GF.cmp
      ..
    interpretation KGFH: composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                           GFH.map GFH.cmp K \<Phi>\<^sub>K
      ..
    interpretation FHKG: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                           HKG.map HKG.cmp F \<Phi>\<^sub>F
        ..
    interpretation \<rho>oH: pseudonatural_equivalence_whisker_right V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          I\<^sub>C.map I\<^sub>C.cmp FG.GF.map FG.GF.cmp H \<Phi>\<^sub>H \<rho>\<^sub>0 \<rho>\<^sub>1
      ..
    interpretation Ko\<rho>oH: pseudonatural_equivalence_whisker_left V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            H \<Phi>\<^sub>H GFH.map GFH.cmp K \<Phi>\<^sub>K \<rho>oH.map\<^sub>0 \<rho>oH.map\<^sub>1
    proof -
      interpret Ko\<rho>oH: pseudonatural_equivalence_whisker_left V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          IH.map IH.cmp GFH.map GFH.cmp K \<Phi>\<^sub>K \<rho>oH.map\<^sub>0 \<rho>oH.map\<^sub>1
        ..
      have "IH.map = H"
      proof
        fix \<mu>
        show "IH.map \<mu> = H \<mu>"
          using H.is_extensional IH.is_extensional
          by (cases "D.arr \<mu>") simp_all
      qed
      moreover have "IH.cmp = \<Phi>\<^sub>H"
      proof
        fix \<mu>\<nu>
        show "IH.cmp \<mu>\<nu> = \<Phi>\<^sub>H \<mu>\<nu>"
          using IH.cmp_def D.VV.arr_char D.VV.dom_simp D.VV.cod_simp H.FF_def
                C.comp_arr_dom C.comp_cod_arr H.\<Phi>.is_natural_1 H.\<Phi>.is_extensional
          by (cases "D.VV.arr \<mu>\<nu>") auto
      qed
      ultimately show "pseudonatural_equivalence_whisker_left V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         H \<Phi>\<^sub>H GFH.map GFH.cmp K \<Phi>\<^sub>K \<rho>oH.map\<^sub>0 \<rho>oH.map\<^sub>1"
        using Ko\<rho>oH.pseudonatural_equivalence_whisker_left_axioms by simp
    qed
    interpretation \<xi>oG: pseudonatural_equivalence_whisker_right V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                          HK.FG.map HK.FG.cmp I\<^sub>C.map I\<^sub>C.cmp G \<Phi>\<^sub>G \<xi>\<^sub>0 \<xi>\<^sub>1
      ..
    interpretation Fo\<xi>oG: pseudonatural_equivalence_whisker_left V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            HKG.map HKG.cmp G \<Phi>\<^sub>G F \<Phi>\<^sub>F \<xi>oG.map\<^sub>0 \<xi>oG.map\<^sub>1
    proof -
      interpret Fo\<xi>oG: pseudonatural_equivalence_whisker_left V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B 
                         HKG.map HKG.cmp IG.map IG.cmp F \<Phi>\<^sub>F \<xi>oG.map\<^sub>0 \<xi>oG.map\<^sub>1
        ..
      have "IG.map = G"
      proof
        fix \<mu>
        show "IG.map \<mu> = G \<mu>"
          using G_.is_extensional IG.is_extensional
          by (cases "B.arr \<mu>") simp_all
      qed
      moreover have "IG.cmp = \<Phi>\<^sub>G"
      proof
        fix \<mu>\<nu>
        show "IG.cmp \<mu>\<nu> = \<Phi>\<^sub>G \<mu>\<nu>"
          using IG.cmp_def B.VV.arr_char B.VV.dom_simp B.VV.cod_simp G_.FF_def
                C.comp_arr_dom C.comp_cod_arr G_.\<Phi>.is_natural_1 G_.\<Phi>.is_extensional
          by (cases "B.VV.arr \<mu>\<nu>") auto
      qed
      ultimately show "pseudonatural_equivalence_whisker_left V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                         HKG.map HKG.cmp G \<Phi>\<^sub>G F \<Phi>\<^sub>F \<xi>oG.map\<^sub>0 \<xi>oG.map\<^sub>1"
        using Fo\<xi>oG.pseudonatural_equivalence_whisker_left_axioms by simp
    qed

    sublocale unit: composite_pseudonatural_equivalence
                      V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                      I\<^sub>D.map I\<^sub>D.cmp HK.GF.map HK.GF.cmp KGFH.map KGFH.cmp
                      \<zeta>\<^sub>0 \<zeta>\<^sub>1 Ko\<rho>oH.map\<^sub>0 Ko\<rho>oH.map\<^sub>1
      ..
    sublocale counit: composite_pseudonatural_equivalence
                        V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                        FHKG.map FHKG.cmp FG.FG.map FG.FG.cmp I\<^sub>B.map I\<^sub>B.cmp
                        Fo\<xi>oG.map\<^sub>0 Fo\<xi>oG.map\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1
      ..

    abbreviation left_map
    where "left_map \<equiv> FH.map"

    abbreviation right_map
    where "right_map \<equiv> KG.map"

    abbreviation left_cmp
    where "left_cmp \<equiv> FH.cmp"

    abbreviation right_cmp
    where "right_cmp \<equiv> KG.cmp"

    abbreviation unit\<^sub>0
    where "unit\<^sub>0 \<equiv> unit.map\<^sub>0"

    abbreviation unit\<^sub>1
    where "unit\<^sub>1 \<equiv> unit.map\<^sub>1"

    abbreviation counit\<^sub>0
    where "counit\<^sub>0 \<equiv> counit.map\<^sub>0"

    abbreviation counit\<^sub>1
    where "counit\<^sub>1 == counit.map\<^sub>1"

    lemma unit\<^sub>0_simp:
    assumes "D.obj a"
    shows "unit\<^sub>0 a = K (\<rho>\<^sub>0 (H.map\<^sub>0 a)) \<star>\<^sub>D \<zeta>\<^sub>0 a"
      using assms unit.map\<^sub>0_def Ko\<rho>oH.map\<^sub>0_def \<rho>oH.map\<^sub>0_def by simp

    lemma unit\<^sub>1_simp:
    assumes "D.ide f"
    shows "unit\<^sub>1 f = \<a>\<^sub>D\<^sup>-\<^sup>1[K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f))), \<zeta>\<^sub>0 (trg\<^sub>D f), f] \<cdot>\<^sub>D
                     (K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f))) \<star>\<^sub>D \<zeta>\<^sub>1 f) \<cdot>\<^sub>D
                     \<a>\<^sub>D[K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f))), K (H f), \<zeta>\<^sub>0 (src\<^sub>D f)] \<cdot>\<^sub>D
                     (D.inv (\<Phi>\<^sub>K (\<rho>\<^sub>0 (H.map\<^sub>0 (trg\<^sub>D f)), H f)) \<cdot>\<^sub>D
                     K (\<rho>\<^sub>1 (H f)) \<cdot>\<^sub>D
                     \<Phi>\<^sub>K (G (F (H f)), \<rho>\<^sub>0 (H.map\<^sub>0 (src\<^sub>D f))) \<star>\<^sub>D \<zeta>\<^sub>0 (src\<^sub>D f)) \<cdot>\<^sub>D
                     \<a>\<^sub>D\<^sup>-\<^sup>1[K (G (F (H f))), K (\<rho>\<^sub>0 (H.map\<^sub>0 (src\<^sub>D f))), \<zeta>\<^sub>0 (src\<^sub>D f)]"
      using assms unit.map\<^sub>1_def Ko\<rho>oH.map\<^sub>0_def \<rho>oH.map\<^sub>0_def Ko\<rho>oH.map\<^sub>1_def \<rho>oH.map\<^sub>1_def
      by simp

    lemma counit\<^sub>0_simp:
    assumes "B.obj a"
    shows "counit\<^sub>0 a = \<sigma>\<^sub>0 a \<star>\<^sub>B F (\<xi>\<^sub>0 (G_.map\<^sub>0 a))"
      using assms counit.map\<^sub>0_def Fo\<xi>oG.map\<^sub>0_def \<xi>oG.map\<^sub>0_def by simp

    lemma counit\<^sub>1_simp:
    assumes "B.ide f"
    shows "counit\<^sub>1 f = \<a>\<^sub>B\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>B f), F (\<xi>\<^sub>0 (G_.map\<^sub>0 (trg\<^sub>B f))), F (H (K (G f)))] \<cdot>\<^sub>B
                       (\<sigma>\<^sub>0 (trg\<^sub>B f) \<star>\<^sub>B
                          B.inv (\<Phi>\<^sub>F (\<xi>\<^sub>0 (G_.map\<^sub>0 (trg\<^sub>B f)), H (K (G f)))) \<cdot>\<^sub>B
                          F (\<xi>\<^sub>1 (G f)) \<cdot>\<^sub>B
                          \<Phi>\<^sub>F (G f, \<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>B
                       \<a>\<^sub>B[\<sigma>\<^sub>0 (trg\<^sub>B f), F (G f), F (\<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))] \<cdot>\<^sub>B
                       (\<sigma>\<^sub>1 f \<star>\<^sub>B F (\<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[f, \<sigma>\<^sub>0 (src\<^sub>B f), F (\<xi>\<^sub>0 (G_.map\<^sub>0 (src\<^sub>B f)))]"
      using assms counit.map\<^sub>1_def Fo\<xi>oG.map\<^sub>0_def Fo\<xi>oG.map\<^sub>1_def \<xi>oG.map\<^sub>0_def \<xi>oG.map\<^sub>1_def
      by simp

    sublocale equivalence_of_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                FH.map FH.cmp KG.map KG.cmp
                unit.map\<^sub>0 unit.map\<^sub>1 counit.map\<^sub>0 counit.map\<^sub>1
    proof -
      interpret FH_KG: composite_pseudofunctor
                          V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          KG.map KG.cmp FH.map FH.cmp
        ..
      interpret KG_FH: composite_pseudofunctor
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         FH.map FH.cmp KG.map KG.cmp
        ..
      have "FH_KG.map = FHKG.map" by auto
      moreover have "FH_KG.cmp = FHKG.cmp"
      proof
        fix \<mu>\<nu>
        show "FH_KG.cmp \<mu>\<nu> = FHKG.cmp \<mu>\<nu>"
        proof (cases "B.VV.arr \<mu>\<nu>")
          case False
          thus ?thesis
            using FH_KG.\<Phi>.is_extensional FHKG.\<Phi>.is_extensional by simp
          next
          case True
          have "FH_KG.cmp \<mu>\<nu> =
                  F (H (K (G (I\<^sub>B.cmp \<mu>\<nu>)))) \<cdot>\<^sub>B
                  F (H (K (G (B.dom (fst \<mu>\<nu>) \<star>\<^sub>B B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                  F (H (K (\<Phi>\<^sub>G (B.dom (fst \<mu>\<nu>), B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                  F (H (\<Phi>\<^sub>K (G (B.dom (fst \<mu>\<nu>)), G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                  (F (H (K (G (B.dom (fst \<mu>\<nu>))) \<star>\<^sub>D K (G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                  F (\<Phi>\<^sub>H (K (G (B.dom (fst \<mu>\<nu>))), K (G (B.dom (snd \<mu>\<nu>)))))) \<cdot>\<^sub>B
                  \<Phi>\<^sub>F (H (K (G (B.dom (fst \<mu>\<nu>)))), H (K (G (B.dom (snd \<mu>\<nu>)))))"
            using True FH_KG.cmp_def FHKG.cmp_def HKG.cmp_def
                  FH.cmp_def HK.FG.cmp_def KG.cmp_def
                  B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                  D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                  G_.FF_def H.FF_def K.FF_def B.comp_assoc
            by auto
          also have "... = F (H (K (G (I\<^sub>B.cmp \<mu>\<nu>)))) \<cdot>\<^sub>B
                           F (H (K (G (B.dom (fst \<mu>\<nu>) \<star>\<^sub>B B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           F (H (K (\<Phi>\<^sub>G (B.dom (fst \<mu>\<nu>), B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           F (H (\<Phi>\<^sub>K (G (B.dom (fst \<mu>\<nu>)), G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           F (\<Phi>\<^sub>H (K (G (B.dom (fst \<mu>\<nu>))), K (G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           \<Phi>\<^sub>F (H (K (G (B.dom (fst \<mu>\<nu>)))), H (K (G (B.dom (snd \<mu>\<nu>)))))"
          proof -
            have "F (H (K (G (B.dom (fst \<mu>\<nu>))) \<star>\<^sub>D K (G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                  F (\<Phi>\<^sub>H (K (G (B.dom (fst \<mu>\<nu>))), K (G (B.dom (snd \<mu>\<nu>))))) =
                    F (\<Phi>\<^sub>H (K (G (B.dom (fst \<mu>\<nu>))), K (G (B.dom (snd \<mu>\<nu>)))))"
              using True B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                    C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                    D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                    B.comp_cod_arr
              by auto
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = F (H (K (G (I\<^sub>B.cmp \<mu>\<nu>)))) \<cdot>\<^sub>B
                           F (H (K (G (B.dom (fst \<mu>\<nu>) \<star>\<^sub>B B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           F (H (K (\<Phi>\<^sub>G (B.dom (fst \<mu>\<nu>), B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           (F (H (K (G (B.dom (fst \<mu>\<nu>)) \<star>\<^sub>C G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           F (H (\<Phi>\<^sub>K (G (B.dom (fst \<mu>\<nu>)), G (B.dom (snd \<mu>\<nu>)))))) \<cdot>\<^sub>B
                           F (\<Phi>\<^sub>H (K (G (B.dom (fst \<mu>\<nu>))), K (G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                           \<Phi>\<^sub>F (H (K (G (B.dom (fst \<mu>\<nu>)))), H (K (G (B.dom (snd \<mu>\<nu>)))))"
          proof -
            have "F (H (K (G (B.dom (fst \<mu>\<nu>)) \<star>\<^sub>C G (B.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>B
                  F (H (\<Phi>\<^sub>K (G (B.dom (fst \<mu>\<nu>)), G (B.dom (snd \<mu>\<nu>))))) =
                    F (H (\<Phi>\<^sub>K (G (B.dom (fst \<mu>\<nu>)), G (B.dom (snd \<mu>\<nu>)))))"
              using True B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                    C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                    D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                    G_.FF_def H.FF_def K.FF_def B.comp_assoc
                    B.comp_cod_arr
              by auto
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = FHKG.cmp \<mu>\<nu>"
            using True FH_KG.cmp_def FHKG.cmp_def HKG.cmp_def
                  FH.cmp_def HK.FG.cmp_def KG.cmp_def
                  B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                  D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                  G_.FF_def H.FF_def K.FF_def B.comp_assoc
            by simp
          finally show ?thesis by blast
        qed
      qed
      moreover have "KG_FH.map = KGFH.map" by auto
      moreover have "KG_FH.cmp = KGFH.cmp"
      proof
        fix \<mu>\<nu>
        show "KG_FH.cmp \<mu>\<nu> = KGFH.cmp \<mu>\<nu>"
        proof (cases "D.VV.arr \<mu>\<nu>")
          case False
          thus ?thesis
            using KG_FH.\<Phi>.is_extensional KGFH.\<Phi>.is_extensional by simp
          next
          case True
          have "KG_FH.cmp \<mu>\<nu> =
                  K (G (F (H (I\<^sub>D.cmp \<mu>\<nu>)))) \<cdot>\<^sub>D
                  K (G (F (H (D.dom (fst \<mu>\<nu>) \<star>\<^sub>D D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                  K (G (F (\<Phi>\<^sub>H (D.dom (fst \<mu>\<nu>), D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                  K (G (\<Phi>\<^sub>F (H (D.dom (fst \<mu>\<nu>)), H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                  (K (G (F (H (D.dom (fst \<mu>\<nu>))) \<star>\<^sub>B F (H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                  K (\<Phi>\<^sub>G (F (H (D.dom (fst \<mu>\<nu>))), F (H (D.dom (snd \<mu>\<nu>)))))) \<cdot>\<^sub>D
                  \<Phi>\<^sub>K (G (F (H (D.dom (fst \<mu>\<nu>)))), G (F (H (D.dom (snd \<mu>\<nu>)))))"
            using True KG_FH.cmp_def FH.cmp_def KG.cmp_def
                  B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                  D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                  G_.FF_def H.FF_def K.FF_def
                  D.comp_assoc
            by auto
          also have "... = K (G (F (H (I\<^sub>D.cmp \<mu>\<nu>)))) \<cdot>\<^sub>D
                           K (G (F (H (D.dom (fst \<mu>\<nu>) \<star>\<^sub>D D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           K (G (F (\<Phi>\<^sub>H (D.dom (fst \<mu>\<nu>), D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           K (G (\<Phi>\<^sub>F (H (D.dom (fst \<mu>\<nu>)), H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           K (\<Phi>\<^sub>G (F (H (D.dom (fst \<mu>\<nu>))), F (H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>K (G (F (H (D.dom (fst \<mu>\<nu>)))), G (F (H (D.dom (snd \<mu>\<nu>)))))"
          proof -
            have "K (G (F (H (D.dom (fst \<mu>\<nu>))) \<star>\<^sub>B F (H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                  K (\<Phi>\<^sub>G (F (H (D.dom (fst \<mu>\<nu>))), F (H (D.dom (snd \<mu>\<nu>))))) =
                    K (\<Phi>\<^sub>G (F (H (D.dom (fst \<mu>\<nu>))), F (H (D.dom (snd \<mu>\<nu>)))))"
              using True KG_FH.cmp_def FH.cmp_def KG.cmp_def
                    B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                    C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                    D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                    D.comp_cod_arr
              by simp
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = K (G (F (H (I\<^sub>D.cmp \<mu>\<nu>)))) \<cdot>\<^sub>D
                           K (G (F (H (D.dom (fst \<mu>\<nu>) \<star>\<^sub>D D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           K (G (F (\<Phi>\<^sub>H (D.dom (fst \<mu>\<nu>), D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           (K (G (F (H (D.dom (fst \<mu>\<nu>)) \<star>\<^sub>C H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           K (G (\<Phi>\<^sub>F (H (D.dom (fst \<mu>\<nu>)), H (D.dom (snd \<mu>\<nu>)))))) \<cdot>\<^sub>D
                           K (\<Phi>\<^sub>G (F (H (D.dom (fst \<mu>\<nu>))), F (H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>K (G (F (H (D.dom (fst \<mu>\<nu>)))), G (F (H (D.dom (snd \<mu>\<nu>)))))"
          proof -
            have "K (G (F (H (D.dom (fst \<mu>\<nu>)) \<star>\<^sub>C H (D.dom (snd \<mu>\<nu>))))) \<cdot>\<^sub>D
                  K (G (\<Phi>\<^sub>F (H (D.dom (fst \<mu>\<nu>)), H (D.dom (snd \<mu>\<nu>))))) =
                    K (G (\<Phi>\<^sub>F (H (D.dom (fst \<mu>\<nu>)), H (D.dom (snd \<mu>\<nu>)))))"
              using True KGFH.cmp_def GFH.cmp_def FG.GF.cmp_def
                    B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                    C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                    D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                    D.comp_cod_arr
              by simp
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = KGFH.cmp \<mu>\<nu>"
            using True KGFH.cmp_def GFH.cmp_def FG.GF.cmp_def
                  B.VV.arr_char B.VV.dom_simp B.VV.cod_simp
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
                  D.VV.arr_char D.VV.dom_simp D.VV.cod_simp
                  F_.FF_def G_.FF_def H.FF_def K.FF_def
                  D.comp_assoc
            by auto
          finally show ?thesis by blast
        qed
      qed
      ultimately show "equivalence_of_bicategories
                         V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         FH.map FH.cmp KG.map KG.cmp
                         unit.map\<^sub>0 unit.map\<^sub>1 counit.map\<^sub>0 counit.map\<^sub>1"
        using B.bicategory_axioms D.bicategory_axioms FH.pseudofunctor_axioms
              KG.pseudofunctor_axioms unit.pseudonatural_equivalence_axioms
              counit.pseudonatural_equivalence_axioms I\<^sub>B.identity_pseudofunctor_axioms
              I\<^sub>D.identity_pseudofunctor_axioms FH_KG.composite_pseudofunctor_axioms
              KG_FH.composite_pseudofunctor_axioms
        unfolding equivalence_of_bicategories_def by simp
    qed

    lemma is_equivalence_of_bicategories:
    shows "equivalence_of_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             left_map left_cmp right_map right_cmp unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1"
      ..

  end

  subsection "Equivalence with a Dense Sub-bicategory"

  text \<open>
    The purpose of this section is to show that, given a bicategory \<open>B\<close> and a sub-bicategory
    defined by a ``dense'' set of objects of \<open>B\<close>, the embedding of the sub-bicategory in \<open>B\<close>
    extends to an equivalence of bicategories.  Here by ``dense'' we mean that every object
    of \<open>B\<close> is equivalent to some object of the subbicategory.
  \<close>

  locale dense_subbicategory =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B +
    subbicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B \<open>\<lambda>\<mu>. B.arr \<mu> \<and> src\<^sub>B \<mu> \<in> Obj \<and> trg\<^sub>B \<mu> \<in> Obj\<close>
  for V\<^sub>B :: "'b comp"                    (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'b comp"                    (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"        ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'b \<Rightarrow> 'b"                    ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'b \<Rightarrow> 'b"
  and trg\<^sub>B :: "'b \<Rightarrow> 'b"
  and Obj :: "'b set" +
  assumes dense: "\<And>a. B.obj a \<Longrightarrow> \<exists>a'. a' \<in> Obj \<and> B.equivalent_objects a' a"
  begin

    notation B.\<a>'         ("\<a>\<^sub>B\<^sup>-\<^sup>1[_, _, _]")
    notation B.lunit      ("\<l>\<^sub>B[_]")
    notation B.lunit'     ("\<l>\<^sub>B\<^sup>-\<^sup>1[_]")
    notation B.runit      ("\<r>\<^sub>B[_]")
    notation B.runit'     ("\<r>\<^sub>B\<^sup>-\<^sup>1[_]")

    notation comp         (infixr "\<cdot>" 55)
    notation hcomp        (infixr "\<star>" 53)
    notation in_hom       ("\<guillemotleft>_ : _ \<Rightarrow> _\<guillemotright>")
    notation in_hhom      ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")
    notation \<a>            ("\<a>[_, _, _]")
    notation \<a>'           ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    notation lunit        ("\<l>[_]")
    notation lunit'       ("\<l>\<^sup>-\<^sup>1[_]")
    notation runit        ("\<r>[_]")
    notation runit'       ("\<r>\<^sup>-\<^sup>1[_]")

    abbreviation (input) Arr
    where "Arr \<equiv> \<lambda>\<mu>. B.arr \<mu> \<and> src\<^sub>B \<mu> \<in> Obj \<and> trg\<^sub>B \<mu> \<in> Obj"

    sublocale emb: embedding_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B Arr
      ..

    abbreviation E
    where "E \<equiv> emb.map"

    abbreviation \<Phi>\<^sub>E
    where "\<Phi>\<^sub>E \<equiv> emb.cmp"

    text \<open>
      We define a projection \<open>P\<close> by transporting arrows of \<open>B\<close> across chosen
      equivalences between objects of \<open>B\<close> and objects of the sub-bicategory.
    \<close>

    definition P\<^sub>0
    where "P\<^sub>0 a \<equiv> SOME a'. obj a' \<and> B.equivalent_objects a' a"

    lemma P\<^sub>0_props:
    assumes "B.obj a"
    shows "obj (P\<^sub>0 a)"
    and "B.equivalent_objects (P\<^sub>0 a) a"
    and "B.equivalent_objects a a' \<Longrightarrow> P\<^sub>0 a = P\<^sub>0 a'"
    and "P\<^sub>0 (P\<^sub>0 a) = P\<^sub>0 a"
    and "B.obj (P\<^sub>0 a)"
    and "P\<^sub>0 a \<in> Obj"
    proof -
      have "\<exists>a'. obj a' \<and> B.equivalent_objects a' a"
        using assms dense [of a] obj_char arr_char
        by (metis (no_types, lifting) B.equivalent_objects_def B.in_hhomE B.obj_def B.obj_simps(3))
      hence 1: "obj (P\<^sub>0 a) \<and> B.equivalent_objects (P\<^sub>0 a) a"
        unfolding P\<^sub>0_def
        using someI_ex [of "\<lambda>a'. obj a' \<and> B.equivalent_objects a' a"] by blast
      show "obj (P\<^sub>0 a)"
        using 1 by simp
      show 2: "B.equivalent_objects (P\<^sub>0 a) a"
        using 1 by simp
      show 3: "\<And>a'. B.equivalent_objects a a' \<Longrightarrow> P\<^sub>0 a = P\<^sub>0 a'"
      proof -
        fix a'
        assume a': "B.equivalent_objects a a'"
        have "(\<lambda>a''. obj a'' \<and> B.equivalent_objects a'' a) =
              (\<lambda>a''. obj a'' \<and> B.equivalent_objects a'' a')"
          using a' B.equivalent_objects_symmetric B.equivalent_objects_transitive by blast
        thus "P\<^sub>0 a = P\<^sub>0 a'"
          unfolding P\<^sub>0_def by simp
      qed
      show "P\<^sub>0 (P\<^sub>0 a) = P\<^sub>0 a"
        using 2 3 [of "P\<^sub>0 a"] B.equivalent_objects_symmetric by auto
      show "B.obj (P\<^sub>0 a)"
        using 1 B.equivalent_objects_def by auto
      thus "P\<^sub>0 a \<in> Obj"
        using 1 3 obj_char arr_char by auto
    qed

    text \<open>
      For each object \<open>a\<close> of \<open>B\<close>, we choose an adjoint equivalence from \<open>a\<close> to \<open>P\<^sub>0 a\<close>.
      The use of adjoint equivalences is necessary in order to establish the required
      coherence conditions.
    \<close>

    definition e
    where "e a = (SOME e. \<guillemotleft>e : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright> \<and>
                   (\<exists>d \<eta> \<epsilon>. adjoint_equivalence_in_bicategory
                              V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B e d \<eta> \<epsilon>))"

    definition d
    where "d a = (SOME d. \<exists>\<eta> \<epsilon>. adjoint_equivalence_in_bicategory
                                  V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) d \<eta> \<epsilon>)"

    definition \<eta>
    where "\<eta> a = (SOME \<eta>. \<exists>\<epsilon>. adjoint_equivalence_in_bicategory
                                V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) (d a) \<eta> \<epsilon>)"

    definition \<epsilon>
    where "\<epsilon> a = (SOME \<epsilon>. adjoint_equivalence_in_bicategory
                            V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) (d a) (\<eta> a) \<epsilon>)"

    lemma chosen_adjoint_equivalence:
    assumes "B.obj a"
    shows "adjoint_equivalence_in_bicategory
             V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) (d a) (\<eta> a) (\<epsilon> a)"
    and "\<guillemotleft>e a : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>" and "B.ide (d a)" and "B.ide (e a)" and "B.iso (\<eta> a)" and "B.iso (\<epsilon> a)"
    proof -
      have "\<exists>e. \<guillemotleft>e : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright> \<and>
                (\<exists>d \<eta> \<epsilon>. adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B e d \<eta> \<epsilon>)"
      proof -
        obtain e where e: "\<guillemotleft>e : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright> \<and> B.equivalence_map e"
          using assms P\<^sub>0_props(2) B.equivalent_objects_symmetric B.equivalent_objects_def
          by meson
        obtain d \<eta> \<epsilon> where d: "adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B e d \<eta> \<epsilon>"
          using e B.equivalence_map_extends_to_adjoint_equivalence by blast
        thus ?thesis
          using e d by auto
      qed
      hence 1: "\<guillemotleft>e a : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright> \<and>
                adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) (d a) (\<eta> a) (\<epsilon> a)"
        using d_def e_def \<eta>_def \<epsilon>_def arr_char
            someI_ex [of "\<lambda>e. \<guillemotleft>e : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright> \<and>
                          (\<exists>d \<eta> \<epsilon>. adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B e d \<eta> \<epsilon>)"]
            someI_ex [of "\<lambda>d. (\<exists>\<eta> \<epsilon>. adjoint_equivalence_in_bicategory
                                       V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) d \<eta> \<epsilon>)"]
            someI_ex [of "\<lambda>\<eta>. \<exists>\<epsilon>. adjoint_equivalence_in_bicategory
                                    V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) (d a) \<eta> \<epsilon>"]
            someI_ex [of "\<lambda>\<epsilon>. adjoint_equivalence_in_bicategory
                                V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) (d a) (\<eta> a) \<epsilon>"]
        by simp
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using 1 by simp
      show "adjoint_equivalence_in_bicategory
              V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B (e a) (d a) (\<eta> a) (\<epsilon> a)" ..
      show "\<guillemotleft>e a : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>" using 1 by simp
      show "B.ide (d a)" by simp
      show "B.ide (e a)" by simp
      show "B.iso (\<eta> a)" by simp
      show "B.iso (\<epsilon> a)" by simp
    qed

    lemma equivalence_data_in_hom\<^sub>B [intro]:
    assumes "B.obj a"
    shows "\<guillemotleft>e a : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>" and "\<guillemotleft>d a : P\<^sub>0 a \<rightarrow>\<^sub>B a\<guillemotright>"
    and "\<guillemotleft>e a : e a \<Rightarrow>\<^sub>B e a\<guillemotright>" and "\<guillemotleft>d a : d a \<Rightarrow>\<^sub>B d a\<guillemotright>"
    and "\<guillemotleft>\<eta> a : a \<rightarrow>\<^sub>B a\<guillemotright>" and "\<guillemotleft>\<epsilon> a : P\<^sub>0 a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<eta> a : a \<Rightarrow>\<^sub>B d a \<star>\<^sub>B e a\<guillemotright>" and "\<guillemotleft>\<epsilon> a : e a \<star>\<^sub>B d a \<Rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>"
    proof -
      interpret adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show e: "\<guillemotleft>e a : a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>"
        using assms chosen_adjoint_equivalence by simp
      show "\<guillemotleft>d a : P\<^sub>0 a \<rightarrow>\<^sub>B a\<guillemotright>" using e antipar by auto
      show "\<guillemotleft>e a : e a \<Rightarrow>\<^sub>B e a\<guillemotright>" by auto
      show "\<guillemotleft>d a : d a \<Rightarrow>\<^sub>B d a\<guillemotright>" by auto
      show "\<guillemotleft>\<eta> a : a \<rightarrow>\<^sub>B a\<guillemotright>" using unit_in_hom e by auto
      show "\<guillemotleft>\<epsilon> a : P\<^sub>0 a \<rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>" using counit_in_hom e by auto
      show "\<guillemotleft>\<eta> a : a \<Rightarrow>\<^sub>B d a \<star>\<^sub>B e a\<guillemotright>" using unit_in_hom e by auto
      show "\<guillemotleft>\<epsilon> a : e a \<star>\<^sub>B d a \<Rightarrow>\<^sub>B P\<^sub>0 a\<guillemotright>" using counit_in_hom e by auto
    qed

    lemma equivalence_data_simps\<^sub>B [simp]:
    assumes "B.obj a"
    shows "B.ide (d a)" and "B.ide (e a)" and "B.iso (\<eta> a)" and "B.iso (\<epsilon> a)"
    and "src\<^sub>B (e a) = a" and "trg\<^sub>B (e a) = P\<^sub>0 a" and "src\<^sub>B (d a) = P\<^sub>0 a" and "trg\<^sub>B (d a) = a"
    and "B.dom (e a) = e a" and "B.cod (e a) = e a"
    and "B.dom (d a) = d a" and "B.cod (d a) = d a"
    and "src\<^sub>B (\<eta> a) = a" and "trg\<^sub>B (\<eta> a) = a" and "src\<^sub>B (\<epsilon> a) = P\<^sub>0 a" and "trg\<^sub>B (\<epsilon> a) = P\<^sub>0 a"
    and "B.dom (\<eta> a) = a" and "B.cod (\<eta> a) = d a \<star>\<^sub>B e a"
    and "B.dom (\<epsilon> a) = e a \<star>\<^sub>B d a" and "B.cod (\<epsilon> a) = P\<^sub>0 a"
      using assms chosen_adjoint_equivalence equivalence_data_in_hom\<^sub>B B.in_hhom_def
                       apply auto
      by (meson B.in_homE)+

    lemma equivalence_data_in_hom [intro]:
    assumes "obj a"
    shows "\<guillemotleft>e a : a \<rightarrow> P\<^sub>0 a\<guillemotright>" and "\<guillemotleft>d a : P\<^sub>0 a \<rightarrow> a\<guillemotright>"
    and "\<guillemotleft>e a : e a \<Rightarrow> e a\<guillemotright>" and "\<guillemotleft>d a : d a \<Rightarrow> d a\<guillemotright>"
    and "\<guillemotleft>\<eta> a : a \<rightarrow> a\<guillemotright>" and "\<guillemotleft>\<epsilon> a : P\<^sub>0 a \<rightarrow> P\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<eta> a : a \<Rightarrow> d a \<star> e a\<guillemotright>" and "\<guillemotleft>\<epsilon> a : e a \<star> d a \<Rightarrow> P\<^sub>0 a\<guillemotright>"
    proof -
      have a: "B.obj a \<and> a \<in> Obj"
        using assms obj_char arr_char by auto
      have P\<^sub>0a: "obj (P\<^sub>0 a) \<and> P\<^sub>0 a \<in> Obj"
        using assms a P\<^sub>0_props [of a] arr_char obj_char by auto
      show ea: "\<guillemotleft>e a : a \<rightarrow> P\<^sub>0 a\<guillemotright>"
        using a P\<^sub>0a arr_char chosen_adjoint_equivalence(2) src_def trg_def by auto
      show "\<guillemotleft>e a : e a \<Rightarrow> e a\<guillemotright>"
        using a ea chosen_adjoint_equivalence(4) ide_char in_hom_char by auto
      show da: "\<guillemotleft>d a : P\<^sub>0 a \<rightarrow> a\<guillemotright>"
        using a P\<^sub>0a arr_char src_def trg_def P\<^sub>0_props(1) equivalence_data_in_hom\<^sub>B(2)
        by auto
      show "\<guillemotleft>d a : d a \<Rightarrow> d a\<guillemotright>"
        using a da chosen_adjoint_equivalence(3) ide_char in_hom_char by auto
      show \<eta>a: "\<guillemotleft>\<eta> a : a \<Rightarrow> d a \<star> e a\<guillemotright>"
      proof
        show 1: "arr (\<eta> a)"
          using assms a P\<^sub>0a da ea arr_char equivalence_data_in_hom\<^sub>B(7) hcomp_closed
          by (metis (no_types, lifting) equivalence_data_in_hom\<^sub>B(5) B.in_hhom_def)
        show "dom (\<eta> a) = a"
          using a 1 dom_char equivalence_data_in_hom\<^sub>B(7) by auto
        show "cod (\<eta> a) = d a \<star> e a"
          using a 1 da ea cod_char in_hom_char equivalence_data_in_hom\<^sub>B(7) hcomp_def
          by (metis (no_types, lifting) hcomp_char in_hhomE B.in_homE)
      qed
      show \<epsilon>a: "\<guillemotleft>\<epsilon> a : e a \<star> d a \<Rightarrow> P\<^sub>0 a\<guillemotright>"
      proof
        show 1: "arr (\<epsilon> a)"
          using assms a P\<^sub>0a da ea arr_char equivalence_data_in_hom\<^sub>B(8) hcomp_closed
          by (metis (no_types, lifting) equivalence_data_in_hom\<^sub>B(6) B.in_hhom_def)
        show "dom (\<epsilon> a) = e a \<star> d a"
          using a 1 da ea dom_char in_hom_char equivalence_data_in_hom\<^sub>B(8) hcomp_def
          by (metis (no_types, lifting) hcomp_char in_hhomE B.in_homE)
        show "cod (\<epsilon> a) = P\<^sub>0 a"
          using a 1 cod_char equivalence_data_in_hom\<^sub>B(8) by auto
      qed
      show "\<guillemotleft>\<eta> a : a \<rightarrow> a\<guillemotright>"
        using assms \<eta>a src_def trg_def src_dom trg_dom
        by (metis (no_types, lifting) in_hhom_def in_hom_char obj_simps(2-3)
            vconn_implies_hpar(1-2))
      show "\<guillemotleft>\<epsilon> a : P\<^sub>0 a \<rightarrow> P\<^sub>0 a\<guillemotright>"
        using P\<^sub>0a \<epsilon>a src_def trg_def src_cod trg_cod
        by (metis (no_types, lifting) in_hhom_def in_hom_char obj_simps(2-3)
            vconn_implies_hpar(1-4))
    qed

    lemma equivalence_data_simps [simp]:
    assumes "obj a"
    shows "ide (d a)" and "ide (e a)" and "iso (\<eta> a)" and "iso (\<epsilon> a)"
    and "src (e a) = a" and "trg (e a) = P\<^sub>0 a" and "src (d a) = P\<^sub>0 a" and "trg (d a) = a"
    and "dom (e a) = e a" and "cod (e a) = e a"
    and "dom (d a) = d a" and "cod (d a) = d a"
    and "src (\<eta> a) = a" and "trg (\<eta> a) = a" and "src (\<epsilon> a) = P\<^sub>0 a" and "trg (\<epsilon> a) = P\<^sub>0 a"
    and "dom (\<eta> a) = a" and "cod (\<eta> a) = d a \<star>\<^sub>B e a"
    and "dom (\<epsilon> a) = e a \<star>\<^sub>B d a" and "cod (\<epsilon> a) = P\<^sub>0 a"
      using assms obj_char arr_char ide_char dom_char cod_char iso_char P\<^sub>0_props
            equivalence_data_in_hom B.iso_is_arr src_def trg_def
      by auto (* 18 sec *)

    definition P
    where "P \<mu> = e (trg\<^sub>B \<mu>) \<star>\<^sub>B \<mu> \<star>\<^sub>B d (src\<^sub>B \<mu>)"

    lemma P_in_hom\<^sub>B [intro]:
    assumes "B.arr \<mu>"
    shows "\<guillemotleft>P \<mu> : P\<^sub>0 (src\<^sub>B \<mu>) \<rightarrow>\<^sub>B P\<^sub>0 (trg\<^sub>B \<mu>)\<guillemotright>"
    and "\<guillemotleft>P \<mu> : P (B.dom \<mu>) \<Rightarrow>\<^sub>B P (B.cod \<mu>)\<guillemotright>"
      unfolding P_def using assms by auto

    lemma P_simps\<^sub>B [simp]:
    assumes "B.arr \<mu>"
    shows "B.arr (P \<mu>)"
    and "src\<^sub>B (P \<mu>) = P\<^sub>0 (src\<^sub>B \<mu>)" and "trg\<^sub>B (P \<mu>) = P\<^sub>0 (trg\<^sub>B \<mu>)"
    and "B.dom (P \<mu>) = P (B.dom \<mu>)" and "B.cod (P \<mu>) = P (B.cod \<mu>)"
      using assms P_in_hom\<^sub>B by blast+

    lemma P_in_hom [intro]:
    assumes "B.arr \<mu>"
    shows "\<guillemotleft>P \<mu> : P\<^sub>0 (src\<^sub>B \<mu>) \<rightarrow> P\<^sub>0 (trg\<^sub>B \<mu>)\<guillemotright>"
    and "\<guillemotleft>P \<mu> : P (B.dom \<mu>) \<Rightarrow> P (B.cod \<mu>)\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>P \<mu> : P\<^sub>0 (src\<^sub>B \<mu>) \<rightarrow> P\<^sub>0 (trg\<^sub>B \<mu>)\<guillemotright>"
        using assms P_in_hom\<^sub>B(1) arr_char src_def trg_def P\<^sub>0_props(1)
        by (metis (no_types, lifting) in_hhom_def obj_char B.in_hhomE B.obj_simps(2)
            B.obj_src B.obj_trg)
      show "\<guillemotleft>P \<mu> : P (B.dom \<mu>) \<Rightarrow> P (B.cod \<mu>)\<guillemotright>"
        using assms 1 dom_char cod_char
        by (intro in_homI) auto
    qed

    lemma P_simps [simp]:
    assumes "B.arr \<mu>"
    shows "arr (P \<mu>)"
    and "src (P \<mu>) = P\<^sub>0 (src\<^sub>B \<mu>)" and "trg (P \<mu>) = P\<^sub>0 (trg\<^sub>B \<mu>)"
    and "dom (P \<mu>) = P (B.dom \<mu>)" and "cod (P \<mu>) = P (B.cod \<mu>)"
      using assms P_in_hom by blast+

    interpretation P: "functor" V\<^sub>B comp P
    proof
      show "\<And>\<mu>. \<not> B.arr \<mu> \<Longrightarrow> P \<mu> = null"
        using P_def null_char B.hseq_char B.hseq_char' by auto
      have 0: "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> B.arr (P \<mu>)"
        by simp
      show 1: "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> arr (P \<mu>)"
        using P_simps\<^sub>B(1) by simp
      show 2: "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> dom (P \<mu>) = P (B.dom \<mu>)"
        using 1 dom_simp by auto
      show 3: "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> cod (P \<mu>) = P (B.cod \<mu>)"
        using 1 cod_simp by auto
      show "\<And>\<mu> \<nu>. B.seq \<mu> \<nu> \<Longrightarrow> P (\<mu> \<cdot>\<^sub>B \<nu>) = P \<mu> \<cdot> P \<nu>"
      proof -
        fix \<mu> \<nu>
        assume seq: "B.seq \<mu> \<nu>"
        show "P (\<mu> \<cdot>\<^sub>B \<nu>) = P \<mu> \<cdot> P \<nu>"
        proof -
          have 4: "P (\<mu> \<cdot>\<^sub>B \<nu>) = e (trg\<^sub>B \<mu>) \<star>\<^sub>B \<mu> \<cdot>\<^sub>B \<nu> \<star>\<^sub>B d (src\<^sub>B \<mu>)"
            unfolding P_def using seq B.src_vcomp B.trg_vcomp by simp
          also have "... = P \<mu> \<cdot>\<^sub>B P \<nu>"
            unfolding P_def
            using seq 0 4 B.whisker_left B.whisker_right
            by (metis equivalence_data_simps\<^sub>B(1-2) B.hseqE B.obj_trg B.seqE B.src_vcomp
                B.vseq_implies_hpar(2))
          also have "... = P \<mu> \<cdot> P \<nu>"
            using seq 1 seq_char comp_char by auto
          finally show ?thesis by blast
        qed
      qed
    qed

    interpretation faithful_functor V\<^sub>B comp P
    proof
      fix \<mu> \<mu>'
      assume par: "B.par \<mu> \<mu>'"
      have 1: "src\<^sub>B \<mu> = src\<^sub>B \<mu>' \<and> trg\<^sub>B \<mu> = trg\<^sub>B \<mu>'"
        using par B.src_dom B.trg_dom by fastforce
      assume eq: "P \<mu> = P \<mu>'"
      interpret src: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                       \<open>e (src\<^sub>B \<mu>)\<close> \<open>d (src\<^sub>B \<mu>)\<close> \<open>\<eta> (src\<^sub>B \<mu>)\<close> \<open>\<epsilon> (src\<^sub>B \<mu>)\<close>
        using par chosen_adjoint_equivalence by simp
      interpret trg: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                       \<open>e (trg\<^sub>B \<mu>)\<close> \<open>d (trg\<^sub>B \<mu>)\<close> \<open>\<eta> (trg\<^sub>B \<mu>)\<close> \<open>\<epsilon> (trg\<^sub>B \<mu>)\<close>
        using par chosen_adjoint_equivalence by simp
      show "\<mu> = \<mu>'"
        using eq par 1
        unfolding P_def
        using B.equivalence_cancel_left [of "e (trg\<^sub>B \<mu>)" "\<mu> \<star>\<^sub>B d (src\<^sub>B \<mu>)" "\<mu>' \<star>\<^sub>B d (src\<^sub>B \<mu>')"]
              B.equivalence_cancel_right [of "d (src\<^sub>B \<mu>)" \<mu> \<mu>']
              B.equivalence_map_def src.dual_equivalence trg.equivalence_in_bicategory_axioms
        by auto
    qed

    interpretation P: weak_arrow_of_homs V\<^sub>B src\<^sub>B trg\<^sub>B comp src trg P
    proof
      fix \<mu>
      assume \<mu>: "B.arr \<mu>"
      interpret src: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                       \<open>e (src\<^sub>B \<mu>)\<close> \<open>d (src\<^sub>B \<mu>)\<close> \<open>\<eta> (src\<^sub>B \<mu>)\<close> \<open>\<epsilon> (src\<^sub>B \<mu>)\<close>
        using \<mu> chosen_adjoint_equivalence by simp
      show "isomorphic (P (src\<^sub>B \<mu>)) (src (P \<mu>))"
      proof (unfold isomorphic_def)
        show "\<exists>f. \<guillemotleft>f : P (src\<^sub>B \<mu>) \<Rightarrow> src (P \<mu>)\<guillemotright> \<and> iso f"
        proof -
          let ?\<phi> = "\<epsilon> (src\<^sub>B \<mu>) \<cdot>\<^sub>B (e (src\<^sub>B \<mu>) \<star>\<^sub>B \<l>\<^sub>B[d (src\<^sub>B \<mu>)])"
          have "\<guillemotleft>?\<phi> : P (src\<^sub>B \<mu>) \<Rightarrow> src (P \<mu>)\<guillemotright> \<and> iso ?\<phi>"
          proof -
            have 1: "\<guillemotleft>?\<phi> : P (src\<^sub>B \<mu>) \<Rightarrow>\<^sub>B P\<^sub>0 (src\<^sub>B \<mu>)\<guillemotright> \<and> B.iso ?\<phi>"
              unfolding P_def using \<mu> by auto
            moreover have "arr ?\<phi> \<and> arr (B.inv ?\<phi>)"
              using \<mu> 1 arr_char P\<^sub>0_props(1)
              by (metis (no_types, lifting) P\<^sub>0_props(6) B.arrI B.arr_inv equivalence_data_simps\<^sub>B(16)
                  B.obj_src src.counit_simps(4-5) B.src_inv B.src_vcomp
                  B.trg_inv B.trg_vcomp)
            moreover have "P\<^sub>0 (src\<^sub>B \<mu>) = src (P \<mu>)"
              using \<mu> by simp
            ultimately show ?thesis
              using \<mu> in_hom_char arr_char iso_char
              by (metis (no_types, lifting) src_closed equivalence_data_simps\<^sub>B(6)
                  B.obj_src P.preserves_arr src.counit_simps(4) B.src.preserves_arr B.src_vcomp)
          qed
          thus ?thesis by blast
        qed
      qed
      interpret trg: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                       \<open>e (trg\<^sub>B \<mu>)\<close> \<open>d (trg\<^sub>B \<mu>)\<close> \<open>\<eta> (trg\<^sub>B \<mu>)\<close> \<open>\<epsilon> (trg\<^sub>B \<mu>)\<close>
        using \<mu> chosen_adjoint_equivalence by simp
      show "isomorphic (P (trg\<^sub>B \<mu>)) (trg (P \<mu>))"
      proof (unfold isomorphic_def)
        show "\<exists>f. \<guillemotleft>f : P (trg\<^sub>B \<mu>) \<Rightarrow> trg (P \<mu>)\<guillemotright> \<and> iso f"
        proof -
          let ?\<psi> = "\<epsilon> (trg\<^sub>B \<mu>) \<cdot>\<^sub>B (e (trg\<^sub>B \<mu>) \<star>\<^sub>B \<l>\<^sub>B[d (trg\<^sub>B \<mu>)])"
          have "\<guillemotleft>?\<psi> : P (trg\<^sub>B \<mu>) \<Rightarrow> trg (P \<mu>)\<guillemotright> \<and> iso ?\<psi>"
          proof -
            have 1: "\<guillemotleft>?\<psi> : P (trg\<^sub>B \<mu>) \<Rightarrow>\<^sub>B P\<^sub>0 (trg\<^sub>B \<mu>)\<guillemotright> \<and> B.iso ?\<psi>"
              unfolding P_def using \<mu> by auto
            moreover have "arr ?\<psi> \<and> arr (B.inv ?\<psi>)"
              using \<mu> 1 arr_char P\<^sub>0_props(1)
              by (metis (no_types, lifting) obj_char B.arrI B.arr_inv B.obj_trg B.src_inv B.trg_inv
                  B.vconn_implies_hpar(1-4))
            moreover have "arr (P (trg\<^sub>B \<mu>)) \<and> arr (P\<^sub>0 (trg\<^sub>B \<mu>))"
              using \<mu> arr_char P\<^sub>0_props(1) P_simps(1) obj_char by auto
            moreover have "P\<^sub>0 (trg\<^sub>B \<mu>) = trg (P \<mu>)"
              using \<mu> by simp
            ultimately show ?thesis
              using in_hom_char iso_char by force
          qed
          thus ?thesis by blast
        qed
      qed
    qed

    text \<open>
      The following seems to be needed to avoid non-confluent simplifications,
      \emph{e.g.}~of \<open>S.src (P \<mu>)\<close> to \<open>P.map\<^sub>0 a\<close> and to \<open>P\<^sub>0 a\<close>.
    \<close>

    lemma P_map\<^sub>0_simp [simp]:
    assumes "B.obj a"
    shows "P.map\<^sub>0 a = P\<^sub>0 a"
      using assms P.map\<^sub>0_def B.obj_simps(1-2) by simp

    interpretation HoPP: composite_functor B.VV.comp VV.comp comp
                           P.FF \<open>\<lambda>\<mu>\<nu>. hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
      ..
    interpretation PoH: composite_functor B.VV.comp V\<^sub>B comp \<open>(\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>)\<close> P
      ..

    no_notation B.in_hom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    definition CMP
    where "CMP f g \<equiv> (e (trg\<^sub>B f) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d (src\<^sub>B g)]) \<cdot>\<^sub>B
                      (e (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B
                          \<l>\<^sub>B[g \<star>\<^sub>B d (src\<^sub>B g)] \<cdot>\<^sub>B (B.inv (\<eta> (trg\<^sub>B g)) \<star>\<^sub>B g \<star>\<^sub>B d (src\<^sub>B g))) \<cdot>\<^sub>B
                      (e (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d (src\<^sub>B f), e (trg\<^sub>B g), g \<star>\<^sub>B d (src\<^sub>B g)]) \<cdot>\<^sub>B
                      \<a>\<^sub>B[e (trg\<^sub>B f), f, d (src\<^sub>B f) \<star>\<^sub>B P g] \<cdot>\<^sub>B
                      \<a>\<^sub>B[e (trg\<^sub>B f) \<star>\<^sub>B f, d (src\<^sub>B f), P g] \<cdot>\<^sub>B
                      (\<a>\<^sub>B\<^sup>-\<^sup>1[e (trg\<^sub>B f), f, d (src\<^sub>B f)] \<star>\<^sub>B P g)"

    text \<open>
      The 2-cell \<open>CMP f g\<close> has the right type to be a compositor for a pseudofunctor
      whose underlying mapping is \<open>P\<close>.
    \<close>

    lemma CMP_in_hom [intro]:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "\<guillemotleft>CMP f g : P\<^sub>0 (src\<^sub>B g) \<rightarrow> P\<^sub>0 (trg\<^sub>B f)\<guillemotright>"
    and "\<guillemotleft>CMP f g : P f \<star> P g \<Rightarrow> P (f \<star>\<^sub>B g)\<guillemotright>"
    and "\<guillemotleft>CMP f g : P\<^sub>0 (src\<^sub>B g) \<rightarrow>\<^sub>B P\<^sub>0 (trg\<^sub>B f)\<guillemotright>"
    and "\<guillemotleft>CMP f g : P f \<star>\<^sub>B P g \<Rightarrow>\<^sub>B P (f \<star>\<^sub>B g)\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>CMP f g : P f \<star>\<^sub>B P g \<Rightarrow>\<^sub>B P (f \<star>\<^sub>B g)\<guillemotright>"
        using assms
        by (unfold P_def CMP_def, intro B.comp_in_homI' B.seqI B.hseqI') auto
      show 2: "\<guillemotleft>CMP f g : P\<^sub>0 (src\<^sub>B g) \<rightarrow>\<^sub>B P\<^sub>0 (trg\<^sub>B f)\<guillemotright>"
        using assms 1 B.src_cod B.trg_cod B.vconn_implies_hpar(1-2) by auto
      show 3: "\<guillemotleft>CMP f g : P f \<star> P g \<Rightarrow> P (f \<star>\<^sub>B g)\<guillemotright>"
      proof -
        have "\<guillemotleft>CMP f g : P f \<star>\<^sub>B P g \<Rightarrow> P (f \<star>\<^sub>B g)\<guillemotright>"
          using assms 1 2 in_hom_char arr_char P\<^sub>0_props(1) P.preserves_arr by auto
        moreover have "P f \<star>\<^sub>B P g = P f \<star> P g"
          using assms hcomp_eqI by simp
        ultimately show ?thesis by simp
      qed
      show "\<guillemotleft>CMP f g : P\<^sub>0 (src\<^sub>B g) \<rightarrow> P\<^sub>0 (trg\<^sub>B f)\<guillemotright>"
        using 2 3 arr_char src_def trg_def by fastforce
    qed

    lemma CMP_simps [simp]:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "arr (CMP f g)"
    and "src (CMP f g) = P\<^sub>0 (src\<^sub>B g)" and "trg (CMP f g) = P\<^sub>0 (trg\<^sub>B f)"
    and "dom (CMP f g) = P f \<star> P g" and "cod (CMP f g) = P (f \<star>\<^sub>B g)"
    and "B.arr (CMP f g)"
    and "src\<^sub>B (CMP f g) = P\<^sub>0 (src\<^sub>B g)" and "trg\<^sub>B (CMP f g) = P\<^sub>0 (trg\<^sub>B f)"
    and "B.dom (CMP f g) = P f \<star>\<^sub>B P g" and "B.cod (CMP f g) = P (f \<star>\<^sub>B g)"
      using assms CMP_in_hom [of f g] by auto

    lemma iso_CMP:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "iso (CMP f g)"
    and "B.iso (CMP f g)"
    proof -
      show "B.iso (CMP f g)"
        unfolding CMP_def P_def
        using assms B.VV.arr_char P.components_are_iso
        by (intro B.isos_compose B.iso_hcomp) auto
      thus "iso (CMP f g)"
        using assms iso_char arr_char CMP_simps(1) by auto
    qed

    abbreviation (input) SRC
    where "SRC \<mu> \<equiv> d (src\<^sub>B \<mu>) \<star>\<^sub>B e (src\<^sub>B \<mu>)"

    abbreviation (input) TRG
    where "TRG \<mu> \<equiv> d (trg\<^sub>B \<mu>) \<star>\<^sub>B e (trg\<^sub>B \<mu>)"

    definition LUNIT
    where "LUNIT f \<equiv> \<l>\<^sub>B[f] \<cdot>\<^sub>B (B.inv (\<eta> (trg\<^sub>B f)) \<star>\<^sub>B f)"

    definition RUNIT
    where "RUNIT f \<equiv> \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B f)))"

    text \<open>
      Here we prove a series of results that would be automatic if we had some notion of
      ``bicategory with \<open>SRC\<close> and \<open>TRG\<close> as alternative source and target''.
      Perhaps this idea can be developed in future work and used to simplify the overall
      development.
    \<close>

    lemma LUNIT_in_hom [intro]:
    assumes "B.ide f"
    shows "\<guillemotleft>LUNIT f : src\<^sub>B f \<rightarrow>\<^sub>B trg\<^sub>B f\<guillemotright>"
    and "\<guillemotleft>LUNIT f : TRG f \<star>\<^sub>B f \<Rightarrow>\<^sub>B f\<guillemotright>"
    proof -
      interpret e_trg_f: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (trg\<^sub>B f)\<close> \<open>d (trg\<^sub>B f)\<close> \<open>\<eta> (trg\<^sub>B f)\<close> \<open>\<epsilon> (trg\<^sub>B f)\<close>
        using assms chosen_adjoint_equivalence by simp
      show "\<guillemotleft>LUNIT f : src\<^sub>B f \<rightarrow>\<^sub>B trg\<^sub>B f\<guillemotright>"
        unfolding LUNIT_def
        using assms e_trg_f.unit_is_iso by auto
      show "\<guillemotleft>LUNIT f : TRG f \<star>\<^sub>B f \<Rightarrow>\<^sub>B f\<guillemotright>"
        unfolding LUNIT_def
        using assms e_trg_f.unit_is_iso by auto
    qed

    lemma LUNIT_simps [simp]:
    assumes "B.ide f"
    shows "B.arr (LUNIT f)"
    and "src\<^sub>B (LUNIT f) = src\<^sub>B f" and "trg\<^sub>B (LUNIT f) = trg\<^sub>B f"
    and "B.dom (LUNIT f) = TRG f \<star>\<^sub>B f"
    and "B.cod (LUNIT f) = f"
      using assms LUNIT_in_hom by auto

    lemma RUNIT_in_hom [intro]:
    assumes "B.ide f"
    shows "\<guillemotleft>RUNIT f : src\<^sub>B f \<rightarrow>\<^sub>B trg\<^sub>B f\<guillemotright>"
    and "\<guillemotleft>RUNIT f : f \<star>\<^sub>B SRC f \<Rightarrow>\<^sub>B f\<guillemotright>"
    proof -
      interpret e_src_f: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (src\<^sub>B f)\<close> \<open>d (src\<^sub>B f)\<close> \<open>\<eta> (src\<^sub>B f)\<close> \<open>\<epsilon> (src\<^sub>B f)\<close>
        using assms chosen_adjoint_equivalence by simp
      show "\<guillemotleft>RUNIT f : src\<^sub>B f \<rightarrow>\<^sub>B trg\<^sub>B f\<guillemotright>"
        unfolding RUNIT_def
        using assms e_src_f.unit_is_iso by auto
      show "\<guillemotleft>RUNIT f : f \<star>\<^sub>B SRC f \<Rightarrow>\<^sub>B f\<guillemotright>"
        unfolding RUNIT_def
        using assms e_src_f.unit_is_iso by auto
    qed

    lemma RUNIT_simps [simp]:
    assumes "B.ide f"
    shows "B.arr (RUNIT f)"
    and "src\<^sub>B (RUNIT f) = src\<^sub>B f" and "trg\<^sub>B (RUNIT f) = trg\<^sub>B f"
    and "B.dom (RUNIT f) = f \<star>\<^sub>B SRC f"
    and "B.cod (RUNIT f) = f"
      using assms RUNIT_in_hom by auto

    lemma iso_LUNIT:
    assumes "B.ide f"
    shows "B.iso (LUNIT f)"
    proof -
      interpret e_trg_f: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (trg\<^sub>B f)\<close> \<open>d (trg\<^sub>B f)\<close> \<open>\<eta> (trg\<^sub>B f)\<close> \<open>\<epsilon> (trg\<^sub>B f)\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis
        using assms e_trg_f.unit_is_iso LUNIT_def LUNIT_simps(1) by auto
    qed

    lemma iso_RUNIT:
    assumes "B.ide f"
    shows "B.iso (RUNIT f)"
    proof -
      interpret e_src_f: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (src\<^sub>B f)\<close> \<open>d (src\<^sub>B f)\<close> \<open>\<eta> (src\<^sub>B f)\<close> \<open>\<epsilon> (src\<^sub>B f)\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis
        using assms e_src_f.unit_is_iso RUNIT_def RUNIT_simps(1) by auto
    qed

    lemma LUNIT_naturality:
    assumes "B.arr \<mu>"
    shows "\<mu> \<cdot>\<^sub>B LUNIT (B.dom \<mu>) = LUNIT (B.cod \<mu>) \<cdot>\<^sub>B (TRG \<mu> \<star>\<^sub>B \<mu>)"
    proof -
      interpret e_trg_\<mu>: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (trg\<^sub>B \<mu>)\<close> \<open>d (trg\<^sub>B \<mu>)\<close> \<open>\<eta> (trg\<^sub>B \<mu>)\<close> \<open>\<epsilon> (trg\<^sub>B \<mu>)\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis
      proof -
        have "\<mu> \<cdot>\<^sub>B LUNIT (B.dom \<mu>) = (\<mu> \<cdot>\<^sub>B \<l>\<^sub>B[B.dom \<mu>]) \<cdot>\<^sub>B (B.inv (\<eta> (trg\<^sub>B \<mu>)) \<star>\<^sub>B B.dom \<mu>)"
          unfolding LUNIT_def
          using assms B.comp_assoc by simp
        also have "... = \<l>\<^sub>B[B.cod \<mu>] \<cdot>\<^sub>B (trg\<^sub>B \<mu> \<star>\<^sub>B \<mu>) \<cdot>\<^sub>B (B.inv (\<eta> (trg\<^sub>B \<mu>)) \<star>\<^sub>B B.dom \<mu>)"
          using assms B.lunit_naturality B.comp_assoc by simp
        also have "... = \<l>\<^sub>B[B.cod \<mu>] \<cdot>\<^sub>B (B.inv (\<eta> (trg\<^sub>B \<mu>)) \<star>\<^sub>B \<mu>)"
          using assms B.interchange [of "trg\<^sub>B \<mu>" "B.inv (\<eta> (trg\<^sub>B \<mu>))" \<mu> "B.dom \<mu>"]
                e_trg_\<mu>.unit_is_iso B.comp_arr_dom B.comp_cod_arr by simp
        also have "... = \<l>\<^sub>B[B.cod \<mu>] \<cdot>\<^sub>B (B.inv (\<eta> (trg\<^sub>B \<mu>)) \<star>\<^sub>B B.cod \<mu>) \<cdot>\<^sub>B (TRG \<mu> \<star>\<^sub>B \<mu>)"
          using assms B.interchange [of "B.inv (\<eta> (trg\<^sub>B \<mu>))" "TRG \<mu>" "B.cod \<mu>" \<mu>]
                e_trg_\<mu>.unit_is_iso B.comp_arr_dom B.comp_cod_arr by simp
        also have "... = LUNIT (B.cod \<mu>) \<cdot>\<^sub>B (TRG \<mu> \<star>\<^sub>B \<mu>)"
          unfolding LUNIT_def
          using assms B.comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma RUNIT_naturality:
    assumes "B.arr \<mu>"
    shows "\<mu> \<cdot>\<^sub>B RUNIT (B.dom \<mu>) = RUNIT (B.cod \<mu>) \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B SRC \<mu>)"
    proof -
      interpret e_src_\<mu>: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (src\<^sub>B \<mu>)\<close> \<open>d (src\<^sub>B \<mu>)\<close> \<open>\<eta> (src\<^sub>B \<mu>)\<close> \<open>\<epsilon> (src\<^sub>B \<mu>)\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis
      proof -
        have "\<mu> \<cdot>\<^sub>B RUNIT (B.dom \<mu>) =
              (\<mu> \<cdot>\<^sub>B \<r>\<^sub>B[B.dom \<mu>]) \<cdot>\<^sub>B (B.dom \<mu> \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B \<mu>)))"
          unfolding RUNIT_def
          using assms B.comp_assoc by simp
        also have "... = \<r>\<^sub>B[B.cod \<mu>] \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B src\<^sub>B \<mu>) \<cdot>\<^sub>B (B.dom \<mu> \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B \<mu>)))"
          using assms B.runit_naturality B.comp_assoc by simp
        also have "... = \<r>\<^sub>B[B.cod \<mu>] \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B \<mu>)))"
          using assms B.interchange [of \<mu> "B.dom \<mu>" "src\<^sub>B \<mu>" "B.inv (\<eta> (src\<^sub>B \<mu>))"]
                e_src_\<mu>.unit_is_iso B.comp_arr_dom B.comp_cod_arr by simp
        also have "... = \<r>\<^sub>B[B.cod \<mu>] \<cdot>\<^sub>B (B.cod \<mu> \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B \<mu>))) \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B SRC \<mu>)"
          using assms B.interchange [of "B.cod \<mu>" \<mu> "B.inv (\<eta> (src\<^sub>B \<mu>))" "SRC \<mu>"]
                e_src_\<mu>.unit_is_iso B.comp_arr_dom B.comp_cod_arr
          by simp
        also have "... = RUNIT (B.cod \<mu>) \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B SRC \<mu>)"
          unfolding RUNIT_def
          using assms B.comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma LUNIT_hcomp:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "LUNIT (f \<star>\<^sub>B g) \<cdot>\<^sub>B \<a>\<^sub>B[d (trg\<^sub>B f) \<star>\<^sub>B e (trg\<^sub>B f), f, g] = LUNIT f \<star>\<^sub>B g"
    proof -
      interpret e_trg_f: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (trg\<^sub>B f)\<close> \<open>d (trg\<^sub>B f)\<close> \<open>\<eta> (trg\<^sub>B f)\<close> \<open>\<epsilon> (trg\<^sub>B f)\<close>
        using assms chosen_adjoint_equivalence by simp
      have "LUNIT (f \<star>\<^sub>B g) \<cdot>\<^sub>B \<a>\<^sub>B[TRG f, f, g] =
            \<l>\<^sub>B[f \<star>\<^sub>B g] \<cdot>\<^sub>B (B.inv (\<eta> (trg\<^sub>B f)) \<star>\<^sub>B f \<star>\<^sub>B g) \<cdot>\<^sub>B \<a>\<^sub>B[TRG f, f, g]"
        unfolding LUNIT_def
        using assms B.comp_assoc by simp
      also have "... = (\<l>\<^sub>B[f \<star>\<^sub>B g] \<cdot>\<^sub>B \<a>\<^sub>B[trg\<^sub>B f, f, g]) \<cdot>\<^sub>B ((B.inv (\<eta> (trg\<^sub>B f)) \<star>\<^sub>B f) \<star>\<^sub>B g)"
        using assms B.assoc_naturality [of "B.inv (\<eta> (trg\<^sub>B f))" f g] e_trg_f.unit_is_iso
              B.comp_assoc
        by simp
      also have "... = (\<l>\<^sub>B[f] \<star>\<^sub>B g) \<cdot>\<^sub>B ((B.inv (\<eta> (trg\<^sub>B f)) \<star>\<^sub>B f) \<star>\<^sub>B g)"
        using assms B.lunit_hcomp by simp
      also have "... = LUNIT f \<star>\<^sub>B g"
        using assms LUNIT_def LUNIT_simps(1) B.whisker_right by auto
      finally show ?thesis by simp
    qed

    lemma RUNIT_hcomp:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "RUNIT (f \<star>\<^sub>B g) = (f \<star>\<^sub>B RUNIT g) \<cdot>\<^sub>B \<a>\<^sub>B[f, g, SRC g]"
    proof -
      interpret e_src_g: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (src\<^sub>B g)\<close> \<open>d (src\<^sub>B g)\<close> \<open>\<eta> (src\<^sub>B g)\<close> \<open>\<epsilon> (src\<^sub>B g)\<close>
        using assms chosen_adjoint_equivalence by simp
      have "(f \<star>\<^sub>B RUNIT g) \<cdot>\<^sub>B \<a>\<^sub>B[f, g, SRC g] =
            (f \<star>\<^sub>B \<r>\<^sub>B[g]) \<cdot>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B g))) \<cdot>\<^sub>B \<a>\<^sub>B[f, g, SRC g]"
        unfolding RUNIT_def
        using assms B.whisker_left e_src_g.unit_is_iso B.comp_assoc by simp
      also have "... = ((f \<star>\<^sub>B \<r>\<^sub>B[g]) \<cdot>\<^sub>B \<a>\<^sub>B[f, g, src\<^sub>B g]) \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B g)))"
        using assms B.assoc_naturality [of f g "B.inv (\<eta> (src\<^sub>B g))"] e_src_g.unit_is_iso
              B.comp_assoc
        by simp
      also have "... = \<r>\<^sub>B[f \<star>\<^sub>B g] \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B g)))"
        using assms B.runit_hcomp by simp
      also have "... = RUNIT (f \<star>\<^sub>B g)"
        using assms RUNIT_def by simp
      finally show ?thesis by simp
    qed

    lemma TRIANGLE:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "(f \<star>\<^sub>B LUNIT g) \<cdot>\<^sub>B \<a>\<^sub>B[f, SRC f, g] = RUNIT f \<star>\<^sub>B g"
    proof -
      interpret e_trg_g: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                            \<open>e (trg\<^sub>B g)\<close> \<open>d (trg\<^sub>B g)\<close> \<open>\<eta> (trg\<^sub>B g)\<close> \<open>\<epsilon> (trg\<^sub>B g)\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis
      proof -
        have "(f \<star>\<^sub>B LUNIT g) \<cdot>\<^sub>B \<a>\<^sub>B[f, SRC f, g] =
              (f \<star>\<^sub>B \<l>\<^sub>B[g]) \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> (trg\<^sub>B g)) \<star>\<^sub>B g) \<cdot>\<^sub>B \<a>\<^sub>B[f, SRC f, g]"
          using assms B.whisker_left e_trg_g.unit_is_iso LUNIT_def LUNIT_simps(1) B.comp_assoc
          by auto
        also have "... = ((f \<star>\<^sub>B \<l>\<^sub>B[g]) \<cdot>\<^sub>B \<a>\<^sub>B[f, src\<^sub>B f, g]) \<cdot>\<^sub>B ((f \<star>\<^sub>B B.inv (\<eta> (trg\<^sub>B g))) \<star>\<^sub>B g)"
          using assms B.assoc_naturality [of f "B.inv (\<eta> (trg\<^sub>B g))" g] e_trg_g.unit_is_iso
                B.comp_assoc
          by auto
        also have "... = (\<r>\<^sub>B[f] \<star>\<^sub>B g) \<cdot>\<^sub>B ((f \<star>\<^sub>B B.inv (\<eta> (trg\<^sub>B g))) \<star>\<^sub>B g)"
          using assms B.triangle by simp
        also have "... = RUNIT f \<star>\<^sub>B g"
          using assms B.whisker_right e_trg_g.unit_is_iso RUNIT_def RUNIT_simps
          by metis
        finally show ?thesis by simp
      qed
    qed

    text \<open>
      The \<open>CMP f g\<close> also satisfy the naturality conditions required of compositors.
    \<close>

    lemma CMP_naturality:
    assumes "B.arr \<mu>" and "B.arr \<nu>" and "src\<^sub>B \<mu> = trg\<^sub>B \<nu>"
    shows "CMP (B.cod \<mu>) (B.cod \<nu>) \<cdot>\<^sub>B (P \<mu> \<star>\<^sub>B P \<nu>)
             = P (\<mu> \<star>\<^sub>B \<nu>) \<cdot>\<^sub>B CMP (B.dom \<mu>) (B.dom \<nu>)"
    proof -
      let ?a = "src\<^sub>B \<nu>"
      let ?b = "src\<^sub>B \<mu>"
      let ?c = "trg\<^sub>B \<mu>"
      let ?f = "B.dom \<mu>"
      let ?g = "B.cod \<mu>"
      let ?h = "B.dom \<nu>"
      let ?k = "B.cod \<nu>"
      have "CMP ?g ?k \<cdot>\<^sub>B (P \<mu> \<star>\<^sub>B P \<nu>)
              = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B
                (e ?c \<star>\<^sub>B ?g \<star>\<^sub>B LUNIT (?k \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                (e ?c \<star>\<^sub>B ?g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?c, ?g, d ?b \<star>\<^sub>B P ?k] \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?c \<star>\<^sub>B ?g, d ?b, P ?k] \<cdot>\<^sub>B
                (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?g, d ?b] \<star>\<^sub>B P ?k) \<cdot>\<^sub>B
                (P \<mu> \<star>\<^sub>B P \<nu>)"
        unfolding CMP_def LUNIT_def using assms B.comp_assoc by simp
      also have "... = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?g \<star>\<^sub>B LUNIT (?k \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c, ?g, d ?b \<star>\<^sub>B P ?k] \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?c \<star>\<^sub>B ?g, d ?b, P ?k] \<cdot>\<^sub>B
                       (((e ?c \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?b) \<star>\<^sub>B P \<nu>)) \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
      proof -
        have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?g, d ?b] \<star>\<^sub>B P ?k) \<cdot>\<^sub>B (P \<mu> \<star>\<^sub>B P \<nu>)
                = \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?g, d ?b] \<cdot>\<^sub>B P \<mu> \<star>\<^sub>B P ?k \<cdot>\<^sub>B P \<nu>"
          using assms P_def B.interchange by fastforce
        also have
          "... = ((e ?c \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?b) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?k \<cdot>\<^sub>B P \<nu>"
          using assms P_def B.assoc'_naturality [of "e ?c" \<mu> "d ?b"] by simp
        also have
          "... = ((e ?c \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?b) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P \<nu> \<cdot>\<^sub>B P ?h"
          using assms B.comp_arr_dom B.comp_cod_arr B.src_cod B.src_dom
                B.trg_cod B.trg_dom P.naturality
          by simp
        also have "... = (((e ?c \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?b) \<star>\<^sub>B P \<nu>) \<cdot>\<^sub>B (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
          using assms B.interchange by auto
        finally have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?g, d ?b] \<star>\<^sub>B P ?k) \<cdot>\<^sub>B (P \<mu> \<star>\<^sub>B P \<nu>)
                        = (((e ?c \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?b) \<star>\<^sub>B P \<nu>) \<cdot>\<^sub>B (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?g \<star>\<^sub>B LUNIT (?k \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?c, ?g, d ?b \<star>\<^sub>B P ?k] \<cdot>\<^sub>B
                       ((e ?c \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?b \<star>\<^sub>B P \<nu>)) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c \<star>\<^sub>B ?f, d ?b, P ?h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
        using assms B.assoc_naturality [of "e ?c \<star>\<^sub>B \<mu>" "d ?b" "P \<nu>"] B.comp_assoc by simp
      also have "... = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?g \<star>\<^sub>B LUNIT (?k \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       ((e ?c \<star>\<^sub>B ?g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?b \<star>\<^sub>B P \<nu>)) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c, ?f, d ?b \<star>\<^sub>B P ?h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c \<star>\<^sub>B ?f, d ?b, P ?h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
        using assms B.assoc_naturality [of "e ?c" \<mu> "d ?b \<star>\<^sub>B P \<nu>"] B.comp_assoc by simp
      also have "... = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B
                       ((e ?c \<star>\<^sub>B ?g \<star>\<^sub>B LUNIT (?k \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B SRC \<mu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c, ?f, d ?b \<star>\<^sub>B P ?h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c \<star>\<^sub>B ?f, d ?b, P ?h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
      proof -
        have
          "(e ?c \<star>\<^sub>B ?g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?b \<star>\<^sub>B P \<nu>)
             = (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B TRG \<nu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
               (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a])"
        proof -
          have "(e ?c \<star>\<^sub>B ?g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?b \<star>\<^sub>B P \<nu>)
                  = e ?c \<star>\<^sub>B (?g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B d ?b \<star>\<^sub>B P \<nu>)"
            using assms P_def B.whisker_left by simp
          also have "... = e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a] \<cdot>\<^sub>B (d ?b \<star>\<^sub>B P \<nu>)"
            using assms P_def B.comp_cod_arr
                  B.interchange [of "?g" \<mu> "\<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?k \<star>\<^sub>B d ?a]" "d ?b \<star>\<^sub>B P \<nu>"]
            by simp
          also have "... = e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B
                             (TRG \<nu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a]"
            using assms P_def B.assoc'_naturality [of "d ?b" "e ?b" "\<nu> \<star>\<^sub>B d ?a"]
            by simp
          also have "... = e ?c \<star>\<^sub>B
                             (\<mu> \<star>\<^sub>B TRG \<nu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (?f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a])"
            using assms B.comp_arr_dom
                  B.interchange [of \<mu> "?f" "TRG \<nu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a""\<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a]"]
            by fastforce
          also have
            "... = (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B TRG \<nu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                   (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a])"
            using assms B.whisker_left by simp
          finally show ?thesis by simp
        qed
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B LUNIT (?h \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c, ?f, d ?b \<star>\<^sub>B P ?h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c \<star>\<^sub>B ?f, d ?b, P ?h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
      proof -
        have "((e ?c \<star>\<^sub>B ?g \<star>\<^sub>B LUNIT (?k \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B TRG \<nu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a))
                = e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B LUNIT (B.cod (\<nu> \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B ((d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a)"
          using assms comp_arr_dom B.comp_cod_arr B.whisker_left
                B.interchange [of "?g" \<mu> "LUNIT (?k \<star>\<^sub>B d ?a)" "(d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a"]
          by fastforce
        also have "... = e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B (\<nu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B LUNIT (?h \<star>\<^sub>B d ?a)"
          using assms LUNIT_naturality [of "\<nu> \<star>\<^sub>B d ?a"] by simp
        also have "... = (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B LUNIT (?h \<star>\<^sub>B d ?a))"
          using assms B.comp_arr_dom B.comp_cod_arr B.whisker_left
                B.interchange [of \<mu> "?f" "\<nu> \<star>\<^sub>B d ?a" "LUNIT (?h \<star>\<^sub>B d ?a)"]
          by simp
        finally have "((e ?c \<star>\<^sub>B ?g \<star>\<^sub>B LUNIT (?k \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                      (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B TRG \<nu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a))
                        = (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B LUNIT (?h \<star>\<^sub>B d ?a))"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = P (\<mu> \<star>\<^sub>B \<nu>) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?f, ?h, d ?a]) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B LUNIT (?h \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (e ?c \<star>\<^sub>B ?f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ?h \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c, ?f, d ?b \<star>\<^sub>B P ?h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?c \<star>\<^sub>B ?f, d ?b, P ?h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, ?f, d ?b] \<star>\<^sub>B P ?h)"
      proof -
        have "(e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a)
                = P (\<mu> \<star>\<^sub>B \<nu>) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?f, ?h, d ?a])"
        proof -
          have "(e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a]) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B \<mu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a)
                  = e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?g, ?k, d ?a] \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B \<nu> \<star>\<^sub>B d ?a)"
            using assms B.whisker_left by simp
          also have "... = e ?c \<star>\<^sub>B ((\<mu> \<star>\<^sub>B \<nu>) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?f, ?h, d ?a]"
            using assms B.assoc'_naturality [of \<mu> \<nu> "d ?a"] by simp
          also have "... = P (\<mu> \<star>\<^sub>B \<nu>) \<cdot>\<^sub>B (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?f, ?h, d ?a])"
            using assms P_def B.whisker_left by simp
          finally show ?thesis by simp
        qed
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = P (\<mu> \<star>\<^sub>B \<nu>) \<cdot>\<^sub>B CMP ?f ?h"
        unfolding CMP_def LUNIT_def using assms by simp
      finally show ?thesis by simp
    qed

    interpretation EV: self_evaluation_map V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B ..
    notation EV.eval ("\<lbrace>_\<rbrace>")

    abbreviation (input) SRCt  ("\<^bold>S\<^bold>R\<^bold>C")
    where "\<^bold>S\<^bold>R\<^bold>C \<mu> \<equiv> \<^bold>\<langle>d (src\<^sub>B \<mu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e (src\<^sub>B \<mu>)\<^bold>\<rangle>"

    abbreviation (input) TRGt  ("\<^bold>T\<^bold>R\<^bold>G")
    where "\<^bold>T\<^bold>R\<^bold>G \<mu> \<equiv> \<^bold>\<langle>d (trg\<^sub>B \<mu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e (trg\<^sub>B \<mu>)\<^bold>\<rangle>"

    abbreviation (input) PRJt  ("\<^bold>P\<^bold>R\<^bold>J")
    where "\<^bold>P\<^bold>R\<^bold>J \<mu> \<equiv> \<^bold>\<langle>e (trg\<^sub>B \<mu>)\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<mu>\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d (src\<^sub>B \<mu>)\<^bold>\<rangle>"

    text \<open>
      The \<open>CMP f g\<close> satisfy the coherence conditions with respect to associativity that are
      required of compositors.
    \<close>

    lemma CMP_coherence:
    assumes "B.ide f" and "B.ide g" and "B.ide h" and "src\<^sub>B f = trg\<^sub>B g" and "src\<^sub>B g = trg\<^sub>B h"
    shows "P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B CMP (f \<star>\<^sub>B g) h \<cdot>\<^sub>B (CMP f g \<star>\<^sub>B P h)
             = CMP f (g \<star>\<^sub>B h) \<cdot>\<^sub>B (P f \<star>\<^sub>B CMP g h) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h]"
    proof -
      text \<open>
        The overall strategy of the proof is to expand the definition of \<open>CMP\<close> on the
        left and right-hand sides, then permute the occurrences of \<open>LUNIT\<close> and
        \<open>RUNIT\<close> to the left ends of both the left-hand side and right-hand side of the
        equation to be proved, so that the initial portions of these expressions become
        identical and the remaining parts to the right consist only of canonical isomorphisms.
        Then the Coherence Theorem is applied to prove syntactically (and automatically) that the
        canonical parts are equal, which implies equality of the complete expressions.
        The rest is just grinding through the calculations.
      \<close>
      let ?a = "trg\<^sub>B f"
      let ?b = "trg\<^sub>B g"
      let ?c = "trg\<^sub>B h"
      let ?d = "src\<^sub>B h"
      have "P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B CMP (f \<star>\<^sub>B g) h \<cdot>\<^sub>B (CMP f g \<star>\<^sub>B P h)
              = P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B
                (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, h, d ?d]) \<cdot>\<^sub>B
                (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<cdot>\<^sub>B
                 (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B d ?c)) \<cdot>\<^sub>B
                 (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<cdot>\<^sub>B
                 \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<cdot>\<^sub>B
                 \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<cdot>\<^sub>B
                 (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g)
                    \<star>\<^sub>B P h)"
        unfolding CMP_def LUNIT_def using assms B.comp_assoc by simp
      also have "... = P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B d ?c)) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
        using assms B.whisker_right P_def by simp (* 6 sec *)
      also have "... = P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B d ?c)) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B (LUNIT h \<star>\<^sub>B d ?d) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]"
          using assms LUNIT_hcomp [of h "d ?d"] B.invert_side_of_triangle by simp
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])"
          using assms B.whisker_left by simp
        finally have "e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B d ?c)) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, h, d ?d]) \<cdot>\<^sub>B (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, h, d ?d] \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h \<star>\<^sub>B d ?d)"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B (((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                                 \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]"
          using assms B.assoc'_naturality [of "f \<star>\<^sub>B g" "LUNIT h" "d ?d"] by simp
        also have "... = (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, h, d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B d ?c)) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d"
          using assms B.whisker_left B.whisker_right P_def by simp
        also have "... = e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<cdot>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d"
          using assms B.assoc_naturality [of f g "LUNIT h"] by simp
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d)"
          using assms B.whisker_left B.whisker_right by simp
        finally have "P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d)"
          by simp
        thus ?thesis using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B d ?c) \<star>\<^sub>B P h)) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "((e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B d ?c)) \<star>\<^sub>B P h)
                = (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g \<star>\<^sub>B d ?c) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h"
          using assms TRIANGLE [of f "g \<star>\<^sub>B d ?c"] B.invert_side_of_triangle by simp
        also have "... = ((e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B d ?c) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                         ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h)"
          using assms B.whisker_left B.whisker_right P_def by simp
        finally have "((e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B d ?c)) \<star>\<^sub>B P h)
                        = ((e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B d ?c) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                          ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h)"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h)) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B TRG g, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B ((e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B d ?c) \<star>\<^sub>B P h)
                = (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c] \<cdot>\<^sub>B (RUNIT f \<star>\<^sub>B g \<star>\<^sub>B d ?c)) \<star>\<^sub>B P h"
          using assms B.whisker_left B.whisker_right P_def by simp
        also have "... = (e ?a \<star>\<^sub>B
                           ((RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B TRG g, g, d ?c])
                              \<star>\<^sub>B P h"
          using assms B.assoc'_naturality [of "RUNIT f" g "d ?c"] by simp
        also have "... = ((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                         ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B TRG g, g, d ?c]) \<star>\<^sub>B P h)"
          using assms B.whisker_left B.whisker_right P_def by simp
        finally have "((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                      ((e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B d ?c) \<star>\<^sub>B P h)
                        = ((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                          ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B TRG g, g, d ?c]) \<star>\<^sub>B P h)"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g)) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h)) \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B ((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h)
                = \<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<cdot>\<^sub>B (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h"
          using assms B.whisker_left B.whisker_right P_def by simp
        also have "... = ((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g)) \<star>\<^sub>B d ?c) \<cdot>\<^sub>B
                         \<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h"
          using assms B.assoc'_naturality [of "e ?a" "RUNIT f \<star>\<^sub>B g" "d ?c"] by simp
        also have "... = (((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g)) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h)"
          using assms B.whisker_left B.whisker_right P_def by simp
        finally have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                      ((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h)
                        = (((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g)) \<star>\<^sub>B d ?c) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                          (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h)"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g)) \<star>\<^sub>B d ?c \<star>\<^sub>B P h)) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
        using assms B.assoc_naturality [of "e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g)" "d ?c" "P h"] B.comp_assoc
        by simp
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c \<star>\<^sub>B P h)) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
        using assms B.assoc_naturality [of "e ?a" "RUNIT f \<star>\<^sub>B g" "d ?c \<star>\<^sub>B P h"] B.comp_assoc
        by simp
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d])) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "((e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c \<star>\<^sub>B P h))
                = e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d] \<cdot>\<^sub>B (d ?c \<star>\<^sub>B P h)"
          using assms B.comp_cod_arr B.whisker_left P_def
                B.interchange [of "f \<star>\<^sub>B g" "RUNIT f \<star>\<^sub>B g"]
          by simp
        also have "... = e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]"
          using assms B.comp_arr_dom P_def by simp
        finally have "((e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B d ?c \<star>\<^sub>B P h))
                        = e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d])) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B
                 \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) =
                e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B
                  \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d] \<cdot>\<^sub>B
                  \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]"
          using assms B.comp_arr_dom B.comp_cod_arr B.whisker_left
                B.interchange
                  [of "f \<star>\<^sub>B g" "RUNIT f \<star>\<^sub>B g" "\<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]" "\<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]"]
          by simp (* 3 sec *)
        also have "... = (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d])"
          using assms B.comp_arr_dom B.whisker_left
                B.interchange [of "RUNIT f \<star>\<^sub>B g" "(f \<star>\<^sub>B SRC f) \<star>\<^sub>B g" "\<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]"
                                  "\<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]"]
          by simp
        finally have "(e ?a \<star>\<^sub>B (f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d])
                        = (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B
                             \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d])
                = e ?a \<star>\<^sub>B (\<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B
                           (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[f, g, ((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]"
        proof -
          have "(\<a>\<^sub>B\<^sup>-\<^sup>1[f, g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B
                (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d])
                  = \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B
                    \<a>\<^sub>B\<^sup>-\<^sup>1[f, g, ((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]"
            using assms B.pentagon' B.comp_assoc by simp
          moreover have "B.inv (\<a>\<^sub>B\<^sup>-\<^sup>1[f, g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h] \<star>\<^sub>B d ?d)
                           = \<a>\<^sub>B[f, g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h] \<star>\<^sub>B d ?d"
            using assms by simp
          ultimately show ?thesis
            using assms B.comp_assoc
                  B.invert_opposite_sides_of_square
                    [of "\<a>\<^sub>B\<^sup>-\<^sup>1[f, g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h] \<star>\<^sub>B d ?d"
                        "\<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B
                           (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d])"
                        "\<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d]"
                        "\<a>\<^sub>B\<^sup>-\<^sup>1[f, g, ((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]"]
            by simp (* 3 sec *)
        qed
        also have "... = (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, TRG h \<star>\<^sub>B h] \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d])
                        = (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, (d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])
                = e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d] \<cdot>\<^sub>B ((RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B
                           (RUNIT f \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]"
          using assms B.hseqI' B.assoc_naturality [of "RUNIT f" g "\<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]"]
          by simp
        also have "... = (e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B \<a>\<^sub>B[f, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B (RUNIT f \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])
                        = (e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d))) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c \<star>\<^sub>B e ?c, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c \<star>\<^sub>B e ?c, h, d ?d]
                = (e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])"
          using assms B.whisker_left B.comp_arr_dom B.comp_cod_arr
                B.interchange [of "RUNIT f" "f \<star>\<^sub>B SRC f" "g \<star>\<^sub>B ((TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
                                  "g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]"]
          by simp (* 5 sec *)
        also have "... = (e ?a \<star>\<^sub>B
                           (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])"
          using assms TRIANGLE [of f "g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d"] by simp
        also have "... = (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])"
          using assms B.whisker_left B.comp_assoc by simp
        finally have "e ?a \<star>\<^sub>B RUNIT f \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]
                        = (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d])"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B f \<star>\<^sub>B
                    (LUNIT g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                    \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b \<star>\<^sub>B e ?b, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]"
          using assms LUNIT_hcomp [of g "(TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d"]
                B.invert_side_of_triangle
          by simp
        also have "... = (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d])"
          using assms B.whisker_left by simp
        finally have "e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d])"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B (LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B f \<star>\<^sub>B
                    \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B (LUNIT g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B f \<star>\<^sub>B
                           ((LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]"
          using assms B.assoc'_naturality [of "LUNIT g" "TRG h \<star>\<^sub>B h" "d ?d"]
          by simp
        also have "... = (e ?a \<star>\<^sub>B f \<star>\<^sub>B (LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B f \<star>\<^sub>B (LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d])"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = ((e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B SRC g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>B g) \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B f \<star>\<^sub>B (LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B
                         (f \<star>\<^sub>B (LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B
                           ((f \<star>\<^sub>B LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>B g) \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]"
          using assms B.assoc'_naturality [of f "LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h" "d ?d"] by simp
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>B g) \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B f \<star>\<^sub>B (LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>B g) \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d])"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>B g) \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
      proof -
        have "(e ?a \<star>\<^sub>B (f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d"
          using assms B.whisker_left B.whisker_right B.comp_arr_dom B.comp_cod_arr
                B.interchange [of g "LUNIT g" "LUNIT h" "(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h"]
          by simp (* 5 sec *)
        thus ?thesis
          using assms by simp
      qed
      finally have L: "P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B CMP (f \<star>\<^sub>B g) h \<cdot>\<^sub>B (CMP f g \<star>\<^sub>B P h)
                         = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>B g) \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                           ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                           ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                           ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"
        by simp

      have "CMP f (g \<star>\<^sub>B h) \<cdot>\<^sub>B (P f \<star>\<^sub>B CMP g h) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h]
              = (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT ((g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B
                (P f \<star>\<^sub>B
                  (e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d]) \<cdot>\<^sub>B
                  (e ?b \<star>\<^sub>B g \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                  (e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                  (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h)) \<cdot>\<^sub>B
                \<a>\<^sub>B[P f, P g, P h]"
        unfolding CMP_def LUNIT_def using assms B.comp_assoc by simp
      also have "... = (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT ((g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
        using assms B.whisker_left P_def B.comp_assoc by auto (* 5 sec *)
      also have "... = ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT ((g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B f \<star>\<^sub>B (LUNIT (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]"
          using assms LUNIT_hcomp [of "g \<star>\<^sub>B h" "d ?d"] B.invert_side_of_triangle
          by simp
        also have "... = (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d])"
          using assms B.whisker_left by simp
        finally have "e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT ((g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B ((f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                                 \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]"
          using assms B.assoc'_naturality [of f "LUNIT (g \<star>\<^sub>B h)" "d ?d"]
                LUNIT_in_hom [of "g \<star>\<^sub>B h"]
          by auto
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B
                       ((P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B RUNIT g \<star>\<^sub>B h \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d)
                = P f \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h \<star>\<^sub>B d ?d) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>B d ?d]"
          using assms TRIANGLE [of g "h \<star>\<^sub>B d ?d"] B.invert_side_of_triangle by simp
        also have "... = (P f \<star>\<^sub>B e ?b \<star>\<^sub>B RUNIT g \<star>\<^sub>B h \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>B d ?d])"
          using assms B.whisker_left P_def by simp
        finally have "P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B LUNIT (h \<star>\<^sub>B d ?d) =
                        (P f \<star>\<^sub>B e ?b \<star>\<^sub>B RUNIT g \<star>\<^sub>B h \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                        (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, TRG h, h \<star>\<^sub>B d ?d])"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "(P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d]) \<cdot>\<^sub>B (P f \<star>\<^sub>B e ?b \<star>\<^sub>B RUNIT g \<star>\<^sub>B h \<star>\<^sub>B d ?d)
                = P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d] \<cdot>\<^sub>B (RUNIT g \<star>\<^sub>B h \<star>\<^sub>B d ?d)"
          using assms B.whisker_left P_def by simp
        also have "... = P f \<star>\<^sub>B e ?b \<star>\<^sub>B
                           ((RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]"
          using assms B.assoc'_naturality [of "RUNIT g" h "d ?d"] by auto
        also have "... = (P f \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d])"
          using assms B.whisker_left P_def by simp
        finally have "(P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, h, d ?d]) \<cdot>\<^sub>B
                      (P f \<star>\<^sub>B e ?b \<star>\<^sub>B RUNIT g \<star>\<^sub>B h \<star>\<^sub>B d ?d)
                        = (P f \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d])"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (((e ?a \<star>\<^sub>B f) \<star>\<^sub>B d ?b) \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B (P f \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = \<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d"
          using assms B.comp_arr_dom B.comp_cod_arr P_def
                B.interchange
                  [of "\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b]" "P f" "P (g \<star>\<^sub>B h)" "e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d"]
          by simp
        also have "... = (((e ?a \<star>\<^sub>B f) \<star>\<^sub>B d ?b) \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
          using assms B.comp_arr_dom B.comp_cod_arr
                B.interchange
                  [of "(e ?a \<star>\<^sub>B f) \<star>\<^sub>B d ?b" "\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b]"
                      "e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d"
                      "e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d"]
          by simp (* 4 sec *)
        finally have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P (g \<star>\<^sub>B h)) \<cdot>\<^sub>B
                      (P f \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                        = (((e ?a \<star>\<^sub>B f) \<star>\<^sub>B d ?b) \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P (g \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f) \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
        using assms P_def B.comp_assoc
              B.assoc_naturality [of "e ?a \<star>\<^sub>B f" "d ?b" "e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d"]
        by simp
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?c \<star>\<^sub>B e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
        using assms P_def B.comp_assoc
              B.assoc_naturality [of "e ?a" f "d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d"]
        by simp
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have
          "(e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
           (e ?a \<star>\<^sub>B f \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
             = e ?a \<star>\<^sub>B f \<star>\<^sub>B
                 \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d] \<cdot>\<^sub>B
                 (d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B f \<star>\<^sub>B
                           (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]"
          using assms B.assoc'_naturality [of "d ?b" "e ?b" "(RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d"] by auto
        also have "... = (e ?a \<star>\<^sub>B f \<star>\<^sub>B SRC f \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d])"
          using assms B.whisker_left by simp
        finally have
          "(e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, (g \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
           (e ?a \<star>\<^sub>B f \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
             = (e ?a \<star>\<^sub>B f \<star>\<^sub>B SRC f \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
               (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d])"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "(e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B f \<star>\<^sub>B TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B f \<star>\<^sub>B
                    \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B f \<star>\<^sub>B
                           ((TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]"
          using assms B.assoc'_naturality [of "TRG g" "RUNIT g \<star>\<^sub>B h" "d ?d"] by simp
        also have "... = (e ?a \<star>\<^sub>B f \<star>\<^sub>B (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B f \<star>\<^sub>B TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B f \<star>\<^sub>B (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d])"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B f \<star>\<^sub>B (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d] \<cdot>\<^sub>B
                          (f \<star>\<^sub>B (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left by simp
        also have "... = e ?a \<star>\<^sub>B
                           ((f \<star>\<^sub>B SRC f \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]"
          using assms
                B.assoc'_naturality [of f "(d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)" "d ?d"]
          by simp
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d])"
          using assms B.whisker_left by simp
        finally have "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B g \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B f \<star>\<^sub>B (TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d])"
          using assms by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B \<a>\<^sub>B[g, d ?c \<star>\<^sub>B e ?c, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d
                = e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B(g \<star>\<^sub>B LUNIT h) \<cdot>\<^sub>B \<a>\<^sub>B[g, SRC g, h]) \<star>\<^sub>B d ?d"
          using assms TRIANGLE [of g h] by simp
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B \<a>\<^sub>B[g, TRG h, h]) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left B.whisker_right by simp
        finally have "e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B (RUNIT g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B \<a>\<^sub>B[g, TRG h, h]) \<star>\<^sub>B d ?d)"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       ((e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B \<a>\<^sub>B[g, SRC g, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d
                = e ?a \<star>\<^sub>B (f \<star>\<^sub>B (LUNIT g \<star>\<^sub>B h) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>B d ?d"
          using assms LUNIT_hcomp [of g h] B.invert_side_of_triangle by simp
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left B.whisker_right by simp
        finally have "e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT (g \<star>\<^sub>B h)) \<star>\<^sub>B d ?d
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>B d ?d)"
          by simp
        thus ?thesis
          using assms B.comp_assoc by simp
      qed
      also have "... = ((e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B (TRG g \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>B h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B \<a>\<^sub>B[g, SRC g, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have
          "(e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
           (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)
             = e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, h] \<cdot>\<^sub>B (TRG g \<star>\<^sub>B g \<star>\<^sub>B LUNIT h)) \<star>\<^sub>B d ?d"
          using assms B.whisker_left B.whisker_right by auto
        also have "... = e ?a \<star>\<^sub>B
                           (f \<star>\<^sub>B ((TRG g \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, SRC g \<star>\<^sub>B h]) \<star>\<^sub>B d ?d"
          using assms B.assoc'_naturality [of "TRG g" g "LUNIT h"] by auto
        also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B (TRG g \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                         (e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>B h]) \<star>\<^sub>B d ?d)"
          using assms B.whisker_left B.whisker_right by auto
        finally have "(e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                      (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)
                        = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B (TRG g \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                          (e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>B h]) \<star>\<^sub>B d ?d)"
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>B h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B (f \<star>\<^sub>B TRG g \<star>\<^sub>B \<a>\<^sub>B[g, d ?c \<star>\<^sub>B e ?c, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                       (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                       (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                       \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have "(e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
              (e ?a \<star>\<^sub>B (f \<star>\<^sub>B (TRG g \<star>\<^sub>B g) \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d)
                = e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d"
          using assms B.whisker_left B.whisker_right B.comp_arr_dom B.comp_cod_arr
                B.interchange [of "LUNIT g" "TRG g \<star>\<^sub>B g" h "LUNIT h"]
          by simp (* 4 sec *)
        thus ?thesis
          using assms by simp
      qed
      finally have R: "CMP f (g \<star>\<^sub>B h) \<cdot>\<^sub>B (P f \<star>\<^sub>B CMP g h) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h]
                         = (e ?a \<star>\<^sub>B (f \<star>\<^sub>B LUNIT g \<star>\<^sub>B LUNIT h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>B h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B \<a>\<^sub>B[g, TRG h, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                           (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                           (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                           (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                           (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                           (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                           (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                           (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P f, P g, P h]"
         using assms by simp

      text \<open>
        The portions of the expressions on the right-hand sides of assertions \<open>L\<close> and \<open>R\<close>
        that are not identical only involve canonical isomorphisms, and thus they can be proved
        equal automatically by the simplifier, once we have expressed them in the formal
        language of \<open>B\<close>.
      \<close>

      let ?LHS = "(e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, (TRG g \<star>\<^sub>B g) \<star>\<^sub>B TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g \<star>\<^sub>B g, TRG h \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B \<a>\<^sub>B[f, d ?b \<star>\<^sub>B e ?b, g \<star>\<^sub>B (TRG h \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG h, h, d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B \<a>\<^sub>B[f \<star>\<^sub>B SRC f, g, TRG h \<star>\<^sub>B h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B ((f \<star>\<^sub>B SRC f) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c \<star>\<^sub>B P h] \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c, P h] \<cdot>\<^sub>B
                  (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, (f \<star>\<^sub>B SRC f) \<star>\<^sub>B g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                  ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B SRC f, g, d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                  ((e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, SRC f, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                  ((e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, g \<star>\<^sub>B d ?c]) \<star>\<^sub>B P h) \<cdot>\<^sub>B
                  (\<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                  (\<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P g] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                  ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B P g) \<star>\<^sub>B P h)"

      let ?LHSt = "(\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, (\<^bold>T\<^bold>R\<^bold>G g \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g, \<^bold>\<langle>g\<^bold>\<rangle>, (\<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> (\<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G h, \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d ?c\<^bold>\<rangle>, \<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle>, (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h\<^bold>] \<^bold>\<cdot>
                   \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?c\<^bold>\<rangle>, \<^bold>P\<^bold>R\<^bold>J h\<^bold>] \<^bold>\<cdot>
                   (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle>, (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?c\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h) \<^bold>\<cdot>
                   ((\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?c\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h) \<^bold>\<cdot>
                   ((\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>S\<^bold>R\<^bold>C f, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?c\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h) \<^bold>\<cdot>
                   ((\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?c\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h) \<^bold>\<cdot>
                   (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J g\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h) \<^bold>\<cdot>
                   (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>P\<^bold>R\<^bold>J g\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h) \<^bold>\<cdot>
                   ((\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J g) \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h)"

      let ?RHS = "(e ?a \<star>\<^sub>B (f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, g, TRG h \<star>\<^sub>B h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B (f \<star>\<^sub>B SRC f \<star>\<^sub>B \<a>\<^sub>B[g, TRG h, h]) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[f, TRG g \<star>\<^sub>B (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[TRG g, (g \<star>\<^sub>B SRC g) \<star>\<^sub>B h, d ?d]) \<cdot>\<^sub>B
                  (e ?a \<star>\<^sub>B f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?a, f, d ?b \<star>\<^sub>B P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?a \<star>\<^sub>B f, d ?b, P ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h)] \<cdot>\<^sub>B
                  (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?a, f, d ?b] \<star>\<^sub>B e ?b \<star>\<^sub>B ((g \<star>\<^sub>B SRC g) \<star>\<^sub>B h) \<star>\<^sub>B d ?d) \<cdot>\<^sub>B
                  (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B SRC g, h, d ?d]) \<cdot>\<^sub>B
                  (P f \<star>\<^sub>B e ?b \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, SRC g, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  (P f \<star>\<^sub>B e ?b \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?c, e ?c, h \<star>\<^sub>B d ?d]) \<cdot>\<^sub>B
                  (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b, g, d ?c \<star>\<^sub>B P h]) \<cdot>\<^sub>B
                  (P f \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B g, d ?c, P h]) \<cdot>\<^sub>B
                  (P f \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, g, d ?c] \<star>\<^sub>B P h) \<cdot>\<^sub>B
                  \<a>\<^sub>B[P f, P g, P h]"

      let ?RHSt = "(\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C f \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G h, \<^bold>\<langle>h\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>T\<^bold>R\<^bold>G g \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>T\<^bold>R\<^bold>G g, (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>\<langle>e ?b\<^bold>\<rangle>, ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>)\<^bold>] \<^bold>\<cdot>
                   \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>, (\<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>)\<^bold>] \<^bold>\<cdot>
                   (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?a\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g) \<^bold>\<star> \<^bold>\<langle>h\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>) \<^bold>\<cdot>
                   (\<^bold>P\<^bold>R\<^bold>J f \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>S\<^bold>R\<^bold>C g, \<^bold>\<langle>h\<^bold>\<rangle>, \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>P\<^bold>R\<^bold>J f \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>S\<^bold>R\<^bold>C g, \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>P\<^bold>R\<^bold>J f \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d ?c\<^bold>\<rangle>, \<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>h\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?d\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>P\<^bold>R\<^bold>J f \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>P\<^bold>R\<^bold>J f \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?c\<^bold>\<rangle>, \<^bold>P\<^bold>R\<^bold>J h\<^bold>]) \<^bold>\<cdot>
                   (\<^bold>P\<^bold>R\<^bold>J f \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?c\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J h) \<^bold>\<cdot>
                   \<^bold>\<a>\<^bold>[\<^bold>P\<^bold>R\<^bold>J f, \<^bold>P\<^bold>R\<^bold>J g, \<^bold>P\<^bold>R\<^bold>J h\<^bold>]"

      have E: "?LHS = ?RHS"
      proof -
        have "?LHS = \<lbrace>?LHSt\<rbrace>"
          using assms B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                B.VV.ide_char B.VV.arr_char P_def
          by simp
        also have "... = \<lbrace>?RHSt\<rbrace>"
          using assms by (intro EV.eval_eqI, auto)
        also have "... = ?RHS"
          using assms B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                B.VV.ide_char B.VV.arr_char P_def
          by simp
        finally show ?thesis by blast
      qed
      show ?thesis
        using L R E by argo
    qed

    interpretation CMP: transformation_by_components B.VV.comp comp HoPP.map PoH.map
                          \<open>\<lambda>\<mu>\<nu>. CMP (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
    proof
      show 1: "\<And>fg. B.VV.ide fg \<Longrightarrow> \<guillemotleft>CMP (fst fg) (snd fg) : HoPP.map fg \<Rightarrow> PoH.map fg\<guillemotright>"
        using CMP_in_hom(2) B.VV.ide_char B.VV.arr_char P.FF_def hcomp_def arr_char
              P\<^sub>0_props(1) P.preserves_arr
        by auto
      show "\<And>fg. B.VV.arr fg \<Longrightarrow>
                   CMP (fst (B.VV.cod fg)) (snd (B.VV.cod fg)) \<cdot> HoPP.map fg =
                   PoH.map fg \<cdot> CMP (fst (B.VV.dom fg)) (snd (B.VV.dom fg))"
      proof -
        fix fg
        assume fg: "B.VV.arr fg"
        have "CMP (fst (B.VV.cod fg)) (snd (B.VV.cod fg)) \<cdot> HoPP.map fg =
              CMP (fst (B.VV.cod fg)) (snd (B.VV.cod fg)) \<cdot>\<^sub>B HoPP.map fg"
        proof -
          have "arr (CMP (fst (B.VV.cod fg)) (snd (B.VV.cod fg)))"
            using fg 1 B.VV.ide_char B.VV.arr_char B.VV.cod_char by simp
          moreover have "B.seq (CMP (fst (B.VV.cod fg)) (snd (B.VV.cod fg)))
                               (fst (P.FF fg) \<star> snd (P.FF fg))"
            using fg 1 B.VV.ide_char B.VV.arr_char B.VV.cod_char HoPP.preserves_arr [of fg]
                  P.FF_def hcomp_char
            by auto
          ultimately show ?thesis
            using fg 1 comp_char B.VV.ide_char B.VV.arr_char by simp
        qed
        also have "... = PoH.map fg \<cdot>\<^sub>B CMP (fst (B.VV.dom fg)) (snd (B.VV.dom fg))"
          using fg CMP_naturality [of "fst fg" "snd fg"]
                B.VV.ide_char B.VV.arr_char B.VV.dom_char B.VV.cod_char P.FF_def
                hcomp_def arr_char P\<^sub>0_props(1) P.preserves_arr
          by auto
        also have "... = PoH.map fg \<cdot> CMP (fst (B.VV.dom fg)) (snd (B.VV.dom fg))"
        proof -
          have "P\<^sub>0 (src\<^sub>B (snd fg)) \<in> Obj \<and> P\<^sub>0 (trg\<^sub>B (fst fg)) \<in> Obj"
            using fg P\<^sub>0_props(6) B.VV.arrE B.obj_src B.obj_trg by meson
          moreover have "B.seq (P (fst fg \<star>\<^sub>B snd fg))
                               (CMP (fst (B.VV.dom fg)) (snd (B.VV.dom fg)))"
            using fg 1 B.VV.ide_char B.VV.arr_char B.VV.dom_char by simp
          ultimately show ?thesis
            using fg 1 comp_char arr_char in_hom_char by simp
        qed
        finally show "CMP (fst (B.VV.cod fg)) (snd (B.VV.cod fg)) \<cdot> HoPP.map fg =
                      PoH.map fg \<cdot> CMP (fst (B.VV.dom fg)) (snd (B.VV.dom fg))"
          by blast
      qed
    qed

    interpretation CMP: natural_isomorphism B.VV.comp comp HoPP.map PoH.map CMP.map
      using iso_CMP B.VV.ide_char B.VV.arr_char CMP.map_simp_ide
      by unfold_locales simp

    definition \<Phi>\<^sub>P
    where "\<Phi>\<^sub>P = CMP.map"

    interpretation \<Phi>\<^sub>P: natural_isomorphism B.VV.comp comp HoPP.map PoH.map \<Phi>\<^sub>P
      unfolding \<Phi>\<^sub>P_def
      using CMP.natural_isomorphism_axioms by simp

    no_notation B.in_hom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    lemma \<Phi>\<^sub>P_in_hom [intro]:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "\<guillemotleft>\<Phi>\<^sub>P (f, g) : src (P g) \<rightarrow> trg (P f)\<guillemotright>"
    and "\<guillemotleft>\<Phi>\<^sub>P (f, g) : P f \<star> P g \<Rightarrow> P (f \<star>\<^sub>B g)\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>\<Phi>\<^sub>P (f, g) : P f \<star> P g \<Rightarrow> P (f \<star>\<^sub>B g)\<guillemotright>"
        using assms B.VV.ide_char B.VV.arr_char P.FF_def by auto
      show "\<guillemotleft>\<Phi>\<^sub>P (f, g) : src (P g) \<rightarrow> trg (P f)\<guillemotright>"
        using 1
        by (metis (no_types, lifting) hcomp_simps(2) in_hhom_def in_hom_char
            src_hcomp vconn_implies_hpar(1-2))
    qed

    lemma \<Phi>\<^sub>P_simps [simp]:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B f = trg\<^sub>B g"
    shows "arr (\<Phi>\<^sub>P (f, g))"
    and "src (\<Phi>\<^sub>P (f, g)) = src (P g)"
    and "trg (\<Phi>\<^sub>P (f, g)) = trg (P f)"
    and "dom (\<Phi>\<^sub>P (f, g)) = P f \<star> P g"
    and "cod (\<Phi>\<^sub>P (f, g)) = P (f \<star>\<^sub>B g)"
      using assms \<Phi>\<^sub>P_in_hom by blast+

    sublocale prj: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B comp hcomp \<a> \<i>\<^sub>B src trg P \<Phi>\<^sub>P
    proof
      fix f g h
      assume f: "B.ide f" and g: "B.ide g" and h: "B.ide h"
      and fg: "src\<^sub>B f = trg\<^sub>B g" and gh: "src\<^sub>B g = trg\<^sub>B h"
      have 1: "ide (P f) \<and> ide (P g) \<and> ide (P h)"
        using f g h P.preserves_ide by simp
      have "P \<a>\<^sub>B[f, g, h] \<cdot> \<Phi>\<^sub>P (f \<star>\<^sub>B g, h) \<cdot> (\<Phi>\<^sub>P (f, g) \<star> P h) =
            P \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B \<Phi>\<^sub>P (f \<star>\<^sub>B g, h) \<cdot>\<^sub>B (\<Phi>\<^sub>P (f, g) \<star>\<^sub>B P h)"
        using f g h fg gh B.VV.arr_char B.VV.dom_char B.VV.cod_char P.FF_def
        by (intro comp_eqI hcomp_eqI seqI hseqI') auto
      also have "... = CMP f (g \<star>\<^sub>B h) \<cdot>\<^sub>B (P f \<star>\<^sub>B CMP g h) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h]"
        using f g h fg gh CMP_coherence CMP.map_simp_ide B.VV.ide_char B.VV.arr_char
              \<Phi>\<^sub>P_def
        by simp
      also have "... = \<Phi>\<^sub>P (f, g \<star>\<^sub>B h) \<cdot>\<^sub>B (P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h]"
        using f g h fg gh B.VV.ide_char B.VV.arr_char \<Phi>\<^sub>P_def by simp
      also have "... = \<Phi>\<^sub>P (f, g \<star>\<^sub>B h) \<cdot> (P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) \<cdot> \<a>\<^sub>B[P f, P g, P h]"
      proof -
        have 2: "arr ((P f \<star> \<Phi>\<^sub>P (g, h)) \<cdot> \<a>[P f, P g, P h])"
          using f g h fg gh B.VV.arr_char B.VV.dom_char P.FF_def by auto
        moreover have "(P f \<star> \<Phi>\<^sub>P (g, h)) \<cdot> \<a>[P f, P g, P h] =
                       (P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h]"
          using f g h fg gh 2 comp_eqI hcomp_eqI assoc_simp by auto
        moreover have 3: "arr (P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h))"
          using f g h fg gh arr_hcompI
          by (intro arr_hcompI hseqI') auto
        moreover have "B.dom (P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) = P f \<star>\<^sub>B P g \<star>\<^sub>B P h"
        proof -
          have "B.dom (P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) = P f \<star>\<^sub>B B.dom (\<Phi>\<^sub>P (g, h))"
            using f g h fg gh 3 B.hcomp_simps(3)
            by (metis (no_types, lifting) 1 arrE ideD(1) ideD(2) dom_char)
          also have "... = P f \<star>\<^sub>B P g \<star>\<^sub>B P h"
            using g h gh dom_char hcomp_char \<Phi>\<^sub>P_simps(1-4) by auto
          finally show ?thesis by blast
        qed
        moreover have "B.dom (\<Phi>\<^sub>P (f, g \<star>\<^sub>B h)) =
                       B.cod ((P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h])"
        proof -
          have "B.dom (\<Phi>\<^sub>P (f, g \<star>\<^sub>B h)) = dom (\<Phi>\<^sub>P (f, g \<star>\<^sub>B h))"
            using f g h fg gh B.VV.arr_char dom_char by simp
          also have "... = cod ((P f \<star> \<Phi>\<^sub>P (g, h)) \<cdot> \<a>[P f, P g, P h])"
            using f g h fg gh 2 VV.arr_char \<Phi>\<^sub>P_simps by simp
          also have "... = B.cod ((P f \<star> \<Phi>\<^sub>P (g, h)) \<cdot> \<a>[P f, P g, P h])"
            using 2 cod_char by presburger
          also have "... = B.cod ((P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h])"
          proof -
            have "(P f \<star> \<Phi>\<^sub>P (g, h)) \<cdot> \<a>[P f, P g, P h] = (P f \<star>\<^sub>B \<Phi>\<^sub>P (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[P f, P g, P h]"
             using f g h fg gh 2 comp_eqI hcomp_eqI assoc_simp by auto
            thus ?thesis by presburger
          qed
          finally show ?thesis by blast
        qed
        moreover have "B.cod \<a>\<^sub>B[P f, P g, P h] = P f \<star>\<^sub>B P g \<star>\<^sub>B P h"
          using f g h fg gh 1 ide_char by auto
        ultimately show ?thesis
          using f g h fg gh B.VV.arr_char assoc_simp assoc_simps(1) dom_char cod_char
          by (intro comp_eqI' seqI arr_compI arr_hcompI) auto
      qed
      also have "... = \<Phi>\<^sub>P (f, g \<star>\<^sub>B h) \<cdot> (P f \<star> \<Phi>\<^sub>P (g, h)) \<cdot> \<a>[P f, P g, P h]"
        using f g h fg gh assoc_simp hcomp_eqI \<Phi>\<^sub>P_simps(1) by auto
      finally show "P \<a>\<^sub>B[f, g, h] \<cdot> \<Phi>\<^sub>P (f \<star>\<^sub>B g, h) \<cdot> (\<Phi>\<^sub>P (f, g) \<star> P h) =
                    \<Phi>\<^sub>P (f, g \<star>\<^sub>B h) \<cdot> (P f \<star> \<Phi>\<^sub>P (g, h)) \<cdot> \<a>[P f, P g, P h]"
        by blast
    qed

    lemma pseudofunctor_prj:
    shows "pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B comp hcomp \<a> \<i>\<^sub>B src trg P \<Phi>\<^sub>P"
      ..

    text \<open>
      We need an explicit formula for the unit constraints for \<open>P\<close>.
    \<close>

    lemma prj_unit_char:
    assumes "B.obj a"
    shows "prj.unit a = (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)"
    proof -
      text \<open>
        We eventually need one of the triangle identities from the following interpretation.
        However in the meantime, it contains a lot of simps that make an otherwise arduous
        calculation much easier.  So interpret it up front.
      \<close>
      interpret adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence(1) by simp

      let ?x = "(e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)"
      have x: "\<guillemotleft>?x : P.map\<^sub>0 a \<Rightarrow>\<^sub>B P a\<guillemotright>"
        using assms P_def P.map\<^sub>0_def P_map\<^sub>0_simp
        by (intro B.comp_in_homI') auto
      have "?x = prj.unit a"
      proof (intro prj.unit_eqI)
        show "B.obj a" by fact
        have a_da: "\<guillemotleft>a \<star>\<^sub>B d a : P\<^sub>0 a \<rightarrow>\<^sub>B a\<guillemotright> \<and> B.ide (a \<star>\<^sub>B d a)"
          using assms B.obj_simps by auto
        show x\<^sub>S: "\<guillemotleft>?x : P.map\<^sub>0 a \<Rightarrow> P a\<guillemotright>"
          using assms x P_map\<^sub>0_simp P_simps\<^sub>B(1) arr_char B.arrI
                equivalence_data_simps\<^sub>B(6) counit_simps(1,4) B.obj_simps(1)
                B.src.preserves_arr B.vconn_implies_hpar(1-4)
          by (metis (no_types, lifting) P_simps(1) in_hom_char)
        show "iso ?x"
          using assms x\<^sub>S B.isos_compose iso_char arr_char by auto
        have *: "\<guillemotleft>?x : P\<^sub>0 a \<rightarrow> P\<^sub>0 a\<guillemotright>"
          using assms x\<^sub>S P\<^sub>0_props vconn_implies_hpar(1-2)
          by (intro in_hhomI) auto
        show "?x \<cdot> \<i>\<^sub>B[P.map\<^sub>0 a] = (P \<i>\<^sub>B[a] \<cdot> \<Phi>\<^sub>P (a, a)) \<cdot> (?x \<star> ?x)"
        proof -
          have 0: "\<guillemotleft>d a \<star>\<^sub>B e a \<star>\<^sub>B a \<star>\<^sub>B d a : P\<^sub>0 a \<rightarrow>\<^sub>B a\<guillemotright>"
            using assms by force
          have 1: "B.seq (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"
            using assms by (elim B.objE, intro B.seqI) auto
          have "(P \<i>\<^sub>B[a] \<cdot> \<Phi>\<^sub>P (a, a)) \<cdot> (?x \<star> ?x) = P \<i>\<^sub>B[a] \<cdot> \<Phi>\<^sub>P (a, a) \<cdot> (?x \<star> ?x)"
            using comp_assoc by simp
          also have "... = P \<i>\<^sub>B[a] \<cdot> (CMP a a \<cdot> (P a \<star> P a)) \<cdot> (?x \<star> ?x)"
            unfolding \<Phi>\<^sub>P_def CMP.map_def
            using assms B.VV.arr_char B.VV.cod_char P.FF_def by auto
          also have "... = P \<i>\<^sub>B[a] \<cdot> (CMP a a \<cdot> (P a \<star>\<^sub>B P a)) \<cdot> (?x \<star>\<^sub>B ?x)"
            using assms x\<^sub>S hcomp_char src_def trg_def by auto
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B (CMP a a \<cdot>\<^sub>B (P a \<star>\<^sub>B P a)) \<cdot>\<^sub>B (?x \<star>\<^sub>B ?x)"
          proof -
            have "\<guillemotleft>P \<i>\<^sub>B[a] \<cdot> (CMP a a \<cdot> (P a \<star>\<^sub>B P a)) \<cdot> (?x \<star>\<^sub>B ?x) : P\<^sub>0 a \<star> P\<^sub>0 a \<Rightarrow> P a\<guillemotright>"
            proof (intro comp_in_homI)
              show "\<guillemotleft>?x \<star>\<^sub>B ?x : P\<^sub>0 a \<star> P\<^sub>0 a \<Rightarrow> P a \<star> P a\<guillemotright>"
              proof -
                have "\<guillemotleft>?x \<star> ?x : P\<^sub>0 a \<star> P\<^sub>0 a \<Rightarrow> P a \<star> P a\<guillemotright>"
                  using assms x\<^sub>S * P\<^sub>0_props P.map\<^sub>0_simps(3)
                  by (intro hcomp_in_vhom) auto
                moreover have "?x \<star> ?x = ?x \<star>\<^sub>B ?x"
                  using x\<^sub>S * by (intro hcomp_eqI) auto
                ultimately show ?thesis by simp
              qed
              show "\<guillemotleft>P a \<star>\<^sub>B P a : P a \<star> P a \<Rightarrow> P a \<star> P a\<guillemotright>"
                using assms hcomp_eqI by fastforce
              show "\<guillemotleft>CMP a a : P a \<star> P a \<Rightarrow> P (a \<star>\<^sub>B a)\<guillemotright>"
                using assms CMP_in_hom(2) by auto
              show "\<guillemotleft>P \<i>\<^sub>B[a] : P (a \<star>\<^sub>B a) \<Rightarrow> P a\<guillemotright>"
                using assms by auto
            qed
            thus ?thesis
              by (intro comp_eqI hcomp_eqI) auto
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a] \<cdot>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a)) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           (P a \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           (?x \<star>\<^sub>B ?x)"
            using assms B.comp_assoc CMP_def by auto
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           (P a \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           (?x \<star>\<^sub>B ?x)"
            using assms 1 B.whisker_left B.comp_assoc by fastforce
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           ((P a \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]))) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
            using assms B.interchange B.comp_assoc by simp
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a \<star>\<^sub>B B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
          proof -
            have "(P a \<star>\<^sub>B P a) \<cdot>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]))
                    = ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]))"
              unfolding P_def
              using assms B.comp_cod_arr [of "(e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
                                             "(e a \<star>\<^sub>B a \<star>\<^sub>B d a) \<star>\<^sub>B (e a \<star>\<^sub>B a \<star>\<^sub>B d a)"]
              by auto
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
          proof -
            have "(e a \<star>\<^sub>B a \<star>\<^sub>B B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                  (e a \<star>\<^sub>B a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])
                    = e a \<star>\<^sub>B (a \<star>\<^sub>B B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B (a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])"
            proof -
              have "B.seq (a \<star>\<^sub>B B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) (a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])"
                using assms by (elim B.objE, intro B.seqI) auto
              thus ?thesis
                using assms B.whisker_left by simp
            qed
            also have "... = e a \<star>\<^sub>B a \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"
              using assms 1 B.whisker_left by fastforce
            finally have "(e a \<star>\<^sub>B a \<star>\<^sub>B B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                          (e a \<star>\<^sub>B a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])
                            = e a \<star>\<^sub>B a \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"
              by blast
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a)) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
          proof -
            have "(e a \<star>\<^sub>B a \<star>\<^sub>B
                    (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a]
                    = \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                      ((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])"
              using assms 1 a_da P_def
                    B.assoc_naturality
                      [of "e a" a "(B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"]
              by fastforce
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           (((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a \<star>\<^sub>B P a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
          proof -
            have 1: "B.ide (e a) \<and> B.ide a \<and> B.ide (d a) \<and> B.ide (P a)"
              using assms ide_char P.preserves_ide by auto
            have 2: "src\<^sub>B (e a) = trg\<^sub>B a \<and> src\<^sub>B a = trg\<^sub>B (d a) \<and> src\<^sub>B (d a) = trg\<^sub>B (P a)"
              using assms by auto
            have "((e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]) \<cdot>\<^sub>B (\<a>\<^sub>B[e a, a, d a] \<star>\<^sub>B P a)
                    = \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a]"
              using assms 1 2 B.pentagon B.comp_assoc by force
            hence "(e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]
                     = (\<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a]) \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a)"
              using assms 1 2
                    B.invert_side_of_triangle(2)
                      [of "\<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a]"
                          "(e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]"
                          "\<a>\<^sub>B[e a, a, d a] \<star>\<^sub>B P a"]
                by fastforce
            hence "\<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a)
                     = \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B
                       \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]"
              using assms 1 2 B.invert_side_of_triangle(1) B.comp_assoc by fastforce
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
          proof -
            have "B.arr (e a) \<and> B.arr a"
              using assms by auto
            moreover have "B.dom (e a) = e a \<and> B.dom a = a \<and> B.cod a = a \<and>
                           B.cod (e a) = e a"
              using assms by auto
            moreover have "B.seq (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"
              using assms by (elim B.objE, intro B.seqI) auto
            moreover have "src\<^sub>B a =
                           trg\<^sub>B ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])"
              using assms a_da trg_vcomp by fastforce
            moreover have "src\<^sub>B a = a \<and> trg\<^sub>B a = a"
              using assms by auto
            moreover have "B.dom ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])
                             = d a \<star>\<^sub>B e a \<star>\<^sub>B a \<star>\<^sub>B d a"
              using assms a_da by fastforce
            moreover have "B.cod ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])
                             = a \<star>\<^sub>B a \<star>\<^sub>B d a"
              using assms a_da by fastforce
            ultimately have "((e a \<star>\<^sub>B a) \<star>\<^sub>B
                                (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                                 \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a \<star>\<^sub>B P a]
                               = \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                                 (e a \<star>\<^sub>B a \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])"
              unfolding P_def
              using assms
                    B.assoc'_naturality
                      [of "e a" a "(B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"]
              by auto
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
          proof -
            have 1: "B.ide (e a) \<and> B.ide a \<and> B.ide (d a) \<and> B.ide (P a)"
              using assms ide_char P.preserves_ide by auto
            have 2: "src\<^sub>B (e a) = trg\<^sub>B a \<and> src\<^sub>B a = trg\<^sub>B (d a) \<and> src\<^sub>B (d a) = trg\<^sub>B (P a)"
              using assms by auto
            have "((e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]) \<cdot>\<^sub>B (\<a>\<^sub>B[e a, a, d a] \<star>\<^sub>B P a)
                    = \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a]"
              using assms 1 2 B.pentagon B.comp_assoc by fastforce
            hence "(e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]
                     = \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                       (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a)"
              using assms 1 2 P.preserves_ide B.comp_assoc
                    B.invert_side_of_triangle(2)
                      [of "\<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a] \<cdot>\<^sub>B \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a]"
                          "(e a \<star>\<^sub>B \<a>\<^sub>B[a, d a, P a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a \<star>\<^sub>B d a, P a]"
                          "\<a>\<^sub>B[e a, a, d a] \<star>\<^sub>B P a"]
              by force
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))"
          proof -
            have "(e a \<star>\<^sub>B a \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                  \<a>\<^sub>B[e a, a, d a \<star>\<^sub>B P a]
                    = \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B ((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                      \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])"
            proof -
              have 1: "B.seq (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"
                using assms by (elim B.objE, intro B.seqI) auto
              moreover have "src\<^sub>B a =
                             trg\<^sub>B ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])"
                using a_da by force
              moreover have "B.arr a \<and> B.dom a = a \<and> B.cod a = a \<and> src\<^sub>B a = a \<and> trg\<^sub>B a = a"
                using assms by auto
              moreover have "B.dom ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])
                               = d a \<star>\<^sub>B e a \<star>\<^sub>B a \<star>\<^sub>B d a"
                using a_da by auto
              moreover have "B.cod ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])
                               = a \<star>\<^sub>B a \<star>\<^sub>B d a"
                using a_da by auto
              ultimately show ?thesis
                unfolding P_def
                using assms
                      B.assoc_naturality
                        [of "e a" a "(B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]"]
                by auto
            qed
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B
                           B.inv (\<epsilon> a))) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
          proof -
            have "((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                  (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))
                    = ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B
                      (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
            proof -
              have "((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                    (B.inv (\<epsilon> a) \<star>\<^sub>B B.inv (\<epsilon> a))
                      = (((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                        ((e a \<star>\<^sub>B d a) \<star>\<^sub>B B.inv (\<epsilon> a))) \<cdot>\<^sub>B
                        (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
                using assms B.comp_arr_dom B.comp_cod_arr B.comp_assoc
                      B.interchange [of "e a \<star>\<^sub>B d a" "B.inv (\<epsilon> a)" "B.inv (\<epsilon> a)" "P\<^sub>0 a"]
                by simp
            also have "... = ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B (e a \<star>\<^sub>B d a) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B
                             B.inv (\<epsilon> a)) \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
                using assms B.interchange by simp
              also have "... = ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B
                               (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
                using assms B.comp_arr_dom by simp
              finally show ?thesis by simp
            qed
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                           (((e a \<star>\<^sub>B a) \<star>\<^sub>B d a) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))) \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
          proof -
            have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B
                  B.inv (\<epsilon> a))
                    = (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B
                      B.inv (\<epsilon> a))"
            proof -
              have "B.seq \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
                using assms a_da by (elim B.objE, intro B.seqI) auto
              moreover have "B.seq (P a) ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
                using assms a_da P_def by auto
              ultimately show ?thesis
                using assms B.interchange by simp
            qed
            also have "... = (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B
                             B.inv (\<epsilon> a))"
            proof -
              have "P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) = (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)"
                using assms x P_def B.comp_cod_arr by blast
              moreover have "\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a"
              proof -
                have "\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])
                        = B.inv ((e a \<star>\<^sub>B \<l>\<^sub>B[d a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a, d a])"
                proof -
                  have "B.iso ((e a \<star>\<^sub>B \<l>\<^sub>B[d a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a, d a])"
                    using assms by (elim B.objE, intro B.isos_compose) auto
                  hence "B.seq (e a \<star>\<^sub>B \<l>\<^sub>B[d a]) \<a>\<^sub>B[e a, a, d a]"
                    by blast
                  moreover have "B.iso \<a>\<^sub>B[e a, a, d a]"
                    using assms by force
                  ultimately have "B.inv ((e a \<star>\<^sub>B \<l>\<^sub>B[d a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a, d a])
                                     = B.inv \<a>\<^sub>B[e a, a, d a] \<cdot>\<^sub>B B.inv (e a \<star>\<^sub>B \<l>\<^sub>B[d a])"
                    using assms B.inv_comp by auto
                  also have "... = \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
                    using assms
                    by (elim B.objE) (simp add: assms)
                  finally show ?thesis by simp
                qed
                also have "... = B.inv (\<r>\<^sub>B[e a] \<star>\<^sub>B d a)"
                  using assms B.triangle [of "d a" "e a"] by simp
                also have "... = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a"
                  using assms by simp
                finally show ?thesis by blast
              qed
              ultimately show ?thesis by simp
            qed
            also have "... = (((e a \<star>\<^sub>B a) \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a]) \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B
                             (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<cdot>\<^sub>B P\<^sub>0 a"
              using assms 0 B.comp_cod_arr B.comp_arr_dom
              by (elim B.objE) auto
            also have "... = ((e a \<star>\<^sub>B a) \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B
                             ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B P\<^sub>0 a"
              using B.comp_assoc by simp
            also have "... = (((e a \<star>\<^sub>B a) \<star>\<^sub>B d a) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B
                             (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a)"
            proof -
              have 1: "\<guillemotleft>\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] : e a \<star>\<^sub>B a \<star>\<^sub>B d a \<Rightarrow>\<^sub>B (e a \<star>\<^sub>B a) \<star>\<^sub>B d a\<guillemotright>"
                using assms a_da by fastforce
              have "B.seq \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
                using assms 1 a_da by auto
              moreover have "B.ide ((e a \<star>\<^sub>B a) \<star>\<^sub>B d a)"
                using assms 0 by fastforce
              ultimately have "B.seq ((e a \<star>\<^sub>B a) \<star>\<^sub>B d a)
                                     (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]))"
                using assms 1 a_da by auto
              moreover have "B.seq ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) (P\<^sub>0 a)"
                using assms
                apply (elim B.objE, intro B.seqI)
                      apply auto
                 apply (metis 0 B.in_hhom_def B.src.preserves_reflects_arr)
                by (metis antipar(2) B.cod_src counit_simps(4) equivalence_data_simps\<^sub>B(15)
                    B.ideD(1) ide_right)
              ultimately show ?thesis
                using assms B.interchange by blast
            qed
            finally have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B P a) \<cdot>\<^sub>B
                          ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))
                            = (((e a \<star>\<^sub>B a) \<star>\<^sub>B d a) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B
                              (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a)"
              by blast
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           (((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
          proof -
            have "\<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P a] \<cdot>\<^sub>B
                  (((e a \<star>\<^sub>B a) \<star>\<^sub>B d a) \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))
                    = ((e a \<star>\<^sub>B a) \<star>\<^sub>B d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B
                      \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a]"
            proof -
              have "B.hseq (e a) a"
                using assms by force
              moreover have "src\<^sub>B (d a) = trg\<^sub>B ?x"
                using assms B.trg_vcomp [of "e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]" "B.inv (\<epsilon> a)"] by simp
              moreover have "B.cod ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) = P a"
                using assms x by blast
              ultimately show ?thesis
                using assms B.assoc_naturality [of "e a \<star>\<^sub>B a" "d a" ?x] by auto
            qed
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B
                              (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                              \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                              (d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
          proof -
            have "((e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                  ((e a \<star>\<^sub>B a) \<star>\<^sub>B d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))
                    = (e a \<star>\<^sub>B a) \<star>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B
                      \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                      (d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
            proof -
              have "B.ide (e a \<star>\<^sub>B a)"
                using assms by force
              moreover have "B.seq ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a])
                                   (d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
                using a_da B.whisker_left by auto
              ultimately show ?thesis
                using assms B.whisker_left B.comp_assoc by fastforce
            qed
            thus ?thesis by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B
                                        (B.inv (\<eta> a) \<star>\<^sub>B d a) \<cdot>\<^sub>B
                                        \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, d a] \<cdot>\<^sub>B
                                        (d a \<star>\<^sub>B B.inv (\<epsilon> a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
          proof -
            have "(B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                  (d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))
                    = (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, d a] \<cdot>\<^sub>B
                      (d a \<star>\<^sub>B B.inv (\<epsilon> a))"
            proof -
              have "(B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                    (d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))
                      = (B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B (\<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                        (d a \<star>\<^sub>B e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B (d a \<star>\<^sub>B B.inv (\<epsilon> a))"
                using assms B.whisker_left B.comp_assoc by simp
              also have "... = ((B.inv (\<eta> a) \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B ((d a \<star>\<^sub>B e a) \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B
                               \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, d a] \<cdot>\<^sub>B (d a \<star>\<^sub>B B.inv (\<epsilon> a))"
               using assms B.assoc'_naturality [of "d a" "e a" "\<l>\<^sub>B\<^sup>-\<^sup>1[d a]"] B.comp_assoc by simp
              also have "... = (B.inv (\<eta> a) \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, d a] \<cdot>\<^sub>B
                               (d a \<star>\<^sub>B B.inv (\<epsilon> a))"
                using assms B.interchange [of "B.inv (\<eta> a)" "d a \<star>\<^sub>B e a" "a \<star>\<^sub>B d a" "\<l>\<^sub>B\<^sup>-\<^sup>1[d a]"]
                      B.comp_arr_dom B.comp_cod_arr
                by simp
              also have "... = (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B (B.inv (\<eta> a) \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, d a] \<cdot>\<^sub>B
                               (d a \<star>\<^sub>B B.inv (\<epsilon> a))"
                using assms B.interchange [of a "B.inv (\<eta> a)" "\<l>\<^sub>B\<^sup>-\<^sup>1[d a]" "d a"]
                      B.comp_arr_dom B.comp_cod_arr B.comp_assoc
                by simp
              finally show ?thesis by blast
            qed
            thus ?thesis
              using comp_assoc by simp
          qed
          also have "... = P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<r>\<^sub>B[d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a)"
          proof -
            have "(B.inv (\<eta> a) \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, d a] \<cdot>\<^sub>B (d a \<star>\<^sub>B B.inv (\<epsilon> a))
                    = \<l>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<r>\<^sub>B[d a]"
            proof -
              have "(B.inv (\<eta> a) \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d a, e a, d a] \<cdot>\<^sub>B (d a \<star>\<^sub>B B.inv (\<epsilon> a))
                      = B.inv (\<eta> a \<star>\<^sub>B d a) \<cdot>\<^sub>B B.inv \<a>\<^sub>B[d a, e a, d a] \<cdot>\<^sub>B B.inv (d a \<star>\<^sub>B \<epsilon> a)"
                using assms by simp
              also have "... = B.inv ((d a \<star>\<^sub>B \<epsilon> a) \<cdot>\<^sub>B \<a>\<^sub>B[d a, e a, d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B d a))"
              proof -
                have "B.iso ((d a \<star>\<^sub>B \<epsilon> a) \<cdot>\<^sub>B \<a>\<^sub>B[d a, e a, d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B d a))"
                  using assms by (intro B.isos_compose) auto
               thus ?thesis
                  using assms B.inv_comp_left B.comp_assoc by auto
              qed
              also have "... = B.inv (\<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a])"
                using assms triangle_right by simp
              also have "... = \<l>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<r>\<^sub>B[d a]"
                using assms B.inv_comp by simp
              finally show ?thesis by blast
            qed
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                           (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                           ((e a \<star>\<^sub>B a) \<star>\<^sub>B (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<r>\<^sub>B[d a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                           \<r>\<^sub>B\<^sup>-\<^sup>1[e a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                           B.inv (\<epsilon> a) \<cdot>\<^sub>B
                           \<i>\<^sub>B[P\<^sub>0 a]"
          proof -
            have "\<r>\<^sub>B[e a \<star>\<^sub>B d a] \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a) = B.inv (\<epsilon> a) \<cdot>\<^sub>B \<i>\<^sub>B[P\<^sub>0 a]"
              using assms B.runit_naturality [of "B.inv (\<epsilon> a)"] B.unitor_coincidence P\<^sub>0_props
              by simp
            hence "B.inv (\<epsilon> a) \<star>\<^sub>B P\<^sub>0 a = \<r>\<^sub>B\<^sup>-\<^sup>1[e a \<star>\<^sub>B d a] \<cdot>\<^sub>B B.inv (\<epsilon> a) \<cdot>\<^sub>B \<i>\<^sub>B[P\<^sub>0 a]"
               using assms P\<^sub>0_props(5) B.invert_side_of_triangle(1) by simp
            thus ?thesis
               using B.comp_assoc by simp
          qed
          also have "... = (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<cdot>\<^sub>B \<i>\<^sub>B[P\<^sub>0 a]"
          proof -
            have P\<^sub>0_a: "B.obj (P\<^sub>0 a) \<and> B.arr (P\<^sub>0 a)"
              using assms a_da by fastforce
            have i_a: "B.\<rr> a = \<i>\<^sub>B[a]"
              using assms B.unitor_coincidence B.\<rr>_ide_simp B.obj_simps
              by (metis (no_types, lifting) B.objE)
            have "P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                  (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                  (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                   \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                   \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                   \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                   ((e a \<star>\<^sub>B a) \<star>\<^sub>B (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<r>\<^sub>B[d a]) \<cdot>\<^sub>B
                   \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a] \<cdot>\<^sub>B
                   (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                   \<r>\<^sub>B\<^sup>-\<^sup>1[e a \<star>\<^sub>B d a]
                     = e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]"
            proof -
              have "P \<i>\<^sub>B[a] \<cdot>\<^sub>B
                    (e a \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[a, a, d a]) \<cdot>\<^sub>B
                    (e a \<star>\<^sub>B a \<star>\<^sub>B \<l>\<^sub>B[a \<star>\<^sub>B d a]) \<cdot>\<^sub>B
                    \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                    \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                    \<a>\<^sub>B[e a, a, a \<star>\<^sub>B a \<star>\<^sub>B d a] \<cdot>\<^sub>B
                    ((e a \<star>\<^sub>B a) \<star>\<^sub>B (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<r>\<^sub>B[d a]) \<cdot>\<^sub>B
                    \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, P\<^sub>0 a] \<cdot>\<^sub>B
                    (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                    \<r>\<^sub>B\<^sup>-\<^sup>1[e a \<star>\<^sub>B d a]
                      = \<lbrace>(\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<r>\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0\<^bold>] \<^bold>\<star> \<^bold>\<langle>d a\<^bold>\<rangle>) \<^bold>\<cdot>
                         (\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         (\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<l>\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         \<^bold>\<a>\<^bold>[\<^bold>\<langle>e a\<^bold>\<rangle>, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                         \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e a\<^bold>\<rangle>, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                         \<^bold>\<a>\<^bold>[\<^bold>\<langle>e a\<^bold>\<rangle>, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                         ((\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0) \<^bold>\<star> (\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> \<^bold>\<r>\<^bold>[\<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         \<^bold>\<a>\<^bold>[\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>d a\<^bold>\<rangle>, \<^bold>\<langle>P\<^sub>0 a\<^bold>\<rangle>\<^sub>0\<^bold>] \<^bold>\<cdot>
                         (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e a\<^bold>\<rangle>, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> (\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>P\<^sub>0 a\<^bold>\<rangle>\<^sub>0) \<^bold>\<cdot>
                         \<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]\<rbrace>"
                unfolding P_def
                using assms B.obj_def [of a] P\<^sub>0_a i_a B.\<alpha>_def B.\<alpha>'.map_ide_simp
                      B.VVV.ide_char B.VVV.arr_char B.VV.ide_char B.VV.arr_char
                      B.\<ll>_ide_simp B.\<rr>_ide_simp
                by (elim B.objE) simp
              also have "... = \<lbrace>\<^bold>\<langle>e a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]\<rbrace>"
                using assms P\<^sub>0_a by (intro EV.eval_eqI) auto
              also have "... = e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]"
                using assms P_def B.\<ll>_ide_simp by simp
              finally show ?thesis by blast
            qed
            thus ?thesis by simp
          qed
          also have "... = ?x \<cdot> \<i>\<^sub>B[P.map\<^sub>0 a]"
          proof -
            have "B.arr \<i>\<^sub>B[P.map\<^sub>0 a] \<and> src\<^sub>B \<i>\<^sub>B[P.map\<^sub>0 a] \<in> Obj \<and> trg\<^sub>B \<i>\<^sub>B[P.map\<^sub>0 a] \<in> Obj \<and>
                  P\<^sub>0 a \<cdot>\<^sub>B P\<^sub>0 a \<in> Obj \<and> B.cod \<i>\<^sub>B[P.map\<^sub>0 a] = P\<^sub>0 a"
              using assms P\<^sub>0_props arr_char unit_simps(1)
              apply auto
              using obj_char
              by (metis (no_types, lifting) B.comp_ide_self B.objE)
            thus ?thesis
              using assms comp_def B.comp_assoc P\<^sub>0_props [of a] by simp
          qed
          finally show ?thesis by argo
        qed
      qed
      thus ?thesis by simp
    qed

    sublocale PoE: composite_pseudofunctor
                     comp hcomp \<a> \<i>\<^sub>B src trg V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                     comp hcomp \<a> \<i>\<^sub>B src trg
                     E \<Phi>\<^sub>E P \<Phi>\<^sub>P
      ..
    sublocale EoP: composite_pseudofunctor
                     V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B comp hcomp \<a> \<i>\<^sub>B src trg V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                     P \<Phi>\<^sub>P E \<Phi>\<^sub>E
      ..
    sublocale I\<^sub>C: identity_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B ..
    sublocale I\<^sub>S: identity_pseudofunctor comp hcomp \<a> \<i>\<^sub>B src trg ..

    no_notation B.in_hom  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    abbreviation (input) unit\<^sub>0
    where "unit\<^sub>0 \<equiv> e"

    definition unit\<^sub>1
    where "unit\<^sub>1 f = (e (trg\<^sub>B f) \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                     \<a>\<^sub>B[e (trg\<^sub>B f), f, src\<^sub>B f] \<cdot>\<^sub>B
                     ((e (trg\<^sub>B f) \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> (src\<^sub>B f))) \<cdot>\<^sub>B
                     \<a>\<^sub>B[e (trg\<^sub>B f) \<star>\<^sub>B f, d (src\<^sub>B f), e (src\<^sub>B f)] \<cdot>\<^sub>B
                     (\<a>\<^sub>B\<^sup>-\<^sup>1[e (trg\<^sub>B f), f, d (src\<^sub>B f)] \<star>\<^sub>B e (src\<^sub>B f))"

    abbreviation (input) \<eta>\<^sub>1
    where "\<eta>\<^sub>1 \<equiv> unit\<^sub>1"

    lemma unit\<^sub>1_in_hom [intro]:
    assumes "B.ide f"
    shows "\<guillemotleft>\<eta>\<^sub>1 f : src\<^sub>B f \<rightarrow>\<^sub>B P\<^sub>0 (trg\<^sub>B f)\<guillemotright>"
    and "\<guillemotleft>\<eta>\<^sub>1 f : (e (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B d (src\<^sub>B f)) \<star>\<^sub>B e (src\<^sub>B f) \<Rightarrow>\<^sub>B e (trg\<^sub>B f) \<star>\<^sub>B f\<guillemotright>"
    proof -
      show "\<guillemotleft>\<eta>\<^sub>1 f : (e (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B d (src\<^sub>B f)) \<star>\<^sub>B e (src\<^sub>B f) \<Rightarrow>\<^sub>B e (trg\<^sub>B f) \<star>\<^sub>B f\<guillemotright>"
        using assms unit\<^sub>1_def by force
      thus "\<guillemotleft>\<eta>\<^sub>1 f : src\<^sub>B f \<rightarrow>\<^sub>B P\<^sub>0 (trg\<^sub>B f)\<guillemotright>"
        using assms B.vconn_implies_hpar(1-2) by auto
    qed

    lemma unit\<^sub>1_simps [simp]:
    assumes "B.ide f"
    shows "B.arr (\<eta>\<^sub>1 f)"
    and "src\<^sub>B (\<eta>\<^sub>1 f) = src\<^sub>B f" and "trg\<^sub>B (\<eta>\<^sub>1 f) = P\<^sub>0 (trg\<^sub>B f)"
    and "B.dom (\<eta>\<^sub>1 f) = (e (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B d (src\<^sub>B f)) \<star>\<^sub>B e (src\<^sub>B f)"
    and "B.cod (\<eta>\<^sub>1 f) = e (trg\<^sub>B f) \<star>\<^sub>B f"
    and "B.iso (\<eta>\<^sub>1 f)"
      using assms unit\<^sub>1_in_hom
           apply auto
      unfolding unit\<^sub>1_def
      by (intro B.isos_compose) auto (* 15 sec *)

    lemma unit\<^sub>1_in_hom\<^sub>S [intro]:
    assumes "ide f"
    shows "\<guillemotleft>\<eta>\<^sub>1 f : src f \<rightarrow> P\<^sub>0 (trg f)\<guillemotright>"
    and "\<guillemotleft>\<eta>\<^sub>1 f : PoE.map f \<star> e (src f) \<Rightarrow> e (trg f) \<star> I\<^sub>S.map f\<guillemotright>"
      using assms ide_char arr_char P\<^sub>0_props(1,6) P.preserves_ide hcomp_def
            src_def trg_def P_def emb.map_def equivalence_data_simps(2)
            in_hom_char
      by auto

    lemma unit\<^sub>1_simps\<^sub>S [simp]:
    assumes "ide f"
    shows "arr (\<eta>\<^sub>1 f)"
    and "src (\<eta>\<^sub>1 f) = src f" and "trg (\<eta>\<^sub>1 f) = P\<^sub>0 (trg f)"
    and "dom (\<eta>\<^sub>1 f) = PoE.map f \<star> e (src f)"
    and "cod (\<eta>\<^sub>1 f) = e (trg f) \<star> I\<^sub>S.map f"
    and "iso (\<eta>\<^sub>1 f)"
      using assms unit\<^sub>1_in_hom\<^sub>S iso_char ide_char arr_char P.components_are_iso
      by auto

    sublocale unit: pseudonatural_equivalence comp hcomp \<a> \<i>\<^sub>B src trg
                      comp hcomp \<a> \<i>\<^sub>B src trg
                      I\<^sub>S.map I\<^sub>S.cmp \<open>P \<circ> E\<close> PoE.cmp unit\<^sub>0 unit\<^sub>1
    proof
      show "\<And>a. obj a \<Longrightarrow> ide (e a)"
        using obj_char ide_char arr_char P\<^sub>0_props(1) by force
      show "\<And>a. obj a \<Longrightarrow> \<guillemotleft>e a : src (I\<^sub>S.map a) \<rightarrow> src ((P \<circ> E) a)\<guillemotright>"
        using emb.map_def
        apply (intro in_hhomI)
          apply auto
        using obj_char by auto
      show "\<And>a. obj a \<Longrightarrow> equivalence_map (e a)"
      proof -
        fix a
        assume a: "obj a"
        interpret Adj': equivalence_in_bicategory comp hcomp \<a> \<i>\<^sub>B src trg
                          \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
          using a by unfold_locales auto
        show "equivalence_map (e a)"
          using Adj'.equivalence_in_bicategory_axioms equivalence_map_def by auto
      qed
      show "\<And>f. ide f \<Longrightarrow> \<guillemotleft>\<eta>\<^sub>1 f : PoE.map f \<star> e (src f) \<Rightarrow> e (trg f) \<star> I\<^sub>S.map f\<guillemotright>"
        using unit\<^sub>1_in_hom\<^sub>S(2) by simp
      show "\<And>f. ide f \<Longrightarrow> iso (\<eta>\<^sub>1 f)"
        by simp
      show *: "\<And>\<mu>. arr \<mu> \<Longrightarrow>
                    \<eta>\<^sub>1 (cod \<mu>) \<cdot> (PoE.map \<mu> \<star> e (src \<mu>)) = (e (trg \<mu>) \<star> I\<^sub>S.map \<mu>) \<cdot> \<eta>\<^sub>1 (dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "arr \<mu>"
        have 1: "B.arr \<mu>"
          using \<mu> arr_char by simp
        let ?f = "B.dom \<mu>"
        let ?g = "B.cod \<mu>"
        let ?a = "src\<^sub>B \<mu>"
        let ?b = "trg\<^sub>B \<mu>"
        have "\<eta>\<^sub>1 (cod \<mu>) \<cdot> (PoE.map \<mu> \<star> e (src \<mu>))
                = ((e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                  ((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                  \<a>\<^sub>B[e ?b \<star>\<^sub>B ?g, d ?a, e ?a] \<cdot>\<^sub>B
                  (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?g, d ?a] \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                  ((e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)"
          using \<mu> unit\<^sub>1_def P_def emb.map_def hcomp_def comp_char src_def cod_simp
                arr_char P\<^sub>0_props [of ?a] P\<^sub>0_props [of ?b]
          by auto (* 12 sec *)
        also have "... = (e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?g, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?g, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)"
          using 1 B.comp_assoc by simp
        also have "... = (e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?g, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?g, d ?a] \<cdot>\<^sub>B (e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a \<cdot>\<^sub>B e ?a)"
          using 1 B.interchange [of "\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?g, d ?a]" "e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a" "e ?a" "e ?a"]
          by simp
        also have "... = (e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?g, d ?a, e ?a] \<cdot>\<^sub>B
                         (((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a \<cdot>\<^sub>B e ?a)"
          using 1 B.assoc'_naturality [of "e ?b" \<mu> "d ?a"] by simp
        also have "... = (e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[e ?b \<star>\<^sub>B ?g, d ?a, e ?a] \<cdot>\<^sub>B
                         (((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a)"
          using 1 B.comp_assoc
                B.interchange [of "(e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?a" "\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a]" "e ?a" "e ?a" ]
          by simp
        also have "... = (e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                         (((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?f, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a)"
          using 1 B.assoc_naturality [of "e ?b \<star>\<^sub>B \<mu>" "d ?a" "e ?a"] B.comp_assoc by simp
        also have "... = (e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?f, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a)"
        proof -
          have "((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B ((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)
                  = (e ?b \<star>\<^sub>B ?g) \<cdot>\<^sub>B (e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B B.inv (\<eta> ?a) \<cdot>\<^sub>B (d ?a \<star>\<^sub>B e ?a)"
            using 1 B.interchange by simp
          also have "... = (e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B B.inv (\<eta> ?a)"
            using 1 B.comp_arr_dom B.comp_cod_arr by simp
          finally have "((e ?b \<star>\<^sub>B ?g) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B ((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)
                          = (e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B B.inv (\<eta> ?a)"
            by simp
          thus ?thesis by simp
        qed
        also have "... = (e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[e ?b, ?g, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B ?a)) \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?f, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a)"
        proof -
          have "(e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B B.inv (\<eta> ?a) = (e ?b \<star>\<^sub>B \<mu>) \<cdot>\<^sub>B (e ?b \<star>\<^sub>B ?f) \<star>\<^sub>B ?a \<cdot>\<^sub>B B.inv (\<eta> ?a)"
            using 1 B.comp_arr_dom B.comp_cod_arr by simp
          also have "... = ((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B ?a) \<cdot>\<^sub>B ((e ?b \<star>\<^sub>B ?f) \<star>\<^sub>B B.inv (\<eta> ?a))"
            using 1 B.interchange by simp
          finally have "(e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B B.inv (\<eta> ?a)
                          = ((e ?b \<star>\<^sub>B \<mu>) \<star>\<^sub>B ?a) \<cdot>\<^sub>B ((e ?b \<star>\<^sub>B ?f) \<star>\<^sub>B B.inv (\<eta> ?a))"
            by blast
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = ((e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B
                         (e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?f, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?f, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a)"
          using 1 B.assoc_naturality [of "e ?b" \<mu> "?a"] B.comp_assoc by simp
        also have "... = (e ?b \<star>\<^sub>B \<mu>) \<cdot>\<^sub>B
                         (e ?b \<star>\<^sub>B \<r>\<^sub>B[?f]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?f, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?f, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a)"
        proof -
          have "(e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B (e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B ?a) = e ?b \<cdot>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[?g] \<cdot>\<^sub>B (\<mu> \<star>\<^sub>B ?a)"
            using 1 B.interchange [of "e ?b" "e ?b" "\<r>\<^sub>B[?g]" "\<mu> \<star>\<^sub>B ?a"] by simp
          also have "... = e ?b \<cdot>\<^sub>B e ?b \<star>\<^sub>B \<mu> \<cdot>\<^sub>B \<r>\<^sub>B[?f]"
            using 1 B.runit_naturality by simp
          also have "... = (e ?b \<star>\<^sub>B \<mu>) \<cdot>\<^sub>B (e ?b \<star>\<^sub>B \<r>\<^sub>B[?f])"
            using 1 B.interchange [of "e ?b" "e ?b" \<mu> "\<r>\<^sub>B[?f]"] by simp
          finally have "(e ?b \<star>\<^sub>B \<r>\<^sub>B[?g]) \<cdot>\<^sub>B (e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B ?a) = (e ?b \<star>\<^sub>B \<mu>) \<cdot>\<^sub>B (e ?b \<star>\<^sub>B \<r>\<^sub>B[?f])"
            by blast
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = (e (trg \<mu>) \<star> I\<^sub>S.map \<mu>) \<cdot> \<eta>\<^sub>1 (dom \<mu>)"
        proof -
          have "arr ((e (trg \<mu>) \<star> I\<^sub>S.map \<mu>) \<cdot> \<eta>\<^sub>1 (dom \<mu>))"
            using \<mu> by simp
          hence 2: "arr ((e ?b \<star>\<^sub>B \<mu>) \<cdot>
                         ((e ?b \<star>\<^sub>B \<r>\<^sub>B[?f]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b, ?f, ?a] \<cdot>\<^sub>B
                         ((e ?b \<star>\<^sub>B ?f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?b \<star>\<^sub>B ?f, d ?a, e ?a] \<cdot>\<^sub>B
                         (B.inv \<a>\<^sub>B[e ?b, ?f, d ?a] \<star>\<^sub>B e ?a)))"
            unfolding unit\<^sub>1_def
            using \<mu> 1 arr_char P\<^sub>0_props trg_def hcomp_def dom_char by simp
          show ?thesis
            unfolding unit\<^sub>1_def
            using \<mu> 1 arr_char P\<^sub>0_props trg_def hcomp_def dom_char
            apply simp
            using 2 comp_eqI by blast
        qed
        finally show "\<eta>\<^sub>1 (cod \<mu>) \<cdot> (PoE.map \<mu> \<star> e (src \<mu>))
                        = (e (trg \<mu>) \<star> I\<^sub>S.map \<mu>) \<cdot> \<eta>\<^sub>1 (dom \<mu>)"
          by simp
      qed
      show "\<And>a. obj a \<Longrightarrow> (e a \<star> I\<^sub>S.unit a) \<cdot> \<r>\<^sup>-\<^sup>1[e a] \<cdot> \<l>[e a] = unit\<^sub>1 a \<cdot> (PoE.unit a \<star> e a)"
      proof -
        fix a
        assume a: "obj a"
        have 0: "B.obj a"
          using a obj_char by blast
        interpret adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
          using 0 chosen_adjoint_equivalence(1) [of a] by simp
        have 1: "arr a \<and> src\<^sub>B a = a"
          using a src_def by auto
        have arr: "B.arr ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
          using a 0 1 emb.map_def by auto
        have src: "src\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) = P\<^sub>0 a"
          using 0 1 B.src_vcomp [of "e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]" "B.inv (\<epsilon> a)"] emb.map_def by simp
        have trg: "trg\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) = P\<^sub>0 a"
          using 0 1 B.trg_vcomp [of "e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]" "B.inv (\<epsilon> a)"] emb.map_def by simp

        have 2: "seq (P a) ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
        proof -
          have "B.arr (P a \<cdot>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)))"
            using a 0 1 P_def emb.map_def
            by (elim B.objE, intro B.seqI) auto
          moreover have "arr (P a)"
            using 0 by auto
          moreover have "arr ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
            apply (unfold arr_char)
            by (simp add: 0 P\<^sub>0_props(6) src trg)
         ultimately show ?thesis
            using seq_char by simp
        qed
        have 3: "obj (P\<^sub>0 a)"
          using 0 P\<^sub>0_props arr_char obj_char by blast
        have 4: "B.seq (P a) ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
          using 2 seq_char by simp

        have "\<eta>\<^sub>1 a \<cdot> (PoE.unit a \<star> e a) = \<eta>\<^sub>1 a \<cdot> (P a \<cdot> (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
        proof -
          have "\<eta>\<^sub>1 a \<cdot> (PoE.unit a \<star> e a) = \<eta>\<^sub>1 a \<cdot> (PoE.unit a \<star>\<^sub>B e a)"
          proof -
            have "arr (PoE.unit a)"
              using a by simp
            moreover have "src (PoE.unit a) = trg (e a)"
              using a obj_char equivalence_data_in_hom\<^sub>B P.map\<^sub>0_def by auto
            ultimately show ?thesis
              using a hcomp_char by simp
          qed
          moreover have "PoE.unit a = P a \<cdot> (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)"
            using a obj_char PoE.unit_char' emb.unit_char' prj_unit_char by simp
          ultimately show ?thesis by argo
        qed
        also have "... = \<eta>\<^sub>1 a \<cdot> (P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
        proof -
          have "arr (P a)"
            using a obj_char B.obj_simps by simp
          moreover have "arr ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a))"
           using 2 by auto
          ultimately show ?thesis
            using a 4 seq_char comp_char by simp
        qed
        also have "... = \<eta>\<^sub>1 a \<cdot>\<^sub>B (P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
        proof -
          have "arr (\<eta>\<^sub>1 a)"
            using a by auto
          moreover have "arr (P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
          proof -
            have 5: "B.arr (P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
              using a 3 obj_char P_def B.obj_simps by auto
            moreover have "src\<^sub>B (P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a) = a"
              using a 0 5 src_hcomp by simp
            moreover have "trg\<^sub>B (P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a) = P\<^sub>0 a"
              using a 0 4 5 B.trg_vcomp [of "P a" "(e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)"] by auto
            moreover have "a \<in> Obj"
              using a obj_char arr_char by auto
            moreover have "P\<^sub>0 a \<in> Obj"
              using 0 P\<^sub>0_props(1) obj_char arr_char B.obj_def by fastforce
            ultimately show ?thesis
              using a obj_char arr_char by presburger
          qed
          moreover have "B.seq (\<eta>\<^sub>1 a) (P a \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
            using 0 3 P_def obj_char
            by (elim B.objE, intro B.seqI) auto (* 6 sec *)
          ultimately show ?thesis
            using 2 comp_char by meson
        qed
        also have "... = (e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B
                         ((e a \<star>\<^sub>B a) \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, e a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B e a) \<cdot>\<^sub>B
                         (((e a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
          using 0 1 unit\<^sub>1_def P_def emb.map\<^sub>0_def emb.map_def B.comp_assoc B.obj_def' by simp
        also have "... = (e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B
                         ((e a \<star>\<^sub>B a) \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a \<star>\<^sub>B a, d a, e a] \<cdot>\<^sub>B
                         ((\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B e a) \<cdot>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a))"
        proof -
          have "(e a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) = e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]"
            using 0 B.comp_cod_arr by simp
          thus ?thesis by simp
        qed
        also have "... = (e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B
                         ((e a \<star>\<^sub>B a) \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[e a \<star>\<^sub>B a, d a, e a] \<cdot>\<^sub>B
                         ((\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a) \<star>\<^sub>B e a)) \<cdot>\<^sub>B
                         (B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
        proof -
          have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B e a) \<cdot>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a)
                  = (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B e a) \<cdot>\<^sub>B
                    ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B e a) \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
            using 0 B.whisker_right by simp
          also have "... = ((\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B e a) \<cdot>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B e a)) \<cdot>\<^sub>B
                           (B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
            using B.comp_assoc by simp
          also have "... = (\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<star>\<^sub>B e a) \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
          proof -
            have "B.seq \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
              using a 0 by (elim B.objE, intro B.seqI) auto
            thus ?thesis
              using 0 B.whisker_right by simp
          qed
          also have "... = ((\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a) \<star>\<^sub>B e a) \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
          proof -
            have "\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a"
            proof -
              have "e a \<star>\<^sub>B \<l>\<^sub>B[d a] = (\<r>\<^sub>B[e a] \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a]"
                using 0 1 B.triangle' [of "e a" "d a"] by simp
              moreover have "B.hseq (e a) \<l>\<^sub>B[d a]"
                using 0 by auto
              moreover have "src\<^sub>B (e a) = a"
                using 0 by simp
              ultimately have "(\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a) \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B[d a]) = \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a]"
                using 0 B.invert_side_of_triangle(1)
                          [of "e a \<star>\<^sub>B \<l>\<^sub>B[d a]" "\<r>\<^sub>B[e a] \<star>\<^sub>B d a" "\<a>\<^sub>B\<^sup>-\<^sup>1[e a, src\<^sub>B (e a), d a]"]
                by simp
              moreover have "B.arr \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a]"
                using 0 B.assoc'_in_hom [of "e a" a "d a"] by fastforce
              ultimately have "\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a = \<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
                using 0 B.invert_side_of_triangle(2)
                          [of "\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a]" "\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a" "e a \<star>\<^sub>B \<l>\<^sub>B[d a]"]
                by simp
              thus ?thesis by simp
            qed
            thus ?thesis by simp
          qed
          finally have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e a, a, d a] \<star>\<^sub>B e a) \<cdot>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<star>\<^sub>B e a) =
                          ((\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a) \<star>\<^sub>B e a) \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
            by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = (e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B
                         (((e a \<star>\<^sub>B a) \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B
                         (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a \<star>\<^sub>B e a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, d a, e a] \<cdot>\<^sub>B
                         (B.inv (\<epsilon> a) \<star>\<^sub>B e a)"
          using 0 B.assoc_naturality [of "\<r>\<^sub>B\<^sup>-\<^sup>1[e a]" "d a" "e a"] B.comp_assoc by simp
        also have "... = (e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B
                         (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a) \<cdot>\<^sub>B
                         ((e a \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, d a, e a] \<cdot>\<^sub>B
                         (B.inv (\<epsilon> a) \<star>\<^sub>B e a))"
        proof -
          have "((e a \<star>\<^sub>B a) \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a \<star>\<^sub>B e a)
                  = (e a \<star>\<^sub>B a) \<cdot>\<^sub>B \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B B.inv (\<eta> a) \<cdot>\<^sub>B (d a \<star>\<^sub>B e a)"
            using 0 B.interchange [of "e a \<star>\<^sub>B a" "\<r>\<^sub>B\<^sup>-\<^sup>1[e a]" "B.inv (\<eta> a)" "d a \<star>\<^sub>B e a"]
            by force
          also have "... = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B e a \<star>\<^sub>B a \<cdot>\<^sub>B B.inv (\<eta> a)"
            using 0 B.comp_arr_dom B.comp_cod_arr by simp
          also have "... = (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a) \<cdot>\<^sub>B (e a \<star>\<^sub>B B.inv (\<eta> a))"
            using 0 B.interchange [of "\<r>\<^sub>B\<^sup>-\<^sup>1[e a]" "e a" a "B.inv (\<eta> a)"] by fastforce
          ultimately have "((e a \<star>\<^sub>B a) \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B d a \<star>\<^sub>B e a)
                             = (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a) \<cdot>\<^sub>B (e a \<star>\<^sub>B B.inv (\<eta> a))"
            by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = ((e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B
                         (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a)) \<cdot>\<^sub>B
                         \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a]"
        proof -
          have "(e a \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B \<a>\<^sub>B[e a, d a, e a] \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B e a)
                  = B.inv ((\<epsilon> a \<star>\<^sub>B e a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e a, d a, e a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<eta> a))"
          proof -
            have "B.iso ((\<epsilon> a \<star>\<^sub>B e a) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e a, d a, e a] \<cdot>\<^sub>B (e a \<star>\<^sub>B \<eta> a))"
              using 0 by (intro B.isos_compose) auto
            thus ?thesis
              using 0 B.inv_comp_left B.comp_assoc by simp
          qed
          also have "... = B.inv (\<l>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<r>\<^sub>B[e a])"
            using 0 triangle_left by simp
          also have "... = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a]"
            using 0 B.inv_comp by simp
          finally have "(e a \<star>\<^sub>B B.inv (\<eta> a)) \<cdot>\<^sub>B \<a>\<^sub>B[e a, d a, e a] \<cdot>\<^sub>B (B.inv (\<epsilon> a) \<star>\<^sub>B e a)
                          = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a]"
            by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a]"
        proof -
          have "(e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a)
                  = ((e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a, a]) \<cdot>\<^sub>B (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a)"
            using B.comp_assoc by simp
          also have "... = (\<r>\<^sub>B[e a] \<star>\<^sub>B a) \<cdot>\<^sub>B (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a)"
            using 0 B.runit_char(2) [of "e a"] B.unitor_coincidence by simp
          also have "... = e a \<star>\<^sub>B a"
            using 0 B.whisker_right [of a "\<r>\<^sub>B[e a]" "\<r>\<^sub>B\<^sup>-\<^sup>1[e a]"] B.comp_arr_inv' by auto
          finally have "(e a \<star>\<^sub>B \<r>\<^sub>B[a]) \<cdot>\<^sub>B \<a>\<^sub>B[e a, a, a] \<cdot>\<^sub>B (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<star>\<^sub>B a) = e a \<star>\<^sub>B a"
            by simp
          thus ?thesis
            using 0 B.comp_cod_arr by simp
        qed
        also have "... = (e a \<star> I\<^sub>S.unit a) \<cdot> \<r>\<^sup>-\<^sup>1[e a] \<cdot> \<l>[e a]"
        proof -
          have "(e a \<star> I\<^sub>S.unit a) \<cdot> \<r>\<^sup>-\<^sup>1[e a] \<cdot> \<l>[e a] = (e a \<star>\<^sub>B a) \<cdot>\<^sub>B \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a]"
          proof -
            have 1: "arr \<l>\<^sub>B[e a] \<and> arr \<r>\<^sub>B\<^sup>-\<^sup>1[e a]"
              using a lunit_simp runit'_simp lunit_simps runit'_simps by simp
            moreover have "arr (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a])"
              using 1 arr_char dom_char cod_char comp_char by auto
            moreover have 2: "hseq (e a) (I\<^sub>S.unit a)"
              using a I\<^sub>S.unit_char by (intro hseqI') auto
            moreover have "B.seq (e a \<star> I\<^sub>S.unit a) (\<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a])"
              using 0 2 hcomp_char arr_char I\<^sub>S.unit_char'
              apply (intro B.seqI)
                  apply auto[4]
              using a by force
            ultimately show ?thesis
              using a comp_char I\<^sub>S.unit_char' lunit_simp runit'_simp hcomp_char
              by auto (* 4 sec *)
          qed
          also have "... = \<r>\<^sub>B\<^sup>-\<^sup>1[e a] \<cdot>\<^sub>B \<l>\<^sub>B[e a]"
            using 0 B.comp_cod_arr by simp
          finally show ?thesis by simp
        qed
        finally show "(e a \<star> I\<^sub>S.unit a) \<cdot> \<r>\<^sup>-\<^sup>1[e a] \<cdot> \<l>[e a] = \<eta>\<^sub>1 a \<cdot> (PoE.unit a \<star> e a)"
          by argo
      qed
      show "\<And>f g. \<lbrakk>ide f; ide g; src g = trg f\<rbrakk> \<Longrightarrow>
                     (e (trg g) \<star> I\<^sub>S.cmp (g, f)) \<cdot>
                     \<a>[e (trg g), I\<^sub>S.map g, I\<^sub>S.map f] \<cdot>
                     (\<eta>\<^sub>1 g \<star> I\<^sub>S.map f) \<cdot>
                     inv \<a>[PoE.map g, e (src g), I\<^sub>S.map f] \<cdot>
                     (PoE.map g \<star> \<eta>\<^sub>1 f) \<cdot>
                     \<a>[PoE.map g, PoE.map f, e (src f)]
                       = \<eta>\<^sub>1 (g \<star> f) \<cdot> (PoE.cmp (g, f) \<star> e (src f))"
      proof -
        fix f g
        assume f: "ide f" and g: "ide g" and fg: "src g = trg f"
        let ?a = "src\<^sub>B f"
        let ?b = "src\<^sub>B g"
        let ?c = "trg\<^sub>B g"
        have hseq: "ide f \<and> ide g \<and> arr f \<and> arr g \<and> src g = trg f"
          using f g fg ide_char by auto
        have hseq\<^sub>B: "B.ide f \<and> B.ide g \<and> B.arr f \<and> B.arr g \<and> src\<^sub>B g = trg\<^sub>B f"
          using f g fg ide_char src_def trg_def by auto
        have 1: "?a = src f \<and> ?b = src g \<and> ?c = trg g"
          using f g fg src_def trg_def by simp
        have "(e (trg g) \<star> I\<^sub>S.cmp (g, f)) \<cdot>
              \<a>[e (trg g), I\<^sub>S.map g, I\<^sub>S.map f] \<cdot>
              (\<eta>\<^sub>1 g \<star> I\<^sub>S.map f) \<cdot>
              inv \<a>[PoE.map g, e (src g), I\<^sub>S.map f] \<cdot>
              (PoE.map g \<star> \<eta>\<^sub>1 f) \<cdot>
              \<a>[PoE.map g, PoE.map f, e (src f)]
                = (e ?c \<star> I\<^sub>S.cmp (g, f)) \<cdot>
                  \<a>[e ?c, I\<^sub>S.map g, I\<^sub>S.map f] \<cdot>
                  (\<eta>\<^sub>1 g \<star> I\<^sub>S.map f) \<cdot>
                  inv \<a>[PoE.map g, e ?b, I\<^sub>S.map f] \<cdot>
                  (PoE.map g \<star> \<eta>\<^sub>1 f) \<cdot>
                  \<a>[PoE.map g, PoE.map f, e ?a]"
          using 1 by simp
        also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))
                            \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                         (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                         (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                         (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         \<a>\<^sub>B[P g, P f, e ?a]"
        proof -
          have "(e ?c \<star> I\<^sub>S.cmp (g, f)) \<cdot>
                \<a>[e ?c, I\<^sub>S.map g, I\<^sub>S.map f] \<cdot>
                (\<eta>\<^sub>1 g \<star> I\<^sub>S.map f) \<cdot>
                inv \<a>[PoE.map g, e ?b, I\<^sub>S.map f] \<cdot>
                (PoE.map g \<star> unit\<^sub>1 f) \<cdot>
                \<a>[PoE.map g, PoE.map f, e ?a]
                  = (e ?c \<star> g \<star> f) \<cdot>
                    \<a>[e ?c, g, f] \<cdot>
                    (\<eta>\<^sub>1 g \<star> f) \<cdot>
                    inv \<a>[P (E g), e ?b, f] \<cdot>
                    (P (E g) \<star> \<eta>\<^sub>1 f) \<cdot>
                    \<a>[P (E g), P (E f), e ?a]"
            using f g fg by simp
          also have "... = (e ?c \<star> g \<star> f) \<cdot>\<^sub>B
                           \<a>[e ?c, g, f] \<cdot>\<^sub>B
                           (\<eta>\<^sub>1 g \<star> f) \<cdot>\<^sub>B
                           inv \<a>[P (E g), e ?b, f] \<cdot>\<^sub>B
                           (P (E g) \<star> \<eta>\<^sub>1 f) \<cdot>\<^sub>B
                           \<a>[P (E g), P (E f), e ?a]"
          proof -
            have "arr ..."
            proof -
              have "\<guillemotleft>... : (P (E g) \<star> P (E f)) \<star> e ?a \<Rightarrow> e ?c \<star> g \<star> f\<guillemotright>"
              proof (intro comp_in_homI)
                show "\<guillemotleft>\<a>[P (E g), P (E f), e ?a] :
                         (P (E g) \<star> P (E f)) \<star> e ?a \<Rightarrow> P (E g) \<star> P (E f) \<star> e ?a\<guillemotright>"
                  using f g fg VVV.arr_char VV.arr_char src_def obj_src assoc_in_hom
                  by force
                show "\<guillemotleft>P (E g) \<star> \<eta>\<^sub>1 f : P (E g) \<star> P (E f) \<star> e ?a \<Rightarrow> P (E g) \<star> e ?b \<star> f\<guillemotright>"
                  using f g fg 1 unit\<^sub>1_in_hom\<^sub>S [of f] vconn_implies_hpar(2)
                  by (intro hcomp_in_vhom) auto
                show "\<guillemotleft>inv \<a>[P (E g), e ?b, f] : P (E g) \<star> e ?b \<star> f \<Rightarrow> (P (E g) \<star> e ?b) \<star> f\<guillemotright>"
                proof -
                  have "\<guillemotleft>\<a>[P (E g), e ?b, f] : (P (E g) \<star> e ?b) \<star> f \<Rightarrow> P (E g) \<star> e ?b \<star> f\<guillemotright>"
                    using f g fg 1 VVV.arr_char VV.arr_char assoc_in_hom by simp
                  moreover have "iso \<a>[P (E g), e ?b, f]"
                    using f g fg 1 VVV.arr_char VV.arr_char iso_assoc by simp
                  ultimately show ?thesis
                    using inv_in_hom by simp
                qed
                show "\<guillemotleft>unit\<^sub>1 g \<star> f : (P (E g) \<star> e ?b) \<star> f \<Rightarrow> (e ?c \<star> g) \<star> f\<guillemotright>"
                  using f g fg 1 unit\<^sub>1_in_hom\<^sub>S [of g]
                  by (intro hcomp_in_vhom) auto
                have 2: "ide (e (trg g))"
                  using g by simp
                have 3: "src (e (trg g)) = trg g"
                  using g trg_def hseqE in_hom_char obj_trg by auto
                show "\<guillemotleft>\<a>[e ?c, g, f] : (e ?c \<star> g) \<star> f \<Rightarrow> e ?c \<star> g \<star> f\<guillemotright>"
                  using f g fg 1 2 3 VVV.arr_char VV.arr_char assoc_in_hom [of "e ?c" g f]
                  by simp
                show "\<guillemotleft>e ?c \<star> g \<star> f : e ?c \<star> g \<star> f \<Rightarrow> e ?c \<star> g \<star> f\<guillemotright>"
                  using f g fg 1 2 3
                  by (intro hcomp_in_vhom) auto
              qed
              thus ?thesis by blast
            qed
            thus ?thesis
              using comp_eqI by blast
          qed
          also have "... = (e ?c \<star> g \<star> f) \<cdot>\<^sub>B
                           \<a>[e ?c, g, f] \<cdot>\<^sub>B
                           (\<eta>\<^sub>1 g \<star> f) \<cdot>\<^sub>B
                           B.inv \<a>[P (E g), e ?b, f] \<cdot>\<^sub>B
                           (P (E g) \<star> \<eta>\<^sub>1 f) \<cdot>\<^sub>B
                           \<a>[P (E g), P (E f), e ?a]"
          proof -
            (*
             * TODO: Maybe assoc should be a definition in subcategory, rather than
             * an abbreviation.  The expansion seems to create problems here.
             *)
            have "iso \<a>[P (E g), e ?b, f]"
              using f g fg hseq hseq\<^sub>B src_def trg_def emb.map\<^sub>0_def emb.map_def arr_char
                    obj_char P\<^sub>0_props(6)
              by (intro iso_assoc) auto
            thus ?thesis
              using f g fg inv_char [of "\<a>[P (E g), e ?b, f]"] by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>[e ?c, g, f] \<cdot>\<^sub>B
                           (\<eta>\<^sub>1 g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           B.inv \<a>[P (E g), e ?b, f] \<cdot>\<^sub>B
                           (P (E g) \<star>\<^sub>B \<eta>\<^sub>1 f) \<cdot>\<^sub>B
                           \<a>[P (E g), P (E f), e ?a]"
          proof -
            have "arr (unit\<^sub>0 ?c)"
              using hseq obj_trg trg_def by auto
            moreover have "arr (g \<star>\<^sub>B f)"
              using hseq hseq\<^sub>B arr_char by auto
            ultimately show ?thesis
              unfolding hcomp_def
              using f g fg hseq\<^sub>B src_def trg_def P\<^sub>0_props(1) emb.map\<^sub>0_def emb.map_def
              by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g, f] \<cdot>\<^sub>B
                           (\<eta>\<^sub>1 g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           B.inv \<a>\<^sub>B[P (E g), e ?b, f] \<cdot>\<^sub>B
                           (P (E g) \<star>\<^sub>B \<eta>\<^sub>1 f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P (E g), P (E f), e ?a]"
          proof -
            have "arr (e ?a) \<and> arr (e ?b) \<and> arr (e ?c)"
              using hseq hseq\<^sub>B src_def trg_def obj_char src.preserves_arr trg.preserves_arr
              by auto
            thus ?thesis
              using f g fg VVV.arr_char VV.arr_char src_def trg_def hseq\<^sub>B
                    emb.map\<^sub>0_def emb.map_def
              by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g, f] \<cdot>\<^sub>B
                           (\<eta>\<^sub>1 g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (B.inv \<a>\<^sub>B[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<eta>\<^sub>1 f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a])"
            using f g fg 1 emb.map_def by simp
          also have "... = (e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g, f] \<cdot>\<^sub>B
                           (\<eta>\<^sub>1 g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<eta>\<^sub>1 f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a])"
            using hseq\<^sub>B P.preserves_ide ide_char B.assoc'_eq_inv_assoc [of "P g" "e ?b" f]
            by simp
          also have "... = (e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g, f] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g]) \<cdot>\<^sub>B
                            \<a>\<^sub>B[e ?c, g, ?b] \<cdot>\<^sub>B
                            ((e ?c \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b)) \<cdot>\<^sub>B
                            \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<cdot>\<^sub>B
                            (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b)
                               \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                                   \<a>\<^sub>B[e ?b, f, ?a] \<cdot>\<^sub>B
                                   ((e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                                   \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                                   (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
            unfolding unit\<^sub>1_def
            using hseq\<^sub>B B.comp_assoc by auto
          also have "... = ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g, f]) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g]) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
            using hseq\<^sub>B ide_char P.preserves_ide B.whisker_left B.whisker_right B.comp_assoc
            by auto
          also have "... = \<a>\<^sub>B[e ?c, g, f] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g]) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B[e ?c, g, ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f)) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "(e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<cdot>\<^sub>B \<a>\<^sub>B[e ?c, g, f] = \<a>\<^sub>B[e ?c, g, f]"
              using hseq\<^sub>B B.comp_cod_arr by auto
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = \<a>\<^sub>B[e ?c, g, f] \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<r>\<^sub>B[g]) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f)) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "(\<a>\<^sub>B[e ?c, g, ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B (((e ?c \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f)
                    = \<a>\<^sub>B[e ?c, g, ?b] \<cdot>\<^sub>B ((e ?c \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f"
              using hseq\<^sub>B B.whisker_right by auto
            also have "... = (e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b)) \<cdot>\<^sub>B
                              \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f"
              using hseq\<^sub>B B.assoc_naturality [of "e ?c" g "B.inv (\<eta> ?b)"] by simp
            also have "... = ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                              (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f)"
              using hseq\<^sub>B B.whisker_right by auto
            finally have "(\<a>\<^sub>B[e ?c, g, ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B (((e ?c \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f)
                            = ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                              (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f)"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (\<a>\<^sub>B[e ?c, g, f] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
            using hseq\<^sub>B B.whisker_left B.whisker_right B.comp_assoc by simp
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                           ((P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
            using hseq\<^sub>B B.comp_assoc
                  B.assoc_naturality [of "e ?c" "\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))" f]
            by fastforce
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           ((P g \<star>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B e ?b \<star>\<^sub>B f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "(P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a]) \<cdot>\<^sub>B (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))
                    = P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a] \<cdot>\<^sub>B ((e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B ide_char P.preserves_ide B.whisker_left by auto
            also have "... = P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]"
              using hseq\<^sub>B B.assoc_naturality [of "e ?b" f "B.inv (\<eta> ?a)"] by auto
            also have "... = (P g \<star>\<^sub>B e ?b \<star>\<^sub>B f \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                             (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a])"
              using hseq\<^sub>B ide_char P.preserves_ide B.whisker_left by auto
            finally have "(P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, ?a]) \<cdot>\<^sub>B (P g \<star>\<^sub>B (e ?b \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))
                            = (P g \<star>\<^sub>B e ?b \<star>\<^sub>B f \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                              (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a])"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B e ?b \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
            using hseq\<^sub>B ide_char P.preserves_ide B.whisker_left B.comp_assoc by auto
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((P g \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
            using hseq\<^sub>B B.comp_assoc
                  B.assoc'_naturality [of "P g" "e ?b" "\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"]
            by simp
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                  ((P g \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                    = (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<cdot>\<^sub>B (P g \<star>\<^sub>B e ?b) \<star>\<^sub>B
                      (f \<cdot>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))"
            proof -
              have "B.seq (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) (P g \<star>\<^sub>B e ?b)"
                using hseq\<^sub>B P.preserves_ide P_def src_def trg_def by auto
              moreover have "B.seq f (\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))"
                using hseq\<^sub>B by simp
              ultimately show ?thesis
                using B.interchange
                        [of "\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b" "P g \<star>\<^sub>B e ?b"
                            f "\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"]
                by presburger
            qed
            also have "... = (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<cdot>\<^sub>B (e ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<star>\<^sub>B e ?b)
                                \<star>\<^sub>B f \<cdot>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.whisker_right P_def by auto
            also have "... = (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.comp_arr_dom B.comp_cod_arr by simp
            finally have "((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B f) \<cdot>\<^sub>B
                          ((P g \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                            = (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                           ((\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "(\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                  ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                    = \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<cdot>\<^sub>B (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b)
                        \<star>\<^sub>B f \<cdot>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.interchange by simp
            also have "... = \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<cdot>\<^sub>B (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b)
                                \<star>\<^sub>B (\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.comp_cod_arr B.comp_arr_dom by simp
            also have "... = (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                             ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a))"
              using hseq\<^sub>B B.interchange by auto
            finally have "(\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b)
                              \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                            = (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                              ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a))"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "(\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B
                  (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                    = \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<cdot>\<^sub>B \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b]
                        \<star>\<^sub>B f \<cdot>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.interchange by simp
            also have "... = \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<cdot>\<^sub>B \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b]
                                \<star>\<^sub>B (\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.comp_cod_arr B.comp_arr_dom by simp
            also have "... = (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                             (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.interchange by auto
            finally have "(\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f) \<cdot>\<^sub>B (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b]
                              \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                            = (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                              (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "\<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                  (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                    = \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B ((e ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<cdot>\<^sub>B
                      \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b]
                         \<star>\<^sub>B (\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a))"
              using hseq\<^sub>B B.comp_arr_dom B.comp_cod_arr by simp
            also have "... = \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                             ((e ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                             (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.interchange by simp
            also have "... = (\<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B
                             ((e ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                             (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using B.comp_assoc by simp
            also have "... = (((e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                             \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                             (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.assoc_naturality [of "e ?c" "g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b"
                                                 "\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"]
              by auto
            also have "... = ((e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                             \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                             (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using B.comp_assoc by simp
            finally have "\<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f] \<cdot>\<^sub>B (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b]
                              \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))
                            = ((e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                              \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                              (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))
                              \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            have "(e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                  ((e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))))
                    = e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<cdot>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b)
                         \<star>\<^sub>B f \<cdot>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.whisker_left B.interchange by fastforce
            also have "... = e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.comp_arr_dom B.comp_cod_arr by auto
            finally have "(e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<cdot>\<^sub>B
                          ((e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))))
                            = e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              by simp
            thus ?thesis by simp
          qed
          finally show ?thesis by blast
        qed
        also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, ?a] \<cdot>\<^sub>B
                         ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                         ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
        proof -
          (* Working from the above expression to the common form, as in the previous part. *)
          have "(e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, ?a] \<cdot>\<^sub>B
                ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)
                  = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                    (\<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, ?a] \<cdot>\<^sub>B
                    ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                    \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                    (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                    ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                    ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                    ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                    ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                    (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                    (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                    ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
            using B.comp_assoc by simp
          also have "... = ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                           (e ?c \<star>\<^sub>B (g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
            using hseq\<^sub>B B.assoc_naturality [of "e ?c" "g \<star>\<^sub>B f" "B.inv (\<eta> ?a)"] B.comp_assoc
            by simp
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
            using hseq\<^sub>B B.whisker_left B.comp_assoc by auto
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a)
                    = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a] \<cdot>\<^sub>B (g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.whisker_right B.whisker_left by auto
            also have "... = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a] \<cdot>\<^sub>B (\<r>\<^sub>B[g] \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                             \<a>\<^sub>B\<^sup>-\<^sup>1[g, ?b, f \<star>\<^sub>B d ?a])
                                \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.triangle' comp_assoc by auto
            also have "... = ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                             ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                             ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.whisker_left B.whisker_right by auto
            finally have "((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                          ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a)
                            = ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                              ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                              ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a)"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B (((g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a))) \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                  ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)
                    = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, ?b, f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.whisker_right B.whisker_left by auto
            also have "... = (e ?c \<star>\<^sub>B
                               (((g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                               \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])
                                 \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.assoc'_naturality [of g "B.inv (\<eta> ?b)" "f \<star>\<^sub>B d ?a"] by auto
            also have "... = ((e ?c \<star>\<^sub>B (((g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a))) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                             (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.whisker_right B.whisker_left by auto
            finally have "((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                          ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)
                            = ((e ?c \<star>\<^sub>B (((g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a))) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                              (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a)"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
            using hseq\<^sub>B B.whisker_right B.whisker_left B.comp_assoc by auto
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B (((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a)) \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                  ((e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)
                    = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a] \<cdot>\<^sub>B
                      ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.whisker_left B.whisker_right by auto
            also have "... = (e ?c \<star>\<^sub>B
                               (((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                                  \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a])
                                 \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.assoc'_naturality [of "\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))" f "d ?a"]
              by auto
            also have "... = ((e ?c \<star>\<^sub>B (((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a))
                                 \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                             ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.whisker_left B.whisker_right by auto
            finally have "((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                          ((e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)
                            = ((e ?c \<star>\<^sub>B (((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a)) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                              ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a)"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                  ((e ?c \<star>\<^sub>B (((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a)) \<star>\<^sub>B e ?a)
                    = \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<cdot>\<^sub>B
                      (e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<star>\<^sub>B d ?a)) \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.whisker_right by auto
            also have "... = ((e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                             \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a"
              using hseq\<^sub>B B.assoc'_naturality [of "e ?c" "(\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f" "d ?a"]
              by fastforce
            also have "... = (((e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<star>\<^sub>B d ?a)
                                \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                             (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.whisker_right by auto
            finally have "(\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                          ((e ?c \<star>\<^sub>B (((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a)) \<star>\<^sub>B e ?a)
                            = (((e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                              (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a)"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "\<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                  (((e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a)
                    = ((e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f)) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                      \<a>\<^sub>B[e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a, e ?a]"
              using hseq\<^sub>B
                    B.assoc_naturality [of "(e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f))"
                                           "d ?a" "e ?a"]
              by fastforce
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           (e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
            using hseq\<^sub>B B.comp_assoc
                  B.assoc_naturality [of "e ?c" "(\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f"
                                         "d ?a \<star>\<^sub>B e ?a"]
            by force
          also have "... = (e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B[g, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (e ?c \<star>\<^sub>B ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))) \<star>\<^sub>B f) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))
                    = e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B \<a>\<^sub>B[g, f, ?a] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.runit_hcomp B.comp_assoc by auto
            also have "... = e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f]) \<cdot>\<^sub>B (g \<star>\<^sub>B f \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                             \<a>\<^sub>B[g, f, d ?a \<star>\<^sub>B e ?a]"
              using hseq\<^sub>B B.assoc_naturality [of g f "B.inv (\<eta> ?a)"] by auto
            also have "... = (e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                             (e ?c \<star>\<^sub>B \<a>\<^sub>B[g, f, d ?a \<star>\<^sub>B e ?a])"
              using hseq\<^sub>B B.whisker_left B.comp_assoc by auto
            finally have "e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a))
                            = (e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                              (e ?c \<star>\<^sub>B \<a>\<^sub>B[g, f, d ?a \<star>\<^sub>B e ?a])"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = ((e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                           (e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a))) \<cdot>\<^sub>B
                           (e ?c \<star>\<^sub>B \<a>\<^sub>B[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "(e ?c \<star>\<^sub>B \<a>\<^sub>B[g, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                  (e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)
                    = e ?c \<star>\<^sub>B \<a>\<^sub>B[g, f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                              ((\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.whisker_left by auto
            also have "... = e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                                     \<a>\<^sub>B[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a \<star>\<^sub>B e ?a]"
              using hseq\<^sub>B B.assoc_naturality [of "\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))" f "d ?a \<star>\<^sub>B e ?a"]
              by auto
            also have "... = (e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                             (e ?c \<star>\<^sub>B \<a>\<^sub>B[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a \<star>\<^sub>B e ?a])"
              using hseq\<^sub>B B.whisker_left by auto
            finally have "(e ?c \<star>\<^sub>B \<a>\<^sub>B[g, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                          (e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f) \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)
                            = (e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                              (e ?c \<star>\<^sub>B \<a>\<^sub>B[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a \<star>\<^sub>B e ?a])"
              by simp
            thus ?thesis
              using B.comp_assoc by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B
                                    \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           (e ?c \<star>\<^sub>B \<a>\<^sub>B[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "(e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                  (e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a))
                    = e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                              (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.whisker_left by auto
            also have "... = e ?c \<star>\<^sub>B g \<cdot>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))
                                  \<star>\<^sub>B (\<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.interchange by auto
            also have "... = e ?c \<star>\<^sub>B (g \<cdot>\<^sub>B \<r>\<^sub>B[g]) \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))
                                  \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)"
              using B.comp_assoc by simp
            also have "... = e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              using hseq\<^sub>B B.comp_arr_dom B.comp_cod_arr by auto
            finally have "(e ?c \<star>\<^sub>B (g \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a)))) \<cdot>\<^sub>B
                          (e ?c \<star>\<^sub>B (\<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a))
                            = e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b)) \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))"
              by simp
            thus ?thesis
              by simp
          qed
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g] \<cdot>\<^sub>B (g \<star>\<^sub>B B.inv (\<eta> ?b))
                                 \<star>\<^sub>B \<r>\<^sub>B[f] \<cdot>\<^sub>B (f \<star>\<^sub>B B.inv (\<eta> ?a))) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                           (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[P g, P f, e ?a]"
          proof -
            let ?LHS = "(e ?c \<star>\<^sub>B \<a>\<^sub>B[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                        \<a>\<^sub>B[e ?c, (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                        \<a>\<^sub>B[e ?c \<star>\<^sub>B (g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                        (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, (g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b)) \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a])) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"

            let ?RHS = "\<a>\<^sub>B[e ?c, g \<star>\<^sub>B d ?b \<star>\<^sub>B e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                        (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, e ?b] \<star>\<^sub>B f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B e ?b) \<star>\<^sub>B (f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                        \<a>\<^sub>B\<^sup>-\<^sup>1[P g, e ?b, f \<star>\<^sub>B d ?a \<star>\<^sub>B e ?a] \<cdot>\<^sub>B
                        (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b, f, d ?a \<star>\<^sub>B e ?a]) \<cdot>\<^sub>B
                        (P g \<star>\<^sub>B \<a>\<^sub>B[e ?b \<star>\<^sub>B f, d ?a, e ?a]) \<cdot>\<^sub>B
                        (P g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?b, f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                        \<a>\<^sub>B[P g, P f, e ?a]"
            have "?LHS = ?RHS"
            proof -
              let ?LHSt = "(\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                           \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                           \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>, \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                           (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>)) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           ((\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           (((\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>])) \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           ((\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J f\<^bold>] \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>P\<^bold>R\<^bold>J f\<^bold>] \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           ((\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J f) \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>)"

              let ?RHSt = "\<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                           (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           (\<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>\<langle>e ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           ((\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>) \<^bold>\<star> ( \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>)) \<^bold>\<cdot>
                           \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>P\<^bold>R\<^bold>J g, \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                           (\<^bold>P\<^bold>R\<^bold>J g \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                           (\<^bold>P\<^bold>R\<^bold>J g \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>, \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                           (\<^bold>P\<^bold>R\<^bold>J g \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>e ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                           \<^bold>\<a>\<^bold>[\<^bold>P\<^bold>R\<^bold>J g, \<^bold>P\<^bold>R\<^bold>J f, \<^bold>\<langle>e ?a\<^bold>\<rangle>\<^bold>]"

              have "?LHS = \<lbrace>?LHSt\<rbrace>"
                using f g fg hseq\<^sub>B B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                      B.VV.ide_char B.VV.arr_char P_def
                by auto
              also have "... = \<lbrace>?RHSt\<rbrace>"
                using hseq\<^sub>B by (intro EV.eval_eqI, auto)
              also have "... = ?RHS"
                using f g fg hseq\<^sub>B B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                      B.VV.ide_char B.VV.arr_char P_def
                by auto
              finally show ?thesis by blast
            qed
            thus ?thesis using hseq\<^sub>B by auto
          qed
          finally show ?thesis by simp
        qed
        also have "... = \<eta>\<^sub>1 (g \<star> f) \<cdot> (PoE.cmp (g, f) \<star> e (src f))"
        proof -
          have "\<eta>\<^sub>1 (g \<star> f) \<cdot> (PoE.cmp (g, f) \<star> e (src f))
                  = \<eta>\<^sub>1 (g \<star> f) \<cdot> (P (E (g \<star> f)) \<cdot> P (\<Phi>\<^sub>E (g, f)) \<cdot> \<Phi>\<^sub>P (E g, E f) \<star> e (src f))"
            using f g fg PoE.cmp_def VV.arr_char VV.dom_char by simp
          also have "... = \<eta>\<^sub>1 (g \<star> f) \<cdot> (P (E (g \<star> f)) \<cdot> P (g \<star>\<^sub>B f) \<cdot> \<Phi>\<^sub>P (E g, E f) \<star> e (src f))"
            using f g fg emb.cmp_def VV.arr_char by simp
          also have "... = \<eta>\<^sub>1 (g \<star> f) \<cdot> (P (E (g \<star> f)) \<cdot> \<Phi>\<^sub>P (E g, E f) \<star> e (src f))"
            using f g fg hseq\<^sub>B comp_cod_arr emb.map_def hseq_char' prj.cmp_simps'(1,5)
            by auto
          also have "... = \<eta>\<^sub>1 (g \<star> f) \<cdot> (P (g \<star>\<^sub>B f) \<cdot> \<Phi>\<^sub>P (g, f) \<star> e (src f))"
            using hseq\<^sub>B hseq emb.map_def hcomp_char hseqI' by auto
          also have "... = \<eta>\<^sub>1 (g \<star> f) \<cdot> (\<Phi>\<^sub>P (g, f) \<cdot> (P g \<star> P f) \<star> e (src f))"
            using hseq\<^sub>B B.VV.arr_char B.VV.dom_char B.VV.cod_char \<Phi>\<^sub>P.naturality [of "(g, f)"]
                  P.FF_def
            by auto
          also have "... = \<eta>\<^sub>1 (g \<star> f) \<cdot> (\<Phi>\<^sub>P (g, f) \<star> e (src f))"
          proof -
            have "\<Phi>\<^sub>P (g, f) \<cdot> (P g \<star> P f) = \<Phi>\<^sub>P (g, f)"
              using f g fg comp_arr_dom [of "\<Phi>\<^sub>P (g, f)" "P g \<star> P f"] VV.arr_char
              by (metis (no_types, lifting) prj.cmp_simps'(1) \<Phi>\<^sub>P_simps(4) hseq\<^sub>B)
            thus ?thesis by simp
          qed
          also have "... = \<eta>\<^sub>1 (g \<star> f) \<cdot>\<^sub>B (\<Phi>\<^sub>P (g, f) \<star> e (src f))"
          proof -
            (* TODO: For some reason, this requires an epic struggle. *)
            have "cod (\<Phi>\<^sub>P (g, f)) = P (g \<star> f)"
              using f g fg \<Phi>\<^sub>P_simps(5) [of g f] VV.arr_char
              by (metis (no_types, lifting) hcomp_eqI hseq hseq\<^sub>B hseqI')
            moreover have "hseq (\<Phi>\<^sub>P (g, f)) (e (src f))"
              using f g fg hseq\<^sub>B 1 B.VV.arr_char by auto
            ultimately have "seq (\<eta>\<^sub>1 (g \<star> f)) (\<Phi>\<^sub>P (g, f) \<star> e (src f))"
              using f g fg hseq\<^sub>B 1 B.VV.arr_char P\<^sub>0_props prj.cmp_simps emb.map_def
                    \<Phi>\<^sub>P_simps(5) [of g f] hcomp_eqI B.VV.dom_char B.VV.cod_char P.FF_def
              by auto
            thus ?thesis
              using comp_eqI by simp
          qed
          also have "... = \<eta>\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>B (\<Phi>\<^sub>P (g, f) \<star>\<^sub>B e (src f))"
            using f g fg hseq\<^sub>B 1 B.VV.arr_char hcomp_eqI by simp
          also have "... = ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, ?a] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           (\<Phi>\<^sub>P (g, f) \<star>\<^sub>B e ?a)"
            unfolding unit\<^sub>1_def
            using hseq\<^sub>B 1 comp_char by simp
          also have "... = ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, ?a] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           (((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                           (e ?c \<star>\<^sub>B g \<star>\<^sub>B
                              \<l>\<^sub>B[f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                              (B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                              (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                              \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<cdot>\<^sub>B
                              \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                              (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f))
                                 \<star>\<^sub>B e ?a)"
          proof -
            have "B.VV.ide (g, f)"
              using f g fg ide_char src_def trg_def B.VV.ide_char by auto
            hence "\<Phi>\<^sub>P (g, f) = CMP g f"
              unfolding \<Phi>\<^sub>P_def
              using f g fg ide_char CMP.map_simp_ide by simp
            also have "... = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                             (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                             (B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                             (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                             \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<cdot>\<^sub>B
                             \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                             (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f)"
              using hseq\<^sub>B CMP_def by auto
            finally have "\<Phi>\<^sub>P (g, f) = (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                                      (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                                      (B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                                      (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                                      \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<cdot>\<^sub>B
                                      \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                                      (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f)"
              by blast
            thus ?thesis by simp
          qed
          also have "... = ((e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, src f] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a)) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                            (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                            (e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                            (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                            \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<cdot>\<^sub>B
                            \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                            (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f)
                               \<star>\<^sub>B e ?a)"
            using f g fg hseq\<^sub>B src_def trg_def B.whisker_left B.comp_assoc by simp
          also have "... = (e ?c \<star>\<^sub>B \<r>\<^sub>B[g \<star>\<^sub>B f]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c, g \<star>\<^sub>B f, src f] \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B f) \<star>\<^sub>B B.inv (\<eta> ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[e ?c \<star>\<^sub>B g \<star>\<^sub>B f, d ?a, e ?a] \<cdot>\<^sub>B
                           (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g \<star>\<^sub>B f, d ?a] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                           ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
          proof -
            have "B.arr ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                        (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                        (e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                        (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                        \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<cdot>\<^sub>B
                        \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                        (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f))"
              using hseq\<^sub>B ide_char P.preserves_ide P_def by auto
            hence "(e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                   (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                   (e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                   (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                   \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<cdot>\<^sub>B
                   \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                   (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f)
                      \<star>\<^sub>B e ?a
                     = ((e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                       ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                       ((e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                       ((e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<star>\<^sub>B e ?a) \<cdot>\<^sub>B
                       ((\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<star>\<^sub>B e ?a)"
              using hseq\<^sub>B B.whisker_right by fastforce
            thus ?thesis
              using B.comp_assoc by simp
          qed
          finally show ?thesis
            using f ide_char src_def by simp
        qed
        finally show "(e (trg g) \<star> I\<^sub>S.cmp (g, f)) \<cdot>
                      \<a>[e (trg g), I\<^sub>S.map g, I\<^sub>S.map f] \<cdot>
                      (\<eta>\<^sub>1 g \<star> I\<^sub>S.map f) \<cdot>
                      inv \<a>[PoE.map g, e (src g), I\<^sub>S.map f] \<cdot>
                      (PoE.map g \<star> \<eta>\<^sub>1 f) \<cdot>
                      \<a>[PoE.map g, PoE.map f, e (src f)]
                        = \<eta>\<^sub>1 (g \<star> f) \<cdot> (PoE.cmp (g, f) \<star> e (src f))"
          by blast
      qed
    qed

    abbreviation (input) counit\<^sub>0
    where "counit\<^sub>0 \<equiv> d"

    definition counit\<^sub>1
    where "counit\<^sub>1 f = \<a>\<^sub>B[d (trg\<^sub>B f), e (trg\<^sub>B f), f \<star>\<^sub>B d (src\<^sub>B f)] \<cdot>\<^sub>B
                       (\<eta> (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B d (src\<^sub>B f)) \<cdot>\<^sub>B
                       \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d (src\<^sub>B f)]"

    abbreviation (input) \<epsilon>\<^sub>1
    where "\<epsilon>\<^sub>1 \<equiv> counit\<^sub>1"

    lemma counit\<^sub>1_in_hom [intro]:
    assumes "B.ide f"
    shows "\<guillemotleft>\<epsilon>\<^sub>1 f : f \<star>\<^sub>B d (src\<^sub>B f) \<Rightarrow>\<^sub>B d (trg\<^sub>B f) \<star>\<^sub>B e (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B d (src\<^sub>B f)\<guillemotright>"
      using assms B.iso_is_arr
      by (unfold counit\<^sub>1_def, intro B.comp_in_homI' B.seqI B.hseqI' B.hcomp_in_vhom) auto

    lemma counit\<^sub>1_simps [simp]:
    assumes "B.ide f"
    shows "B.arr (\<epsilon>\<^sub>1 f)"
    and "src\<^sub>B (\<epsilon>\<^sub>1 f) = P\<^sub>0 (src\<^sub>B f)" and "trg\<^sub>B (\<epsilon>\<^sub>1 f) = trg\<^sub>B f"
    and "B.dom (\<epsilon>\<^sub>1 f) = f \<star>\<^sub>B d (src\<^sub>B f)"
    and "B.cod (\<epsilon>\<^sub>1 f) = d (trg\<^sub>B f) \<star>\<^sub>B e (trg\<^sub>B f) \<star>\<^sub>B f \<star>\<^sub>B d (src\<^sub>B f)"
    and "B.iso (\<epsilon>\<^sub>1 f)"
      using assms counit\<^sub>1_in_hom
           apply auto
      using B.vconn_implies_hpar(1)
        apply fastforce
      using B.vconn_implies_hpar(2)
        apply fastforce
      unfolding counit\<^sub>1_def
      apply (intro B.isos_compose)
      by auto

    lemma technical:
    assumes "B.ide f" and "B.ide g" and "src\<^sub>B g = trg\<^sub>B f"
    shows "(\<epsilon>\<^sub>1 g \<star>\<^sub>B P f) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d (src\<^sub>B g), P f] \<cdot>\<^sub>B (g \<star>\<^sub>B \<epsilon>\<^sub>1 f)
             = (\<a>\<^sub>B[d (trg\<^sub>B g), e (trg\<^sub>B g), g \<star>\<^sub>B d (src\<^sub>B g)] \<star>\<^sub>B P f) \<cdot>\<^sub>B
               (\<a>\<^sub>B[d (trg\<^sub>B g) \<star>\<^sub>B e (trg\<^sub>B g), g, d (src\<^sub>B g)] \<star>\<^sub>B P f) \<cdot>\<^sub>B
               \<a>\<^sub>B\<^sup>-\<^sup>1[(d (trg\<^sub>B g) \<star>\<^sub>B e (trg\<^sub>B g)) \<star>\<^sub>B g, d (src\<^sub>B g), P f] \<cdot>\<^sub>B
               (((d (trg\<^sub>B g) \<star>\<^sub>B e (trg\<^sub>B g)) \<star>\<^sub>B g) \<star>\<^sub>B d (src\<^sub>B g) \<star>\<^sub>B P f) \<cdot>\<^sub>B
               (((d (trg\<^sub>B g) \<star>\<^sub>B e (trg\<^sub>B g)) \<star>\<^sub>B g)
                  \<star>\<^sub>B \<a>\<^sub>B[d (src\<^sub>B g), e (src\<^sub>B g), f \<star>\<^sub>B d (src\<^sub>B f)]) \<cdot>\<^sub>B
               ((\<eta> (trg\<^sub>B g) \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B (\<eta> (src\<^sub>B g) \<star>\<^sub>B f \<star>\<^sub>B d (src\<^sub>B f))) \<cdot>\<^sub>B
               (g \<star>\<^sub>B \<a>\<^sub>B[src\<^sub>B g, f, d (src\<^sub>B f)] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d (src\<^sub>B f)))"
    proof -
      let ?a = "src\<^sub>B f"
      let ?b = "src\<^sub>B g"
      let ?c = "trg\<^sub>B g"
      have "(\<epsilon>\<^sub>1 g \<star>\<^sub>B P f) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] \<cdot>\<^sub>B (g \<star>\<^sub>B \<epsilon>\<^sub>1 f)
              = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<cdot>\<^sub>B
                (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<cdot>\<^sub>B
                \<l>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b]
                   \<star>\<^sub>B P f) \<cdot>\<^sub>B
                \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] \<cdot>\<^sub>B
                (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                      (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                      \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
        using assms counit\<^sub>1_def by simp
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       ((\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<l>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
      proof -
        have "\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<cdot>\<^sub>B
              (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<cdot>\<^sub>B
              \<l>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b]
                \<star>\<^sub>B P f
                = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  ((\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  (\<l>\<^sub>B\<^sup>-\<^sup>1[g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f)"
          using assms B.iso_is_arr B.whisker_right P_def by auto
        moreover have "g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                           (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a]
                         = (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                           (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
          using assms B.iso_is_arr B.whisker_left by simp
        ultimately show ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       ((\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[?c, g, d ?b] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
        using assms B.lunit_hcomp [of g "d ?b"] B.comp_assoc by simp
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (((\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[?c, g, d ?b] \<star>\<^sub>B P f)) \<cdot>\<^sub>B
                       ((\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
        using assms B.whisker_right P_def B.comp_assoc by simp
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (((\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
      proof -
        have "((\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B (\<a>\<^sub>B[?c, g, d ?b] \<star>\<^sub>B P f) =
              (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<cdot>\<^sub>B \<a>\<^sub>B[?c, g, d ?b] \<star>\<^sub>B P f"
          using assms B.whisker_right P_def B.iso_is_arr by simp
        also have "... = \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<cdot>\<^sub>B ((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b) \<star>\<^sub>B P f"
          using assms B.assoc_naturality [of "\<eta> ?c" g "d ?b"] B.iso_is_arr by simp
        also have "... = (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         (((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b) \<star>\<^sub>B P f)"
          using assms B.whisker_right P_def B.iso_is_arr by simp
        finally have "((\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B (\<a>\<^sub>B[?c, g, d ?b] \<star>\<^sub>B P f) =
                        (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                        (((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b) \<star>\<^sub>B P f)"
          by blast
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       ((((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[?c \<star>\<^sub>B g, d ?b, P f]) \<cdot>\<^sub>B
                       (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
      proof -
        have "((\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] =
              \<a>\<^sub>B\<^sup>-\<^sup>1[?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b \<star>\<^sub>B P f)"
          using assms B.assoc'_naturality [of "\<l>\<^sub>B\<^sup>-\<^sup>1[g]" "d ?b" "P f"] by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                       (((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b \<star>\<^sub>B P f)) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
      proof -
        have "(((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b) \<star>\<^sub>B P f) \<cdot>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[?c \<star>\<^sub>B g, d ?b, P f] =
              \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B ((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f)"
          using assms B.assoc'_naturality [of "\<eta> ?c \<star>\<^sub>B g" "d ?b" "P f"] B.iso_is_arr
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                       (((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a])) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
        using assms B.whisker_right B.iso_is_arr P_def B.comp_assoc by simp
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                       (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])"
      proof -
        have "((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
              (g \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a])
                = (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a])"
          using assms B.comp_arr_dom B.comp_cod_arr B.iso_is_arr P_def
                B.interchange [of "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]" g]
                B.interchange [of "(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g" "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]"]
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                       (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       (((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a]))"
      proof -
        have "((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B (g \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)
                = (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                  ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)"
          using assms B.comp_arr_dom B.comp_cod_arr B.iso_is_arr P_def
                B.interchange [of "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]" g]
                B.interchange [of "(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g" "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]"]
          by simp
        thus ?thesis
          using B.comp_assoc by simp
      qed
      also have "... = (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                       (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                       (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                       ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                       (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a))"
      proof -
        have "((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])
                = (\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a]"
          using assms B.comp_arr_dom B.iso_is_arr P_def
                B.interchange [of "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]" g "\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a" "\<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a]"]
          by simp
        also have "... = (\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B
                           (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B
                           (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)"
          using assms B.lunit_hcomp by simp
        also have "... = ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a))"
          using assms B.comp_arr_dom B.iso_is_arr P_def
                B.interchange [of "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]" g]
          by simp
        finally have "((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (g \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[f \<star>\<^sub>B d ?a])
                        = ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                          (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a))"
          by blast
        thus ?thesis by simp
      qed
      finally show ?thesis by blast
    qed

    sublocale counit: pseudonatural_equivalence
                        V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                        \<open>E \<circ> P\<close> EoP.cmp I\<^sub>C.map I\<^sub>C.cmp counit\<^sub>0 counit\<^sub>1
    proof
      show "\<And>a. B.obj a \<Longrightarrow> B.ide (d a)"
        by simp
      show "\<And>a. B.obj a \<Longrightarrow> B.equivalence_map (d a)"
      proof -
        fix a
        assume a: "B.obj a"
        interpret Adj: adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                         \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
          using a chosen_adjoint_equivalence by simp
        show "B.equivalence_map (d a)"
          using Adj.equivalence_in_bicategory_axioms B.equivalence_map_def Adj.dual_equivalence
          by blast
      qed
      show "\<And>a. B.obj a \<Longrightarrow> \<guillemotleft>d a : src\<^sub>B ((E \<circ> P) a) \<rightarrow>\<^sub>B src\<^sub>B (I\<^sub>C.map a)\<guillemotright>"
        unfolding emb.map_def by fastforce
      show "\<And>f. B.ide f \<Longrightarrow> B.iso (\<epsilon>\<^sub>1 f)"
        by simp
      show "\<And>f. B.ide f \<Longrightarrow> \<guillemotleft>\<epsilon>\<^sub>1 f : I\<^sub>C.map f \<star>\<^sub>B d (src\<^sub>B f) \<Rightarrow>\<^sub>B d (trg\<^sub>B f) \<star>\<^sub>B (E \<circ> P) f\<guillemotright>"
        unfolding counit\<^sub>1_def P_def emb.map_def
        using P_def P_simps(1)
        by (intro B.comp_in_homI' B.seqI B.hseqI') (auto simp add: B.iso_is_arr)
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> \<epsilon>\<^sub>1 (B.cod \<mu>) \<cdot>\<^sub>B (I\<^sub>C.map \<mu> \<star>\<^sub>B d (src\<^sub>B \<mu>))
                               = (d (trg\<^sub>B \<mu>) \<star>\<^sub>B (E \<circ> P) \<mu>) \<cdot>\<^sub>B \<epsilon>\<^sub>1 (B.dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "B.arr \<mu>"
        let ?a = "src\<^sub>B \<mu>"
        let ?b = "trg\<^sub>B \<mu>"
        let ?f = "B.dom \<mu>"
        let ?g = "B.cod \<mu>"
        have "\<epsilon>\<^sub>1 ?g \<cdot>\<^sub>B (I\<^sub>C.map \<mu> \<star>\<^sub>B d ?a)
                = (\<a>\<^sub>B[d ?b, e ?b, ?g \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                  (\<eta> ?b \<star>\<^sub>B ?g \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                  \<l>\<^sub>B\<^sup>-\<^sup>1[?g \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                  (\<mu> \<star>\<^sub>B d ?a)"
          using \<mu> counit\<^sub>1_def P_def emb.map_def arr_char P\<^sub>0_props(1) by simp
        also have "... = (d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?b, e ?b, ?f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<eta> ?b \<star>\<^sub>B ?f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         \<l>\<^sub>B\<^sup>-\<^sup>1[?f \<star>\<^sub>B d ?a]"
        proof -
          have "(\<a>\<^sub>B[d ?b, e ?b, ?g \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                (\<eta> ?b \<star>\<^sub>B ?g \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                \<l>\<^sub>B\<^sup>-\<^sup>1[?g \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                (\<mu> \<star>\<^sub>B d ?a)
                  = \<a>\<^sub>B[d ?b, e ?b, ?g \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                    (\<eta> ?b \<star>\<^sub>B ?g \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                    \<l>\<^sub>B\<^sup>-\<^sup>1[?g \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                    (\<mu> \<star>\<^sub>B d ?a)"
            using B.comp_assoc by simp
          also have "... = \<a>\<^sub>B[d ?b, e ?b, ?g \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                           ((\<eta> ?b \<star>\<^sub>B ?g \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           (?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                           \<l>\<^sub>B\<^sup>-\<^sup>1[?f \<star>\<^sub>B d ?a]"
            using \<mu> B.lunit'_naturality [of "\<mu> \<star>\<^sub>B d ?a"] B.comp_assoc by simp
          also have "... = (\<a>\<^sub>B[d ?b, e ?b, ?g \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                           ((d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                           (\<eta> ?b \<star>\<^sub>B ?f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           \<l>\<^sub>B\<^sup>-\<^sup>1[?f \<star>\<^sub>B d ?a]"
          proof -
            have "(\<eta> ?b \<star>\<^sub>B ?g \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) =
                    \<eta> ?b \<cdot>\<^sub>B ?b \<star>\<^sub>B ?g \<cdot>\<^sub>B \<mu> \<star>\<^sub>B d ?a \<cdot>\<^sub>B d ?a"
              using \<mu> B.iso_is_arr
                    B.interchange [of "\<eta> ?b" ?b "(?g \<star>\<^sub>B d ?a)" "\<mu> \<star>\<^sub>B d ?a"]
                    B.interchange [of "?g" \<mu> "d ?a" "d ?a"]
              by simp
            also have "... = (d ?b \<star>\<^sub>B e ?b) \<cdot>\<^sub>B \<eta> ?b \<star>\<^sub>B \<mu> \<cdot>\<^sub>B ?f \<star>\<^sub>B d ?a \<cdot>\<^sub>B d ?a"
              using \<mu> B.comp_arr_dom B.comp_cod_arr apply simp
              by (metis B.arrI equivalence_data_in_hom\<^sub>B(7) equivalence_data_simps\<^sub>B(17-18)
                  B.obj_trg)
            also have "... = ((d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (\<eta> ?b \<star>\<^sub>B ?f \<star>\<^sub>B d ?a)"
              using \<mu> B.iso_is_arr B.interchange [of "d ?b \<star>\<^sub>B e ?b" "\<eta> ?b" "\<mu> \<star>\<^sub>B d ?a" "?f \<star>\<^sub>B d ?a"]
                    B.interchange [of \<mu> "?f" "d ?a" "d ?a"]
              by simp
            finally have "(\<eta> ?b \<star>\<^sub>B ?g \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a)
                            = ((d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (\<eta> ?b \<star>\<^sub>B ?f \<star>\<^sub>B d ?a)"
              by blast
            thus ?thesis using B.comp_assoc by simp
          qed
          also have "... = (d ?b \<star>\<^sub>B e ?b \<star>\<^sub>B \<mu> \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           \<a>\<^sub>B[d ?b, e ?b, ?f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                           (\<eta> ?b \<star>\<^sub>B ?f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           \<l>\<^sub>B\<^sup>-\<^sup>1[?f \<star>\<^sub>B d ?a]"
            using \<mu> B.assoc_naturality [of "d ?b" "e ?b" "\<mu> \<star>\<^sub>B d ?a"] B.comp_assoc by simp
          finally show ?thesis by simp
        qed
        also have "... = (d ?b \<star>\<^sub>B (E \<circ> P) \<mu>) \<cdot>\<^sub>B \<epsilon>\<^sub>1 ?f"
          using \<mu> counit\<^sub>1_def P_def emb.map_def arr_char P\<^sub>0_props(1) P_simps\<^sub>B(1)
          by (simp add: P\<^sub>0_props(6))
        finally show "\<epsilon>\<^sub>1 (?g) \<cdot>\<^sub>B (I\<^sub>C.map \<mu> \<star>\<^sub>B d ?a) = (d ?b \<star>\<^sub>B (E \<circ> P) \<mu>) \<cdot>\<^sub>B \<epsilon>\<^sub>1 ?f"
          by blast
      qed
      show "\<And>f g. \<lbrakk>B.ide f; B.ide g; src\<^sub>B g = trg\<^sub>B f\<rbrakk> \<Longrightarrow>
                    (d (trg\<^sub>B g) \<star>\<^sub>B EoP.cmp (g, f)) \<cdot>\<^sub>B
                    \<a>\<^sub>B[d (trg\<^sub>B g), (E \<circ> P) g, (E \<circ> P) f] \<cdot>\<^sub>B
                    (\<epsilon>\<^sub>1 g \<star>\<^sub>B (E \<circ> P) f) \<cdot>\<^sub>B
                    B.inv \<a>\<^sub>B[I\<^sub>C.map g, d (src\<^sub>B g), (E \<circ> P) f] \<cdot>\<^sub>B (I\<^sub>C.map g \<star>\<^sub>B \<epsilon>\<^sub>1 f) \<cdot>\<^sub>B
                    \<a>\<^sub>B[I\<^sub>C.map g, I\<^sub>C.map f, d (src\<^sub>B f)]
                      = \<epsilon>\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>B (I\<^sub>C.cmp (g, f) \<star>\<^sub>B d (src\<^sub>B f))"
      proof -
        fix f g
        assume f: "B.ide f" and g: "B.ide g" and fg: "src\<^sub>B g = trg\<^sub>B f"
        let ?a = "src\<^sub>B f"
        let ?b = "src\<^sub>B g"
        let ?c = "trg\<^sub>B g"
        have "(d ?c \<star>\<^sub>B EoP.cmp (g, f)) \<cdot>\<^sub>B
              \<a>\<^sub>B[d ?c, (E \<circ> P) g, (E \<circ> P) f] \<cdot>\<^sub>B
              (\<epsilon>\<^sub>1 g \<star>\<^sub>B (E \<circ> P) f) \<cdot>\<^sub>B
              B.inv \<a>\<^sub>B[I\<^sub>C.map g, d ?b, (E \<circ> P) f] \<cdot>\<^sub>B
              (I\<^sub>C.map g \<star>\<^sub>B \<epsilon>\<^sub>1 f) \<cdot>\<^sub>B
              \<a>\<^sub>B[I\<^sub>C.map g, I\<^sub>C.map f, d ?a]
                = (d ?c \<star>\<^sub>B P (g \<star>\<^sub>B f) \<cdot>\<^sub>B CMP.map (g, f) \<cdot>\<^sub>B (P g \<star>\<^sub>B P f)) \<cdot>\<^sub>B
                  \<a>\<^sub>B[d ?c, P g, P f] \<cdot>\<^sub>B
                  (\<epsilon>\<^sub>1 g \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] \<cdot>\<^sub>B
                  (g \<star>\<^sub>B \<epsilon>\<^sub>1 f) \<cdot>\<^sub>B
                  \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "src\<^sub>B (e ?c \<star>\<^sub>B g \<star>\<^sub>B d ?b) = trg\<^sub>B (e ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)"
            using f g fg src_def trg_def arr_char P_simps\<^sub>B(1)
            by (simp add: P\<^sub>0_props(1,6) arr_char)
          moreover have "B.inv \<a>\<^sub>B[g, d ?b, P f] = \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f]"
            using f g fg by (simp add: P_def)
          ultimately show ?thesis
            using f g fg emb.map_def P.preserves_reflects_arr P.preserves_reflects_arr
                  P.preserves_reflects_arr \<Phi>\<^sub>P_def emb.cmp_def
                  EoP.cmp_def B.VV.arr_char B.VV.dom_char VV.arr_char
            by simp
        qed
        also have "... = (d ?c \<star>\<^sub>B CMP.map (g, f)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, P g, P f] \<cdot>\<^sub>B
                         ((\<epsilon>\<^sub>1 g \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         \<a>\<^sub>B\<^sup>-\<^sup>1[g, d ?b, P f] \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<epsilon>\<^sub>1 f)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "\<guillemotleft>CMP.map (g, f) : P g \<star> P f \<Rightarrow> P (g \<star>\<^sub>B f)\<guillemotright>"
            using f g fg VV.arr_char VV.cod_char P.FF_def \<Phi>\<^sub>P_def \<Phi>\<^sub>P_in_hom(2) by auto
          hence "\<guillemotleft>CMP.map (g, f) : P g \<star>\<^sub>B P f \<Rightarrow>\<^sub>B P (g \<star>\<^sub>B f)\<guillemotright>"
            using in_hom_char hcomp_char by auto
          hence "P (g \<star>\<^sub>B f) \<cdot>\<^sub>B CMP.map (g, f) \<cdot>\<^sub>B (P g \<star>\<^sub>B P f) = CMP.map (g, f)"
            using B.comp_arr_dom B.comp_cod_arr by auto
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = (d ?c \<star>\<^sub>B CMP.map (g, f)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, P g, P f] \<cdot>\<^sub>B
                         (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
          using f g fg technical B.comp_assoc by simp
        also have "... = (d ?c \<star>\<^sub>B (e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         (e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f] \<cdot>\<^sub>B
                         \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                         (\<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, P g, P f] \<cdot>\<^sub>B
                         (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
          using f g fg CMP.map_simp_ide CMP_def B.VV.ide_char B.VV.arr_char
                B.whisker_left B.whisker_left B.comp_assoc
          by simp
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         ((d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, P g, P f] \<cdot>\<^sub>B
                         (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a])) \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
          using f g fg B.whisker_left P_def B.comp_assoc by simp (* 11 sec *)
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         ((d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "(d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                (d ?c \<star>\<^sub>B \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f]) \<cdot>\<^sub>B
                (d ?c \<star>\<^sub>B \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f]) \<cdot>\<^sub>B
                (d ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                \<a>\<^sub>B[d ?c, P g, P f] \<cdot>\<^sub>B
                (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a])
                  = \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                    \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a]"
          proof -
            have "(d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[d ?b, e ?b, f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                  (d ?c \<star>\<^sub>B \<a>\<^sub>B[e ?c, g, d ?b \<star>\<^sub>B P f]) \<cdot>\<^sub>B
                  (d ?c \<star>\<^sub>B \<a>\<^sub>B[e ?c \<star>\<^sub>B g, d ?b, P f]) \<cdot>\<^sub>B
                  (d ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  \<a>\<^sub>B[d ?c, P g, P f] \<cdot>\<^sub>B
                  (\<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, d ?b] \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  \<a>\<^sub>B\<^sup>-\<^sup>1[(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g, d ?b, P f] \<cdot>\<^sub>B
                  (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B d ?b \<star>\<^sub>B P f) \<cdot>\<^sub>B
                  (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B \<a>\<^sub>B[d ?b, e ?b, f \<star>\<^sub>B d ?a])
                    = \<lbrace>(\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       (\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J f\<^bold>]) \<^bold>\<cdot>
                       (\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>P\<^bold>R\<^bold>J f\<^bold>]) \<^bold>\<cdot>
                       (\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J f) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[\<^bold>\<langle>d ?c\<^bold>\<rangle>, \<^bold>P\<^bold>R\<^bold>J g, \<^bold>P\<^bold>R\<^bold>J f\<^bold>] \<^bold>\<cdot>
                       (\<^bold>\<a>\<^bold>[\<^bold>\<langle>d ?c\<^bold>\<rangle>, \<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J f) \<^bold>\<cdot>
                       (\<^bold>\<a>\<^bold>[\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J f) \<^bold>\<cdot>
                       \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[(\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?c\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>P\<^bold>R\<^bold>J f\<^bold>] \<^bold>\<cdot>
                       (((\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?c\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>P\<^bold>R\<^bold>J f) \<^bold>\<cdot>
                       (((\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?c\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle>) \<^bold>\<star>
                             \<^bold>\<a>\<^bold>[\<^bold>\<langle>d ?b\<^bold>\<rangle>, \<^bold>\<langle>e ?b\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>])\<rbrace>"
              using f g fg B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                    B.VV.ide_char B.VV.arr_char P_def B.\<ll>_ide_simp
              by auto
            also have "... = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>d ?c\<^bold>\<rangle>, \<^bold>\<langle>e ?c\<^bold>\<rangle>,
                                \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                              \<^bold>\<a>\<^bold>[\<^bold>\<langle>d ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?c\<^bold>\<rangle>, \<^bold>\<langle>g\<^bold>\<rangle>,
                                (\<^bold>\<langle>d ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>e ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using f g fg by (intro EV.eval_eqI, auto)
            also have "... = \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                             \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a]"
              using f g fg B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                    B.VV.ide_char B.VV.arr_char P_def B.\<ll>_ide_simp
              by auto
            finally show ?thesis by blast
          qed
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "(d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a] =
                  \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                  ((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a)"
            using f g fg
                  B.assoc_naturality
                    [of "d ?c" "e ?c" "g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a"]
            by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         ((((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, (d ?b \<star>\<^sub>B e ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a] =
                  \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                  (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a)"
            using f g fg
                  B.assoc_naturality
                    [of "d ?c \<star>\<^sub>B e ?c" g "B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a"]
            by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "(((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)
                  = (\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"
          proof -
            have "(((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<star>\<^sub>B B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                  ((\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)
                    = ((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g) \<cdot>\<^sub>B (\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B
                      (B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)"
              using f g fg
                    B.interchange [of "(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g" "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]"
                                      "B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a"
                                      "\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"]
              by fastforce
            also have "... = (\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B
                               (B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)"
              using f g fg B.comp_cod_arr [of "(\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g]" "(d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g"]
              by (auto simp add: B.iso_is_arr)
            also have "... = (\<eta> ?c \<star>\<^sub>B g) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"
            proof -
              have "(B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)
                      = B.inv (\<eta> ?b) \<cdot>\<^sub>B \<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"
              proof -
                have "B.seq (B.inv (\<eta> ?b)) (\<eta> ?b)"
                  using f g fg chosen_adjoint_equivalence(5) by fastforce
                thus ?thesis
                  using f g fg B.whisker_right by simp
              qed
              also have "... = ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"
                using f g fg chosen_adjoint_equivalence(5) B.comp_inv_arr' by simp
              finally have "(B.inv (\<eta> ?b) \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (\<eta> ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)
                              = ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"
                by blast
              thus ?thesis
                using B.comp_assoc by simp
            qed
            finally show ?thesis by simp
          qed
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<a>\<^sub>B[d ?c \<star>\<^sub>B e ?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         ((\<eta> ?c \<star>\<^sub>B g) \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
          using f g fg B.comp_assoc
                B.whisker_right [of "?b \<star>\<^sub>B f \<star>\<^sub>B d ?a" "\<eta> ?c \<star>\<^sub>B g" "\<l>\<^sub>B\<^sup>-\<^sup>1[g]"]
            by fastforce
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         ((d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
          using f g fg B.iso_is_arr B.comp_assoc
                B.assoc_naturality [of "\<eta> ?c" g "?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"]
          by simp
        also have "... = (d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
         proof -
          have "(d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] =
                  \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                  ((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a])"
            using f g fg B.iso_is_arr
                  B.assoc_naturality [of "d ?c" "e ?c" "g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]"]
            by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = ((d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a)
                   = (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a])"
            using f g fg B.comp_arr_dom B.comp_cod_arr B.iso_is_arr
                  B.interchange [of "d ?c \<star>\<^sub>B e ?c" "\<eta> ?c"
                                    "g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]" "g \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a"]
                  B.interchange [of "\<eta> ?c" ?c
                                    "g \<star>\<^sub>B f \<star>\<^sub>B d ?a" "g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]"]
            by auto
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>B[d ?c, e ?c, (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B f \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         (?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "(d ?c \<star>\<^sub>B e ?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                \<a>\<^sub>B[d ?c, e ?c, g \<star>\<^sub>B f \<star>\<^sub>B d ?a] =
                  \<a>\<^sub>B[d ?c, e ?c, (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                  ((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a])"
            using f g fg B.assoc_naturality [of "d ?c" "e ?c" "\<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]"] by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>B[d ?c, e ?c, (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<eta> ?c \<star>\<^sub>B (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                         (?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                         \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                         (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                         (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                         \<a>\<^sub>B[g, f, d ?a]"
        proof -
          have "((d ?c \<star>\<^sub>B e ?c) \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B (\<eta> ?c \<star>\<^sub>B g \<star>\<^sub>B f \<star>\<^sub>B d ?a)
                  = (\<eta> ?c \<star>\<^sub>B (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B (?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a])"
            using f g fg B.comp_arr_dom B.comp_cod_arr B.iso_is_arr
                  B.interchange [of "d ?c \<star>\<^sub>B e ?c" "\<eta> ?c" "\<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]" "g \<star>\<^sub>B f \<star>\<^sub>B d ?a"]
                  B.interchange [of "\<eta> ?c" ?c "(g \<star>\<^sub>B f) \<star>\<^sub>B d ?a" "\<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]"]
            by auto
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = \<epsilon>\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>B (I\<^sub>C.cmp (g, f) \<star>\<^sub>B d ?a)"
        proof -
          have "\<epsilon>\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>B (I\<^sub>C.cmp (g, f) \<star>\<^sub>B d ?a)
                  = \<a>\<^sub>B[d ?c, e ?c, (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                    (\<eta> ?c \<star>\<^sub>B (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                    \<l>\<^sub>B\<^sup>-\<^sup>1[(g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B d ?a)"
            using f g fg counit\<^sub>1_def B.comp_assoc by simp
          also have "... = \<a>\<^sub>B[d ?c, e ?c, (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                           (\<eta> ?c \<star>\<^sub>B (g \<star>\<^sub>B f) \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           (?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                           (?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                           \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                           (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                           (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                           \<a>\<^sub>B[g, f, d ?a]"
          proof -
            have "\<l>\<^sub>B\<^sup>-\<^sup>1[(g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B d ?a)
                    = (?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                      (?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                      \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                      (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                      (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                      \<a>\<^sub>B[g, f, d ?a]"
            proof -
              have "\<l>\<^sub>B\<^sup>-\<^sup>1[(g \<star>\<^sub>B f) \<star>\<^sub>B d ?a] \<cdot>\<^sub>B ((g \<star>\<^sub>B f) \<star>\<^sub>B d ?a) =
                      \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[(\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> ((\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>)\<rbrace>"
                using f g fg B.\<ll>_ide_simp by auto
              also have "... = \<lbrace>(\<^bold>\<langle>?c\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                                (\<^bold>\<langle>?c\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<l>\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                                \<^bold>\<a>\<^bold>[\<^bold>\<langle>?c\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                                (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                                (\<^bold>\<langle>g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>d ?a\<^bold>\<rangle>)) \<^bold>\<cdot>
                                \<^bold>\<a>\<^bold>[\<^bold>\<langle>g\<^bold>\<rangle>, \<^bold>\<langle>f\<^bold>\<rangle>, \<^bold>\<langle>d ?a\<^bold>\<rangle>\<^bold>]\<rbrace>"
                using f g fg by (intro EV.eval_eqI, auto)
              also have "... = (?c \<star>\<^sub>B \<a>\<^sub>B\<^sup>-\<^sup>1[g, f, d ?a]) \<cdot>\<^sub>B
                               (?c \<star>\<^sub>B g \<star>\<^sub>B \<l>\<^sub>B[f \<star>\<^sub>B d ?a]) \<cdot>\<^sub>B
                               \<a>\<^sub>B[?c, g, ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a] \<cdot>\<^sub>B
                               (\<l>\<^sub>B\<^sup>-\<^sup>1[g] \<star>\<^sub>B ?b \<star>\<^sub>B f \<star>\<^sub>B d ?a) \<cdot>\<^sub>B
                               (g \<star>\<^sub>B \<a>\<^sub>B[?b, f, d ?a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[f] \<star>\<^sub>B d ?a)) \<cdot>\<^sub>B
                               \<a>\<^sub>B[g, f, d ?a]"
                using f g fg B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                      B.VV.ide_char B.VV.arr_char P_def B.\<ll>_ide_simp
                by auto
              finally show ?thesis by blast
            qed
            thus ?thesis by simp
          qed
          finally show ?thesis by simp
        qed
        finally show "(d ?c \<star>\<^sub>B EoP.cmp (g, f)) \<cdot>\<^sub>B
                      \<a>\<^sub>B[d ?c, (E \<circ> P) g, (E \<circ> P) f] \<cdot>\<^sub>B
                      (\<epsilon>\<^sub>1 g \<star>\<^sub>B (E \<circ> P) f) \<cdot>\<^sub>B
                      B.inv \<a>\<^sub>B[I\<^sub>C.map g, d ?b, (E \<circ> P) f] \<cdot>\<^sub>B (I\<^sub>C.map g \<star>\<^sub>B \<epsilon>\<^sub>1 f) \<cdot>\<^sub>B
                      \<a>\<^sub>B[I\<^sub>C.map g, I\<^sub>C.map f, d ?a]
                        = \<epsilon>\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>B (I\<^sub>C.cmp (g, f) \<star>\<^sub>B d ?a)"
          by blast
      qed
      show "\<And>a. B.obj a \<Longrightarrow>
                  (d a \<star>\<^sub>B EoP.unit a) \<cdot>\<^sub>B \<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a] = \<epsilon>\<^sub>1 a \<cdot>\<^sub>B (I\<^sub>C.unit a \<star>\<^sub>B d a)"
      proof -
        fix a
        assume a: "B.obj a"
        interpret adjoint_equivalence_in_bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B \<open>e a\<close> \<open>d a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
          using a chosen_adjoint_equivalence by simp
        have 0: "src\<^sub>B a = a \<and> trg\<^sub>B a = a"
          using a by auto
        have 1: "obj (P\<^sub>0 a)"
          using a P\<^sub>0_props(1) by simp
        have "(d a \<star>\<^sub>B EoP.unit a) \<cdot>\<^sub>B \<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a]
                = (d a \<star>\<^sub>B ((e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B src\<^sub>B (a \<star>\<^sub>B d (src\<^sub>B a))) \<cdot>\<^sub>B
                  \<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a]"
        proof -
          have "B.hseq (e (trg\<^sub>B a)) (a \<star>\<^sub>B d (src\<^sub>B a))"
            using a by (elim B.objE, intro B.hseqI') auto
          moreover have "arr (src\<^sub>B (d (src\<^sub>B a)))"
            using a arr_char P\<^sub>0_props(1) obj_char B.obj_simps(1) by auto
          moreover have "arr (src\<^sub>B (a \<star>\<^sub>B d (src\<^sub>B a)))"
            using a arr_char P\<^sub>0_props(1) obj_char calculation(1) by fastforce
          moreover have "src\<^sub>B (a \<star>\<^sub>B d (src\<^sub>B a)) \<in> Obj \<and> trg\<^sub>B (e (trg\<^sub>B a)) \<in> Obj"
            using a B.obj_simps P\<^sub>0_props obj_char arr_char by simp
          moreover have "P\<^sub>0 a \<cdot>\<^sub>B P\<^sub>0 a \<in> Obj"
            using 1 arr_char P\<^sub>0_props(1) obj_char
            by (metis (no_types, lifting) B.cod_trg B.obj_def' B.trg.is_natural_2)
          moreover have "emb.unit (P\<^sub>0 (src\<^sub>B a)) = P\<^sub>0 (src\<^sub>B a)"
            using a 0 1 emb.unit_char' P.map\<^sub>0_def src_def by simp
          ultimately show ?thesis
            using a emb.map_def EoP.unit_char' prj_unit_char emb.unit_char' P.map\<^sub>0_def P_def
                  src_def arr_char obj_char
            by simp
        qed
        also have "... = (d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a) \<cdot>\<^sub>B P\<^sub>0 a) \<cdot>\<^sub>B
                         \<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a]"
          using a 1 B.comp_assoc B.obj_simps by auto
        also have "... = (d a \<star>\<^sub>B (e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B \<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a]"
          using a B.comp_arr_dom by simp
        also have "... = (d a \<star>\<^sub>B e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B (d a \<star>\<^sub>B B.inv (\<epsilon> a)) \<cdot>\<^sub>B \<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a]"
          using a B.whisker_left B.comp_assoc by simp
        also have "... = ((d a \<star>\<^sub>B e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B \<a>\<^sub>B[d a, e a, d a]) \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B d a)"
          using a triangle_right B.comp_assoc
                B.invert_side_of_triangle(1) [of "\<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a]" "d a \<star>\<^sub>B \<epsilon> a"]
          by simp
        also have "... = \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B ((d a \<star>\<^sub>B e a) \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B d a)"
        proof -
          have "(d a \<star>\<^sub>B e a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]) \<cdot>\<^sub>B \<a>\<^sub>B[d a, e a, d a] =
                \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B ((d a \<star>\<^sub>B e a) \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
            using a B.assoc_naturality [of "d a" "e a" "\<l>\<^sub>B\<^sup>-\<^sup>1[d a]"] by simp
          thus ?thesis
            using B.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
          using a B.interchange [of "d a \<star>\<^sub>B e a" "\<eta> a" "\<l>\<^sub>B\<^sup>-\<^sup>1[d a]" "d a"]
                B.comp_arr_dom B.comp_cod_arr
          by simp
        also have "... = \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B[a, a, d a] \<cdot>\<^sub>B
                         (\<l>\<^sub>B\<^sup>-\<^sup>1[a] \<star>\<^sub>B d a)"
        proof -
          have "\<a>\<^sub>B[a, a, d a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[a] \<star>\<^sub>B d a) = a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]"
          proof -
            (* TODO: I wanted to prove this directly, but missed some necessary trick. *)
            have "\<a>\<^sub>B[a, a, d a] \<cdot>\<^sub>B (\<l>\<^sub>B\<^sup>-\<^sup>1[a] \<star>\<^sub>B d a) = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0\<^bold>] \<^bold>\<star> \<^bold>\<langle>d a\<^bold>\<rangle>)\<rbrace>"
              using a ide_char B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                    B.VV.ide_char B.VV.arr_char P_def B.\<ll>_ide_simp
              by auto
            also have "... = \<lbrace>\<^bold>\<langle>a\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>d a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using a ide_char by (intro EV.eval_eqI, auto)
            also have "... = a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a]"
              using a ide_char B.\<alpha>_def B.\<alpha>'.map_ide_simp B.VVV.ide_char B.VVV.arr_char
                    B.VV.ide_char B.VV.arr_char P_def B.\<ll>_ide_simp
              by auto
            finally show ?thesis by blast
          qed
          hence "\<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B[a, a, d a] \<cdot>\<^sub>B
                 (\<l>\<^sub>B\<^sup>-\<^sup>1[a] \<star>\<^sub>B d a)
                   = \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B (a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
            by simp
          also have "... = \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[d a])"
            using a B.interchange [of "\<eta> a" a "a \<star>\<^sub>B d a" "\<l>\<^sub>B\<^sup>-\<^sup>1[d a]"] B.comp_arr_dom B.comp_cod_arr
            by simp
          finally show ?thesis by simp
        qed
        also have "... = \<epsilon>\<^sub>1 a \<cdot>\<^sub>B (I\<^sub>C.unit a \<star>\<^sub>B d a)"
        proof -
          have "\<epsilon>\<^sub>1 a \<cdot>\<^sub>B (I\<^sub>C.unit a \<star>\<^sub>B d a) =
                \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[a \<star>\<^sub>B d a] \<cdot>\<^sub>B (a \<star>\<^sub>B d a)"
            using a 0 counit\<^sub>1_def I\<^sub>C.unit_char' B.comp_assoc by simp
          also have "... = \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<l>\<^sub>B\<^sup>-\<^sup>1[a \<star>\<^sub>B d a]"
          proof -
            have "B.arr \<l>\<^sub>B\<^sup>-\<^sup>1[a \<star>\<^sub>B d a]"
              using a
              by (metis B.ide_hcomp B.lunit'_simps(1) B.objE equivalence_data_simps\<^sub>B(8) ide_right)
            moreover have "B.dom \<l>\<^sub>B\<^sup>-\<^sup>1[a \<star>\<^sub>B d a] = a \<star>\<^sub>B d a"
              using a
              by (metis B.ide_hcomp B.lunit'_simps(4) B.objE antipar(1) equivalence_data_simps\<^sub>B(5)
                  ide_right)
            ultimately show ?thesis
              using a B.comp_arr_dom [of "\<l>\<^sub>B\<^sup>-\<^sup>1[a \<star>\<^sub>B d a]" "a \<star>\<^sub>B d a"] by simp
          qed
          also have "... = \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B[a, a, d a] \<cdot>\<^sub>B
                           (\<l>\<^sub>B\<^sup>-\<^sup>1[a] \<star>\<^sub>B d a)"
            using a B.lunit_hcomp(4) [of a "d a"] by auto
          finally have "\<epsilon>\<^sub>1 a \<cdot>\<^sub>B (I\<^sub>C.unit a \<star>\<^sub>B d a) =
                        \<a>\<^sub>B[d a, e a, a \<star>\<^sub>B d a] \<cdot>\<^sub>B (\<eta> a \<star>\<^sub>B a \<star>\<^sub>B d a) \<cdot>\<^sub>B \<a>\<^sub>B[a, a, d a] \<cdot>\<^sub>B
                        (\<l>\<^sub>B\<^sup>-\<^sup>1[a] \<star>\<^sub>B d a)"
            by simp
          thus ?thesis by simp
        qed
        finally show "(d a \<star>\<^sub>B EoP.unit a) \<cdot>\<^sub>B \<r>\<^sub>B\<^sup>-\<^sup>1[d a] \<cdot>\<^sub>B \<l>\<^sub>B[d a] = \<epsilon>\<^sub>1 a \<cdot>\<^sub>B (I\<^sub>C.unit a \<star>\<^sub>B d a)"
          by blast
      qed
    qed

    sublocale equivalence_of_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B comp hcomp \<a> \<i>\<^sub>B src trg
                E \<Phi>\<^sub>E P \<Phi>\<^sub>P unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1
      ..

    lemma induces_equivalence:
    shows "equivalence_of_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B comp hcomp \<a> \<i>\<^sub>B src trg
             E \<Phi>\<^sub>E P \<Phi>\<^sub>P unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1"
      ..

  end

  subsection "Equivalence Pseudofunctors, Bijective on Objects"

  text \<open>
    Here we carry out the extension of an equivalence pseudofunctor \<open>F\<close> to an equivalence
    of bicategories in the special case that the object map of \<open>F\<close> is bijective.
    The bijectivity assumption simplifies the construction of the unit and counit of the
    equivalence (the components at objects are in fact identities), as well as the proofs
    of the associated coherence conditions.
  \<close>

  locale equivalence_pseudofunctor_bij_on_obj =
    equivalence_pseudofunctor +
  assumes bij_on_obj: "bij_betw map\<^sub>0 (Collect C.obj) (Collect D.obj)"
  begin

    abbreviation F\<^sub>0
    where "F\<^sub>0 \<equiv> map\<^sub>0"

    definition G\<^sub>0
    where "G\<^sub>0 = inv_into (Collect C.obj) F\<^sub>0"

    lemma G\<^sub>0_props:
    shows "D.obj b \<Longrightarrow> C.obj (G\<^sub>0 b) \<and> F\<^sub>0 (G\<^sub>0 b) = b"
    and "C.obj a \<Longrightarrow> D.obj (F\<^sub>0 a) \<and> G\<^sub>0 (F\<^sub>0 a) = a"
    proof -
      have surj: "F\<^sub>0 ` (Collect C.obj) = Collect D.obj"
        using bij_on_obj bij_betw_imp_surj_on by blast
      assume b: "D.obj b"
      show "C.obj (G\<^sub>0 b) \<and> F\<^sub>0 (G\<^sub>0 b) = b"
      proof
        show "C.obj (G\<^sub>0 b)"
          unfolding G\<^sub>0_def
          using b by (metis inv_into_into mem_Collect_eq surj)
        show "F\<^sub>0 (G\<^sub>0 b) = b"
          unfolding G\<^sub>0_def
          using b by (simp add: f_inv_into_f surj)
      qed
      next
      have bij: "bij_betw G\<^sub>0 (Collect D.obj) (Collect C.obj)"
        using bij_on_obj G\<^sub>0_def bij_betw_inv_into by auto
      have surj: "G\<^sub>0 ` (Collect D.obj) = Collect C.obj"
        using bij_on_obj G\<^sub>0_def
        by (metis bij_betw_def bij_betw_inv_into)
      assume a: "C.obj a"
      show "D.obj (F\<^sub>0 a) \<and> G\<^sub>0 (F\<^sub>0 a) = a"
        using a bij surj G\<^sub>0_def bij_betw_imp_inj_on bij_on_obj by force
    qed

    text \<open>
      We extend \<open>G\<^sub>0\<close> to all arrows of \<open>D\<close> using chosen adjoint equivalences, which extend \<open>F\<close>,
      between \<open>hom\<^sub>C (a, a')\<close> and \<open>hom\<^sub>D (F a, F a')\<close>.  The use of adjoint equivalences restricts
      choices that prevent us from validating the necessary coherence conditions.
    \<close>

    definition G
    where "G \<nu> = (if D.arr \<nu> then
                     equivalence_pseudofunctor_at_hom.G\<^sub>1 V\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D src\<^sub>D trg\<^sub>D F
                       (G\<^sub>0 (src\<^sub>D \<nu>)) (G\<^sub>0 (trg\<^sub>D \<nu>)) \<nu>
                  else C.null)"

    lemma G_in_hom [intro]:
    assumes "D.arr \<nu>"
    shows "\<guillemotleft>G \<nu> : G\<^sub>0 (src\<^sub>D \<nu>) \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<nu>)\<guillemotright>"
    and "\<guillemotleft>G \<nu> : G (D.dom \<nu>) \<Rightarrow>\<^sub>C G (D.cod \<nu>)\<guillemotright>"
    proof -
      have 1: "src\<^sub>D \<nu> = F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<and> trg\<^sub>D \<nu> = F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))"
        using assms G\<^sub>0_props by simp
      interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : G\<^sub>0 (src\<^sub>D \<nu>) \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<nu>)\<guillemotright>\<close>
        using assms C.hhom_is_subcategory by simp
      interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))\<guillemotright>\<close>
        using assms 1 D.in_hhom_def D.hhom_is_subcategory by simp
      interpret Faa': equivalence_pseudofunctor_at_hom
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>G\<^sub>0 (src\<^sub>D \<nu>)\<close> \<open>G\<^sub>0 (trg\<^sub>D \<nu>)\<close>
        using assms G\<^sub>0_props(1) by unfold_locales auto
      have 2: "hom\<^sub>D.arr \<nu>"
        using assms 1 hom\<^sub>D.arr_char by simp
      show "\<guillemotleft>G \<nu> : G (D.dom \<nu>) \<Rightarrow>\<^sub>C G (D.cod \<nu>)\<guillemotright>"
        unfolding G_def
        using assms 2 hom\<^sub>C.arr_char hom\<^sub>C.dom_char hom\<^sub>C.cod_char hom\<^sub>D.dom_char hom\<^sub>D.cod_char
              Faa'.\<eta>\<epsilon>.F.preserves_arr Faa'.\<eta>\<epsilon>.F.preserves_dom Faa'.\<eta>\<epsilon>.F.preserves_cod
        by (intro C.in_homI) auto
      thus "C.in_hhom (G \<nu>) (G\<^sub>0 (src\<^sub>D \<nu>)) (G\<^sub>0 (trg\<^sub>D \<nu>))"
      proof -
        have "hom\<^sub>C.arr (Faa'.G\<^sub>1 \<nu>)"
          using 2 by simp
        thus ?thesis
          using G_def assms hom\<^sub>C.arrE by presburger
      qed
    qed

    lemma G_simps [simp]:
    assumes "D.arr \<nu>"
    shows "C.arr (G \<nu>)"
    and "src\<^sub>C (G \<nu>) = G\<^sub>0 (src\<^sub>D \<nu>)" and "trg\<^sub>C (G \<nu>) = G\<^sub>0 (trg\<^sub>D \<nu>)"
    and "C.dom (G \<nu>) = G (D.dom \<nu>)" and "C.cod (G \<nu>) = G (D.cod \<nu>)"
      using assms G_in_hom by auto

    interpretation G: "functor" V\<^sub>D V\<^sub>C G
    proof
      show "\<And>f. \<not> D.arr f \<Longrightarrow> G f = C.null"
        unfolding G_def by simp
      fix \<nu>
      assume \<nu>: "D.arr \<nu>"
      show "C.arr (G \<nu>)"
        using \<nu> by simp
      show "C.dom (G \<nu>) = G (D.dom \<nu>)"
        using \<nu> by simp
      show "C.cod (G \<nu>) = G (D.cod \<nu>)"
        using \<nu> by simp
      next
      fix \<mu> \<nu>
      assume \<mu>\<nu>: "D.seq \<mu> \<nu>"
      have 1: "D.arr \<mu> \<and> D.arr \<nu> \<and> src\<^sub>D \<mu> = src\<^sub>D \<nu> \<and> trg\<^sub>D \<mu> = trg\<^sub>D \<nu> \<and>
               src\<^sub>D \<mu> = F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<mu>)) \<and> trg\<^sub>D \<mu> = F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<mu>)) \<and>
               src\<^sub>D \<nu> = F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<and> trg\<^sub>D \<nu> = F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))"
        using \<mu>\<nu> G\<^sub>0_props D.vseq_implies_hpar by auto
      interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : G\<^sub>0 (src\<^sub>D \<nu>) \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<nu>)\<guillemotright>\<close>
        using 1 C.hhom_is_subcategory by simp
      interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))\<guillemotright>\<close>
        using 1 D.hhom_is_subcategory
        by (simp add: D.in_hhom_def subcategory_axioms_def subcategory_def)
      interpret hom\<^sub>D': subcategory V\<^sub>D
                         \<open>\<lambda>\<nu>'. D.arr \<nu>' \<and> src\<^sub>D \<nu>' = src\<^sub>D \<nu> \<and> trg\<^sub>D \<nu>' = trg\<^sub>D \<nu>\<close>
        using 1 D.hhom_is_subcategory
        by (simp add: D.in_hhom_def subcategory_axioms_def subcategory_def)
      interpret Faa': equivalence_pseudofunctor_at_hom
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>G\<^sub>0 (src\<^sub>D \<nu>)\<close> \<open>G\<^sub>0 (trg\<^sub>D \<nu>)\<close>
        using \<mu>\<nu> 1 G\<^sub>0_props(1) by unfold_locales auto
      have 2: "hom\<^sub>D.seq \<mu> \<nu>"
        using \<mu>\<nu> 1 hom\<^sub>D.arr_char hom\<^sub>D.comp_def by fastforce
      have "G (hom\<^sub>D.comp \<mu> \<nu>) = hom\<^sub>C.comp (G \<mu>) (G \<nu>)"
        unfolding G_def
        using 1 2 G\<^sub>0_props Faa'.G\<^sub>1_props hom\<^sub>D.arr_char Faa'.\<eta>\<epsilon>.F.preserves_comp_2 by auto
      thus "G (\<mu> \<cdot>\<^sub>D \<nu>) = G \<mu> \<cdot>\<^sub>C G \<nu>"
        using \<mu>\<nu> 1 2 G_def hom\<^sub>C.comp_simp hom\<^sub>D.comp_simp D.src_vcomp D.trg_vcomp
              Faa'.\<eta>\<epsilon>.F.preserves_arr
        by metis
    qed

    lemma functor_G:
    shows "functor V\<^sub>D V\<^sub>C G"
      ..

    interpretation G: faithful_functor V\<^sub>D V\<^sub>C G
    proof
      fix f f'
      assume par: "D.par f f'"
      assume eq: "G f = G f'"
      have 1: "src\<^sub>D f = src\<^sub>D f' \<and> trg\<^sub>D f = trg\<^sub>D f'"
        using par D.src_dom D.trg_dom by fastforce
      interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : G\<^sub>0 (src\<^sub>D f) \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D f)\<guillemotright>\<close>
        using par C.hhom_is_subcategory by simp
      interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (G\<^sub>0 (src\<^sub>D f)) \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 (trg\<^sub>D f))\<guillemotright>\<close>
        using par D.hhom_is_subcategory
        by (simp add: D.in_hhom_def subcategory_axioms_def subcategory_def)
      interpret F: equivalence_pseudofunctor_at_hom
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>G\<^sub>0 (src\<^sub>D f)\<close> \<open>G\<^sub>0 (trg\<^sub>D f)\<close>
        using par G\<^sub>0_props(1) by unfold_locales auto
      interpret F': equivalence_pseudofunctor_at_hom
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>G\<^sub>0 (src\<^sub>D f')\<close> \<open>G\<^sub>0 (trg\<^sub>D f')\<close>
        using par G\<^sub>0_props(1) by unfold_locales auto
      have 2: "hom\<^sub>D.par f f'"
        using par 1 hom\<^sub>D.arr_char hom\<^sub>D.dom_char hom\<^sub>D.cod_char G\<^sub>0_props by simp
      have "F.G\<^sub>1 f = F.G\<^sub>1 f'"
        using par eq G_def G_simps(2-3) by metis
      thus "f = f'"
        using F.\<eta>\<epsilon>.F_is_faithful
        by (simp add: 2 faithful_functor_axioms_def faithful_functor_def)
    qed

    interpretation FG: composite_functor V\<^sub>D V\<^sub>C V\<^sub>D G F ..
    interpretation FG: faithful_functor V\<^sub>D V\<^sub>D "F o G"
      using faithful_functor_axioms G.faithful_functor_axioms faithful_functors_compose
      by blast

    interpretation GF: composite_functor V\<^sub>C V\<^sub>D V\<^sub>C F G ..
    interpretation GF: faithful_functor V\<^sub>C V\<^sub>C "G o F"
      using faithful_functor_axioms G.faithful_functor_axioms faithful_functors_compose
      by blast

    interpretation G: weak_arrow_of_homs V\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C src\<^sub>C trg\<^sub>C G
    proof
      have *: "\<And>b. D.obj b \<Longrightarrow> C.isomorphic (G b) (src\<^sub>C (G b))"
      proof -
        fix b
        assume b: "D.obj b"
        interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : G\<^sub>0 b \<rightarrow>\<^sub>C G\<^sub>0 b\<guillemotright>\<close>
          using b C.hhom_is_subcategory by simp
        interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (G\<^sub>0 b) \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 b)\<guillemotright>\<close>
          using b D.hhom_is_subcategory
          by (simp add: D.in_hhom_def subcategory_axioms_def subcategory_def)
        interpret Faa': equivalence_pseudofunctor_at_hom
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          F \<Phi> \<open>G\<^sub>0 b\<close> \<open>G\<^sub>0 b\<close>
          using b G\<^sub>0_props(1) by unfold_locales auto
        have 1: "C.in_hhom (G\<^sub>0 b) (G\<^sub>0 b) (G\<^sub>0 b)"
          using b G\<^sub>0_props by force

        text \<open>
          Using the unit constraints of \<open>F\<close> and the fact that \<open>F\<^sub>0 (G\<^sub>0 b) = b\<close>,
          we obtain an isomorphism \<open>\<guillemotleft>?\<psi> : b \<Rightarrow>\<^sub>D F (G\<^sub>0 b)\<guillemotright>\<close>, which is also
          an isomorphism in \<open>hom\<^sub>D\<close>.
        \<close>

        let ?\<psi> = "unit (G\<^sub>0 b)"
        have \<psi>: "\<guillemotleft>?\<psi> : b \<Rightarrow>\<^sub>D F (G\<^sub>0 b)\<guillemotright> \<and> D.iso ?\<psi>"
          using b G\<^sub>0_props unit_char by auto
        have \<psi>_in_hhom: "D.in_hhom ?\<psi> b b"
          using b \<psi> 1 D.src_dom D.trg_dom by fastforce
        have 2: "hom\<^sub>D.arr ?\<psi> \<and> hom\<^sub>D.arr (D.inv ?\<psi>)"
        proof -
          have "D.in_hhom ?\<psi> (F\<^sub>0 (G\<^sub>0 b)) (F\<^sub>0 (G\<^sub>0 b))"
            using b \<psi>_in_hhom G\<^sub>0_props by simp
          thus ?thesis
            using \<psi> by auto
        qed
        have \<psi>': "hom\<^sub>D.in_hom ?\<psi> b (Faa'.F\<^sub>1 (G\<^sub>0 b))"
        proof
          show "hom\<^sub>D.arr ?\<psi>"
            using 2 by simp
          show "hom\<^sub>D.dom ?\<psi> = b"
            using 2 \<psi> hom\<^sub>D.dom_char by auto
          show "hom\<^sub>D.cod ?\<psi> = Faa'.F\<^sub>1 (G\<^sub>0 b)"
          proof -
            have "\<guillemotleft>?\<psi> : b \<Rightarrow>\<^sub>D Faa'.F\<^sub>1 (G\<^sub>0 b)\<guillemotright> \<and> D.iso ?\<psi>"
              unfolding Faa'.F\<^sub>1_def using b \<psi> 1 G\<^sub>0_props by auto
            thus ?thesis
              using 2 \<psi> hom\<^sub>D.cod_char by auto
          qed
        qed

        text \<open>
          Transposing \<open>?\<psi>\<close> via the adjunction \<open>\<eta>\<epsilon>\<close> yields an isomorphism from
          \<open>G b\<close> to \<open>G\<^sub>0 b\<close> in \<open>hom\<^sub>C\<close>, hence in \<open>C\<close>.
        \<close>

        have **: "hom\<^sub>C.isomorphic (G b) (G\<^sub>0 b)"
        proof -
          have "hom\<^sub>C.in_hom (Faa'.\<eta>\<epsilon>.\<psi> (G\<^sub>0 b) ?\<psi>) (Faa'.G\<^sub>1 b) (G\<^sub>0 b)"
          proof -
            have "hom\<^sub>D.in_hom ?\<psi> b (Faa'.F\<^sub>1 (G\<^sub>0 b))"
              using \<psi>' by simp
            moreover have "hom\<^sub>C.ide (G\<^sub>0 b)"
              using b 1 hom\<^sub>C.ide_char G\<^sub>0_props hom\<^sub>C.arr_char by auto
            ultimately show ?thesis
              using \<psi> Faa'.\<eta>\<epsilon>.\<psi>_in_hom hom\<^sub>D.in_hom_char hom\<^sub>D.arr_char by simp
          qed
          moreover have "hom\<^sub>C.iso (Faa'.\<eta>\<epsilon>.\<psi> (G\<^sub>0 b) ?\<psi>)"
          proof (unfold Faa'.\<eta>\<epsilon>.\<psi>_def)
            have "hom\<^sub>C.iso_in_hom (hom\<^sub>C.comp (Faa'.\<epsilon> (G\<^sub>0 b))
                    (Faa'.G\<^sub>1 ?\<psi>)) (Faa'.G\<^sub>1 b) (G\<^sub>0 b)"
            proof (intro hom\<^sub>C.comp_iso_in_hom)
              show "hom\<^sub>C.iso_in_hom (Faa'.G\<^sub>1 (unit (G\<^sub>0 b)))
                      (Faa'.G\<^sub>1 b) (Faa'.\<eta>\<epsilon>.FG.map (G\<^sub>0 b))"
                using \<psi> \<psi>' 1 2 hom\<^sub>D.iso_char Faa'.\<eta>\<epsilon>.F.preserves_iso hom\<^sub>D.iso_char
                      Faa'.\<eta>\<epsilon>.F.preserves_iso hom\<^sub>C.in_hom_char hom\<^sub>C.arr_char
                by auto
              show "hom\<^sub>C.iso_in_hom (Faa'.\<epsilon> (G\<^sub>0 b)) (Faa'.\<eta>\<epsilon>.FG.map (G\<^sub>0 b)) (G\<^sub>0 b)"
              proof
                show "hom\<^sub>C.iso (Faa'.\<epsilon> (G\<^sub>0 b))"
                proof -
                  have "hom\<^sub>C.ide (G\<^sub>0 b)"
                    using b 1 G\<^sub>0_props hom\<^sub>C.ide_char hom\<^sub>C.arr_char by auto
                  thus ?thesis
                    using b G\<^sub>0_props Faa'.\<eta>\<epsilon>.\<epsilon>.components_are_iso by simp
                qed
                show "hom\<^sub>C.in_hom (Faa'.\<epsilon> (G\<^sub>0 b)) (Faa'.\<eta>\<epsilon>.FG.map (G\<^sub>0 b)) (G\<^sub>0 b)"
                  using \<psi> \<psi>' 1
                  by (metis C.ide_src C.in_hhom_def Faa'.\<eta>\<epsilon>.\<epsilon>.preserves_hom hom\<^sub>C.arrI
                      hom\<^sub>C.ideI hom\<^sub>C.ide_in_hom hom\<^sub>C.map_simp)
              qed
            qed
            thus "hom\<^sub>C.iso (hom\<^sub>C.comp (Faa'.\<epsilon> (G\<^sub>0 b)) (Faa'.G\<^sub>1 (unit (G\<^sub>0 b))))" by auto
          qed
          ultimately show ?thesis
            unfolding G_def
            using b hom\<^sub>C.isomorphic_def D.obj_def D.obj_simps(3) by auto
        qed
        hence "hom\<^sub>C.isomorphic (G b) (src\<^sub>C (G b))"
          using b G_in_hom(1) by auto
        moreover have "\<And>f g. hom\<^sub>C.isomorphic f g \<Longrightarrow> C.isomorphic f g"
          using hom\<^sub>C.iso_char hom\<^sub>C.isomorphic_def C.isomorphic_def hom\<^sub>C.in_hom_char hom\<^sub>C.arr_char
          by auto
        ultimately show "C.isomorphic (G b) (src\<^sub>C (G b))"
          by simp
      qed
      fix \<nu>
      assume \<nu>: "D.arr \<nu>"
      show "C.isomorphic (G (src\<^sub>D \<nu>)) (src\<^sub>C (G \<nu>))"
        using \<nu> * by force
      show "C.isomorphic (G (trg\<^sub>D \<nu>)) (trg\<^sub>C (G \<nu>))"
        using \<nu> * by force
    qed

    lemma weak_arrow_of_homs_G:
    shows "weak_arrow_of_homs V\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C src\<^sub>C trg\<^sub>C G"
      ..

    sublocale H\<^sub>DoGG: composite_functor D.VV.comp C.VV.comp V\<^sub>C
                       G.FF \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>C snd \<mu>\<nu>\<close>
      ..
    sublocale GoH\<^sub>D: composite_functor D.VV.comp V\<^sub>D V\<^sub>C \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D snd \<mu>\<nu>\<close> G
      ..

    text \<open>
      To get the unit \<open>\<eta>\<close> of the equivalence of bicategories, we piece together the
      units from the local equivalences.  The components at objects will in fact be identities.
    \<close>

    definition \<eta>
    where "\<eta> \<nu> = (if D.arr \<nu> then
                    equivalence_pseudofunctor_at_hom.\<eta> V\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D src\<^sub>D trg\<^sub>D F
                      (G\<^sub>0 (src\<^sub>D \<nu>)) (G\<^sub>0 (trg\<^sub>D \<nu>)) \<nu>
                  else D.null)"

    lemma \<eta>_in_hom:
    assumes "D.arr \<nu>"
    shows [intro]: "\<guillemotleft>\<eta> \<nu> : src\<^sub>D \<nu> \<rightarrow>\<^sub>D trg\<^sub>D \<nu>\<guillemotright>"
    and [intro]: "\<guillemotleft>\<eta> \<nu> : D.dom \<nu> \<Rightarrow>\<^sub>D F (G (D.cod \<nu>))\<guillemotright>"
    and "D.ide \<nu> \<Longrightarrow> D.iso (\<eta> \<nu>)"
    proof -
      interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : G\<^sub>0 (src\<^sub>D \<nu>) \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<nu>)\<guillemotright>\<close>
        using assms C.hhom_is_subcategory by simp
      interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))\<guillemotright>\<close>
        using assms D.hhom_is_subcategory
        by (simp add: D.in_hhom_def subcategory_axioms_def subcategory_def)
      interpret Faa': equivalence_pseudofunctor_at_hom V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>G\<^sub>0 (src\<^sub>D \<nu>)\<close> \<open>G\<^sub>0 (trg\<^sub>D \<nu>)\<close>
        using assms G\<^sub>0_props(1) by unfold_locales auto
      have 1: "\<guillemotleft>\<eta> \<nu> : D.dom \<nu> \<Rightarrow>\<^sub>D F (G (D.cod \<nu>))\<guillemotright> \<and> (D.ide \<nu> \<longrightarrow> D.iso (\<eta> \<nu>))"
      proof -
        have "src\<^sub>D \<nu> = F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<and> trg\<^sub>D \<nu> = F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))"
          using assms G\<^sub>0_props by simp
        hence "hom\<^sub>D.arr \<nu>"
          using assms hom\<^sub>D.arr_char hom\<^sub>D.ide_char by simp
        hence "hom\<^sub>D.in_hom (Faa'.\<eta> \<nu>) (D.dom \<nu>) (F (G (D.cod \<nu>))) \<and>
               (D.ide \<nu> \<longrightarrow> hom\<^sub>D.iso (Faa'.\<eta> \<nu>))"
          using assms Faa'.\<eta>\<epsilon>.\<eta>.preserves_hom [of \<nu> "D.dom \<nu>" "D.cod \<nu>"]
                hom\<^sub>D.map_def G_def Faa'.F\<^sub>1_def
          apply simp
          by (simp add: D.arr_iff_in_hom hom\<^sub>D.arr_char hom\<^sub>D.cod_closed hom\<^sub>D.dom_closed
              hom\<^sub>D.ide_char hom\<^sub>D.in_hom_char)
        thus ?thesis
          unfolding \<eta>_def
          using hom\<^sub>D.in_hom_char hom\<^sub>D.iso_char by auto
      qed
      show "\<guillemotleft>\<eta> \<nu> : D.dom \<nu> \<Rightarrow>\<^sub>D F (G (D.cod \<nu>))\<guillemotright>"
        using 1 by simp
      thus "D.in_hhom (\<eta> \<nu>) (src\<^sub>D \<nu>) (trg\<^sub>D \<nu>)"
        using assms D.src_dom D.trg_dom [of "\<eta> \<nu>"] by fastforce
      show "D.ide \<nu> \<Longrightarrow> D.iso (\<eta> \<nu>)"
        using 1 by simp
    qed

    lemma \<eta>_simps [simp]:
    assumes "D.arr \<nu>"
    shows "D.arr (\<eta> \<nu>)"
    and "src\<^sub>D (\<eta> \<nu>) = src\<^sub>D \<nu>" and "trg\<^sub>D (\<eta> \<nu>) = trg\<^sub>D \<nu>"
    and "D.dom (\<eta> \<nu>) = D.dom \<nu>" and "D.cod (\<eta> \<nu>) = F (G (D.cod \<nu>))"
    and "D.ide \<nu> \<Longrightarrow> D.iso (\<eta> \<nu>)"
      using assms \<eta>_in_hom by auto

    lemma \<eta>_naturality:
    assumes "D.arr \<nu>"
    shows "\<eta> (D.cod \<nu>) \<cdot>\<^sub>D \<nu> = \<eta> \<nu>" and "F (G \<nu>) \<cdot>\<^sub>D \<eta> (D.dom \<nu>) = \<eta> \<nu>"
    and "\<nu> \<cdot>\<^sub>D D.inv (\<eta> (D.dom \<nu>)) = D.inv (\<eta> (D.cod \<nu>)) \<cdot>\<^sub>D F (G \<nu>)"
    proof -
      interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>'. \<guillemotleft>\<mu>' : G\<^sub>0 (src\<^sub>D \<nu>) \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<nu>)\<guillemotright>\<close>
        using assms C.hhom_is_subcategory by simp
      interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))\<guillemotright>\<close>
        using D.hhom_is_subcategory by simp
      interpret Faa': equivalence_pseudofunctor_at_hom
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>G\<^sub>0 (src\<^sub>D \<nu>)\<close> \<open>G\<^sub>0 (trg\<^sub>D \<nu>)\<close>
        using assms G\<^sub>0_props by unfold_locales auto
      show 1: "\<eta> (D.cod \<nu>) \<cdot>\<^sub>D \<nu> = \<eta> \<nu>"
        unfolding \<eta>_def
        using assms Faa'.\<eta>\<epsilon>.\<eta>.is_natural_2 hom\<^sub>D.comp_char G_def hom\<^sub>D.cod_simp
              G_in_hom(1) hom\<^sub>C.arr_char hom\<^sub>D.arr_char hom\<^sub>D.cod_closed
        apply simp
        by (metis (no_types, lifting) D.ext Faa'.\<eta>\<epsilon>.F.preserves_reflects_arr
            Faa'.\<eta>\<epsilon>.\<eta>.preserves_reflects_arr)
      show 2: "F (G \<nu>) \<cdot>\<^sub>D \<eta> (D.dom \<nu>) = \<eta> \<nu>"
        unfolding \<eta>_def
        using assms D.src_dom D.src_cod D.trg_dom D.trg_cod Faa'.\<eta>\<epsilon>.\<eta>.is_natural_1
              hom\<^sub>D.comp_char G_def Faa'.F\<^sub>1_def hom\<^sub>D.dom_simp hom\<^sub>D.cod_simp
        apply simp
        by (metis (no_types, lifting) D.not_arr_null Faa'.\<eta>\<epsilon>.\<eta>.is_extensional
            \<eta>_def \<eta>_simps(1) hom\<^sub>D.null_char)
      show "\<nu> \<cdot>\<^sub>D D.inv (\<eta> (D.dom \<nu>)) = D.inv (\<eta> (D.cod \<nu>)) \<cdot>\<^sub>D F (G \<nu>)"
        using assms 1 2
        by (simp add: D.invert_opposite_sides_of_square)
    qed

    text \<open>
      The fact that \<open>G\<^sub>0\<close> is chosen to be right-inverse to \<open>F\<close> implies that \<open>\<eta>\<close> is an
      ordinary natural isomorphism (with respect to vertical composition) from \<open>I\<^sub>D\<close> to \<open>FG\<close>.
    \<close>

    interpretation \<eta>: natural_isomorphism V\<^sub>D V\<^sub>D D.map FG.map \<eta>
      using \<eta>_simps \<eta>_naturality \<eta>_def
      by unfold_locales auto

    text \<open>
      In view of the bijectivity assumption, we can obtain the counit \<open>\<epsilon>\<close> the same way.
    \<close>

    definition \<epsilon>
    where "\<epsilon> \<mu> = (if C.arr \<mu> then
                    equivalence_pseudofunctor_at_hom.\<epsilon> V\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D src\<^sub>D trg\<^sub>D F
                      (src\<^sub>C \<mu>) (trg\<^sub>C \<mu>) \<mu>
                  else C.null)"

    lemma \<epsilon>_in_hom:
    assumes "C.arr \<mu>"
    shows [intro]: "\<guillemotleft>\<epsilon> \<mu> : src\<^sub>C \<mu> \<rightarrow>\<^sub>C trg\<^sub>C \<mu>\<guillemotright>"
    and [intro]: "\<guillemotleft>\<epsilon> \<mu> : G (F (C.dom \<mu>)) \<Rightarrow>\<^sub>C C.cod \<mu>\<guillemotright>"
    and "C.ide \<mu> \<Longrightarrow> C.iso (\<epsilon> \<mu>)"
    proof -
      interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>'. \<guillemotleft>\<mu>' : src\<^sub>C \<mu> \<rightarrow>\<^sub>C trg\<^sub>C \<mu>\<guillemotright>\<close>
        using C.hhom_is_subcategory by simp
      interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (src\<^sub>C \<mu>) \<rightarrow>\<^sub>D F\<^sub>0 (trg\<^sub>C \<mu>)\<guillemotright>\<close>
        using assms D.hhom_is_subcategory
        by (simp add: D.in_hhom_def subcategory_axioms_def subcategory_def)
      interpret Faa': equivalence_pseudofunctor_at_hom
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>G\<^sub>0 (F\<^sub>0 (src\<^sub>C \<mu>))\<close> \<open>G\<^sub>0 (F\<^sub>0 (trg\<^sub>C \<mu>))\<close>
        using assms G\<^sub>0_props
        by unfold_locales simp_all
      have 1: "\<guillemotleft>\<epsilon> \<mu> : G (F (C.dom \<mu>)) \<Rightarrow>\<^sub>C C.cod \<mu>\<guillemotright> \<and> (C.ide \<mu> \<longrightarrow> C.iso (\<epsilon> \<mu>))"
      proof -
        have "hom\<^sub>C.arr \<mu>"
          using assms hom\<^sub>C.arr_char by simp
        hence "hom\<^sub>C.in_hom \<mu> (C.dom \<mu>) (C.cod \<mu>)"
          using assms hom\<^sub>C.in_hom_char hom\<^sub>C.dom_char hom\<^sub>C.cod_char by auto
        hence "hom\<^sub>C.in_hom (Faa'.\<epsilon> \<mu>) (G (F (C.dom \<mu>))) (C.cod \<mu>) \<and>
               (C.ide \<mu> \<longrightarrow> hom\<^sub>C.iso (Faa'.\<epsilon> \<mu>))"
          using assms Faa'.\<eta>\<epsilon>.\<epsilon>.preserves_hom [of \<mu> "C.dom \<mu>" "C.cod \<mu>"]
                Faa'.\<eta>\<epsilon>.\<epsilon>.components_are_iso hom\<^sub>C.map_def G_def Faa'.F\<^sub>1_def G\<^sub>0_props
          by (simp add: hom\<^sub>C.ideI)
        thus ?thesis
          unfolding \<epsilon>_def
          using assms hom\<^sub>C.in_hom_char hom\<^sub>C.iso_char G\<^sub>0_props(2) by simp
      qed
      show "\<guillemotleft>\<epsilon> \<mu> : G (F (C.dom \<mu>)) \<Rightarrow>\<^sub>C C.cod \<mu>\<guillemotright>"
        using 1 by simp
      thus "C.in_hhom (\<epsilon> \<mu>) (src\<^sub>C \<mu>) (trg\<^sub>C \<mu>)"
        using assms C.src_cod C.trg_cod [of "\<epsilon> \<mu>"] by fastforce
      show "C.ide \<mu> \<Longrightarrow> C.iso (\<epsilon> \<mu>)"
        using 1 by simp
    qed

    lemma \<epsilon>_simps [simp]:
    assumes "C.arr \<mu>"
    shows "C.arr (\<epsilon> \<mu>)"
    and "src\<^sub>C (\<epsilon> \<mu>) = src\<^sub>C \<mu>" and "trg\<^sub>C (\<epsilon> \<mu>) = trg\<^sub>C \<mu>"
    and "C.dom (\<epsilon> \<mu>) = G (F (C.dom \<mu>))" and "C.cod (\<epsilon> \<mu>) = C.cod \<mu>"
    and "C.ide \<mu> \<Longrightarrow> C.iso (\<epsilon> \<mu>)"
      using assms \<epsilon>_in_hom by auto

    lemma \<epsilon>_naturality:
    assumes "C.arr \<mu>"
    shows "\<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C G (F \<mu>) = \<epsilon> \<mu>" and "\<mu> \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) = \<epsilon> \<mu>"
    and "G (F \<mu>) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom \<mu>)) = C.inv (\<epsilon> (C.cod \<mu>)) \<cdot>\<^sub>C \<mu>"
    proof -
      interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>'. \<guillemotleft>\<mu>' : src\<^sub>C \<mu> \<rightarrow>\<^sub>C trg\<^sub>C \<mu>\<guillemotright>\<close>
        using assms C.hhom_is_subcategory by simp
      interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>. \<guillemotleft>\<nu> : F\<^sub>0 (src\<^sub>C \<mu>) \<rightarrow>\<^sub>D F\<^sub>0 (trg\<^sub>C \<mu>)\<guillemotright>\<close>
        using assms D.hhom_is_subcategory
        by (simp add: D.in_hhom_def subcategory_axioms_def subcategory_def)
      interpret Faa': equivalence_pseudofunctor_at_hom
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        F \<Phi> \<open>src\<^sub>C \<mu>\<close> \<open>trg\<^sub>C \<mu>\<close>
        using assms by unfold_locales simp_all
      show 1: "\<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C G (F \<mu>) = \<epsilon> \<mu>"
        unfolding \<epsilon>_def
        using assms C.src_dom C.src_cod C.trg_dom C.trg_cod Faa'.\<eta>\<epsilon>.\<epsilon>.is_natural_2
              hom\<^sub>C.comp_char G_def Faa'.F\<^sub>1_def G\<^sub>0_props hom\<^sub>C.dom_char hom\<^sub>C.cod_char
        apply simp
        by (metis (no_types, lifting) C.in_hhomI Faa'.\<eta>\<epsilon>.\<epsilon>.preserves_reflects_arr hom\<^sub>C.arr_char
            hom\<^sub>C.not_arr_null hom\<^sub>C.null_char)
      show 2: "\<mu> \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) = \<epsilon> \<mu>"
        unfolding \<epsilon>_def
        using assms C.src_dom C.src_cod C.trg_dom C.trg_cod Faa'.\<eta>\<epsilon>.\<epsilon>.is_natural_1
              hom\<^sub>C.comp_char G_def Faa'.F\<^sub>1_def G\<^sub>0_props hom\<^sub>C.dom_char hom\<^sub>C.cod_char
        apply simp
        by (metis (no_types, lifting) C.in_hhomI Faa'.\<eta>\<epsilon>.\<epsilon>.preserves_reflects_arr
            hom\<^sub>C.arr_char hom\<^sub>C.not_arr_null hom\<^sub>C.null_char)
      show "G (F \<mu>) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom \<mu>)) = C.inv (\<epsilon> (C.cod \<mu>)) \<cdot>\<^sub>C \<mu>"
        using assms 1 2 C.invert_opposite_sides_of_square by simp
    qed

    interpretation \<epsilon>: natural_isomorphism V\<^sub>C V\<^sub>C GF.map C.map \<epsilon>
      using \<epsilon>_simps \<epsilon>_naturality \<epsilon>_def
      by unfold_locales auto

    interpretation GFG: composite_functor V\<^sub>D V\<^sub>C V\<^sub>C G \<open>GF.map\<close> ..
    interpretation FGF: composite_functor V\<^sub>C V\<^sub>D V\<^sub>D F \<open>FG.map\<close> ..

    interpretation Go\<eta>: natural_transformation V\<^sub>D V\<^sub>C G GFG.map \<open>G \<circ> \<eta>\<close>
    proof -
      have "G \<circ> D.map = G"
        using G.natural_transformation_axioms by auto
      moreover have "G \<circ> FG.map = GFG.map"
        by auto
      ultimately show "natural_transformation V\<^sub>D V\<^sub>C G GFG.map (G \<circ> \<eta>)"
        using \<eta>.natural_transformation_axioms G.natural_transformation_axioms
              horizontal_composite [of V\<^sub>D V\<^sub>D D.map FG.map \<eta> V\<^sub>C G G G] by simp
    qed

    interpretation \<eta>oF: natural_transformation V\<^sub>C V\<^sub>D F FGF.map \<open>\<eta> \<circ> F\<close>
      using \<eta>.natural_transformation_axioms natural_transformation_axioms
            horizontal_composite [of V\<^sub>C V\<^sub>D F F F V\<^sub>D D.map FG.map \<eta>]
      by simp

    interpretation \<epsilon>oG: natural_transformation V\<^sub>D V\<^sub>C GFG.map G \<open>\<epsilon> \<circ> G\<close>
      using \<epsilon>.natural_transformation_axioms G.natural_transformation_axioms
            horizontal_composite [of V\<^sub>D V\<^sub>C G G G V\<^sub>C GF.map C.map \<epsilon>]
      by simp

    interpretation Fo\<epsilon>: natural_transformation V\<^sub>C V\<^sub>D FGF.map F \<open>F \<circ> \<epsilon>\<close>
    proof -
      have "F \<circ> C.map = F"
        using natural_transformation_axioms by auto
      moreover have "F \<circ> GF.map = FGF.map"
        by auto
      ultimately show "natural_transformation V\<^sub>C V\<^sub>D FGF.map F (F \<circ> \<epsilon>)"
        using \<epsilon>.natural_transformation_axioms natural_transformation_axioms
              horizontal_composite [of V\<^sub>C V\<^sub>C GF.map C.map \<epsilon> V\<^sub>D F F F]
        by simp
    qed

    interpretation \<epsilon>oG_Go\<eta>: vertical_composite V\<^sub>D V\<^sub>C G GFG.map G \<open>G \<circ> \<eta>\<close> \<open>\<epsilon> \<circ> G\<close> ..
    interpretation Fo\<epsilon>_\<eta>oF: vertical_composite V\<^sub>C V\<^sub>D F FGF.map F \<open>\<eta> \<circ> F\<close> \<open>F \<circ> \<epsilon>\<close> ..

    text \<open>
      Bijectivity results in an ordinary adjunction between the vertical categories.
    \<close>

    lemma adjunction_\<eta>\<epsilon>:
    shows "unit_counit_adjunction V\<^sub>C V\<^sub>D G F \<eta> \<epsilon>"
    proof
      show "\<epsilon>oG_Go\<eta>.map = G"
      proof
        fix \<nu>
        have "\<not> D.arr \<nu> \<Longrightarrow> \<epsilon>oG_Go\<eta>.map \<nu> = G \<nu>"
          unfolding \<epsilon>oG_Go\<eta>.map_def
          by (simp add: G.is_extensional)
        moreover have "D.arr \<nu> \<Longrightarrow> \<epsilon>oG_Go\<eta>.map \<nu> = G \<nu>"
        proof -
          assume \<nu>: "D.arr \<nu>"
          interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>'. \<guillemotleft>\<mu>' : G\<^sub>0 (src\<^sub>D \<nu>) \<rightarrow>\<^sub>C G\<^sub>0 (trg\<^sub>D \<nu>)\<guillemotright>\<close>
            using \<nu> C.hhom_is_subcategory by simp
          interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>'. \<guillemotleft>\<nu>' : F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>)) \<rightarrow>\<^sub>D F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>))\<guillemotright>\<close>
            using D.hhom_is_subcategory by simp
          interpret Faa': equivalence_pseudofunctor_at_hom
                            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            F \<Phi> \<open>G\<^sub>0 (src\<^sub>D \<nu>)\<close> \<open>G\<^sub>0 (trg\<^sub>D \<nu>)\<close>
            using \<nu> G\<^sub>0_props by unfold_locales simp_all
          show "\<epsilon>oG_Go\<eta>.map \<nu> = G \<nu>"
          proof -
            have 1: "C.arr (Faa'.G\<^sub>1 (D.cod \<nu>))"
              using \<nu> hom\<^sub>D.arr_char G_def
              by (metis Faa'.\<eta>\<epsilon>.F.preserves_reflects_arr G_in_hom(1) hom\<^sub>C.arr_char
                  hom\<^sub>C.inclusion hom\<^sub>D.cod_closed)
            have 2: "D.arr (Faa'.\<eta> \<nu>)"
              using \<nu> hom\<^sub>D.arr_char
              by (metis D.in_hhomI D.obj_src D.obj_trg Faa'.\<eta>\<epsilon>.\<eta>.preserves_reflects_arr
                  G\<^sub>0_props(1) hom\<^sub>D.inclusion)
            have 3: "src\<^sub>C (Faa'.G\<^sub>1 (D.cod \<nu>)) = G\<^sub>0 (src\<^sub>D \<nu>)"
              using \<nu>
              by (metis D.arr_cod D.src_cod D.trg_cod G_def G_simps(2))
            have 4: "trg\<^sub>C (Faa'.G\<^sub>1 (D.cod \<nu>)) = G\<^sub>0 (trg\<^sub>D \<nu>)"
              using \<nu>
              by (metis D.arr_cod D.src_cod D.trg_cod G_def G_simps(3))
            have 5: "hom\<^sub>D.arr \<nu>"
              using \<nu> hom\<^sub>D.arr_char G\<^sub>0_props by simp
            have "\<epsilon>oG_Go\<eta>.map \<nu> = \<epsilon> (G (D.cod \<nu>)) \<cdot>\<^sub>C G (\<eta> \<nu>)"
              using \<nu> \<epsilon>oG_Go\<eta>.map_def by simp
            also have "... = Faa'.\<epsilon> (Faa'.G\<^sub>1 (D.cod \<nu>)) \<cdot>\<^sub>C Faa'.G\<^sub>1 (Faa'.\<eta> \<nu>)"
              using \<nu> 1 2 3 4 \<eta>_def \<epsilon>_def G_def G_simps(2-3) \<eta>_simps(2-3) by auto
            also have "... = hom\<^sub>C.comp ((Faa'.\<epsilon> \<circ> Faa'.G\<^sub>1) (hom\<^sub>D.cod \<nu>)) ((Faa'.G\<^sub>1 \<circ> Faa'.\<eta>) \<nu>)"
            proof -
              have "Faa'.\<epsilon> (Faa'.G\<^sub>1 (D.cod \<nu>)) \<cdot>\<^sub>C Faa'.G\<^sub>1 (Faa'.\<eta> \<nu>) = Faa'.\<eta>\<epsilon>.\<epsilon>FoF\<eta>.map \<nu>"
              proof -
                have "C.seq (Faa'.\<epsilon> (Faa'.G\<^sub>1 (hom\<^sub>D.cod \<nu>))) (Faa'.G\<^sub>1 (Faa'.\<eta> \<nu>))"
                proof -
                  have "hom\<^sub>C.seq (Faa'.\<epsilon> (Faa'.G\<^sub>1 (hom\<^sub>D.cod \<nu>))) (Faa'.G\<^sub>1 (Faa'.\<eta> \<nu>))"
                    using \<nu> 5 hom\<^sub>C.arr_char hom\<^sub>C.seq_char Faa'.\<eta>\<epsilon>.F.preserves_arr
                    apply (intro hom\<^sub>C.seqI)
                      apply auto
                    using Faa'.\<eta>\<epsilon>.\<epsilon>.preserves_reflects_arr hom\<^sub>C.inclusion hom\<^sub>D.arr_cod
                    by presburger
                  thus ?thesis
                    using hom\<^sub>C.seq_char by simp
                qed
                moreover have "D.in_hhom (Faa'.\<eta> \<nu>) (F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>))) (F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>)))"
                  using \<nu> 5 Faa'.\<eta>\<epsilon>.\<eta>.preserves_reflects_arr hom\<^sub>D.arrE by blast
                moreover have "D.in_hhom (D.cod \<nu>) (F\<^sub>0 (G\<^sub>0 (src\<^sub>D \<nu>))) (F\<^sub>0 (G\<^sub>0 (trg\<^sub>D \<nu>)))"
                  using \<nu> 5 hom\<^sub>D.arrE hom\<^sub>D.cod_closed by blast
                ultimately show ?thesis
                  using \<nu> 5 Faa'.\<eta>\<epsilon>.\<epsilon>FoF\<eta>.map_def hom\<^sub>D.arr_char hom\<^sub>C.comp_char hom\<^sub>D.cod_char
                  by simp
              qed
              thus ?thesis
                using \<nu> 5 Faa'.\<eta>\<epsilon>.\<epsilon>FoF\<eta>.map_def by simp
            qed
            also have "... = G \<nu>"
              using \<nu> 5 G_def Faa'.\<eta>\<epsilon>.triangle_F Faa'.\<eta>\<epsilon>.\<epsilon>FoF\<eta>.map_simp_1 [of \<nu>] by simp
            finally show ?thesis by simp
          qed
        qed
        ultimately show "\<epsilon>oG_Go\<eta>.map \<nu> = G \<nu>" by auto
      qed
      show "Fo\<epsilon>_\<eta>oF.map = F"
      proof
        fix \<mu>
        have "\<not> C.arr \<mu> \<Longrightarrow> Fo\<epsilon>_\<eta>oF.map \<mu> = F \<mu>"
          unfolding Fo\<epsilon>_\<eta>oF.map_def
          by (simp add: is_extensional)
        moreover have "C.arr \<mu> \<Longrightarrow> Fo\<epsilon>_\<eta>oF.map \<mu> = F \<mu>"
        proof -
          assume \<mu>: "C.arr \<mu>"
          interpret hom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>'. \<guillemotleft>\<mu>' : src\<^sub>C \<mu> \<rightarrow>\<^sub>C trg\<^sub>C \<mu>\<guillemotright>\<close>
            using \<mu> C.hhom_is_subcategory by simp
          interpret hom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<nu>. \<guillemotleft>\<nu> : F\<^sub>0 (src\<^sub>C \<mu>) \<rightarrow>\<^sub>D F\<^sub>0 (trg\<^sub>C \<mu>)\<guillemotright>\<close>
            using \<mu> D.in_hhom_def D.hhom_is_subcategory by simp
          interpret Faa': equivalence_pseudofunctor_at_hom
                            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                            F \<Phi> \<open>src\<^sub>C \<mu>\<close> \<open>trg\<^sub>C \<mu>\<close>
            using \<mu> by unfold_locales auto
          show "Fo\<epsilon>_\<eta>oF.map \<mu> = F \<mu>"
          proof -
            have 1: "hom\<^sub>C.arr \<mu>"
              using \<mu> hom\<^sub>C.arr_char by simp
            have "Fo\<epsilon>_\<eta>oF.map \<mu> = F (\<epsilon> (C.cod \<mu>)) \<cdot>\<^sub>D \<eta> (F \<mu>)"
              using \<mu> Fo\<epsilon>_\<eta>oF.map_def by simp
            also have "... = Faa'.F\<^sub>1 (Faa'.\<epsilon> (C.cod \<mu>)) \<cdot>\<^sub>D Faa'.\<eta> (Faa'.F\<^sub>1 \<mu>)"
              unfolding \<eta>_def \<epsilon>_def G_def
              using \<mu> G\<^sub>0_props Faa'.F\<^sub>1_def
              by auto
            also have "... = hom\<^sub>D.comp ((Faa'.F\<^sub>1 \<circ> Faa'.\<epsilon>) (hom\<^sub>C.cod \<mu>)) ((Faa'.\<eta> \<circ> Faa'.F\<^sub>1) \<mu>)"
            proof -
              have 2: "hom\<^sub>C.arr (C.cod \<mu>)"
                using 1 hom\<^sub>C.cod_char [of \<mu>] hom\<^sub>C.arr_cod hom\<^sub>C.dom_char hom\<^sub>C.cod_char
                by simp
              moreover have "D.seq (Faa'.F\<^sub>1 (Faa'.\<epsilon> (C.cod \<mu>))) (Faa'.\<eta> (Faa'.F\<^sub>1 \<mu>))"
              proof -
                have "hom\<^sub>D.seq (Faa'.F\<^sub>1 (Faa'.\<epsilon> (C.cod \<mu>))) (Faa'.\<eta> (Faa'.F\<^sub>1 \<mu>))"
                  using \<mu> 1 2 hom\<^sub>D.arr_char hom\<^sub>D.seq_char Faa'.\<eta>\<epsilon>.G.preserves_arr
                        hom\<^sub>C.cod_simp hom\<^sub>C.dom_cod
                  by (intro hom\<^sub>D.seqI) auto
                thus ?thesis
                  using hom\<^sub>D.seq_char by simp
              qed
              ultimately show ?thesis
                using 1 hom\<^sub>D.comp_char hom\<^sub>C.dom_char hom\<^sub>C.cod_char by simp
            qed
            also have "... = Faa'.\<eta>\<epsilon>.G\<epsilon>o\<eta>G.map \<mu>"
              unfolding Faa'.\<eta>\<epsilon>.G\<epsilon>o\<eta>G.map_def
              using 1 by simp
            also have "... = F \<mu>"
              using \<mu> Faa'.\<eta>\<epsilon>.triangle_G hom\<^sub>C.arr_char Faa'.\<eta>\<epsilon>.\<epsilon>FoF\<eta>.map_def
                    hom\<^sub>D.arr_char hom\<^sub>C.comp_char hom\<^sub>D.comp_char Faa'.F\<^sub>1_def
              by simp
            finally show ?thesis by simp
          qed
        qed
        ultimately show "Fo\<epsilon>_\<eta>oF.map \<mu> = F \<mu>" by auto
      qed
    qed

    interpretation \<eta>\<epsilon>: unit_counit_adjunction V\<^sub>C V\<^sub>D G F \<eta> \<epsilon>
      using adjunction_\<eta>\<epsilon> by simp

    text \<open>
      We now use the adjunction between the vertical categories to define the
      compositors for \<open>G\<close>.  Without the bijectivity assumption, we would only obtain
      \<open>\<eta>\<close> and \<open>\<epsilon>\<close> as pseudonatural equivalences, rather than natural isomorphisms,
      which would make everything more complicated.
    \<close>

    definition \<Phi>\<^sub>G\<^sub>0
    where "\<Phi>\<^sub>G\<^sub>0 f f' = C.inv (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))"

    lemma \<Phi>\<^sub>G\<^sub>0_in_hom:
    assumes "D.ide f" and "D.ide f'" and "src\<^sub>D f = trg\<^sub>D f'"
    shows "\<guillemotleft>\<Phi>\<^sub>G\<^sub>0 f f' : G f \<star>\<^sub>C G f' \<Rightarrow>\<^sub>C G (f \<star>\<^sub>D f')\<guillemotright>"
    proof (unfold \<Phi>\<^sub>G\<^sub>0_def, intro C.inv_in_hom)
      show 1: "\<guillemotleft>\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')) :
                  G (f \<star>\<^sub>D f') \<Rightarrow>\<^sub>C G f \<star>\<^sub>C G f'\<guillemotright>"
      proof
        show "\<guillemotleft>\<epsilon> (G f \<star>\<^sub>C G f') : G (F (G f \<star>\<^sub>C G f')) \<Rightarrow>\<^sub>C G f \<star>\<^sub>C G f'\<guillemotright>"
          using assms \<epsilon>_in_hom by auto
        show "\<guillemotleft>G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')) : G (f \<star>\<^sub>D f') \<Rightarrow>\<^sub>C G (F (G f \<star>\<^sub>C G f'))\<guillemotright>"
        proof -
          have "\<guillemotleft>\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f') : f \<star>\<^sub>D f' \<Rightarrow>\<^sub>D F (G f \<star>\<^sub>C G f')\<guillemotright>"
            using assms \<eta>_in_hom
            by (intro D.comp_in_homI') auto
          thus ?thesis by auto
        qed
      qed
      show "C.iso (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))"
      proof (intro C.isos_compose)
        show "C.iso (G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))"
        proof -
          have "D.iso (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f'))"
            using assms \<eta>_in_hom
            by (intro D.isos_compose D.seqI) auto
          thus ?thesis by simp
        qed
        show "C.iso (\<epsilon> (G f \<star>\<^sub>C G f'))"
          using assms \<epsilon>_in_hom by simp
        show "C.seq (\<epsilon> (G f \<star>\<^sub>C G f')) (G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))"
          using 1 by auto
      qed
    qed

    lemma iso_\<Phi>\<^sub>G\<^sub>0:
    assumes "D.ide f" and "D.ide f'" and "src\<^sub>D f = trg\<^sub>D f'"
    shows "C.iso (\<Phi>\<^sub>G\<^sub>0 f f')"
    proof (unfold \<Phi>\<^sub>G\<^sub>0_def, intro C.iso_inv_iso C.isos_compose)
      show 1: "C.iso (G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))"
        using assms \<eta>_in_hom D.in_hhom_def cmp_simps'(1) cmp_simps(4) by auto
      show "C.iso (\<epsilon> (G f \<star>\<^sub>C G f'))"
        using assms \<epsilon>_in_hom by simp
      show "C.seq (\<epsilon> (G f \<star>\<^sub>C G f')) (G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))"
        using assms 1 by force
    qed

    lemma \<Phi>\<^sub>G\<^sub>0_naturality:
    assumes "D.arr \<nu>" and "D.arr \<nu>'" and "src\<^sub>D \<nu> = trg\<^sub>D \<nu>'"
    shows "\<Phi>\<^sub>G\<^sub>0 (D.cod \<nu>) (D.cod \<nu>') \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>') =
           G (\<nu> \<star>\<^sub>D \<nu>') \<cdot>\<^sub>C \<Phi>\<^sub>G\<^sub>0 (D.dom \<nu>) (D.dom \<nu>')"
    proof -
      let ?X = "\<epsilon> (G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>')) \<cdot>\<^sub>C
                G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>')) \<cdot>\<^sub>D (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>')))"
      have iso_X: "C.iso ?X"
        using assms C.VV.arr_char C.VV.dom_char C.VV.cod_char FF_def
        by (intro C.isos_compose) auto
      have "\<Phi>\<^sub>G\<^sub>0 (D.cod \<nu>) (D.cod \<nu>') \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>') = C.inv ?X \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>')"
        unfolding \<Phi>\<^sub>G\<^sub>0_def by simp
      also have "... = (C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>')) \<cdot>\<^sub>D
                                 (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>')))) \<cdot>\<^sub>C
                        C.inv (\<epsilon> (G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>')))) \<cdot>\<^sub>C
                       (G \<nu> \<star>\<^sub>C G \<nu>')"
        using assms iso_X \<eta>_in_hom \<epsilon>_in_hom
        by (simp add: C.inv_comp_left(1))
      also have "... = (C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>'))) \<cdot>\<^sub>C
                               G (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>'))) \<cdot>\<^sub>C
                        C.inv (\<epsilon> (G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>')))) \<cdot>\<^sub>C
                       (G \<nu> \<star>\<^sub>C G \<nu>')"
      proof -
        have "G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>')) \<cdot>\<^sub>D (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>'))) =
              G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>'))) \<cdot>\<^sub>C G (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>'))"
          using assms iso_X \<eta>_in_hom by fast
        thus ?thesis by simp
      qed
      also have "... = C.inv (G (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>'))) \<cdot>\<^sub>C
                       C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>')))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>'))) \<cdot>\<^sub>C
                       (G \<nu> \<star>\<^sub>C G \<nu>')"
      proof -
        have "C.iso (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>'))) \<cdot>\<^sub>C G (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>')))"
          using assms iso_X \<eta>_in_hom C.VV.arr_char C.VV.dom_char C.VV.cod_char FF_def
          by (intro C.isos_compose C.seqI) auto
        hence "C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>'))) \<cdot>\<^sub>C
               G (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>')))
                 = C.inv (G (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>'))) \<cdot>\<^sub>C
                   C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>'))))"
          using assms \<eta>_in_hom
          by (simp add: C.inv_comp_right(1))
        thus ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = G (D.inv (\<eta> (D.cod \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.cod \<nu>'))) \<cdot>\<^sub>C
                       C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>')))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>'))) \<cdot>\<^sub>C
                       (G \<nu> \<star>\<^sub>C G \<nu>')"
      proof -
        have "C.inv (G (\<eta> (D.cod \<nu>) \<star>\<^sub>D \<eta> (D.cod \<nu>'))) =
                G (D.inv (\<eta> (D.cod \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.cod \<nu>')))"
          using assms \<eta>_in_hom D.ide_cod D.iso_hcomp D.src_cod D.trg_cod G.preserves_inv
                \<eta>_simps(2-3) D.inv_hcomp
          by (metis D.arr_cod)
        thus ?thesis by simp
      qed
      also have "... = G (D.inv (\<eta> (D.cod \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.cod \<nu>'))) \<cdot>\<^sub>C
                       (C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>')))) \<cdot>\<^sub>C
                       G (F (G \<nu> \<star>\<^sub>C G \<nu>'))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')))"
      proof -
        have "C.inv (\<epsilon> (G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>'))) \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>')
                = G (F (G \<nu> \<star>\<^sub>C G \<nu>')) \<cdot>\<^sub>C C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')))"
        proof -
          have "G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>') = C.dom (G \<nu> \<star>\<^sub>C G \<nu>')"
            by (simp add: assms)
          thus ?thesis
            using assms C.hcomp_simps(4) C.hseqI' G.preserves_cod G.preserves_hseq
                  \<epsilon>_naturality(3)
            by presburger
        qed
        thus ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = (G (D.inv (\<eta> (D.cod \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.cod \<nu>'))) \<cdot>\<^sub>C
                        G (F (G \<nu>) \<star>\<^sub>D F (G \<nu>'))) \<cdot>\<^sub>C
                       G (D.inv (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>')))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')))"
      proof -
        have "C.inv (G (\<Phi> (G (D.cod \<nu>), G (D.cod \<nu>')))) \<cdot>\<^sub>C G (F (G \<nu> \<star>\<^sub>C G \<nu>')) =
              G (D.inv (\<Phi> (C.cod (G \<nu>), C.cod (G \<nu>'))) \<cdot>\<^sub>D F (G \<nu> \<star>\<^sub>C G \<nu>'))"
          using assms by (simp add: G.preserves_inv)
        also have "... = G ((F (G \<nu>) \<star>\<^sub>D F (G \<nu>')) \<cdot>\<^sub>D D.inv (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>'))))"
          using assms C.VV.arr_char C.VV.dom_char C.VV.cod_char FF_def
                \<Phi>.inv_naturality [of "(G \<nu>, G \<nu>')"]
          by simp
        also have "... = G (F (G \<nu>) \<star>\<^sub>D F (G \<nu>')) \<cdot>\<^sub>C
                         G (D.inv (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>'))))"
          using assms by simp
        finally show ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = G (\<nu> \<star>\<^sub>D \<nu>') \<cdot>\<^sub>C
                       G (D.inv (\<eta> (D.dom \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.dom \<nu>'))) \<cdot>\<^sub>C
                       G (D.inv (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>')))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')))"
      proof -
        have "G (D.inv (\<eta> (D.cod \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.cod \<nu>'))) \<cdot>\<^sub>C G (F (G \<nu>) \<star>\<^sub>D F (G \<nu>')) =
                G ((D.inv (\<eta> (D.cod \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.cod \<nu>'))) \<cdot>\<^sub>D (F (G \<nu>) \<star>\<^sub>D F (G \<nu>')))"
          using assms by simp
        also have "... = G (D.inv (\<eta> (D.cod \<nu>)) \<cdot>\<^sub>D F (G \<nu>)
                           \<star>\<^sub>D D.inv (\<eta> (D.cod \<nu>')) \<cdot>\<^sub>D F (G \<nu>'))"
          using assms D.interchange by simp
        also have "... = G (\<nu> \<cdot>\<^sub>D D.inv (\<eta> (D.dom \<nu>)) \<star>\<^sub>D \<nu>' \<cdot>\<^sub>D D.inv (\<eta> (D.dom \<nu>')))"
          using assms \<eta>_naturality by simp
        also have "... = G ((\<nu> \<star>\<^sub>D \<nu>') \<cdot>\<^sub>D (D.inv (\<eta> (D.dom \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.dom \<nu>'))))"
          using assms D.interchange by simp
        also have "... = G (\<nu> \<star>\<^sub>D \<nu>') \<cdot>\<^sub>C G (D.inv (\<eta> (D.dom \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.dom \<nu>')))"
          using assms by simp
        finally show ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = G (\<nu> \<star>\<^sub>D \<nu>') \<cdot>\<^sub>C \<Phi>\<^sub>G\<^sub>0 (D.dom \<nu>) (D.dom \<nu>')"
      proof -
        have "G (D.inv (\<eta> (D.dom \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.dom \<nu>'))) \<cdot>\<^sub>C
              G (D.inv (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>')))) \<cdot>\<^sub>C
              C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')))
                = C.inv (G (\<eta> (D.dom \<nu>) \<star>\<^sub>D \<eta> (D.dom \<nu>'))) \<cdot>\<^sub>C
                  C.inv (G (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>')))) \<cdot>\<^sub>C
                  C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')))"
        proof -
          have "G (D.inv (\<eta> (D.dom \<nu>)) \<star>\<^sub>D D.inv (\<eta> (D.dom \<nu>'))) =
                  C.inv (G (\<eta> (D.dom \<nu>) \<star>\<^sub>D \<eta> (D.dom \<nu>')))"
            using assms cmp_components_are_iso
            by (metis D.arr_dom D.ide_dom D.inv_hcomp D.iso_hcomp D.src_dom D.trg_dom
                      G.preserves_inv \<eta>_simps(2) \<eta>_simps(3) \<eta>_simps(6))
          moreover have "G (D.inv (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>')))) =
                           C.inv (G (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>'))))"
            using assms cmp_components_are_iso
            by (simp add: G.preserves_inv)
          ultimately show ?thesis by simp
        qed
        also have "... = C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')) \<cdot>\<^sub>C
                         G (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>'))) \<cdot>\<^sub>C
                         G (\<eta> (D.dom \<nu>) \<star>\<^sub>D \<eta> (D.dom \<nu>')))"
        proof -
          have "C.iso (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')) \<cdot>\<^sub>C
                       G (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>'))) \<cdot>\<^sub>C
                       G (\<eta> (D.dom \<nu>) \<star>\<^sub>D \<eta> (D.dom \<nu>')))"
            using assms \<eta>_in_hom \<epsilon>_in_hom cmp_simps'(1,4) C.VV.cod_char
            by (intro C.isos_compose C.seqI) auto
          thus ?thesis
            using assms cmp_components_are_iso C.comp_assoc C.inv_comp_left by simp
        qed
        also have "... = C.inv (\<epsilon> (G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')) \<cdot>\<^sub>C
                                G (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>')) \<cdot>\<^sub>D
                                (\<eta> (D.dom \<nu>) \<star>\<^sub>D \<eta> (D.dom \<nu>'))))"
        proof -
          have "G (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>'))) \<cdot>\<^sub>C G (\<eta> (D.dom \<nu>) \<star>\<^sub>D \<eta> (D.dom \<nu>')) =
                  G (\<Phi> (C.dom (G \<nu>), C.dom (G \<nu>')) \<cdot>\<^sub>D (\<eta> (D.dom \<nu>) \<star>\<^sub>D \<eta> (D.dom \<nu>')))"
            using assms cmp_simps'(1,4) by auto
          thus ?thesis by simp
        qed
        also have "... = \<Phi>\<^sub>G\<^sub>0 (D.dom \<nu>) (D.dom \<nu>')"
          unfolding \<Phi>\<^sub>G\<^sub>0_def
          using assms by simp
        finally show ?thesis by simp
      qed
      finally show ?thesis by simp
    qed

    interpretation \<Phi>\<^sub>G: transformation_by_components D.VV.comp V\<^sub>C H\<^sub>DoGG.map GoH\<^sub>D.map
                         \<open>\<lambda>fg. \<Phi>\<^sub>G\<^sub>0 (fst fg) (snd fg)\<close>
      using D.VV.ide_char D.VV.arr_char \<Phi>\<^sub>G\<^sub>0_in_hom \<Phi>\<^sub>G\<^sub>0_naturality G.FF_def
            D.VV.dom_char D.VV.cod_char
      by unfold_locales auto

    interpretation \<Phi>\<^sub>G: natural_isomorphism D.VV.comp V\<^sub>C H\<^sub>DoGG.map GoH\<^sub>D.map \<Phi>\<^sub>G.map
      using \<Phi>\<^sub>G.map_simp_ide D.VV.ide_char D.VV.arr_char iso_\<Phi>\<^sub>G\<^sub>0 by unfold_locales simp

    abbreviation \<Phi>\<^sub>G
    where "\<Phi>\<^sub>G \<equiv> \<Phi>\<^sub>G.map"

    lemma \<Phi>\<^sub>G_in_hom [intro]:
    assumes "D.arr \<nu>" and "D.arr \<nu>'" and "src\<^sub>D \<nu> = trg\<^sub>D \<nu>'"
    shows "C.in_hhom (\<Phi>\<^sub>G.map (\<nu>, \<nu>')) (src\<^sub>C (G (D.dom \<nu>'))) (trg\<^sub>C (G (D.cod \<nu>)))"
    and "\<guillemotleft>\<Phi>\<^sub>G.map (\<nu>, \<nu>') : G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>') \<Rightarrow>\<^sub>C G (D.cod \<nu> \<star>\<^sub>D D.cod \<nu>')\<guillemotright>"
    proof -
      show "\<guillemotleft>\<Phi>\<^sub>G.map (\<nu>, \<nu>') : G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>') \<Rightarrow>\<^sub>C G (D.cod \<nu> \<star>\<^sub>D D.cod \<nu>')\<guillemotright>"
      proof -
        have "\<Phi>\<^sub>G.map (\<nu>, \<nu>') = \<Phi>\<^sub>G\<^sub>0 (D.cod \<nu>) (D.cod \<nu>') \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>')"
          using assms D.VV.arr_char \<Phi>\<^sub>G.map_def \<Phi>\<^sub>G\<^sub>0_in_hom G.FF_def D.VV.cod_char
          by simp
        moreover have "\<guillemotleft>\<Phi>\<^sub>G\<^sub>0 (D.cod \<nu>) (D.cod \<nu>') \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>') :
                         G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>') \<Rightarrow>\<^sub>C G (D.cod \<nu> \<star>\<^sub>D D.cod \<nu>')\<guillemotright>"
          using assms \<Phi>\<^sub>G\<^sub>0_in_hom by (intro C.comp_in_homI) auto
        ultimately show ?thesis by simp
      qed
      thus "C.in_hhom (\<Phi>\<^sub>G.map (\<nu>, \<nu>')) (src\<^sub>C (G (D.dom \<nu>'))) (trg\<^sub>C (G (D.cod \<nu>)))"
        using assms C.vconn_implies_hpar(1-2) by auto
    qed

    lemma \<Phi>\<^sub>G_simps [simp]:
    assumes "D.arr \<nu>" and "D.arr \<nu>'" and "src\<^sub>D \<nu> = trg\<^sub>D \<nu>'"
    shows "C.arr (\<Phi>\<^sub>G.map (\<nu>, \<nu>'))"
    and "src\<^sub>C (\<Phi>\<^sub>G.map (\<nu>, \<nu>')) = src\<^sub>C (G (D.dom \<nu>'))"
    and "trg\<^sub>C (\<Phi>\<^sub>G.map (\<nu>, \<nu>')) = trg\<^sub>C (G (D.cod \<nu>))"
    and "C.dom (\<Phi>\<^sub>G.map (\<nu>, \<nu>')) = G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>')"
    and "C.cod  (\<Phi>\<^sub>G.map (\<nu>, \<nu>')) = G (D.cod \<nu> \<star>\<^sub>D D.cod \<nu>')"
      using assms \<Phi>\<^sub>G_in_hom
          apply auto
      by fast+

    lemma \<Phi>\<^sub>G_map_simp_ide:
    assumes "D.ide f" and "D.ide f'" and "src\<^sub>D f = trg\<^sub>D f'"
    shows "\<Phi>\<^sub>G.map (f, f') = G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> f')) \<cdot>\<^sub>C G (D.inv (\<Phi> (G f, G f'))) \<cdot>\<^sub>C
                            C.inv (\<epsilon> (G f \<star>\<^sub>C G f'))"
    proof -
      have "\<Phi>\<^sub>G.map (f, f') = C.inv (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))"
        using assms \<Phi>\<^sub>G.map_simp_ide D.VV.ide_char D.VV.arr_char \<Phi>\<^sub>G\<^sub>0_def G.FF_def by auto
      also have "... = C.inv (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f')) \<cdot>\<^sub>C G (\<eta> f \<star>\<^sub>D \<eta> f'))"
        using assms D.VV.ide_char D.VV.arr_char cmp_simps(1,4) by simp
      also have "... = C.inv (G (\<eta> f \<star>\<^sub>D \<eta> f')) \<cdot>\<^sub>C C.inv (G (\<Phi> (G f, G f'))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G f \<star>\<^sub>C G f'))"
      proof -
        have "C.iso (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f')) \<cdot>\<^sub>C G (\<eta> f \<star>\<^sub>D \<eta> f'))"
          using assms C.VV.ide_char C.VV.arr_char FF_def
          by (intro C.isos_compose C.seqI) auto
        thus ?thesis
          using assms C.inv_comp_left(1-2) cmp_components_are_iso C.comp_assoc by simp
      qed
      also have "... = G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> f')) \<cdot>\<^sub>C G (D.inv (\<Phi> (G f, G f'))) \<cdot>\<^sub>C
                         C.inv (\<epsilon> (G f \<star>\<^sub>C G f'))"
        using assms cmp_components_are_iso D.ideD(1) D.inv_hcomp D.iso_hcomp
              G.preserves_ide G.preserves_inv G_simps(2-3) \<eta>_simps(2-3,6)
        by metis
      finally show ?thesis by blast
    qed

    lemma \<eta>_hcomp:
    assumes "D.ide f" and "D.ide f'" and "src\<^sub>D f = trg\<^sub>D f'"
    shows "\<eta> (f \<star>\<^sub>D f') = F (\<Phi>\<^sub>G.map (f, f')) \<cdot>\<^sub>D \<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')"
    proof -
      have 1: "\<guillemotleft>F (\<Phi>\<^sub>G.map (f, f')) \<cdot>\<^sub>D \<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f') :
                  f \<star>\<^sub>D f' \<Rightarrow>\<^sub>D F (G (f \<star>\<^sub>D f'))\<guillemotright>"
        using assms by fastforce
      have 2: "\<guillemotleft>\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f')) \<cdot>\<^sub>C G (\<eta> f \<star>\<^sub>D \<eta> f') :
                  G (f \<star>\<^sub>D f') \<Rightarrow>\<^sub>C G f \<star>\<^sub>C G f'\<guillemotright>"
        using assms G.preserves_hom cmp_in_hom(2)
        by (intro C.comp_in_homI) auto
      have "F (\<Phi>\<^sub>G.map (f, f')) \<cdot>\<^sub>D \<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')
              = F (C.inv (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')))) \<cdot>\<^sub>D
                  \<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')"
        using assms \<Phi>\<^sub>G.map_simp_ide D.VV.ide_char D.VV.arr_char \<Phi>\<^sub>G\<^sub>0_def by simp
      also have "... = F (C.inv (G (\<eta> f \<star>\<^sub>D \<eta> f')) \<cdot>\<^sub>C C.inv (G (\<Phi> (G f, G f'))) \<cdot>\<^sub>C
                          C.inv (\<epsilon> (G f \<star>\<^sub>C G f'))) \<cdot>\<^sub>D
                       \<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')"
      proof -
        have "C.inv (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f'))) =
              C.inv (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f')) \<cdot>\<^sub>C G (\<eta> f \<star>\<^sub>D \<eta> f'))"
          using assms 1 by force
        also have "... = C.inv (G (\<eta> f \<star>\<^sub>D \<eta> f')) \<cdot>\<^sub>C C.inv (G (\<Phi> (G f, G f'))) \<cdot>\<^sub>C
                           C.inv (\<epsilon> (G f \<star>\<^sub>C G f'))"
        proof -
          have "C.iso (\<epsilon> (G f \<star>\<^sub>C G f') \<cdot>\<^sub>C G (\<Phi> (G f, G f')) \<cdot>\<^sub>C G (\<eta> f \<star>\<^sub>D \<eta> f'))"
            using assms 2 by (intro C.isos_compose) auto
          thus ?thesis
            using assms 1 C.inv_comp_left C.comp_assoc by simp
        qed
        finally show ?thesis by simp
      qed
      also have "... = F (C.inv (G (\<eta> f \<star>\<^sub>D \<eta> f'))) \<cdot>\<^sub>D
                         F (C.inv (G (\<Phi> (G f, G f')))) \<cdot>\<^sub>D F (C.inv (\<epsilon> (G f \<star>\<^sub>C G f'))) \<cdot>\<^sub>D
                         \<Phi> (G f, G f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')"
      proof -
        have "C.arr ((C.inv (G (\<eta> f \<star>\<^sub>D \<eta> f')) \<cdot>\<^sub>C C.inv (G (\<Phi> (G f, G f'))) \<cdot>\<^sub>C
                               C.inv (\<epsilon> (G f \<star>\<^sub>C G f'))))"
          using assms 1 2 cmp_components_are_iso C.VV.ide_char C.VV.arr_char FF_def
          by (intro C.seqI) auto
        thus ?thesis
          using C.inv_comp_left D.comp_assoc by auto
      qed
      also have "... = D.inv (F (G (\<eta> f \<star>\<^sub>D \<eta> f'))) \<cdot>\<^sub>D
                       D.inv (F (G (\<Phi> (G f, G f')))) \<cdot>\<^sub>D
                       D.inv (F (\<epsilon> (G f \<star>\<^sub>C G f'))) \<cdot>\<^sub>D
                       \<Phi> (G f, G f') \<cdot>\<^sub>D
                       (\<eta> f \<star>\<^sub>D \<eta> f')"
        using assms by (simp add: preserves_inv)
      also have "... = D.inv ((\<eta> (F (G f) \<star>\<^sub>D F (G f'))) \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D
                         D.inv (\<eta> (f \<star>\<^sub>D f'))) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G f \<star>\<^sub>C G f')) \<cdot>\<^sub>D \<Phi> (G f, G f') \<cdot>\<^sub>D
                              D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f')))) \<cdot>\<^sub>D
                       D.inv (F (\<epsilon> (G f \<star>\<^sub>C G f'))) \<cdot>\<^sub>D
                       \<Phi> (G f, G f') \<cdot>\<^sub>D
                       (\<eta> f \<star>\<^sub>D \<eta> f')"
      proof -
        have *: "\<And>\<nu>. D.arr \<nu> \<Longrightarrow> \<eta> (D.cod \<nu>) \<cdot>\<^sub>D \<nu> \<cdot>\<^sub>D D.inv (\<eta> (D.dom \<nu>)) = F (G \<nu>)"
          by (metis (full_types) D.arr_dom D.comp_assoc D.ide_dom D.invert_side_of_triangle(2)
              \<eta>_naturality(1-2) \<eta>_simps(1,6))
        have "F (G (\<eta> f \<star>\<^sub>D \<eta> f')) =
              \<eta> (F (G f) \<star>\<^sub>D F (G f')) \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D D.inv (\<eta> (f \<star>\<^sub>D f'))"
          using assms * [of "\<eta> f \<star>\<^sub>D \<eta> f'"] by simp
        moreover have "F (G (\<Phi> (G f, G f'))) =
                         \<eta> (F (G f \<star>\<^sub>C G f')) \<cdot>\<^sub>D \<Phi> (G f, G f') \<cdot>\<^sub>D D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f')))"
          using assms 1 * [of "\<Phi> (G f, G f')"] cmp_simps(5) by fastforce
        ultimately show ?thesis by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D f') \<cdot>\<^sub>D
                       D.inv (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D
                       ((D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f')))) \<cdot>\<^sub>D (\<eta> (F (G f) \<star>\<^sub>D F (G f')))) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G f, G f')) \<cdot>\<^sub>D
                       ((D.inv (\<eta> (F (G f \<star>\<^sub>C G f')))) \<cdot>\<^sub>D D.inv (F (\<epsilon> (G f \<star>\<^sub>C G f')))) \<cdot>\<^sub>D
                       \<Phi> (G f, G f')) \<cdot>\<^sub>D
                       (\<eta> f \<star>\<^sub>D \<eta> f')"
      proof -
        have "D.inv ((\<eta> (F (G f) \<star>\<^sub>D F (G f'))) \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D D.inv (\<eta> (f \<star>\<^sub>D f')))
                = \<eta> (f \<star>\<^sub>D f') \<cdot>\<^sub>D D.inv (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f')))"
        proof -
          have "D.iso (\<eta> (F (G f) \<star>\<^sub>D F (G f')) \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D D.inv (\<eta> (f \<star>\<^sub>D f')))"
            using assms by (intro D.isos_compose) auto
          thus ?thesis
            using assms D.inv_comp_left D.comp_assoc by simp
        qed
        moreover have
          "D.inv (\<eta> (F (G f \<star>\<^sub>C G f')) \<cdot>\<^sub>D \<Phi> (G f, G f') \<cdot>\<^sub>D D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f')))) =
           \<eta> (F (G f) \<star>\<^sub>D F (G f')) \<cdot>\<^sub>D D.inv (\<Phi> (G f, G f')) \<cdot>\<^sub>D D.inv (\<eta> (F (G f \<star>\<^sub>C G f')))"
        proof -
          have "D.iso (\<eta> (F (G f \<star>\<^sub>C G f')) \<cdot>\<^sub>D \<Phi> (G f, G f') \<cdot>\<^sub>D D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f'))))"
          proof -
            have 1: "D.seq (\<Phi> (G f, G f')) (D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f'))))"
              using assms by (intro D.seqI) auto
            moreover have "D.seq (\<eta> (F (G f \<star>\<^sub>C G f')))
                                 (\<Phi> (G f, G f') \<cdot>\<^sub>D D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f'))))"
              using assms 1 by auto
            ultimately show ?thesis
              using assms cmp_components_are_iso \<eta>_in_hom
                by (intro D.isos_compose) auto
          qed
          thus ?thesis
            using assms D.comp_inv_arr' D.comp_assoc D.inv_comp_left cmp_components_are_iso
            by auto
        qed
        ultimately show ?thesis
          using D.comp_assoc by simp
      qed
      also have "... =  \<eta> (f \<star>\<^sub>D f') \<cdot>\<^sub>D
                        D.inv (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D
                        (D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f'))) \<cdot>\<^sub>D (\<eta> (F (G f) \<star>\<^sub>D F (G f')))) \<cdot>\<^sub>D
                        (D.inv (\<Phi> (G f, G f')) \<cdot>\<^sub>D \<Phi> (G f, G f')) \<cdot>\<^sub>D
                        (\<eta> f \<star>\<^sub>D \<eta> f')"
      proof -
        have "(D.inv (\<eta> (F (G f \<star>\<^sub>C G f')))) \<cdot>\<^sub>D D.inv (F (\<epsilon> (G f \<star>\<^sub>C G f'))) \<cdot>\<^sub>D \<Phi> (G f, G f')
                = F (G f \<star>\<^sub>C G f') \<cdot>\<^sub>D \<Phi> (G f, G f')"
        proof -
          have "(D.inv (\<eta> (F (G f \<star>\<^sub>C G f')))) \<cdot>\<^sub>D D.inv (F (\<epsilon> (G f \<star>\<^sub>C G f')))
                  = D.inv (F (\<epsilon> (G f \<star>\<^sub>C G f')) \<cdot>\<^sub>D \<eta> (F (G f \<star>\<^sub>C G f')))"
            using assms by (simp add: D.inv_comp)
          also have "... = F (G f \<star>\<^sub>C G f')"
            using assms \<eta>\<epsilon>.triangle_G Fo\<epsilon>_\<eta>oF.map_simp_ide by fastforce
          finally show ?thesis using D.comp_assoc by metis
        qed
        also have "... = \<Phi> (G f, G f')"
          using assms D.comp_cod_arr cmp_in_hom(2) [of "G f" "G f'"] by auto
        finally have "(D.inv (\<eta> (F (G f \<star>\<^sub>C G f')))) \<cdot>\<^sub>D D.inv (F (\<epsilon> (G f \<star>\<^sub>C G f'))) \<cdot>\<^sub>D
                      \<Phi> (G f, G f')
                        = \<Phi> (G f, G f')"
          by blast
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D f') \<cdot>\<^sub>D
                       D.inv (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D
                       (D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G f'))) \<cdot>\<^sub>D (\<eta> (F (G f) \<star>\<^sub>D F (G f')))) \<cdot>\<^sub>D
                       (\<eta> f \<star>\<^sub>D \<eta> f')"
        using assms D.comp_cod_arr D.comp_inv_arr' cmp_components_are_iso by simp
      also have "... = \<eta> (f \<star>\<^sub>D f') \<cdot>\<^sub>D D.inv (\<eta> f \<star>\<^sub>D \<eta> f') \<cdot>\<^sub>D (\<eta> f \<star>\<^sub>D \<eta> f')"
        using assms \<eta>_in_hom D.comp_inv_arr' D.comp_cod_arr by simp
      also have "... = \<eta> (f \<star>\<^sub>D f')"
          using assms D.comp_inv_arr' [of "\<eta> f \<star>\<^sub>D \<eta> f'"] D.comp_arr_dom by simp
      finally show ?thesis by simp
    qed

    lemma \<epsilon>_hcomp:
    assumes "C.ide g" and "C.ide g'" and "src\<^sub>C g = trg\<^sub>C g'"
    shows "\<epsilon> (g \<star>\<^sub>C g') = (\<epsilon> g \<star>\<^sub>C \<epsilon> g') \<cdot>\<^sub>C C.inv (\<Phi>\<^sub>G.map (F g, F g')) \<cdot>\<^sub>C C.inv (G (\<Phi> (g, g')))"
    proof -
      have 1: "\<guillemotleft>\<epsilon> (G (F g) \<star>\<^sub>C G (F g')) \<cdot>\<^sub>C G (\<Phi> (G (F g), G (F g')) \<cdot>\<^sub>D (\<eta> (F g) \<star>\<^sub>D \<eta> (F g'))) :
                 G (F g \<star>\<^sub>D F g') \<Rightarrow>\<^sub>C G (F g) \<star>\<^sub>C G (F g')\<guillemotright>"
        using assms by fastforce
      have "(\<epsilon> g \<star>\<^sub>C \<epsilon> g') \<cdot>\<^sub>C C.inv (\<Phi>\<^sub>G.map (F g, F g')) \<cdot>\<^sub>C C.inv (G (\<Phi> (g, g')))
              = (\<epsilon> g \<star>\<^sub>C \<epsilon> g') \<cdot>\<^sub>C
                C.inv (C.inv (\<epsilon> (G (F g) \<star>\<^sub>C G (F g')) \<cdot>\<^sub>C G (\<Phi> (G (F g), G (F g')) \<cdot>\<^sub>D
                                (\<eta> (F g) \<star>\<^sub>D \<eta> (F g'))))) \<cdot>\<^sub>C
                C.inv (G (\<Phi> (g, g')))"
        using assms \<Phi>\<^sub>G.map_simp_ide D.VV.ide_char D.VV.arr_char \<Phi>\<^sub>G\<^sub>0_def by simp
      also have "... = ((\<epsilon> g \<star>\<^sub>C \<epsilon> g') \<cdot>\<^sub>C \<epsilon> (G (F g) \<star>\<^sub>C G (F g'))) \<cdot>\<^sub>C
                       G (\<Phi> (G (F g), G (F g')) \<cdot>\<^sub>D (\<eta> (F g) \<star>\<^sub>D \<eta> (F g'))) \<cdot>\<^sub>C
                       C.inv (G (\<Phi> (g, g')))"
      proof -
        have "C.iso (\<epsilon> (G (F g) \<star>\<^sub>C G (F g')) \<cdot>\<^sub>C G (\<Phi> (G (F g), G (F g')) \<cdot>\<^sub>D
              (\<eta> (F g) \<star>\<^sub>D \<eta> (F g'))))"
          using assms 1
          by (intro C.isos_compose D.isos_compose G.preserves_iso) auto
        thus ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = \<epsilon> (g \<star>\<^sub>C g') \<cdot>\<^sub>C
                       (G (F (\<epsilon> g \<star>\<^sub>C \<epsilon> g')) \<cdot>\<^sub>C G (\<Phi> (G (F g), G (F g')) \<cdot>\<^sub>D
                         (\<eta> (F g) \<star>\<^sub>D \<eta> (F g')))) \<cdot>\<^sub>C
                       C.inv (G (\<Phi> (g, g')))"
      proof -
        have "(\<epsilon> g \<star>\<^sub>C \<epsilon> g') \<cdot>\<^sub>C \<epsilon> (G (F g) \<star>\<^sub>C G (F g')) = \<epsilon> (g \<star>\<^sub>C g') \<cdot>\<^sub>C G (F (\<epsilon> g \<star>\<^sub>C \<epsilon> g'))"
          using assms \<epsilon>_naturality [of "\<epsilon> g \<star>\<^sub>C \<epsilon> g'"] by simp
        thus ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = \<epsilon> (g \<star>\<^sub>C g') \<cdot>\<^sub>C
                       G ((F (\<epsilon> g \<star>\<^sub>C \<epsilon> g') \<cdot>\<^sub>D \<Phi> (G (F g), G (F g'))) \<cdot>\<^sub>D (\<eta> (F g) \<star>\<^sub>D \<eta> (F g'))) \<cdot>\<^sub>C
                       C.inv (G (\<Phi> (g, g')))"
        using assms C.VV.ide_char C.VV.arr_char FF_def D.comp_assoc by auto
      also have "... = \<epsilon> (g \<star>\<^sub>C g') \<cdot>\<^sub>C
                       G (\<Phi> (g, g') \<cdot>\<^sub>D (F (\<epsilon> g) \<star>\<^sub>D F (\<epsilon> g')) \<cdot>\<^sub>D (\<eta> (F g) \<star>\<^sub>D \<eta> (F g'))) \<cdot>\<^sub>C
                       C.inv (G (\<Phi> (g, g')))"
      proof -
        have "F (\<epsilon> g \<star>\<^sub>C \<epsilon> g') \<cdot>\<^sub>D \<Phi> (G (F g), G (F g')) = \<Phi> (g, g') \<cdot>\<^sub>D (F (\<epsilon> g) \<star>\<^sub>D F (\<epsilon> g'))"
          using assms C.VV.arr_char D.VV.ide_char D.VV.arr_char FF_def
                \<Phi>.naturality [of "(\<epsilon> g, \<epsilon> g')"] C.VV.dom_char C.VV.cod_char
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<epsilon> (g \<star>\<^sub>C g') \<cdot>\<^sub>C
                       G (\<Phi> (g, g') \<cdot>\<^sub>D (F (\<epsilon> g) \<cdot>\<^sub>D \<eta> (F g) \<star>\<^sub>D F (\<epsilon> g') \<cdot>\<^sub>D \<eta> (F g'))) \<cdot>\<^sub>C
                       C.inv (G (\<Phi> (g, g')))"
        using assms D.interchange by simp
      also have "... = \<epsilon> (g \<star>\<^sub>C g') \<cdot>\<^sub>C G (\<Phi> (g, g') \<cdot>\<^sub>D (F g \<star>\<^sub>D F g')) \<cdot>\<^sub>C C.inv (G (\<Phi> (g, g')))"
        using assms \<eta>\<epsilon>.triangle_G Fo\<epsilon>_\<eta>oF.map_def [of g] Fo\<epsilon>_\<eta>oF.map_def [of g'] by simp
      also have "... = \<epsilon> (g \<star>\<^sub>C g') \<cdot>\<^sub>C G (\<Phi> (g, g')) \<cdot>\<^sub>C C.inv (G (\<Phi> (g, g')))"
        using assms D.comp_arr_dom cmp_simps(1) cmp_simps(4) by auto
      also have "... = \<epsilon> (g \<star>\<^sub>C g')"
        using assms D.comp_arr_dom C.comp_arr_inv' C.VV.ide_char C.VV.arr_char
              cmp_components_are_iso C.comp_arr_dom
        by simp
      finally show ?thesis by simp
    qed

    lemma G_preserves_hcomp:
    assumes "D.hseq \<nu> \<nu>'"
    shows "G (\<nu> \<star>\<^sub>D \<nu>') = \<Phi>\<^sub>G.map (D.cod \<nu>, D.cod \<nu>') \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>') \<cdot>\<^sub>C
                         C.inv (\<Phi>\<^sub>G.map (D.dom \<nu>, D.dom \<nu>'))"
    proof -
      have "G (\<nu> \<star>\<^sub>D \<nu>') \<cdot>\<^sub>C \<Phi>\<^sub>G.map (D.dom \<nu>, D.dom \<nu>') =
            \<Phi>\<^sub>G.map (D.cod \<nu>, D.cod \<nu>') \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>')"
        using assms \<Phi>\<^sub>G.naturality D.VV.arr_char D.VV.cod_char G.FF_def D.VV.dom_char by auto
      moreover have "C.seq (\<Phi>\<^sub>G.map (D.cod \<nu>, D.cod \<nu>')) (G \<nu> \<star>\<^sub>C G \<nu>')"
      proof
        show "\<guillemotleft>G \<nu> \<star>\<^sub>C G \<nu>' :
                 G (D.dom \<nu>) \<star>\<^sub>C G (D.dom \<nu>') \<Rightarrow>\<^sub>C G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>')\<guillemotright>"
          using assms G_in_hom(2) by auto
        show "\<guillemotleft>\<Phi>\<^sub>G.map (D.cod \<nu>, D.cod \<nu>') :
                 G (D.cod \<nu>) \<star>\<^sub>C G (D.cod \<nu>') \<Rightarrow>\<^sub>C G (D.cod \<nu> \<star>\<^sub>D D.cod \<nu>')\<guillemotright>"
          using assms \<Phi>\<^sub>G\<^sub>0_in_hom \<Phi>\<^sub>G.map_simp_ide D.VV.ide_char D.VV.arr_char by auto
      qed
      moreover have "C.iso (\<Phi>\<^sub>G.map (D.dom \<nu>, D.dom \<nu>'))"
        using assms \<Phi>\<^sub>G.components_are_iso D.VV.ide_char D.VV.arr_char by auto
      ultimately show ?thesis
        using assms \<Phi>\<^sub>G.components_are_iso C.comp_assoc
              C.invert_side_of_triangle(2)
                [of "\<Phi>\<^sub>G.map (D.cod \<nu>, D.cod \<nu>') \<cdot>\<^sub>C (G \<nu> \<star>\<^sub>C G \<nu>')"
                    "G (\<nu> \<star>\<^sub>D \<nu>')" "\<Phi>\<^sub>G.map (D.dom \<nu>, D.dom \<nu>')"]
        by simp
    qed

    lemma coherence_LHS:
    assumes "D.ide f" and "D.ide g" and "D.ide h"
    and "src\<^sub>D f = trg\<^sub>D g" and "src\<^sub>D g = trg\<^sub>D h"
    shows "F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>G.map (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>G.map (f, g) \<star>\<^sub>C G h))
             = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
               \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
               (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
    proof -
      have "F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>G.map (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>G.map (f, g) \<star>\<^sub>C G h))
              = F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C
                (G (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>C
                G (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h))) \<cdot>\<^sub>C
                C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)) \<cdot>\<^sub>C
                (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<cdot>\<^sub>C
                G (D.inv (\<Phi> (G f, G g))) \<cdot>\<^sub>C
                C.inv (\<epsilon> (G f \<star>\<^sub>C G g)) \<star>\<^sub>C G h))"
        using assms \<Phi>\<^sub>G_map_simp_ide C.comp_assoc by simp
      also have "... = F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C
                       (G (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>C
                       G (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)) \<cdot>\<^sub>C
                       (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>C G h) \<cdot>\<^sub>C
                       (G (D.inv (\<Phi> (G f, G g))) \<star>\<^sub>C G h) \<cdot>\<^sub>C
                       (C.inv (\<epsilon> (G f \<star>\<^sub>C G g)) \<star>\<^sub>C G h))"
        using assms C.whisker_right D.comp_assoc by simp
      also have "... = F (G \<a>\<^sub>D[f, g, h]) \<cdot>\<^sub>D
                       F (G (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       F (G (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>C G h) \<cdot>\<^sub>D
                       F (G (D.inv (\<Phi> (G f, G g))) \<star>\<^sub>C G h) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g)) \<star>\<^sub>C G h)"
      proof -
        have "C.arr (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C
                     (G (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>C
                     G (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h))) \<cdot>\<^sub>C
                     C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)) \<cdot>\<^sub>C
                     (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>C G h) \<cdot>\<^sub>C
                     (G (D.inv (\<Phi> (G f, G g))) \<star>\<^sub>C G h) \<cdot>\<^sub>C
                     (C.inv (\<epsilon> (G f \<star>\<^sub>C G g)) \<star>\<^sub>C G h))"
          using assms \<Phi>\<^sub>G_simps G.FF_def G\<^sub>0_props by auto
        thus ?thesis
          by (metis C.seqE preserves_comp_2)
      qed
      also have "... = F (G \<a>\<^sub>D[f, g, h]) \<cdot>\<^sub>D
                       F (G (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       F (G (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       (\<Phi> (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                       (F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       ((D.inv (\<Phi> (G (F (G f) \<star>\<^sub>D F (G g)), G h))) \<cdot>\<^sub>D
                       (\<Phi> (G (F (G f) \<star>\<^sub>D F (G g)), G h)) \<cdot>\<^sub>D
                       (F (G (D.inv (\<Phi> (G f, G g)))) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       ((D.inv (\<Phi> (G (F (G f \<star>\<^sub>C G g)), G h))) \<cdot>\<^sub>D
                       (\<Phi> (G (F (G f \<star>\<^sub>C G g)), G h)) \<cdot>\<^sub>D
                       (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h)))"
        using assms G\<^sub>0_props preserves_hcomp FF_def D.comp_assoc by auto
      also have "... = F (G \<a>\<^sub>D[f, g, h]) \<cdot>\<^sub>D
                       F (G (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       F (G (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       (\<Phi> (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                       (F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (F (G (D.inv (\<Phi> (G f, G g)))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h)))"
       proof -
        have "((D.inv (\<Phi> (G (F (G f) \<star>\<^sub>D F (G g)), G h))) \<cdot>\<^sub>D
              (\<Phi> (G (F (G f) \<star>\<^sub>D F (G g)), G h))) \<cdot>\<^sub>D
              (F (G (D.inv (\<Phi> (G f, G g)))) \<star>\<^sub>D F (G h))
                = F (G (D.inv (\<Phi> (G f, G g)))) \<star>\<^sub>D F (G h)"
          using assms \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char G\<^sub>0_props FF_def
                D.comp_inv_arr' D.comp_cod_arr
          by simp
        moreover have "(D.inv (\<Phi> (G (F (G f \<star>\<^sub>C G g)), G h)) \<cdot>\<^sub>D
                       \<Phi> (G (F (G f \<star>\<^sub>C G g)), G h)) \<cdot>\<^sub>D
                       (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) =
                         F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)"
          using assms D.comp_cod_arr \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char
                G\<^sub>0_props FF_def D.comp_inv_arr'
          by simp
        ultimately show ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                       ((D.inv (\<eta> ((f \<star>\<^sub>D g) \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       (\<eta> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D
                       (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       (((D.inv (\<eta> (F (G (f \<star>\<^sub>D g)) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (\<eta> (F (G (f \<star>\<^sub>D g)) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h))) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       (\<Phi> (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                       ((\<eta> (f \<star>\<^sub>D g) \<cdot>\<^sub>D
                       (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G g)))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       ((\<eta> (F (G f) \<star>\<^sub>D F (G g)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g)) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G f \<star>\<^sub>C G g)))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h)))"
      proof -
        have "\<And>\<nu>. D.arr \<nu> \<Longrightarrow> F (G \<nu>) = \<eta> (D.cod \<nu>) \<cdot>\<^sub>D \<nu> \<cdot>\<^sub>D D.inv (\<eta> (D.dom \<nu>))"
          by (metis (full_types) D.arr_dom D.comp_assoc D.ide_dom D.invert_side_of_triangle(2)
              \<eta>_naturality(1-2) \<eta>_simps(1,6))
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                       (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       (\<Phi> (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                       ((\<eta> (f \<star>\<^sub>D g) \<cdot>\<^sub>D
                       (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (\<eta> (F (G f) \<star>\<^sub>D F (G g)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g)) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h)))"
      proof -
        have "(D.inv (\<eta> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D \<eta> ((f \<star>\<^sub>D g) \<star>\<^sub>D h)) \<cdot>\<^sub>D
              (D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))
                = D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h)"
          using assms D.comp_inv_arr' D.comp_cod_arr \<eta>_in_hom by simp
        moreover have "((D.inv (\<eta> (F (G (f \<star>\<^sub>D g)) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       \<eta> (F (G (f \<star>\<^sub>D g)) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h))
                         = D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h))"
          using assms D.comp_inv_arr' D.comp_cod_arr by simp
        ultimately show ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                       ((D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                       D.inv (\<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                       (\<Phi> (G (f \<star>\<^sub>D g), G h) \<cdot>\<^sub>D
                       (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (((D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))))"
      proof -
        have "(\<eta> (f \<star>\<^sub>D g) \<cdot>\<^sub>D
              (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<cdot>\<^sub>D
              D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
              (\<eta> (F (G f) \<star>\<^sub>D F (G g)) \<cdot>\<^sub>D
              D.inv (\<Phi> (G f, G g)) \<cdot>\<^sub>D
              D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))
                = (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                  ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                  (((D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                  (\<eta> (F (G f) \<star>\<^sub>D F (G g)) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                  (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                  (D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))"
          using assms D.comp_assoc D.whisker_right by simp
        also have "... = (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                         ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                         (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                         (D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))"
        proof -
          have "((D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                (\<eta> (F (G f) \<star>\<^sub>D F (G g)) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h))
                  = D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)"
            using assms D.comp_inv_arr' D.comp_cod_arr
                  D.interchange [of "D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G g)))" "\<eta> (F (G f) \<star>\<^sub>D F (G g))"
                                    "F (G h)" "F (G h)"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        finally show ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                       ((D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                       ((D.inv (\<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       \<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                       (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
      proof -
        have "((D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
              (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
              D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))
                = D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
        proof -
          have "((D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                (F (C.inv (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))
                  = ((D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                    (D.inv (F (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                    D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
            using assms by (simp add: preserves_inv)
          also have "... = (D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<cdot>\<^sub>D
                           D.inv (F (\<epsilon> (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h) \<cdot>\<^sub>D F (G h)) \<cdot>\<^sub>D
                           D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
            using assms \<Phi>.components_are_iso
                  D.interchange [of "D.inv (\<eta> (F (G f \<star>\<^sub>C G g)))" "D.inv (F (\<epsilon> (G f \<star>\<^sub>C G g)))"
                                    "F (G h)" "F (G h)"]
            by simp
          also have "... = (D.inv (F (\<epsilon> (G f \<star>\<^sub>C G g)) \<cdot>\<^sub>D \<eta> (F (G f \<star>\<^sub>C G g))) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                           D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
          proof -
            have "D.iso (F (\<epsilon> (G f \<star>\<^sub>C G g)) \<cdot>\<^sub>D \<eta> (F (G f \<star>\<^sub>C G g)))"
              using assms by auto
            hence "D.inv (\<eta> (F (G f \<star>\<^sub>C G g))) \<cdot>\<^sub>D D.inv (F (\<epsilon> (G f \<star>\<^sub>C G g))) =
                  D.inv (F (\<epsilon> (G f \<star>\<^sub>C G g)) \<cdot>\<^sub>D \<eta> (F (G f \<star>\<^sub>C G g)))"
              using assms by (simp add: D.inv_comp_right(1))
            thus ?thesis
              using assms by simp
          qed
          also have "... = (F (G f \<star>\<^sub>C G g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
            using assms \<eta>\<epsilon>.triangle_G Fo\<epsilon>_\<eta>oF.map_def [of "G f \<star>\<^sub>C G g"] by simp
          also have "... = D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
            using assms D.comp_cod_arr by simp
          finally show ?thesis by simp
        qed
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                       ((D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       ((D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                       \<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
                       (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
      proof -
        have "((D.inv (\<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))))) \<cdot>\<^sub>D
              (\<Phi> (G (f \<star>\<^sub>D g), G h))
                = \<Phi> (G (f \<star>\<^sub>D g), G h)"
        proof -
          have "D.inv (\<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D F (C.inv (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) =
                D.inv (\<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h))) \<cdot>\<^sub>D D.inv (F (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)))"
            using assms preserves_inv by simp
          also have "... = D.inv (F (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)) \<cdot>\<^sub>D \<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)))"
          proof -
            have "D.iso (F (\<epsilon> (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)) \<cdot>\<^sub>D \<eta> (F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)))"
              using assms by auto
            thus ?thesis
              using assms D.inv_comp_right(1) by simp
          qed
          also have "... = F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)"
            using assms \<eta>\<epsilon>.triangle_G Fo\<epsilon>_\<eta>oF.map_def [of "G (f \<star>\<^sub>D g) \<star>\<^sub>C G h"] by simp
          finally show ?thesis
            using assms D.comp_cod_arr [of "\<Phi> (G (f \<star>\<^sub>D g), G h)" "F (G (f \<star>\<^sub>D g) \<star>\<^sub>C G h)"]
            by fastforce
        qed
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                       (((D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D
                       (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
      proof -
        have "((D.inv (\<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D \<Phi> (G (f \<star>\<^sub>D g), G h)) \<cdot>\<^sub>D
              (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h)))
                = \<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h)"
          using assms D.comp_inv_arr' \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char
                G\<^sub>0_props FF_def D.comp_cod_arr
          by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       (\<a>\<^sub>D[f, g, h] \<cdot>\<^sub>D
                       ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
      proof -
        have "((D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
              ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h))
                = (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D D.inv (\<eta> h)"
        proof -
          have "(D.inv (\<eta> (f \<star>\<^sub>D g)) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D (\<eta> (f \<star>\<^sub>D g) \<star>\<^sub>D F (G h))
                  = (f \<star>\<^sub>D g) \<star>\<^sub>D D.inv (\<eta> h)"
            using assms D.comp_inv_arr' D.comp_arr_dom
                  D.interchange [of "D.inv (\<eta> (f \<star>\<^sub>D g))" "\<eta> (f \<star>\<^sub>D g)" "D.inv (\<eta> h)" "F (G h)"]
                  D.invert_side_of_triangle(2)
            by simp
          moreover have "((f \<star>\<^sub>D g) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D
                         ((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D F (G h))
                           = (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)) \<star>\<^sub>D D.inv (\<eta> h)"
            using assms D.comp_cod_arr D.comp_arr_dom
                  D.interchange [of "f \<star>\<^sub>D g" "D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g)" "D.inv (\<eta> h)" "F (G h)"]
            by simp
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D
                       \<a>\<^sub>D[F (G f), F (G g), F (G h)]) \<cdot>\<^sub>D
                       (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
        using assms D.assoc_naturality [of "D.inv (\<eta> f)" "D.inv (\<eta> g)" "D.inv (\<eta> h)"]
              D.comp_assoc
        by simp
      finally show ?thesis
        using D.comp_assoc by simp
    qed

    lemma coherence_RHS:
    assumes "D.ide f" and "D.ide g" and "D.ide h"
    and "src\<^sub>D f = trg\<^sub>D g" and "src\<^sub>D g = trg\<^sub>D h"
    shows "F (\<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h)))
             = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
               (F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h))) \<cdot>\<^sub>D
               D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))"
    proof -
      have "F (\<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h)))
              = F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>C
                G (D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>C
                C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))) \<cdot>\<^sub>C
                (G f \<star>\<^sub>C G (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>C
                        G (D.inv (\<Phi> (G g, G h))) \<cdot>\<^sub>C
                        C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))"
        using assms \<Phi>\<^sub>G_map_simp_ide C.comp_assoc by simp
      also have "... = F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>C
                       G (D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>C
                       C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))) \<cdot>\<^sub>C
                       (G f \<star>\<^sub>C G (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>C
                       (G f \<star>\<^sub>C G (D.inv (\<Phi> (G g, G h)))) \<cdot>\<^sub>C
                       (G f \<star>\<^sub>C C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))"
        using assms C.whisker_left by simp
      also have "... = F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       F (G (D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h))))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       F (G f \<star>\<^sub>C G (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       F (G f \<star>\<^sub>C G (D.inv (\<Phi> (G g, G h)))) \<cdot>\<^sub>D
                       F (G f \<star>\<^sub>C C.inv (\<epsilon> (G g \<star>\<^sub>C G h)))"
      proof -
        have "C.arr (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>C
                     G (D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>C
                     C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))) \<cdot>\<^sub>C
                     (G f \<star>\<^sub>C G (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>C
                     (G f \<star>\<^sub>C G (D.inv (\<Phi> (G g, G h)))) \<cdot>\<^sub>C
                     (G f \<star>\<^sub>C C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))"
          using assms G\<^sub>0_props by auto
        thus ?thesis
          using assms by (metis C.seqE preserves_comp_2)
      qed
      also have "... = F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       F (G (D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h))))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       (\<Phi> (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (G (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)))) \<cdot>\<^sub>D
                       ((D.inv (\<Phi> (G f, G (F (G g) \<star>\<^sub>D F (G h))))) \<cdot>\<^sub>D
                       (\<Phi> (G f, G (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (G (D.inv (\<Phi> (G g, G h)))))) \<cdot>\<^sub>D
                       ((D.inv (\<Phi> (G f, G (F (G g \<star>\<^sub>C G h))))) \<cdot>\<^sub>D
                       (\<Phi> (G f, G (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h)))"
        using assms preserves_hcomp G\<^sub>0_props D.comp_assoc by simp
      also have "... = F (G (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       F (G (D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h))))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       (\<Phi> (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (G (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (G (D.inv (\<Phi> (G g, G h))))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h)))"
      proof -
        have "D.inv (\<Phi> (G f, G (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                     \<Phi> (G f, G (F (G g) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D
                     (F (G f) \<star>\<^sub>D F (G (D.inv (\<Phi> (G g, G h)))))
                = (F (G f) \<star>\<^sub>D F (G (D.inv (\<Phi> (G g, G h)))))"
        proof -
          have "D.inv (\<Phi> (G f, G (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D \<Phi> (G f, G (F (G g) \<star>\<^sub>D F (G h)))
                  = F (G f) \<star>\<^sub>D F (G (F (G g) \<star>\<^sub>D F (G h)))"
            using assms D.comp_inv_arr D.inv_is_inverse G\<^sub>0_props FF_def by simp
          moreover have "... = D.cod (F (G f) \<star>\<^sub>D F (G (D.inv (\<Phi> (G g, G h)))))"
            using assms G\<^sub>0_props by simp
          moreover have "D.hseq (F (G f)) (F (G (D.inv (\<Phi> (G g, G h)))))"
            using assms G\<^sub>0_props by auto
          ultimately show ?thesis
            using assms D.comp_assoc
                  D.comp_cod_arr [of "F (G f) \<star>\<^sub>D F (G (D.inv (\<Phi> (G g, G h))))"
                                     "F (G f) \<star>\<^sub>D F (G (F (G g) \<star>\<^sub>D F (G h)))"]
            by metis
        qed
        moreover have "D.inv (\<Phi> (G f, G (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       (\<Phi> (G f, G (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))
                         = (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))"
        proof -
          have "D.inv (\<Phi> (G f, G (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D \<Phi> (G f, G (F (G g \<star>\<^sub>C G h)))
                  = F (G f) \<star>\<^sub>D F (G (F (G g \<star>\<^sub>C G h)))"
            using assms D.comp_inv_arr D.inv_is_inverse G\<^sub>0_props by simp
          moreover have "... = D.cod (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))"
            using assms by simp
          moreover have "D.hseq (F (G f)) (F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))"
            using assms by (intro D.hseqI') auto
          ultimately show ?thesis
            using assms D.comp_assoc
                  D.comp_cod_arr [of "F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h)))"
                                     "F (G f) \<star>\<^sub>D F (G (F (G g \<star>\<^sub>C G h)))"]
            by metis
        qed
        ultimately show ?thesis by simp
      qed
      also have "... = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       ((D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G (g \<star>\<^sub>D h))))) \<cdot>\<^sub>D
                       \<eta> (F (G f) \<star>\<^sub>D F (G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       ((D.inv (\<eta> (F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       F (C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))))) \<cdot>\<^sub>D
                       \<Phi> (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D
                          \<eta> (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                          (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D
                          D.inv (\<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D
                          \<eta> (F (G g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                          D.inv (\<Phi> (G g, G h)) \<cdot>\<^sub>D
                          D.inv (\<eta> (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))"
      proof -
        have "\<And>\<nu>. D.arr \<nu> \<Longrightarrow> F (G \<nu>) = \<eta> (D.cod \<nu>) \<cdot>\<^sub>D \<nu> \<cdot>\<^sub>D D.inv (\<eta> (D.dom \<nu>))"
          by (metis (full_types) D.arr_dom D.comp_assoc D.ide_dom D.invert_side_of_triangle(2)
              \<eta>_naturality(1-2) \<eta>_simps(1,6))
        thus ?thesis
          using assms D.comp_assoc by simp
      qed
      also have "... = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       \<Phi> (G f, G (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D
                          \<eta> (g \<star>\<^sub>D h) \<cdot>\<^sub>D
                          (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D
                          D.inv (\<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D
                          \<eta> (F (G g) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                          D.inv (\<Phi> (G g, G h)) \<cdot>\<^sub>D
                          D.inv (\<eta> (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))"
      proof -
        have "D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D \<eta> (F (G f) \<star>\<^sub>D F (G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
              D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))
                = D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))"
        proof -
          have "D.inv (\<eta> (F (G f) \<star>\<^sub>D F (G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D \<eta> (F (G f) \<star>\<^sub>D F (G (g \<star>\<^sub>D h))) =
                F (G f) \<star>\<^sub>D F (G (g \<star>\<^sub>D h))"
            using assms D.comp_inv_arr D.inv_is_inverse by simp
          moreover have "... = D.cod (D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h))))"
            using assms by simp
          ultimately show ?thesis
            using assms D.comp_cod_arr [of "D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))"]
            by (metis D.arr_inv D.comp_assoc D.hcomp_simps(2) D.ideD(1) D.ide_hcomp
                G.preserves_ide G_simps(2) G_simps(3) cmp_components_are_iso)
        qed
        moreover have "(D.inv (\<eta> (F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                          F (C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))))) \<cdot>\<^sub>D
                       \<Phi> (G f, G (g \<star>\<^sub>D h))
                         = \<Phi> (G f, G (g \<star>\<^sub>D h))"
        proof -
          have "D.inv (\<eta> (F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D F (C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))))
                  = F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))"
          proof -
            have "D.inv (\<eta> (F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D F (C.inv (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) =
                  D.inv (\<eta> (F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D D.inv (F (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))))"
              using assms by (simp add: preserves_inv)
            also have "... = D.inv (F (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D \<eta> (F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))))"
            proof -
              have "D.iso (F (\<epsilon> (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D \<eta> (F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))))"
                using assms by auto
              thus ?thesis
                using assms by (simp add: D.inv_comp_right(1))
            qed
            also have "... = F (G f \<star>\<^sub>C G (g \<star>\<^sub>D h))"
              using assms Fo\<epsilon>_\<eta>oF.map_def [of "G f \<star>\<^sub>C G (g \<star>\<^sub>D h)"] \<eta>\<epsilon>.triangle_G by simp
            finally show ?thesis by blast
          qed
          moreover have "... = D.cod (\<Phi> (G f, G (g \<star>\<^sub>D h)))"
            using assms by simp
          moreover have "D.arr (\<Phi> (G f, G (g \<star>\<^sub>D h)))"
            using assms by auto
          ultimately show ?thesis
            using D.comp_cod_arr by simp
        qed
        ultimately show ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       ((D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       \<Phi> (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D \<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)) \<cdot>\<^sub>D
                       (((F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D \<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h)))) \<cdot>\<^sub>D
                       ((F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))"
        using assms D.whisker_left D.comp_assoc by simp
      also have "... = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       (((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D \<eta> (g \<star>\<^sub>D h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))"
      proof -
        have "(D.inv (\<Phi> (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D \<Phi> (G f, G (g \<star>\<^sub>D h))) \<cdot>\<^sub>D (F (G f) \<star>\<^sub>D \<eta> (g \<star>\<^sub>D h))
                = (F (G f) \<star>\<^sub>D \<eta> (g \<star>\<^sub>D h))"
          using assms D.comp_inv_arr' G\<^sub>0_props D.comp_cod_arr by simp
        moreover have "((F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D \<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h)))
                         = F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h))"
        proof -
          have "(F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                (F (G f) \<star>\<^sub>D \<eta> (F (G g) \<star>\<^sub>D F (G h)))
                  = F (G f) \<star>\<^sub>D F (G g) \<star>\<^sub>D F (G h)"
          proof -
            have "(F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g) \<star>\<^sub>D F (G h)))) \<cdot>\<^sub>D
                  (F (G f) \<star>\<^sub>D \<eta> (F (G g) \<star>\<^sub>D F (G h)))
                    = F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g) \<star>\<^sub>D F (G h))) \<cdot>\<^sub>D \<eta> (F (G g) \<star>\<^sub>D F (G h))"
              using assms D.interchange [of "F (G f)" "F (G f)"] by simp
            also have "... = F (G f) \<star>\<^sub>D F (G g) \<star>\<^sub>D F (G h)"
              using assms D.comp_inv_arr' by simp
            finally show ?thesis by blast
          qed
          moreover have "... = D.cod (F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h)))"
            using assms by simp
          moreover have "D.arr (F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h)))"
            using assms by simp
          ultimately show ?thesis
            using D.comp_cod_arr by simp
        qed
        moreover have "((F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))
                         = D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))"
        proof -
          have "(F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))
                  = F (G f) \<star>\<^sub>D F (G g \<star>\<^sub>C G h)"
          proof -
            have "(F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g \<star>\<^sub>C G h)))) \<cdot>\<^sub>D
                  (F (G f) \<star>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h))))
                    = F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g \<star>\<^sub>C G h))) \<cdot>\<^sub>D F (C.inv (\<epsilon> (G g \<star>\<^sub>C G h)))"
              using assms D.interchange [of "F (G f)" "F (G f)"] by simp
            also have "... = F (G f) \<star>\<^sub>D D.inv (\<eta> (F (G g \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                                        D.inv (F (\<epsilon> (G g \<star>\<^sub>C G h)))"
              using assms preserves_inv by simp
            also have "... = F (G f) \<star>\<^sub>D D.inv (F (\<epsilon> (G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D \<eta> (F (G g \<star>\<^sub>C G h)))"
            proof -
              have "D.iso (F (\<epsilon> (G g \<star>\<^sub>C G h)) \<cdot>\<^sub>D \<eta> (F (G g \<star>\<^sub>C G h)))"
                using assms by auto
              thus ?thesis
                using assms by (simp add: D.inv_comp_right(1))
            qed
            also have "... = F (G f) \<star>\<^sub>D F (G g \<star>\<^sub>C G h)"
              using assms \<eta>\<epsilon>.triangle_G Fo\<epsilon>_\<eta>oF.map_def [of "G g \<star>\<^sub>C G h"] by simp
            finally show ?thesis by blast
          qed
          thus ?thesis using assms D.comp_cod_arr by simp
        qed
        ultimately show ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                       (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                       (F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))"
      proof -
        have "((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
              (F (G f) \<star>\<^sub>D \<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
              (F (G f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))
                = D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)"
          using assms D.comp_cod_arr D.comp_arr_dom D.interchange
        proof -
          have "((D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                (F (G f) \<star>\<^sub>D \<eta> (g \<star>\<^sub>D h))) \<cdot>\<^sub>D
                (F (G f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))
                  = (D.inv (\<eta> f) \<cdot>\<^sub>D F (G f) \<star>\<^sub>D D.inv (\<eta> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D \<eta> (g \<star>\<^sub>D h)) \<cdot>\<^sub>D
                    (F (G f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))"
            using assms D.interchange by simp
          also have "... = (D.inv (\<eta> f) \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D (F (G f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))"
            using assms D.comp_inv_arr' D.comp_arr_dom by simp
          also have "... = D.inv (\<eta> f) \<cdot>\<^sub>D F (G f) \<star>\<^sub>D (g \<star>\<^sub>D h) \<cdot>\<^sub>D (D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))"
            using assms D.interchange by simp
          also have "... = D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h)"
            using assms D.comp_arr_dom D.comp_cod_arr by simp
          finally show ?thesis by simp
        qed
        thus ?thesis
          using D.comp_assoc by simp
      qed
      finally show ?thesis by blast
    qed

    interpretation G: pseudofunctor
                        V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G.map
    proof
      show "\<And>f g h. \<lbrakk>D.ide f; D.ide g; D.ide h; src\<^sub>D f = trg\<^sub>D g; src\<^sub>D g = trg\<^sub>D h\<rbrakk>
                      \<Longrightarrow> G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>G.map (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>G.map (f, g) \<star>\<^sub>C G h) =
                          \<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h]"
      proof -
        fix f g h
        assume f: "D.ide f" and g: "D.ide g" and h: "D.ide h"
        assume fg: "src\<^sub>D f = trg\<^sub>D g" and gh: "src\<^sub>D g = trg\<^sub>D h"
        have "F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>G.map (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>G.map (f, g) \<star>\<^sub>C G h)) =
              F (\<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h])"
        proof -
          have "F (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>G.map (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>G.map (f, g) \<star>\<^sub>C G h))
                  = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                    (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                    \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D
                    (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                    D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))"
            using f g h fg gh coherence_LHS by simp
          also have "... = (\<eta> (f \<star>\<^sub>D g \<star>\<^sub>D h) \<cdot>\<^sub>D
                           (D.inv (\<eta> f) \<star>\<^sub>D D.inv (\<eta> g) \<star>\<^sub>D D.inv (\<eta> h))) \<cdot>\<^sub>D
                           ((F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h))) \<cdot>\<^sub>D
                           D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                           F \<a>\<^sub>C[G f, G g, G h]"
          proof -
            have "\<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D (D.inv (\<Phi> (G f, G g)) \<star>\<^sub>D F (G h)) \<cdot>\<^sub>D
                  D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h))
                    = \<a>\<^sub>D[F (G f), F (G g), F (G h)] \<cdot>\<^sub>D D.inv (\<Phi> (G f \<star>\<^sub>C G g, G h) \<cdot>\<^sub>D
                      (\<Phi> (G f, G g) \<star>\<^sub>D F (G h)))"
            proof -
              have "D.iso (\<Phi> (G f \<star>\<^sub>C G g, G h) \<cdot>\<^sub>D (\<Phi> (G f, G g) \<star>\<^sub>D F (G h)))"
                using f g h fg gh \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char FF_def
                by (intro D.iso_hcomp D.isos_compose D.seqI) auto
              thus ?thesis
                using f g h fg gh
                by (simp add: C.VV.arr_char D.inv_comp_right(1))
            qed
            also have "... = D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D (F (G f) \<star>\<^sub>D \<Phi> (G g, G h))) \<cdot>\<^sub>D
                             F \<a>\<^sub>C[G f, G g, G h]"
              using f g h fg gh cmp_simps assoc_coherence D.comp_assoc D.isos_compose
                    \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char FF_def
                    D.invert_opposite_sides_of_square
              by simp
            also have "... = ((F (G f) \<star>\<^sub>D D.inv (\<Phi> (G g, G h))) \<cdot>\<^sub>D
                                          D.inv (\<Phi> (G f, G g \<star>\<^sub>C G h))) \<cdot>\<^sub>D
                             F \<a>\<^sub>C[G f, G g, G h]"
            proof -
              have "D.iso (\<Phi> (G f, G g \<star>\<^sub>C G h) \<cdot>\<^sub>D (F (G f) \<star>\<^sub>D \<Phi> (G g, G h)))"
                using f g h fg gh \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char FF_def
                by auto
              thus ?thesis
                using f g h fg gh \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char FF_def
                by (simp add: C.VV.arr_char D.comp_assoc D.inv_comp_right(1))
            qed
            finally show ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = F (\<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h))) \<cdot>\<^sub>D
                           F \<a>\<^sub>C[G f, G g, G h]"
            using f g h fg gh coherence_RHS D.comp_assoc by simp
          also have "... = F ((\<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h))) \<cdot>\<^sub>C
                           \<a>\<^sub>C[G f, G g, G h])"
            using f g h fg gh \<Phi>\<^sub>G_simps by auto
          also have "... = F (\<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h)) \<cdot>\<^sub>C
                           \<a>\<^sub>C[G f, G g, G h])"
            using C.comp_assoc by simp
          finally show ?thesis by simp
        qed
        moreover have "C.par (G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>G.map (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C
                               (\<Phi>\<^sub>G.map (f, g) \<star>\<^sub>C G h))
                             (\<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h])"
          using f g h fg gh \<Phi>\<^sub>G_simps by auto
        ultimately show "G \<a>\<^sub>D[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>G.map (f \<star>\<^sub>D g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>G.map (f, g) \<star>\<^sub>C G h) =
                         \<Phi>\<^sub>G.map (f, g \<star>\<^sub>D h) \<cdot>\<^sub>C (G f \<star>\<^sub>C \<Phi>\<^sub>G.map (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[G f, G g, G h]"
          using is_faithful by blast
      qed
    qed

    interpretation GF: composite_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi> G \<Phi>\<^sub>G.map
      ..
    interpretation FG: composite_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G.map F \<Phi>
      ..
    interpretation I\<^sub>C: identity_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C ..
    interpretation I\<^sub>D: identity_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D ..

    lemma \<eta>_equals_FG_unit:
    assumes "D.obj a"
    shows "\<eta> a = FG.unit a"
    proof (intro FG.unit_eqI)
      show "D.obj a" by fact
      show "D.iso (\<eta> a)"
        using assms by auto
      show "\<guillemotleft>\<eta> a : FG.map\<^sub>0 a \<Rightarrow>\<^sub>D FG.map a\<guillemotright>"
        using assms \<eta>_in_hom [of a] FG.map\<^sub>0_def G\<^sub>0_props D.obj_def
        by (metis D.ideD(2) D.ideD(3) D.objE D.vconn_implies_hpar(3) \<eta>.preserves_cod
            \<eta>_simps(5))
      show "\<eta> a \<cdot>\<^sub>D \<i>\<^sub>D[FG.map\<^sub>0 a] = (FG.map \<i>\<^sub>D[a] \<cdot>\<^sub>D FG.cmp (a, a)) \<cdot>\<^sub>D (\<eta> a \<star>\<^sub>D \<eta> a)"
      proof -
        have "(FG.map \<i>\<^sub>D[a] \<cdot>\<^sub>D FG.cmp (a, a)) \<cdot>\<^sub>D (\<eta> a \<star>\<^sub>D \<eta> a) =
              F (G \<i>\<^sub>D[a]) \<cdot>\<^sub>D FG.cmp (a, a) \<cdot>\<^sub>D (\<eta> a \<star>\<^sub>D \<eta> a)"
          using assms D.comp_assoc by simp
        also have "... = F (G \<i>\<^sub>D[a]) \<cdot>\<^sub>D F (G (I\<^sub>D.cmp (a, a))) \<cdot>\<^sub>D F (\<Phi>\<^sub>G.map (a, a)) \<cdot>\<^sub>D
                         \<Phi> (G a, G a) \<cdot>\<^sub>D (\<eta> a \<star>\<^sub>D \<eta> a)"
          using assms FG.cmp_def D.comp_assoc D.VV.arr_char D.VV.dom_char D.VV.cod_char
          by auto
        also have "... = F (G \<i>\<^sub>D[a]) \<cdot>\<^sub>D F (G (I\<^sub>D.cmp (a, a))) \<cdot>\<^sub>D \<eta> (a \<star>\<^sub>D a)"
          using assms \<eta>_hcomp by auto
        also have "... = F (G \<i>\<^sub>D[a]) \<cdot>\<^sub>D \<eta> (a \<star>\<^sub>D a)"
          using assms D.comp_cod_arr by auto
        also have "... = \<eta> a \<cdot>\<^sub>D \<i>\<^sub>D[a]"
          using assms \<eta>_naturality [of "\<i>\<^sub>D[a]"] by simp
        also have "... = \<eta> a \<cdot>\<^sub>D \<i>\<^sub>D[FG.map\<^sub>0 a]"
          using assms \<open>\<guillemotleft>\<eta> a : FG.map\<^sub>0 a \<Rightarrow>\<^sub>D FG.map a\<guillemotright>\<close> by fastforce
        finally show ?thesis by simp
      qed
    qed

    lemma \<epsilon>_hcomp':
    assumes "C.ide g" and "C.ide f" and "src\<^sub>C g = trg\<^sub>C f"
    shows "\<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C GF.cmp (g, f) = \<epsilon> g \<star>\<^sub>C \<epsilon> f"
    proof -
      have "\<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C GF.cmp (g, f)
              = (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C C.inv (\<Phi>\<^sub>G.map (F g, F f)) \<cdot>\<^sub>C C.inv (G (\<Phi> (g, f))) \<cdot>\<^sub>C
                G (F (g \<star>\<^sub>C f)) \<cdot>\<^sub>C G (\<Phi> (g, f)) \<cdot>\<^sub>C \<Phi>\<^sub>G.map (F g, F f)"
        using assms \<epsilon>_hcomp GF.cmp_def C.VV.arr_char C.comp_cod_arr
              C.comp_inv_arr' C.comp_assoc C.VV.dom_char C.VV.cod_char
        by simp
      also have "... = (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C C.inv (\<Phi>\<^sub>G.map (F g, F f)) \<cdot>\<^sub>C (C.inv (G (\<Phi> (g, f))) \<cdot>\<^sub>C
                       G (F (g \<star>\<^sub>C f)) \<cdot>\<^sub>C G (\<Phi> (g, f))) \<cdot>\<^sub>C \<Phi>\<^sub>G.map (F g, F f)"
        using C.comp_assoc by simp
      also have "... = (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C C.inv (\<Phi>\<^sub>G.map (F g, F f)) \<cdot>\<^sub>C (C.inv (G (\<Phi> (g, f))) \<cdot>\<^sub>C
                       G (\<Phi> (g, f))) \<cdot>\<^sub>C \<Phi>\<^sub>G.map (F g, F f)"
        using assms C.comp_ide_arr [of "G (F (g \<star>\<^sub>C f))" "G (\<Phi> (g, f))"]
              C.VV.arr_char C.VV.dom_char C.VV.cod_char
        by simp
      also have "... = (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C C.inv (\<Phi>\<^sub>G.map (F g, F f)) \<cdot>\<^sub>C \<Phi>\<^sub>G.map (F g, F f)"
      proof -
        have "C.inv (G (\<Phi> (g, f))) \<cdot>\<^sub>C G (\<Phi> (g, f)) = G (F g \<star>\<^sub>D F f)"
          using assms C.comp_inv_arr' cmp_components_are_iso C.inv_is_inverse
                C.VV.arr_char C.VV.ide_char cmp_simps(4)
          by auto
        moreover have "... = C.cod (\<Phi>\<^sub>G.map (F g, F f))"
          using assms by simp
        ultimately have "(C.inv (G (\<Phi> (g, f))) \<cdot>\<^sub>C G (\<Phi> (g, f))) \<cdot>\<^sub>C \<Phi>\<^sub>G.map (F g, F f) =
                         \<Phi>\<^sub>G.map (F g, F f)"
          using assms C.comp_cod_arr [of "\<Phi>\<^sub>G.map (F g, F f)" "G (F g \<star>\<^sub>D F f)"]
                C.ideD(1) G.cmp_simps(1) preserves_ide preserves_src preserves_trg
          by presburger
        thus ?thesis by simp
      qed
      also have "... = \<epsilon> g \<star>\<^sub>C \<epsilon> f"
        using assms C.comp_inv_arr' C.comp_arr_dom [of "\<epsilon> g \<star>\<^sub>C \<epsilon> f" "G (F g) \<star>\<^sub>C G (F f)"]
        by simp
      finally show ?thesis by simp
    qed

    lemma \<epsilon>_inverts_GF_unit:
    assumes "C.obj a"
    shows "\<epsilon> a \<cdot>\<^sub>C GF.unit a = a"
    proof -
      have "\<epsilon> a \<cdot>\<^sub>C GF.unit a = I\<^sub>C.unit a"
      proof (intro I\<^sub>C.unit_eqI)
        show "C.obj a" by fact
        show 1: "\<guillemotleft>\<epsilon> a \<cdot>\<^sub>C GF.unit a : I\<^sub>C.map\<^sub>0 a \<Rightarrow>\<^sub>C I\<^sub>C.map a\<guillemotright>"
        proof -
          have "src\<^sub>C (G (F a)) = src\<^sub>C (I\<^sub>C.map a)"
            using assms G\<^sub>0_props C.obj_def' by simp
          thus ?thesis
            using assms I\<^sub>C.map\<^sub>0_def GF.map\<^sub>0_def GF.unit_in_hom
            by (intro C.comp_in_homI') auto
        qed
        show "C.iso (\<epsilon> a \<cdot>\<^sub>C GF.unit a)"
          using assms \<epsilon>_in_hom GF.unit_char(2)
          by (intro C.isos_compose) auto
        show "(\<epsilon> a \<cdot>\<^sub>C GF.unit a) \<cdot>\<^sub>C \<i>\<^sub>C[I\<^sub>C.map\<^sub>0 a]
                = (I\<^sub>C.map \<i>\<^sub>C[a] \<cdot>\<^sub>C I\<^sub>C.cmp (a, a)) \<cdot>\<^sub>C (\<epsilon> a \<cdot>\<^sub>C GF.unit a \<star>\<^sub>C \<epsilon> a \<cdot>\<^sub>C GF.unit a)"
        proof -
          have "(I\<^sub>C.map \<i>\<^sub>C[a] \<cdot>\<^sub>C I\<^sub>C.cmp (a, a)) \<cdot>\<^sub>C (\<epsilon> a \<cdot>\<^sub>C GF.unit a \<star>\<^sub>C \<epsilon> a \<cdot>\<^sub>C GF.unit a) =
                \<i>\<^sub>C[a] \<cdot>\<^sub>C (a \<star>\<^sub>C a) \<cdot>\<^sub>C (\<epsilon> a \<cdot>\<^sub>C GF.unit a \<star>\<^sub>C \<epsilon> a \<cdot>\<^sub>C GF.unit a)"
            using assms C.comp_assoc by simp
          also have "... = \<i>\<^sub>C[a] \<cdot>\<^sub>C (\<epsilon> a \<cdot>\<^sub>C GF.unit a \<star>\<^sub>C \<epsilon> a \<cdot>\<^sub>C GF.unit a)"
          proof -
            have "C.hseq (\<epsilon> a \<cdot>\<^sub>C GF.unit a) (\<epsilon> a \<cdot>\<^sub>C GF.unit a)"
              using assms GF.unit_simps C.iso_is_arr \<open>C.iso (\<epsilon> a \<cdot>\<^sub>C GF.unit a)\<close>
              by (intro C.hseqI') auto
            moreover have "a \<star>\<^sub>C a = C.cod (\<epsilon> a \<cdot>\<^sub>C GF.unit a \<star>\<^sub>C \<epsilon> a \<cdot>\<^sub>C GF.unit a)"
            proof -
              have "C.cod (\<epsilon> a \<cdot>\<^sub>C GF.unit a) = a"
                using assms 1 C.obj_simps by auto
              moreover have "C.hseq (\<epsilon> a \<cdot>\<^sub>C GF.unit a) (\<epsilon> a \<cdot>\<^sub>C GF.unit a)"
                using assms 1 C.src_dom [of "\<epsilon> a \<cdot>\<^sub>C GF.unit a"] C.trg_dom [of "\<epsilon> a \<cdot>\<^sub>C GF.unit a"]
                by (intro C.hseqI') auto
              ultimately show ?thesis by auto
            qed
            ultimately show ?thesis
              using C.comp_cod_arr by simp
          qed
          also have "... = \<i>\<^sub>C[a] \<cdot>\<^sub>C (\<epsilon> a \<star>\<^sub>C \<epsilon> a) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C GF.unit a)"
            using assms C.interchange [of "\<epsilon> a" "GF.unit a" "\<epsilon> a" "GF.unit a"]
            by (simp add: C.iso_is_arr \<open>C.iso (\<epsilon> a \<cdot>\<^sub>C GF.unit a)\<close>)
          also have "... = \<i>\<^sub>C[a] \<cdot>\<^sub>C (\<epsilon> (a \<star>\<^sub>C a) \<cdot>\<^sub>C GF.cmp (a, a)) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C GF.unit a)"
            using assms \<epsilon>_hcomp' [of a a] by auto
          also have "... = (\<i>\<^sub>C[a] \<cdot>\<^sub>C \<epsilon> (a \<star>\<^sub>C a)) \<cdot>\<^sub>C GF.cmp (a, a) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C GF.unit a)"
            using C.comp_assoc by simp
          also have "... = (\<epsilon> a \<cdot>\<^sub>C G (F \<i>\<^sub>C[a])) \<cdot>\<^sub>C GF.cmp (a, a) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C GF.unit a)"
            using assms \<epsilon>_naturality [of "\<i>\<^sub>C[a]"] by simp
          also have "... = \<epsilon> a \<cdot>\<^sub>C (G (F \<i>\<^sub>C[a]) \<cdot>\<^sub>C GF.cmp (a, a)) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C GF.unit a)"
            using C.comp_assoc by simp
          also have "... = \<epsilon> a \<cdot>\<^sub>C GF.unit a \<cdot>\<^sub>C \<i>\<^sub>C[GF.map\<^sub>0 a]"
            using assms GF.unit_char [of a] by simp
          also have "... = (\<epsilon> a \<cdot>\<^sub>C GF.unit a) \<cdot>\<^sub>C \<i>\<^sub>C[I\<^sub>C.map\<^sub>0 a]"
          proof -
            have "GF.map\<^sub>0 a = I\<^sub>C.map\<^sub>0 a"
              using assms G\<^sub>0_props(2) [of a] GF.map\<^sub>0_def by auto
            thus ?thesis
              using assms GF.unit_char [of a] C.comp_assoc by simp
          qed
          finally show ?thesis
            using C.comp_assoc by simp
        qed
      qed
      thus ?thesis
        using assms I\<^sub>C.unit_char' by simp
    qed

    lemma \<eta>_respects_comp:
    assumes "D.ide f" and "D.ide g" and "src\<^sub>D g = trg\<^sub>D f"
    shows "(\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (g \<star>\<^sub>D f))] \<cdot>\<^sub>D \<eta> (g \<star>\<^sub>D f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]) \<cdot>\<^sub>D ((g \<star>\<^sub>D f) \<star>\<^sub>D src\<^sub>D f)
             = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D
               \<r>\<^sub>D[g \<star>\<^sub>D f]"
    and "(trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[trg\<^sub>D g, F (G g), F (G f)] \<cdot>\<^sub>D
         (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<cdot>\<^sub>D \<eta> g \<cdot>\<^sub>D \<r>\<^sub>D[g] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[g, src\<^sub>D g, F (G f)] \<cdot>\<^sub>D
         (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)] \<cdot>\<^sub>D \<eta> f \<cdot>\<^sub>D \<r>\<^sub>D[f]) \<cdot>\<^sub>D \<a>\<^sub>D[g, f, src\<^sub>D f]
           = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D
             \<r>\<^sub>D[g \<star>\<^sub>D f]"
    proof -
      show "(\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (g \<star>\<^sub>D f))] \<cdot>\<^sub>D \<eta> (g \<star>\<^sub>D f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]) \<cdot>\<^sub>D ((g \<star>\<^sub>D f) \<star>\<^sub>D src\<^sub>D f)
              = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D
                \<r>\<^sub>D[g \<star>\<^sub>D f]"
      proof -
        have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (g \<star>\<^sub>D f))] \<cdot>\<^sub>D \<eta> (g \<star>\<^sub>D f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]) \<cdot>\<^sub>D ((g \<star>\<^sub>D f) \<star>\<^sub>D src\<^sub>D f)
                = \<l>\<^sub>D\<^sup>-\<^sup>1[F (G (g \<star>\<^sub>D f))] \<cdot>\<^sub>D \<eta> (g \<star>\<^sub>D f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]"
          using assms D.comp_assoc D.comp_arr_dom by simp
        also have 1: "... = (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (g \<star>\<^sub>D f))] \<cdot>\<^sub>D F (\<Phi>\<^sub>G.map (g, f))) \<cdot>\<^sub>D
                            \<Phi> (G g, G f) \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]"
          using assms \<eta>_hcomp D.comp_assoc by simp
        also have "... = (trg\<^sub>D g \<star>\<^sub>D F (\<Phi>\<^sub>G.map (g, f))) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g \<star>\<^sub>C G f)] \<cdot>\<^sub>D
                         \<Phi> (G g, G f)) \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]"
        proof -
          have "\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (g \<star>\<^sub>D f))] \<cdot>\<^sub>D F (\<Phi>\<^sub>G.map (g, f)) =
                (trg\<^sub>D g \<star>\<^sub>D F (\<Phi>\<^sub>G.map (g, f))) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g \<star>\<^sub>C G f)]"
            using assms G\<^sub>0_props D.lunit'_naturality [of "F (\<Phi>\<^sub>G.map (g, f))"] \<Phi>\<^sub>G_in_hom [of g f]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((trg\<^sub>D g \<star>\<^sub>D F (\<Phi>\<^sub>G.map (g, f))) \<cdot>\<^sub>D (trg\<^sub>D g \<star>\<^sub>D \<Phi> (G g, G f))) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]"
        proof -
          have "\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g \<star>\<^sub>C G f)] \<cdot>\<^sub>D \<Phi> (G g, G f)
                  = (trg\<^sub>D g \<star>\<^sub>D \<Phi> (G g, G f)) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)]"
            using assms D.lunit'_naturality [of "\<Phi> (G g, G f)"] G\<^sub>0_props by fastforce
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (trg\<^sub>D g \<star>\<^sub>D F (\<Phi>\<^sub>G.map (g, f)) \<cdot>\<^sub>D \<Phi> (G g, G f)) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]"
          using assms 1 D.whisker_left [of "trg\<^sub>D g" "F (\<Phi>\<^sub>G.map (g, f))" "\<Phi> (G g, G f)"]
          by force
        also have "... = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]"
        proof -
          have 1: "FG.cmp (g, f) = (F (G (g \<star>\<^sub>D f)) \<cdot>\<^sub>D F (\<Phi>\<^sub>G.map (g, f))) \<cdot>\<^sub>D \<Phi> (G g, G f)"
            using assms FG.cmp_def D.VV.arr_char D.VV.dom_char D.comp_assoc by simp
          also have "... = F (\<Phi>\<^sub>G.map (g, f)) \<cdot>\<^sub>D \<Phi> (G g, G f)"
          proof -
            have "D.cod (F (\<Phi>\<^sub>G (g, f))) = F (G (g \<star>\<^sub>D f))"
              using assms 1
              by (metis (mono_tags, lifting) D.cod_eqI D.ideD(1) D.ide_hcomp D.seqE
                  FG.cmp_simps'(1) G.preserves_ide preserves_ide)
            thus ?thesis
              using assms D.comp_cod_arr [of "F (\<Phi>\<^sub>G.map (g, f))" "F (G (g \<star>\<^sub>D f))"]
              by fastforce
          qed
          finally have "FG.cmp (g, f) = F (\<Phi>\<^sub>G.map (g, f)) \<cdot>\<^sub>D \<Phi> (G g, G f)" by simp
          thus ?thesis by simp
        qed
        finally show ?thesis by simp
      qed
      show "(trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
            \<a>\<^sub>D[trg\<^sub>D g, F (G g), F (G f)] \<cdot>\<^sub>D
            (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<cdot>\<^sub>D \<eta> g \<cdot>\<^sub>D \<r>\<^sub>D[g] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
            D.inv \<a>\<^sub>D[g, src\<^sub>D g, F (G f)] \<cdot>\<^sub>D
            (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)] \<cdot>\<^sub>D \<eta> f \<cdot>\<^sub>D \<r>\<^sub>D[f]) \<cdot>\<^sub>D
            \<a>\<^sub>D[g, f, src\<^sub>D f]
              = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D
                (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D
                \<r>\<^sub>D[g \<star>\<^sub>D f]"
      proof -
        have "(trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
              \<a>\<^sub>D[trg\<^sub>D g, F (G g), F (G f)] \<cdot>\<^sub>D
              (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<cdot>\<^sub>D \<eta> g \<cdot>\<^sub>D \<r>\<^sub>D[g] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
              D.inv \<a>\<^sub>D[g, src\<^sub>D g, F (G f)] \<cdot>\<^sub>D
              (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)] \<cdot>\<^sub>D \<eta> f \<cdot>\<^sub>D \<r>\<^sub>D[f]) \<cdot>\<^sub>D
              \<a>\<^sub>D[g, f, src\<^sub>D f]
                = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                  \<a>\<^sub>D[trg\<^sub>D g, F (G g), F (G f)] \<cdot>\<^sub>D
                  (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                  (\<eta> g \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                  (\<r>\<^sub>D[g] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                  D.inv \<a>\<^sub>D[g, src\<^sub>D g, F (G f)] \<cdot>\<^sub>D
                  (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)]) \<cdot>\<^sub>D
                  (g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D
                  (g \<star>\<^sub>D \<r>\<^sub>D[f]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[g, f, src\<^sub>D f]"
          using assms D.comp_assoc D.whisker_right D.whisker_left by simp
        also have "... = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[trg\<^sub>D g, F (G g), F (G f)] \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<star>\<^sub>D F (G f))) \<cdot>\<^sub>D
                         (\<eta> g \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                         (\<r>\<^sub>D[g] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[g, src\<^sub>D g, F (G f)] \<cdot>\<^sub>D
                         (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)]) \<cdot>\<^sub>D
                         (g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D
                         ((g \<star>\<^sub>D \<r>\<^sub>D[f]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[g, f, src\<^sub>D f])"
          using assms D.comp_cod_arr D.VV.ide_char D.VV.arr_char D.VV.dom_char
                FG.FF_def G\<^sub>0_props D.comp_assoc
          by presburger
        also have "... = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D
                         (\<eta> g \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                         ((\<r>\<^sub>D[g] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[g, src\<^sub>D g, F (G f)]) \<cdot>\<^sub>D
                         (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)]) \<cdot>\<^sub>D
                         (g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D
                         \<r>\<^sub>D[g \<star>\<^sub>D f]"
        proof -
          have "(g \<star>\<^sub>D \<r>\<^sub>D[f]) \<cdot>\<^sub>D \<a>\<^sub>D[g, f, src\<^sub>D f] = \<r>\<^sub>D[g \<star>\<^sub>D f]"
            using assms D.runit_hcomp by simp
          moreover have "\<a>\<^sub>D[trg\<^sub>D g, F (G g), F (G f)] \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<star>\<^sub>D F (G f)) =
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)]"
            using assms D.lunit_hcomp [of "F (G g)" "F (G f)"] G\<^sub>0_props by simp
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D
                         (\<eta> g \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                         (((g \<star>\<^sub>D \<l>\<^sub>D[F (G f)]) \<cdot>\<^sub>D
                         (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)])) \<cdot>\<^sub>D
                         (g \<star>\<^sub>D \<eta> f)) \<cdot>\<^sub>D
                         \<r>\<^sub>D[g \<star>\<^sub>D f]"
        proof -
          have "(\<r>\<^sub>D[g] \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[g, src\<^sub>D g, F (G f)] = g \<star>\<^sub>D \<l>\<^sub>D[F (G f)]"
            using assms D.triangle' [of g "F (G f)"] G\<^sub>0_props by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D
                         ((\<eta> g \<star>\<^sub>D F (G f)) \<cdot>\<^sub>D
                         (g \<star>\<^sub>D \<eta> f)) \<cdot>\<^sub>D
                         \<r>\<^sub>D[g \<star>\<^sub>D f]"
        proof -
          have "((g \<star>\<^sub>D \<l>\<^sub>D[F (G f)]) \<cdot>\<^sub>D (g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)])) \<cdot>\<^sub>D (g \<star>\<^sub>D \<eta> f) = g \<star>\<^sub>D \<eta> f"
            using assms D.interchange [of g g "\<l>\<^sub>D[F (G f)]" "\<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)]"]
                  D.comp_arr_inv' D.comp_cod_arr
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g) \<star>\<^sub>D F (G f)] \<cdot>\<^sub>D
                           (\<eta> g \<star>\<^sub>D \<eta> f) \<cdot>\<^sub>D \<r>\<^sub>D[g \<star>\<^sub>D f]"
          using assms D.interchange [of "\<eta> g" g "F (G f)" "\<eta> f"] D.comp_arr_dom D.comp_cod_arr
          by simp
        finally show ?thesis by simp
      qed
    qed

    lemma \<eta>_respects_unit:
    assumes "D.obj a"
    shows "(a \<star>\<^sub>D FG.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[a] \<cdot>\<^sub>D \<l>\<^sub>D[a] =
           (\<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod a)] \<cdot>\<^sub>D \<eta> a \<cdot>\<^sub>D \<r>\<^sub>D[D.dom a]) \<cdot>\<^sub>D (I\<^sub>D.unit a \<star>\<^sub>D a)"
    proof -
      have "(\<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod a)] \<cdot>\<^sub>D \<eta> a \<cdot>\<^sub>D \<r>\<^sub>D[D.dom a]) \<cdot>\<^sub>D (I\<^sub>D.unit a \<star>\<^sub>D a) =
            (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G a)] \<cdot>\<^sub>D \<eta> a) \<cdot>\<^sub>D \<r>\<^sub>D[a]"
        using assms I\<^sub>D.lunit_coherence I\<^sub>D.unit_char' D.comp_arr_dom D.comp_assoc by auto
      also have "... = ((a \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[a]) \<cdot>\<^sub>D \<r>\<^sub>D[a]"
        using assms D.lunit'_naturality [of "\<eta> a"] by auto
      also have "... = (a \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[a] \<cdot>\<^sub>D \<r>\<^sub>D[a]"
        using D.comp_assoc by simp
      also have "... = (a \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[a] \<cdot>\<^sub>D \<l>\<^sub>D[a]"
        using assms D.unitor_coincidence by simp
      also have "... = (a \<star>\<^sub>D FG.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[a] \<cdot>\<^sub>D \<l>\<^sub>D[a]"
        using assms \<eta>_equals_FG_unit by simp
      finally show ?thesis by simp
    qed

    lemma \<epsilon>_respects_comp:
    assumes "C.ide f" and "C.ide g" and "src\<^sub>C g = trg\<^sub>C f"
    shows "(trg\<^sub>C g \<star>\<^sub>C g \<star>\<^sub>C f) \<cdot>\<^sub>C \<a>\<^sub>C[trg\<^sub>C g, g, f] \<cdot>\<^sub>C (\<l>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<epsilon> g \<cdot>\<^sub>C \<r>\<^sub>C[G (F g)] \<star>\<^sub>C f) \<cdot>\<^sub>C
           C.inv \<a>\<^sub>C[G (F g), src\<^sub>C g, f] \<cdot>\<^sub>C (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)]) \<cdot>\<^sub>C
           \<a>\<^sub>C[G (F g), G (F f), src\<^sub>C f]
             = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
    and "(\<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C \<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F (g \<star>\<^sub>C f))]) \<cdot>\<^sub>C (GF.cmp (g, f) \<star>\<^sub>C src\<^sub>C f)
           = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
    proof -
      have "(trg\<^sub>C g \<star>\<^sub>C g \<star>\<^sub>C f) \<cdot>\<^sub>C
            \<a>\<^sub>C[trg\<^sub>C g, g, f] \<cdot>\<^sub>C
            (\<l>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<epsilon> g \<cdot>\<^sub>C \<r>\<^sub>C[G (F g)] \<star>\<^sub>C f) \<cdot>\<^sub>C
            C.inv \<a>\<^sub>C[G (F g), src\<^sub>C g, f] \<cdot>\<^sub>C
            (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)]) \<cdot>\<^sub>C
            \<a>\<^sub>C[G (F g), G (F f), src\<^sub>C f]
              = ((trg\<^sub>C g \<star>\<^sub>C g \<star>\<^sub>C f) \<cdot>\<^sub>C
                \<a>\<^sub>C[trg\<^sub>C g, g, f]) \<cdot>\<^sub>C
                (\<l>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<epsilon> g \<cdot>\<^sub>C \<r>\<^sub>C[G (F g)] \<star>\<^sub>C f) \<cdot>\<^sub>C
                C.inv \<a>\<^sub>C[G (F g), src\<^sub>C g, f] \<cdot>\<^sub>C
                (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)]) \<cdot>\<^sub>C
                \<a>\<^sub>C[G (F g), G (F f), src\<^sub>C f]"
        using assms C.comp_assoc by simp
      also have "... = \<a>\<^sub>C[trg\<^sub>C g, g, f] \<cdot>\<^sub>C
                       (\<l>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<epsilon> g \<cdot>\<^sub>C \<r>\<^sub>C[G (F g)] \<star>\<^sub>C f) \<cdot>\<^sub>C
                       C.inv \<a>\<^sub>C[G (F g), src\<^sub>C g, f] \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)]) \<cdot>\<^sub>C
                       \<a>\<^sub>C[G (F g), G (F f), src\<^sub>C f]"
        using assms C.comp_cod_arr by simp
      also have "... = (\<a>\<^sub>C[trg\<^sub>C g, g, f] \<cdot>\<^sub>C
                       (\<l>\<^sub>C\<^sup>-\<^sup>1[g] \<star>\<^sub>C f)) \<cdot>\<^sub>C
                       (\<epsilon> g \<star>\<^sub>C f) \<cdot>\<^sub>C
                       (\<r>\<^sub>C[G (F g)] \<star>\<^sub>C f) \<cdot>\<^sub>C
                       C.inv \<a>\<^sub>C[G (F g), src\<^sub>C g, f] \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f]) \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C
                       ((G (F g) \<star>\<^sub>C \<r>\<^sub>C[G (F f)]) \<cdot>\<^sub>C
                       \<a>\<^sub>C[G (F g), G (F f), src\<^sub>C f])"
        using assms C.whisker_left C.whisker_right C.comp_assoc by simp
      also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C
                       (\<epsilon> g \<star>\<^sub>C f) \<cdot>\<^sub>C
                       ((\<r>\<^sub>C[G (F g)] \<star>\<^sub>C f) \<cdot>\<^sub>C
                       C.inv \<a>\<^sub>C[G (F g), src\<^sub>C g, f]) \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f]) \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C
                       \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
        using assms G\<^sub>0_props C.lunit_hcomp C.runit_hcomp C.comp_assoc by simp
      also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C
                       (\<epsilon> g \<star>\<^sub>C f) \<cdot>\<^sub>C
                       (((G (F g) \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f])) \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<epsilon> f)) \<cdot>\<^sub>C
                       \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
        using assms G\<^sub>0_props C.triangle' C.comp_assoc by simp
      also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C
                       ((\<epsilon> g \<star>\<^sub>C f) \<cdot>\<^sub>C
                       (G (F g) \<star>\<^sub>C \<epsilon> f)) \<cdot>\<^sub>C
                       \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
      proof -
        have "(G (F g) \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>C (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f]) = G (F g) \<star>\<^sub>C f"
          using assms C.whisker_left [of "G (F g)" "\<l>\<^sub>C[f]" "\<l>\<^sub>C\<^sup>-\<^sup>1[f]"] C.comp_arr_inv'
          by simp
        moreover have "... = C.cod (G (F g) \<star>\<^sub>C \<epsilon> f)"
          using assms G\<^sub>0_props by auto
        moreover have "C.hseq (G (F g)) (\<epsilon> f)"
          using assms G\<^sub>0_props by simp
        ultimately have "((G (F g) \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>C (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f])) \<cdot>\<^sub>C (G (F g) \<star>\<^sub>C \<epsilon> f) =
                         (G (F g) \<star>\<^sub>C \<epsilon> f)"
          using assms G\<^sub>0_props C.comp_cod_arr by presburger
        thus ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
        using assms C.interchange [of "\<epsilon> g" "G (F g)" f "\<epsilon> f"] C.comp_cod_arr C.comp_arr_dom
        by simp
      finally show "(trg\<^sub>C g \<star>\<^sub>C g \<star>\<^sub>C f) \<cdot>\<^sub>C
                    \<a>\<^sub>C[trg\<^sub>C g, g, f] \<cdot>\<^sub>C
                    (\<l>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<epsilon> g \<cdot>\<^sub>C \<r>\<^sub>C[G (F g)] \<star>\<^sub>C f) \<cdot>\<^sub>C
                    C.inv \<a>\<^sub>C[G (F g), src\<^sub>C g, f] \<cdot>\<^sub>C
                    (G (F g) \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)]) \<cdot>\<^sub>C
                    \<a>\<^sub>C[G (F g), G (F f), src\<^sub>C f]
                      = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
        by simp
      show "(\<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C \<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F (g \<star>\<^sub>C f))]) \<cdot>\<^sub>C (GF.cmp (g, f) \<star>\<^sub>C src\<^sub>C f)
              = ..."
      proof -
        have "(\<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C \<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F (g \<star>\<^sub>C f))]) \<cdot>\<^sub>C (GF.cmp (g, f) \<star>\<^sub>C src\<^sub>C f) =
              \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C \<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F (g \<star>\<^sub>C f))] \<cdot>\<^sub>C (GF.cmp (g, f) \<star>\<^sub>C src\<^sub>C f)"
          using assms C.comp_assoc by simp
        also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C (\<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C GF.cmp (g, f)) \<cdot>\<^sub>C \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
        proof -
          have "src\<^sub>C (GF.cmp (g, f)) = src\<^sub>C f"
            using assms G\<^sub>0_props by simp
          hence "\<r>\<^sub>C[G (F (g \<star>\<^sub>C f))] \<cdot>\<^sub>C (GF.cmp (g, f) \<star>\<^sub>C src\<^sub>C f) =
                GF.cmp (g, f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
            using assms C.runit_naturality [of "GF.cmp (g, f)"] C.VV.arr_char C.VV.cod_char
                  GF.cmp_simps'(1,4-5)
            by simp
          thus ?thesis
            using C.comp_assoc by simp
        qed
        also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C (\<epsilon> g \<star>\<^sub>C \<epsilon> f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F g) \<star>\<^sub>C G (F f)]"
          using assms \<epsilon>_hcomp' by simp
        ultimately show ?thesis by simp
      qed
    qed

    lemma \<epsilon>_respects_unit:
    assumes "C.obj a"
    shows "(a \<star>\<^sub>C I\<^sub>C.unit a) \<cdot>\<^sub>C \<r>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<l>\<^sub>C[a] =
           (\<l>\<^sub>C\<^sup>-\<^sup>1[C.cod a] \<cdot>\<^sub>C \<epsilon> a \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.dom a)]) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C a)"
    proof -
      have "(\<l>\<^sub>C\<^sup>-\<^sup>1[C.cod a] \<cdot>\<^sub>C \<epsilon> a \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.dom a)]) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C a) =
            \<l>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<epsilon> a \<cdot>\<^sub>C \<r>\<^sub>C[G (F a)] \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C a)"
        using assms C.comp_assoc by auto
      also have "... = (\<l>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<epsilon> a) \<cdot>\<^sub>C GF.unit a \<cdot>\<^sub>C \<r>\<^sub>C[a]"
      proof -
        have "src\<^sub>C (GF.unit a) = a"
          using assms GF.unit_simps(2) GF.map\<^sub>0_def [of a] G\<^sub>0_props
          by (simp add: C.obj_simps(1-2))
        thus ?thesis
          using assms C.runit_naturality [of "GF.unit a"] C.comp_assoc by simp
      qed
      also have "... = (a \<star>\<^sub>C \<epsilon> a) \<cdot>\<^sub>C (\<l>\<^sub>C\<^sup>-\<^sup>1[G (F a)] \<cdot>\<^sub>C GF.unit a) \<cdot>\<^sub>C \<r>\<^sub>C[a]"
      proof -
        have "\<l>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<epsilon> a = (a \<star>\<^sub>C \<epsilon> a) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[G (F a)]"
          using assms C.lunit'_naturality [of "\<epsilon> a"] by auto
        thus ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = ((a \<star>\<^sub>C \<epsilon> a) \<cdot>\<^sub>C (a \<star>\<^sub>C GF.unit a)) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<r>\<^sub>C[a]"
      proof -
        have "\<l>\<^sub>C\<^sup>-\<^sup>1[G (F a)] \<cdot>\<^sub>C GF.unit a = (a \<star>\<^sub>C GF.unit a) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[a]"
          using assms C.lunit'_naturality [of "GF.unit a"] G\<^sub>0_props C.obj_simps
          by (simp add: GF.map\<^sub>0_def)
        thus ?thesis
          using C.comp_assoc by simp
      qed
      also have "... = (a \<star>\<^sub>C \<epsilon> a \<cdot>\<^sub>C GF.unit a) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<r>\<^sub>C[a]"
        using assms C.interchange [of a a "\<epsilon> a" "GF.unit a"] by force
      also have "... = (a \<star>\<^sub>C \<epsilon> a \<cdot>\<^sub>C GF.unit a) \<cdot>\<^sub>C \<r>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<l>\<^sub>C[a]"
        using assms C.unitor_coincidence by simp
      also have "... = (a \<star>\<^sub>C I\<^sub>C.unit a) \<cdot>\<^sub>C \<r>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<l>\<^sub>C[a]"
        using assms \<epsilon>_inverts_GF_unit I\<^sub>C.unit_char' by simp
      finally show ?thesis by simp
    qed

    abbreviation counit\<^sub>0
    where "counit\<^sub>0 \<equiv> \<lambda>b. b"

    abbreviation counit\<^sub>1
    where "counit\<^sub>1 \<equiv> \<lambda>g. \<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<cdot>\<^sub>D \<eta> g \<cdot>\<^sub>D \<r>\<^sub>D[g]"

    interpretation \<epsilon>: pseudonatural_equivalence
                        V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        FG.map FG.cmp I\<^sub>D.map I\<^sub>D.cmp counit\<^sub>0 counit\<^sub>1
    proof
      show "\<And>a. D.obj a \<Longrightarrow> D.ide a"
        by auto
      show "\<And>f. D.ide f \<Longrightarrow> D.iso (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)] \<cdot>\<^sub>D \<eta> f \<cdot>\<^sub>D \<r>\<^sub>D[f])"
        using D.iso_lunit' D.iso_runit \<eta>_in_hom
        by (intro D.isos_compose D.seqI) auto
      show "\<And>a. D.obj a \<Longrightarrow> \<guillemotleft>a : src\<^sub>D (FG.map a) \<rightarrow>\<^sub>D src\<^sub>D (I\<^sub>D.map a)\<guillemotright>"
        using D.obj_def G\<^sub>0_props(1) by auto
      show "\<And>f. D.ide f \<Longrightarrow> \<guillemotleft>\<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)] \<cdot>\<^sub>D \<eta> f \<cdot>\<^sub>D \<r>\<^sub>D[f] :
                                I\<^sub>D.map f \<star>\<^sub>D src\<^sub>D f \<Rightarrow>\<^sub>D trg\<^sub>D f \<star>\<^sub>D FG.map f\<guillemotright>"
        using G\<^sub>0_props
        by (intro D.comp_in_homI') auto
      show "\<And>\<mu>. D.arr \<mu> \<Longrightarrow>
                (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (D.cod \<mu>))] \<cdot>\<^sub>D \<eta> (D.cod \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.cod \<mu>]) \<cdot>\<^sub>D (I\<^sub>D.map \<mu> \<star>\<^sub>D src\<^sub>D \<mu>)
                  = (trg\<^sub>D \<mu> \<star>\<^sub>D FG.map \<mu>) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G (D.dom \<mu>))] \<cdot>\<^sub>D \<eta> (D.dom \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]"
      proof -
        fix \<mu>
        assume \<mu>: "D.arr \<mu>"
        have "(\<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D \<eta> (D.cod \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.cod \<mu>]) \<cdot>\<^sub>D
              (I\<^sub>D.map \<mu> \<star>\<^sub>D src\<^sub>D \<mu>)
                = \<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D \<eta> \<mu> \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D \<eta> (D.cod \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.cod \<mu>]) \<cdot>\<^sub>D
                (I\<^sub>D.map \<mu> \<star>\<^sub>D src\<^sub>D \<mu>)
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D (\<eta> (D.cod \<mu>) \<cdot>\<^sub>D \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]"
            using \<mu> D.runit_naturality D.comp_assoc by simp
          also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D \<eta> \<mu> \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]"
            using \<mu> \<eta>_naturality(1) by simp
          finally show ?thesis by blast
        qed
        also have "... = (trg\<^sub>D \<mu> \<star>\<^sub>D FG.map \<mu>) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.dom \<mu>)] \<cdot>\<^sub>D \<eta> (D.dom \<mu>) \<cdot>\<^sub>D
                         \<r>\<^sub>D[D.dom \<mu>]"
        proof -
          have "\<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D \<eta> \<mu> \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>] =
                \<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D (FG.map \<mu> \<cdot>\<^sub>D \<eta> (D.dom \<mu>)) \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]"
            using \<mu> \<eta>_naturality(2) D.comp_assoc by simp
          also have "... = (\<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.cod \<mu>)] \<cdot>\<^sub>D FG.map \<mu>) \<cdot>\<^sub>D \<eta> (D.dom \<mu>) \<cdot>\<^sub>D
                           \<r>\<^sub>D[D.dom \<mu>]"
            using D.comp_assoc by simp
          also have "... = ((trg\<^sub>D \<mu> \<star>\<^sub>D FG.map \<mu>) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.dom \<mu>)]) \<cdot>\<^sub>D
                           \<eta> (D.dom \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]"
            using \<mu> D.lunit'_naturality [of "FG.map \<mu>"] G\<^sub>0_props by simp
          also have "... = (trg\<^sub>D \<mu> \<star>\<^sub>D FG.map \<mu>) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[FG.map (D.dom \<mu>)] \<cdot>\<^sub>D
                           \<eta> (D.dom \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.dom \<mu>]"
            using D.comp_assoc by simp
          finally show ?thesis by blast
        qed
        finally show "(\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (D.cod \<mu>))] \<cdot>\<^sub>D \<eta> (D.cod \<mu>) \<cdot>\<^sub>D \<r>\<^sub>D[D.cod \<mu>]) \<cdot>\<^sub>D
                      (I\<^sub>D.map \<mu> \<star>\<^sub>D src\<^sub>D \<mu>)
                        = (trg\<^sub>D \<mu> \<star>\<^sub>D FG.map \<mu>) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G (D.dom \<mu>))] \<cdot>\<^sub>D \<eta> (D.dom \<mu>) \<cdot>\<^sub>D
                          \<r>\<^sub>D[D.dom \<mu>]"
          by simp
      qed
      show "\<And>f g. \<lbrakk>D.ide f; D.ide g; src\<^sub>D g = trg\<^sub>D f\<rbrakk>
                    \<Longrightarrow> (trg\<^sub>D g \<star>\<^sub>D FG.cmp (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[trg\<^sub>D g, FG.map g, FG.map f] \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G g)] \<cdot>\<^sub>D \<eta> g \<cdot>\<^sub>D \<r>\<^sub>D[g] \<star>\<^sub>D FG.map f) \<cdot>\<^sub>D
                        D.inv \<a>\<^sub>D[I\<^sub>D.map g, src\<^sub>D g, FG.map f] \<cdot>\<^sub>D
                        (I\<^sub>D.map g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F (G f)] \<cdot>\<^sub>D \<eta> f \<cdot>\<^sub>D \<r>\<^sub>D[f]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[I\<^sub>D.map g, I\<^sub>D.map f, src\<^sub>D f]
                          = (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G (g \<star>\<^sub>D f))] \<cdot>\<^sub>D \<eta> (g \<star>\<^sub>D f) \<cdot>\<^sub>D
                            \<r>\<^sub>D[g \<star>\<^sub>D f]) \<cdot>\<^sub>D
                            (I\<^sub>D.cmp (g, f) \<star>\<^sub>D src\<^sub>D f)"
        using \<eta>_respects_comp by simp
      show "\<And>a. D.obj a \<Longrightarrow> (a \<star>\<^sub>D FG.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[a] \<cdot>\<^sub>D \<l>\<^sub>D[a] =
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F (G a)] \<cdot>\<^sub>D \<eta> a \<cdot>\<^sub>D \<r>\<^sub>D[a]) \<cdot>\<^sub>D (I\<^sub>D.unit a \<star>\<^sub>D a)"
        using \<eta>_respects_unit by auto
      show "\<And>a. D.obj a \<Longrightarrow> D.equivalence_map a"
        using D.obj_is_equivalence_map by simp
    qed

    abbreviation unit\<^sub>0
    where "unit\<^sub>0 \<equiv> \<lambda>a. a"

    abbreviation unit\<^sub>1
    where "unit\<^sub>1 \<equiv> \<lambda>f. \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)]"

    interpretation \<eta>: pseudonatural_equivalence
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                           I\<^sub>C.map I\<^sub>C.cmp GF.map GF.cmp unit\<^sub>0 unit\<^sub>1
    proof
      show "\<And>a. C.obj a \<Longrightarrow> C.ide a"
        by auto
      show "\<And>f. C.ide f \<Longrightarrow> C.iso (\<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)])"
        using C.iso_runit C.iso_lunit'
        by (intro C.isos_compose) auto
      show "\<And>a. C.obj a \<Longrightarrow> \<guillemotleft>a : src\<^sub>C (I\<^sub>C.map a) \<rightarrow>\<^sub>C src\<^sub>C (GF.map a)\<guillemotright>"
        by (simp_all add: C.obj_simps(1-3) G\<^sub>0_props(2))
      show "\<And>f. C.ide f \<Longrightarrow> \<guillemotleft>\<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)] :
                               GF.map f \<star>\<^sub>C src\<^sub>C f \<Rightarrow>\<^sub>C trg\<^sub>C f \<star>\<^sub>C I\<^sub>C.map f\<guillemotright>"
        using G\<^sub>0_props by auto
      show "\<And>\<mu>. C.arr \<mu> \<Longrightarrow>
                  (\<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C \<r>\<^sub>C[G (F (C.cod \<mu>))]) \<cdot>\<^sub>C
                  (GF.map \<mu> \<star>\<^sub>C src\<^sub>C \<mu>)
                    = (trg\<^sub>C \<mu> \<star>\<^sub>C I\<^sub>C.map \<mu>) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[C.dom \<mu>] \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) \<cdot>\<^sub>C
                      \<r>\<^sub>C[G (F (C.dom \<mu>))]"
      proof -
        fix \<mu>
        assume \<mu>: "C.arr \<mu>"
        have "(\<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.cod \<mu>)]) \<cdot>\<^sub>C
              (GF.map \<mu> \<star>\<^sub>C src\<^sub>C \<mu>)
                = \<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<epsilon> \<mu> \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
        proof -
          have "(\<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.cod \<mu>)]) \<cdot>\<^sub>C
                (GF.map \<mu> \<star>\<^sub>C src\<^sub>C \<mu>)
                  = \<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.cod \<mu>)] \<cdot>\<^sub>C
                    (GF.map \<mu> \<star>\<^sub>C src\<^sub>C \<mu>)"
            using C.comp_assoc by simp
          also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C (\<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C GF.map \<mu>) \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
            using \<mu> C.runit_naturality [of "GF.map \<mu>"] G\<^sub>0_props C.comp_assoc by simp
          also have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<epsilon> \<mu> \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
            using \<mu> \<epsilon>_naturality(1) [of \<mu>] by simp
          finally show ?thesis by blast
        qed
        also have "... = (trg\<^sub>C \<mu> \<star>\<^sub>C I\<^sub>C.map \<mu>) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[C.dom \<mu>] \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) \<cdot>\<^sub>C
                         \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
        proof -
          have "... = \<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C (\<mu> \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>)) \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
            using \<mu> \<epsilon>_naturality(2) [of \<mu>] by simp
          also have "... = (\<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<mu>) \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) \<cdot>\<^sub>C \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
            using C.comp_assoc by simp
          also have "... = ((trg\<^sub>C \<mu> \<star>\<^sub>C I\<^sub>C.map \<mu>) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[C.dom \<mu>]) \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) \<cdot>\<^sub>C
                           \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
            using \<mu> C.lunit'_naturality [of \<mu>] by simp
          also have "... = (trg\<^sub>C \<mu> \<star>\<^sub>C I\<^sub>C.map \<mu>) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[C.dom \<mu>] \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) \<cdot>\<^sub>C
                           \<r>\<^sub>C[GF.map (C.dom \<mu>)]"
            using C.comp_assoc by simp
          finally show ?thesis by blast
        qed
        finally show "(\<l>\<^sub>C\<^sup>-\<^sup>1[C.cod \<mu>] \<cdot>\<^sub>C \<epsilon> (C.cod \<mu>) \<cdot>\<^sub>C \<r>\<^sub>C[G (F (C.cod \<mu>))]) \<cdot>\<^sub>C
                      (GF.map \<mu> \<star>\<^sub>C src\<^sub>C \<mu>)
                        = (trg\<^sub>C \<mu> \<star>\<^sub>C I\<^sub>C.map \<mu>) \<cdot>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[C.dom \<mu>] \<cdot>\<^sub>C \<epsilon> (C.dom \<mu>) \<cdot>\<^sub>C
                          \<r>\<^sub>C[G (F (C.dom \<mu>))]"
          by simp
      qed
      show "\<And>f g. \<lbrakk>C.ide f; C.ide g; src\<^sub>C g = trg\<^sub>C f\<rbrakk> \<Longrightarrow>
                    (trg\<^sub>C g \<star>\<^sub>C I\<^sub>C.cmp (g, f)) \<cdot>\<^sub>C
                    \<a>\<^sub>C[trg\<^sub>C g, I\<^sub>C.map g, I\<^sub>C.map f] \<cdot>\<^sub>C
                    (\<l>\<^sub>C\<^sup>-\<^sup>1[g] \<cdot>\<^sub>C \<epsilon> g \<cdot>\<^sub>C \<r>\<^sub>C[G (F g)] \<star>\<^sub>C I\<^sub>C.map f) \<cdot>\<^sub>C
                    C.inv \<a>\<^sub>C[GF.map g, src\<^sub>C g, I\<^sub>C.map f] \<cdot>\<^sub>C
                    (GF.map g \<star>\<^sub>C \<l>\<^sub>C\<^sup>-\<^sup>1[f] \<cdot>\<^sub>C \<epsilon> f \<cdot>\<^sub>C \<r>\<^sub>C[G (F f)]) \<cdot>\<^sub>C
                    \<a>\<^sub>C[GF.map g, GF.map f, src\<^sub>C f]
                      = (\<l>\<^sub>C\<^sup>-\<^sup>1[g \<star>\<^sub>C f] \<cdot>\<^sub>C \<epsilon> (g \<star>\<^sub>C f) \<cdot>\<^sub>C \<r>\<^sub>C[G (F (g \<star>\<^sub>C f))]) \<cdot>\<^sub>C
                        (GF.cmp (g, f) \<star>\<^sub>C src\<^sub>C f)"
        using \<epsilon>_respects_comp by simp
      show "\<And>a. C.obj a \<Longrightarrow> (a \<star>\<^sub>C I\<^sub>C.unit a) \<cdot>\<^sub>C \<r>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<l>\<^sub>C[a] =
                             (\<l>\<^sub>C\<^sup>-\<^sup>1[a] \<cdot>\<^sub>C \<epsilon> a \<cdot>\<^sub>C \<r>\<^sub>C[G (F a)]) \<cdot>\<^sub>C (GF.unit a \<star>\<^sub>C a)"
        using \<epsilon>_respects_unit by auto
      show "\<And>a. C.obj a \<Longrightarrow> C.equivalence_map a"
        using C.obj_is_equivalence_map by simp
    qed

    interpretation EQ: equivalence_of_bicategories
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         F \<Phi> G \<Phi>\<^sub>G.map unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1
      ..

    lemma extends_to_equivalence_of_bicategories:
    shows "equivalence_of_bicategories V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
             F \<Phi> G \<Phi>\<^sub>G.map unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1"
      ..

  end

  subsection "Equivalence Pseudofunctors Extend to Equivalences of Bicategories"

  text \<open>
    Now we put the pieces together and prove that an arbitrary equivalence pseudofunctor extends
    to an equivalence of bicategories.
  \<close>

  context equivalence_pseudofunctor
  begin

    text \<open>
      Define a set of objects \<open>U\<close> of \<open>C\<close> by choosing a representative of each equivalence
      class of objects having the same image under the object map of the given equivalence
      pseudofunctor.  Then \<open>U\<close> is obviously dense, because every object of \<open>C\<close> belongs to
      such an equivalence class.
    \<close>

    definition U
    where "U = {a. C.obj a \<and> a = (SOME a'. C.obj a' \<and> map\<^sub>0 a' = map\<^sub>0 a)}"

    lemma U_dense:
    assumes "C.obj a"
    shows "\<exists>a' \<in> U. C.equivalent_objects a a'"
    proof -
      let ?a' = "SOME a'. C.obj a' \<and> map\<^sub>0 a' = map\<^sub>0 a"
      have "\<exists>a'. C.obj a' \<and> map\<^sub>0 a' = map\<^sub>0 a"
        using assms by auto
      hence 1: "?a' \<in> U \<and> map\<^sub>0 ?a' = map\<^sub>0 a"
        using assms U_def someI_ex [of "\<lambda>a'. C.obj a' \<and> map\<^sub>0 a' = map\<^sub>0 a"] by simp
      hence "C.equivalent_objects ?a' a"
        using D.equivalent_objects_reflexive reflects_equivalent_objects [of ?a' a]
        by (simp add: U_def assms)
      thus ?thesis
        using 1 C.equivalent_objects_symmetric by auto
    qed

    text \<open>
      Take \<open>V\<close> to be the collection of images of all objects of \<open>C\<close> under the given equivalence
      pseudofunctor.  Since equivalence pseudofunctors are biessentially surjective on objects,
      \<open>V\<close> is dense.  Moreover, by construction, the object map of the given equivalence
      pseudofunctor is a bijection from \<open>U\<close> to \<open>V\<close>.
    \<close>

    definition V
    where "V = map\<^sub>0 ` Collect C.obj"

    lemma V_dense:
    assumes "D.obj b"
    shows "\<exists>b'. b' \<in> map\<^sub>0 ` Collect C.obj \<and> D.equivalent_objects b b'"
      using assms biessentially_surjective_on_objects D.equivalent_objects_symmetric
      by blast

    lemma bij_betw_U_V:
    shows "bij_betw map\<^sub>0 U V"
    proof -
      have "inj_on map\<^sub>0 U"
        using U_def by (intro inj_onI) simp
      moreover have "map\<^sub>0 ` U = V"
      proof
        show "map\<^sub>0 ` U \<subseteq> V"
          using U_def V_def by auto
        show "V \<subseteq> map\<^sub>0 ` U"
        proof
          fix b
          assume b: "b \<in> V"
          obtain a where a: "C.obj a \<and> map\<^sub>0 a = b"
            using b V_def by auto
          let ?a' = "SOME a'. C.obj a' \<and> map\<^sub>0 a' = map\<^sub>0 a"
          have 1: "C.obj ?a' \<and> map\<^sub>0 ?a' = b"
            using a someI_ex [of "\<lambda>a'. C.obj a' \<and> map\<^sub>0 a' = map\<^sub>0 a"] by auto
          moreover have "?a' = (SOME a''. C.obj a'' \<and> map\<^sub>0 a'' = map\<^sub>0 ?a')"
            using a 1 by simp
          ultimately have "?a' \<in> U"
            unfolding U_def by simp
          thus "b \<in> map\<^sub>0 ` U"
             using a 1 U_def
             by (metis (no_types, lifting) image_eqI)
        qed
      qed
      ultimately show ?thesis
        using bij_betw_def [of map\<^sub>0 U V] by simp
    qed

    abbreviation (input) Arr\<^sub>U
    where "Arr\<^sub>U \<equiv> \<lambda>\<mu>. C.arr \<mu> \<and> src\<^sub>C \<mu> \<in> U \<and> trg\<^sub>C \<mu> \<in> U"

    interpretation C\<^sub>U: subbicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C Arr\<^sub>U
      using C.\<ll>_ide_simp C.\<rr>_ide_simp
      apply unfold_locales
                  apply auto
       apply (metis C.comp_ide_self C.ide_src C.src_cod C.src_dom)
      by (metis C.trg.is_natural_2 C.trg.naturality C.trg_cod)

    interpretation C\<^sub>U: dense_subbicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C U  (* 25 sec *)
    proof
      show "\<And>a. C.obj a \<Longrightarrow> \<exists>a'. a' \<in> U \<and> C.equivalent_objects a' a"
        using U_dense C.equivalent_objects_symmetric by blast
      (* TODO: The above inference is trivial, but qed consumes 15 seconds! *)
    qed (* 15 sec *)

    abbreviation (input) Arr\<^sub>V
    where "Arr\<^sub>V \<equiv> \<lambda>\<mu>. D.arr \<mu> \<and> src\<^sub>D \<mu> \<in> V \<and> trg\<^sub>D \<mu> \<in> V"

    interpretation D\<^sub>V: subbicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D Arr\<^sub>V
      using D.\<ll>_ide_simp D.\<rr>_ide_simp
      apply unfold_locales
                  apply auto
       apply (metis D.comp_ide_self D.ide_src D.src_cod D.src_dom)
      by (metis D.trg.is_natural_2 D.trg.naturality D.trg_cod)

    interpretation D\<^sub>V: dense_subbicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V  (* 35 sec *)
      using V_dense D.equivalent_objects_def D.equivalent_objects_symmetric V_def
      by unfold_locales metis (* 20 sec -- time is similar doing it this way. *)

    interpretation F\<^sub>U: restricted_pseudofunctor
                         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>
                         \<open>\<lambda>\<mu>. C.arr \<mu> \<and> src\<^sub>C \<mu> \<in> U \<and> trg\<^sub>C \<mu> \<in> U\<close>
      ..

    interpretation F\<^sub>U\<^sub>V: corestricted_pseudofunctor
                         C\<^sub>U.comp C\<^sub>U.hcomp C\<^sub>U.\<a> \<i>\<^sub>C C\<^sub>U.src C\<^sub>U.trg
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F\<^sub>U.map F\<^sub>U.cmp \<open>\<lambda>a. a \<in> V\<close>
    proof
      show "\<And>\<mu>. C\<^sub>U.arr \<mu> \<Longrightarrow> D\<^sub>V.arr (F\<^sub>U.map \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "C\<^sub>U.arr \<mu>"
        have "src\<^sub>C \<mu> \<in> U \<and> trg\<^sub>C \<mu> \<in> U"
          using \<mu> C\<^sub>U.arr_char by simp
        moreover have "\<And>a. a \<in> U \<Longrightarrow> F\<^sub>U.map\<^sub>0 a = map\<^sub>0 a"
        proof -
          fix a :: 'a
          assume a: "a \<in> U"
          hence 1: "C.obj a"
            using U_def by blast
          have "src\<^sub>C a = a"
            using a U_def by blast
          thus "F\<^sub>U.map\<^sub>0 a = map\<^sub>0 a"
            using a 1 C.obj_simps(1,3) C\<^sub>U.arr_char F\<^sub>U.map\<^sub>0_def map\<^sub>0_def by presburger
        qed
        ultimately have "F\<^sub>U.map\<^sub>0 (src\<^sub>C \<mu>) \<in> V \<and> F\<^sub>U.map\<^sub>0 (trg\<^sub>C \<mu>) \<in> V"
          using \<mu> bij_betw_U_V bij_betw_def
          by (metis (no_types, lifting) image_eqI)
        hence "src\<^sub>D (F\<^sub>U.map \<mu>) \<in> V \<and> trg\<^sub>D (F\<^sub>U.map \<mu>) \<in> V"
          using \<mu> F\<^sub>U.map\<^sub>0_def C\<^sub>U.src_def C\<^sub>U.trg_def F\<^sub>U.preserves_src F\<^sub>U.preserves_trg
          by auto
        thus "D\<^sub>V.arr (F\<^sub>U.map \<mu>)"
          using \<mu> D\<^sub>V.arr_char [of "F\<^sub>U.map \<mu>"] by blast
      qed
    qed

    interpretation F\<^sub>U\<^sub>V: equivalence_pseudofunctor
                         C\<^sub>U.comp C\<^sub>U.hcomp C\<^sub>U.\<a> \<i>\<^sub>C C\<^sub>U.src C\<^sub>U.trg
                         D\<^sub>V.comp D\<^sub>V.hcomp D\<^sub>V.\<a> \<i>\<^sub>D D\<^sub>V.src D\<^sub>V.trg
                         F\<^sub>U\<^sub>V.map F\<^sub>U\<^sub>V.cmp
    proof
      show "\<And>f f'. \<lbrakk>C\<^sub>U.par f f'; F\<^sub>U.map f = F\<^sub>U.map f'\<rbrakk> \<Longrightarrow> f = f'"
        using C\<^sub>U.arr_char C\<^sub>U.dom_char C\<^sub>U.cod_char
        by (metis (no_types, lifting) is_faithful)
      show "\<And>a b g. \<lbrakk>C\<^sub>U.obj a; C\<^sub>U.obj b; D\<^sub>V.in_hhom g (F\<^sub>U\<^sub>V.map\<^sub>0 a) (F\<^sub>U\<^sub>V.map\<^sub>0 b);
                      D\<^sub>V.ide g\<rbrakk>
                       \<Longrightarrow> \<exists>f. C\<^sub>U.in_hhom f a b \<and> C\<^sub>U.ide f \<and> D\<^sub>V.isomorphic (F\<^sub>U.map f) g"
      proof -
        fix a b g
        assume a: "C\<^sub>U.obj a" and b: "C\<^sub>U.obj b"
        assume g: "D\<^sub>V.in_hhom g (F\<^sub>U\<^sub>V.map\<^sub>0 a) (F\<^sub>U\<^sub>V.map\<^sub>0 b)" and ide_g: "D\<^sub>V.ide g"
        have 1: "\<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) g"
        proof -
          have "C.obj a \<and> C.obj b"
            using a b C\<^sub>U.obj_char by simp
          moreover have "\<guillemotleft>g : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright>"
            using a b g D\<^sub>V.in_hhom_def D\<^sub>V.arr_char D\<^sub>V.src_def D\<^sub>V.trg_def
            by (intro D.in_hhomI) auto
          moreover have "D.ide g"
            using ide_g D\<^sub>V.ide_char D\<^sub>V.arr_char by simp
          ultimately show ?thesis
            using locally_essentially_surjective by simp
        qed
        obtain f where f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) g"
          using 1 by blast
        have 2: "C\<^sub>U.in_hhom f a b"
          using f a b C\<^sub>U.arr_char C\<^sub>U.obj_char C\<^sub>U.src_def C\<^sub>U.trg_def by fastforce
        moreover have "C\<^sub>U.ide f"
          using f 2 C\<^sub>U.ide_char C\<^sub>U.arr_char by auto
        moreover have "D\<^sub>V.isomorphic (F\<^sub>U\<^sub>V.map f) g"
        proof -
          obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : F f \<Rightarrow>\<^sub>D g\<guillemotright> \<and> D.iso \<phi>"
            using f D.isomorphic_def by auto
          have 3: "D\<^sub>V.in_hom \<phi> (F\<^sub>U\<^sub>V.map f) g"
          proof -
            have "D\<^sub>V.arr \<phi>"
              using f g \<phi> 2 D\<^sub>V.arr_char
              by (metis (no_types, lifting) D.arrI D.vconn_implies_hpar(1-4) D\<^sub>V.ideD(1) ide_g)
            thus ?thesis
              using \<phi> 2 D\<^sub>V.dom_char D\<^sub>V.cod_char
              by (intro D\<^sub>V.in_homI) auto
          qed
          moreover have "D\<^sub>V.iso \<phi>"
            using \<phi> D\<^sub>V.iso_char D\<^sub>V.arr_char 3 by fastforce
          ultimately show ?thesis
            using D\<^sub>V.isomorphic_def by auto
        qed
        ultimately show "\<exists>f. C\<^sub>U.in_hhom f a b \<and> C\<^sub>U.ide f \<and> D\<^sub>V.isomorphic (F\<^sub>U\<^sub>V.map f) g"
          by auto
      qed
      show "\<And>f f' \<nu>. \<lbrakk>C\<^sub>U.ide f; C\<^sub>U.ide f'; C\<^sub>U.src f = C\<^sub>U.src f'; C\<^sub>U.trg f = C\<^sub>U.trg f';
                      D\<^sub>V.in_hom \<nu> (F\<^sub>U.map f) (F\<^sub>U.map f')\<rbrakk>
                          \<Longrightarrow> \<exists>\<mu>. C\<^sub>U.in_hom \<mu> f f' \<and> F\<^sub>U.map \<mu> = \<nu>"
      proof -
        fix f f' \<nu>
        assume f: "C\<^sub>U.ide f" and f': "C\<^sub>U.ide f'"
        and eq_src: "C\<^sub>U.src f = C\<^sub>U.src f'" and eq_trg: "C\<^sub>U.trg f = C\<^sub>U.trg f'"
        and \<nu>: "D\<^sub>V.in_hom \<nu> (F\<^sub>U.map f) (F\<^sub>U.map f')"
        have 1: "C.ide f \<and> C.ide f'"
          using f f' C\<^sub>U.ide_char C\<^sub>U.arr_char by simp
        have 2: "\<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C f'\<guillemotright> \<and> F \<mu> = \<nu>"
        proof -
          have "src\<^sub>C f = src\<^sub>C f' \<and> trg\<^sub>C f = trg\<^sub>C f'"
            using f f' 1 eq_src eq_trg C\<^sub>U.src_def C\<^sub>U.trg_def by simp
          moreover have "\<guillemotleft>\<nu> : F f \<Rightarrow>\<^sub>D F f'\<guillemotright>"
            using \<nu> D\<^sub>V.in_hom_char D\<^sub>V.arr_char by auto
          ultimately show ?thesis
            using 1 locally_full by simp
        qed
        obtain \<mu> where \<mu>: "\<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C f'\<guillemotright> \<and> F \<mu> = \<nu>"
          using 2 by auto
        have 3: "C\<^sub>U.in_hom \<mu> f f'"
          using \<mu> f f' C\<^sub>U.in_hom_char C\<^sub>U.ide_char C\<^sub>U.arr_char by auto
        moreover have "F\<^sub>U.map \<mu> = \<nu>"
          using \<mu> 3 by auto
        ultimately show "\<exists>\<mu>. C\<^sub>U.in_hom \<mu> f f' \<and> F\<^sub>U.map \<mu> = \<nu>"
          by auto
      qed
      show "\<And>b. D\<^sub>V.obj b \<Longrightarrow> \<exists>a. C\<^sub>U.obj a \<and> D\<^sub>V.equivalent_objects (F\<^sub>U\<^sub>V.map\<^sub>0 a) b"
      proof -
        fix b
        assume b: "D\<^sub>V.obj b"
        obtain a where a: "C.obj a \<and> map\<^sub>0 a = b"
          using b D\<^sub>V.obj_char D\<^sub>V.arr_char V_def by auto
        have 1: "D.obj b \<and> b \<in> V"
          using a b D\<^sub>V.obj_char V_def by auto
        obtain a' where a': "a' \<in> U \<and> C.equivalent_objects a' a"
          using a U_dense C.equivalent_objects_symmetric by blast
        have obj_a': "C\<^sub>U.obj a'"
          using a' U_def C\<^sub>U.obj_char C\<^sub>U.arr_char by fastforce
        moreover have "D\<^sub>V.equivalent_objects (F\<^sub>U\<^sub>V.map\<^sub>0 a') b"
        proof -
          have "D.equivalent_objects (map\<^sub>0 a') (map\<^sub>0 a)"
            using a' preserves_equivalent_objects by simp
          hence 2: "D.equivalent_objects (map\<^sub>0 a') b"
            using a D.equivalent_objects_transitive by simp
          obtain e where e: "\<guillemotleft>e : map\<^sub>0 a' \<rightarrow>\<^sub>D b\<guillemotright> \<and> D.equivalence_map e"
            using 2 D.equivalent_objects_def by auto
          have 3: "D.obj (map\<^sub>0 a') \<and> map\<^sub>0 a' \<in> V"
            using a' e U_def V_def by simp
          moreover have e_in_hhom: "D\<^sub>V.in_hhom e (F\<^sub>U\<^sub>V.map\<^sub>0 a') b"
          proof
            show 4: "D\<^sub>V.arr e"
              using 1 3 a e b D\<^sub>V.arr_char D\<^sub>V.obj_char V_def
              by (metis (no_types, lifting) D.in_hhomE)
            show "D\<^sub>V.src e = F\<^sub>U\<^sub>V.map\<^sub>0 a'"
              using e 4 D\<^sub>V.src_def F\<^sub>U\<^sub>V.map\<^sub>0_def obj_a' map\<^sub>0_def by auto
            show "D\<^sub>V.trg e = b"
              using e 4 D\<^sub>V.trg_def by auto
          qed
          moreover have "D\<^sub>V.equivalence_map e"
          proof -
            obtain d \<eta> \<epsilon> where d: "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D e d \<eta> \<epsilon>"
              using e D.equivalence_map_def by auto
            interpret e: equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D e d \<eta> \<epsilon>
              using d by simp
            have "equivalence_in_bicategory D\<^sub>V.comp D\<^sub>V.hcomp D\<^sub>V.\<a> \<i>\<^sub>D D\<^sub>V.src D\<^sub>V.trg e d \<eta> \<epsilon>"
            proof
              show ide_e: "D\<^sub>V.ide e"
                using e e_in_hhom D\<^sub>V.ide_char by auto
              show ide_d: "D\<^sub>V.ide d"
                using d ide_e e.antipar D\<^sub>V.ide_char D\<^sub>V.arr_char by simp
              show 4: "D\<^sub>V.in_hom \<eta> (D\<^sub>V.src e) (D\<^sub>V.hcomp d e)"
              proof -
                have "D\<^sub>V.hseq d e"
                  using ide_d ide_e e.antipar D\<^sub>V.src_def D\<^sub>V.trg_def by simp
                thus ?thesis
                  using ide_d ide_e e.unit_in_hom D\<^sub>V.arr_char D\<^sub>V.ide_char
                        D\<^sub>V.dom_char D\<^sub>V.cod_char D\<^sub>V.src_def D\<^sub>V.trg_def
                  by (intro D\<^sub>V.in_homI) auto
              qed
              show 5: "D\<^sub>V.in_hom \<epsilon> (D\<^sub>V.hcomp e d) (D\<^sub>V.src d)"
              proof -
                have "D\<^sub>V.hseq e d"
                  using ide_d ide_e e.antipar D\<^sub>V.src_def D\<^sub>V.trg_def by simp
                thus ?thesis
                  using ide_d ide_e e.antipar e.counit_in_hom D\<^sub>V.arr_char D\<^sub>V.ide_char
                        D\<^sub>V.dom_char D\<^sub>V.cod_char D\<^sub>V.src_def D\<^sub>V.trg_def
                  by (intro D\<^sub>V.in_homI) auto
              qed
              show "D\<^sub>V.iso \<eta>"
                using 4 D\<^sub>V.iso_char D\<^sub>V.arr_char by fastforce
              show "D\<^sub>V.iso \<epsilon>"
                using 5 D\<^sub>V.iso_char D\<^sub>V.arr_char by fastforce
            qed
            thus ?thesis
              using D\<^sub>V.equivalence_map_def by auto
          qed
          ultimately show ?thesis
            using D\<^sub>V.equivalent_objects_def by auto
        qed
        ultimately show "\<exists>a. C\<^sub>U.obj a \<and> D\<^sub>V.equivalent_objects (F\<^sub>U\<^sub>V.map\<^sub>0 a) b" by auto
      qed
    qed

    interpretation F\<^sub>U\<^sub>V: equivalence_pseudofunctor_bij_on_obj
                         C\<^sub>U.comp C\<^sub>U.hcomp C\<^sub>U.\<a> \<i>\<^sub>C C\<^sub>U.src C\<^sub>U.trg
                         D\<^sub>V.comp D\<^sub>V.hcomp D\<^sub>V.\<a> \<i>\<^sub>D D\<^sub>V.src D\<^sub>V.trg
                         F\<^sub>U\<^sub>V.map F\<^sub>U\<^sub>V.cmp
    proof
      have "Collect C\<^sub>U.obj = U"
        using C\<^sub>U.obj_char C\<^sub>U.arr_char U_def by fastforce
      moreover have "Collect D\<^sub>V.obj = V"
        using D\<^sub>V.obj_char D\<^sub>V.arr_char V_def D.obj_def' map\<^sub>0_simps(1) by auto
      moreover have "\<And>a. a \<in> Collect C\<^sub>U.obj \<Longrightarrow> F\<^sub>U\<^sub>V.map\<^sub>0 a = map\<^sub>0 a"
        using F\<^sub>U\<^sub>V.map\<^sub>0_def C\<^sub>U.obj_char C\<^sub>U.arr_char D\<^sub>V.src_def
              F\<^sub>U.map\<^sub>0_simp F\<^sub>U\<^sub>V.map\<^sub>0_simp by auto
      ultimately show "bij_betw F\<^sub>U\<^sub>V.map\<^sub>0 (Collect C\<^sub>U.obj) (Collect D\<^sub>V.obj)"
        using bij_betw_U_V
        by (simp add: bij_betw_U_V bij_betw_cong)
    qed

    interpretation EQ\<^sub>U\<^sub>V: equivalence_of_bicategories  (* 25 sec *)
                          D\<^sub>V.comp D\<^sub>V.hcomp D\<^sub>V.\<a> \<i>\<^sub>D D\<^sub>V.src D\<^sub>V.trg
                          C\<^sub>U.comp C\<^sub>U.hcomp C\<^sub>U.\<a> \<i>\<^sub>C C\<^sub>U.src C\<^sub>U.trg
                          F\<^sub>U\<^sub>V.map F\<^sub>U\<^sub>V.cmp F\<^sub>U\<^sub>V.G F\<^sub>U\<^sub>V.\<Phi>\<^sub>G
                          F\<^sub>U\<^sub>V.unit\<^sub>0 F\<^sub>U\<^sub>V.unit\<^sub>1 F\<^sub>U\<^sub>V.counit\<^sub>0 F\<^sub>U\<^sub>V.counit\<^sub>1
      using F\<^sub>U\<^sub>V.extends_to_equivalence_of_bicategories by blast  (* 18 sec, mostly "by" *)

    text \<open>
      Now compose \<open>EQ\<^sub>U\<^sub>V\<close> with the equivalence from \<open>D\<^sub>V\<close> to \<open>D\<close> and the converse of the equivalence
      from \<open>C\<^sub>U\<close> to \<open>C\<close>.  The result is an equivalence of bicategories from \<open>C\<close> to \<open>D\<close>.
    \<close>

    interpretation EQ\<^sub>C: equivalence_of_bicategories
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C C\<^sub>U.comp C\<^sub>U.hcomp C\<^sub>U.\<a> \<i>\<^sub>C C\<^sub>U.src C\<^sub>U.trg
                           C\<^sub>U.E C\<^sub>U.\<Phi>\<^sub>E C\<^sub>U.P C\<^sub>U.\<Phi>\<^sub>P
                           C\<^sub>U.unit\<^sub>0 C\<^sub>U.unit\<^sub>1 C\<^sub>U.counit\<^sub>0 C\<^sub>U.counit\<^sub>1
      using C\<^sub>U.induces_equivalence by simp

    interpretation EQ\<^sub>C': converse_equivalence_of_bicategories
                           V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C C\<^sub>U.comp C\<^sub>U.hcomp C\<^sub>U.\<a> \<i>\<^sub>C C\<^sub>U.src C\<^sub>U.trg
                           C\<^sub>U.E C\<^sub>U.\<Phi>\<^sub>E C\<^sub>U.P C\<^sub>U.\<Phi>\<^sub>P
                           C\<^sub>U.unit\<^sub>0 C\<^sub>U.unit\<^sub>1 C\<^sub>U.counit\<^sub>0 C\<^sub>U.counit\<^sub>1
      ..

    interpretation EQ\<^sub>D: equivalence_of_bicategories
                           V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D D\<^sub>V.comp D\<^sub>V.hcomp D\<^sub>V.\<a> \<i>\<^sub>D D\<^sub>V.src D\<^sub>V.trg
                           D\<^sub>V.E D\<^sub>V.\<Phi>\<^sub>E D\<^sub>V.P D\<^sub>V.\<Phi>\<^sub>P
                           D\<^sub>V.unit\<^sub>0 D\<^sub>V.unit\<^sub>1 D\<^sub>V.counit\<^sub>0 D\<^sub>V.counit\<^sub>1
      using D\<^sub>V.induces_equivalence by simp

    interpretation EQ\<^sub>U\<^sub>VoEQ\<^sub>C': composite_equivalence_of_bicategories  (* 50 sec *)
                               D\<^sub>V.comp D\<^sub>V.hcomp D\<^sub>V.\<a> \<i>\<^sub>D D\<^sub>V.src D\<^sub>V.trg
                               C\<^sub>U.comp C\<^sub>U.hcomp C\<^sub>U.\<a> \<i>\<^sub>C C\<^sub>U.src C\<^sub>U.trg
                               V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                               F\<^sub>U\<^sub>V.map F\<^sub>U\<^sub>V.cmp F\<^sub>U\<^sub>V.G F\<^sub>U\<^sub>V.\<Phi>\<^sub>G
                               C\<^sub>U.P C\<^sub>U.\<Phi>\<^sub>P C\<^sub>U.E C\<^sub>U.\<Phi>\<^sub>E
                               F\<^sub>U\<^sub>V.unit\<^sub>0 F\<^sub>U\<^sub>V.unit\<^sub>1 F\<^sub>U\<^sub>V.counit\<^sub>0 F\<^sub>U\<^sub>V.counit\<^sub>1
                               EQ\<^sub>C'.unit\<^sub>0 EQ\<^sub>C'.unit\<^sub>1 EQ\<^sub>C'.counit\<^sub>0 EQ\<^sub>C'.counit\<^sub>1
      ..  (* 40 sec *)

    interpretation EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C': composite_equivalence_of_bicategories  (* 50 sec *)
                                   V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                                   D\<^sub>V.comp D\<^sub>V.hcomp D\<^sub>V.\<a> \<i>\<^sub>D D\<^sub>V.src D\<^sub>V.trg
                                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                                   D\<^sub>V.E D\<^sub>V.\<Phi>\<^sub>E D\<^sub>V.P D\<^sub>V.\<Phi>\<^sub>P
                                   EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp
                                   EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_cmp
                                   D\<^sub>V.unit\<^sub>0 D\<^sub>V.unit\<^sub>1 D\<^sub>V.counit\<^sub>0 D\<^sub>V.counit\<^sub>1
                                   EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0 EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>1
                                   EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>0 EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>1
      ..  (* 40 sec *)

    lemma induces_equivalence_of_bicategories:
    shows "equivalence_of_bicategories V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
             EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp
             EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_cmp
             EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>1
             EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>1"
      ..

    lemma left_map_simp:
    assumes "C.arr \<mu>"
    shows "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map \<mu> = D\<^sub>V.E (F (C\<^sub>U.P \<mu>))"
      using assms by simp

    lemma right_map_simp:
    assumes "D.arr \<nu>"
    shows "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map \<nu> = C\<^sub>U.E (F\<^sub>U\<^sub>V.G (D\<^sub>V.P \<nu>))"
      using assms by simp

    lemma unit\<^sub>0_simp:
    assumes "C.obj a"
    shows "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0 a =
           C\<^sub>U.E (F\<^sub>U\<^sub>V.G (D\<^sub>V.unit\<^sub>0 (D\<^sub>V.src (F (C\<^sub>U.P a))))) \<star>\<^sub>C C\<^sub>U.E (C\<^sub>U.P\<^sub>0 (src\<^sub>C a))
             \<star>\<^sub>C EQ\<^sub>C'.unit\<^sub>0 a"
      using assms EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0_simp EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0_simp
            EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0_def C\<^sub>U.src_def
      by auto

    (*
     * TODO: Expansions of the other parts of the equivalence are not comprehensible
     * without interpreting a bunch of other locales.  I don't know that there is any particular
     * value to doing that.  The above show that the pseudofunctors between C and D and the
     * components of the unit of the equivalence are as expected.
     *)

    text \<open>
      We've now got an equivalence of bicategories between \<open>C\<close> and \<open>D\<close>, but it involves
      \<open>EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map\<close> and not the originally given equivalence pseudofunctor \<open>F\<close>.
      However, we can patch things up by showing that \<open>EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map\<close> is pseudonaturally
      equivalent to \<open>F\<close>.  From this, we may conclude, using the fact that equivalences of
      bicategories respect pseudonatural equivalence, that there is an equivalence of bicategories
      between \<open>C\<close> and \<open>D\<close> that involves \<open>F\<close> and \<open>EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map\<close>, rather than
      \<open>EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map\<close> and \<open>EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map\<close>.
    \<close>

    abbreviation \<tau>\<^sub>0
    where "\<tau>\<^sub>0 a \<equiv> F (C\<^sub>U.counit\<^sub>0 a)"

    abbreviation \<tau>\<^sub>1
    where "\<tau>\<^sub>1 f \<equiv> D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f), C\<^sub>U.P f)) \<cdot>\<^sub>D F (C\<^sub>U.counit\<^sub>1 f) \<cdot>\<^sub>D
                    \<Phi> (f, C\<^sub>U.counit\<^sub>0 (src\<^sub>C f))"

    lemma \<tau>\<^sub>0_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>\<tau>\<^sub>0 a : map\<^sub>0 (C\<^sub>U.P\<^sub>0 a) \<rightarrow>\<^sub>D map\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<tau>\<^sub>0 a : \<tau>\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0 a\<guillemotright>"
    proof -
      show "\<guillemotleft>\<tau>\<^sub>0 a : map\<^sub>0 (C\<^sub>U.P\<^sub>0 a) \<rightarrow>\<^sub>D map\<^sub>0 a\<guillemotright>"
      proof
        show "D.arr (\<tau>\<^sub>0 a)"
          using assms by simp
        show "src\<^sub>D (\<tau>\<^sub>0 a) = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)"
          using assms map\<^sub>0_def C\<^sub>U.counit.ide_map\<^sub>0_obj C\<^sub>U.equivalence_data_simps\<^sub>B(7) C.ideD(1)
                preserves_src
          by presburger
        show "trg\<^sub>D (\<tau>\<^sub>0 a) = map\<^sub>0 a"
          using assms by auto
      qed
      show "\<guillemotleft>\<tau>\<^sub>0 a : \<tau>\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0 a\<guillemotright>"
        using assms by auto
    qed

    lemma \<tau>\<^sub>0_simps [simp]:
    assumes "C.obj a"
    shows "D.ide (\<tau>\<^sub>0 a)"
    and "src\<^sub>D (\<tau>\<^sub>0 a) = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)" and "trg\<^sub>D (\<tau>\<^sub>0 a) = map\<^sub>0 a"
      using assms \<tau>\<^sub>0_in_hom(1) [of a] by auto

    lemma \<tau>\<^sub>1_in_hom [intro]:
    assumes "C.ide f"
    shows "\<guillemotleft>\<tau>\<^sub>1 f : map\<^sub>0 (C\<^sub>U.P\<^sub>0 (src\<^sub>C f)) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C f)\<guillemotright>"
    and "\<guillemotleft>\<tau>\<^sub>1 f : F f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F (C\<^sub>U.P f)\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>\<tau>\<^sub>1 f : F f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F (C\<^sub>U.P f)\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>\<Phi> (f, C\<^sub>U.d (src\<^sub>C f)) : F f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D F (f \<star>\<^sub>C C\<^sub>U.counit\<^sub>0 (src\<^sub>C f))\<guillemotright>"
          using assms by auto
        show "\<guillemotleft>F (C\<^sub>U.counit\<^sub>1 f) :
                 F (f \<star>\<^sub>C C\<^sub>U.counit\<^sub>0 (src\<^sub>C f)) \<Rightarrow>\<^sub>D F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>C C\<^sub>U.P f)\<guillemotright>"
          using assms C\<^sub>U.counit\<^sub>1_in_hom [of f] C\<^sub>U.P_def by auto
        show "\<guillemotleft>D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f), C\<^sub>U.P f)) :
                   F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>C C\<^sub>U.P f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F (C\<^sub>U.P f)\<guillemotright>"
          using assms C.VV.arr_char C.VV.ide_char \<Phi>.components_are_iso
          by (metis (no_types, lifting) C\<^sub>U.P_def C\<^sub>U.counit.ide_map\<^sub>0_obj C\<^sub>U.counit\<^sub>1_simps(1,5)
              C\<^sub>U.equivalence_data_simps\<^sub>B(2) C.hseqE C.ide_hcomp C.obj_trg D.arr_cod D.inv_in_homI
              cmp_components_are_iso cmp_in_hom(2) preserves_cod preserves_reflects_arr)
      qed
      show "\<guillemotleft>\<tau>\<^sub>1 f : map\<^sub>0 (C\<^sub>U.P\<^sub>0 (src\<^sub>C f)) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C f)\<guillemotright>"
        using assms 1 D.src_dom [of "\<tau>\<^sub>1 f"] D.trg_dom [of "\<tau>\<^sub>1 f"]
              C\<^sub>U.P\<^sub>0_props map\<^sub>0_def [of "C\<^sub>U.P\<^sub>0 (src\<^sub>C f)"] C\<^sub>U.emb.map\<^sub>0_simp
        by (intro D.in_hhomI) auto
    qed

    lemma \<tau>\<^sub>1_simps [simp]:
    assumes "C.ide f"
    shows "D.arr (\<tau>\<^sub>1 f)"
    and "src\<^sub>D (\<tau>\<^sub>1 f) = map\<^sub>0 (C\<^sub>U.P\<^sub>0 (src\<^sub>C f))" and "trg\<^sub>D (\<tau>\<^sub>1 f) = map\<^sub>0 (trg\<^sub>C f)"
    and "D.dom (\<tau>\<^sub>1 f) = F f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)" and "D.cod (\<tau>\<^sub>1 f) = \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F (C\<^sub>U.P f)"
      using assms \<tau>\<^sub>1_in_hom by blast+

    lemma iso_\<tau>\<^sub>1:
    assumes "C.ide f"
    shows "D.iso (\<tau>\<^sub>1 f)"
    proof -
      have "C.VV.ide (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f), C\<^sub>U.P f)"
      proof -
        have "C.VV.arr (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f), C\<^sub>U.P f)"
          using assms C\<^sub>U.equivalence_data_simps\<^sub>B(7) C.ideD(1) by auto
        moreover have "C.VxV.ide (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f), C\<^sub>U.P f)"
          using assms C\<^sub>U.prj.preserves_ide [of f] C\<^sub>U.ide_char by simp
        ultimately show ?thesis
          using assms C.VV.ide_char [of "(C\<^sub>U.counit\<^sub>0 (trg\<^sub>C f), C\<^sub>U.P f)"] by blast
      qed
      hence "D.iso (\<Phi> (C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f))"
        by simp
      thus ?thesis
        using assms C.VV.ide_char C.VV.arr_char \<Phi>.components_are_iso
        by (intro D.isos_compose) auto
    qed

    interpretation \<tau>: pseudonatural_equivalence
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp F \<Phi>
                          \<tau>\<^sub>0 \<tau>\<^sub>1
    proof
      show "\<And>a. C.obj a \<Longrightarrow> D.ide (\<tau>\<^sub>0 a)"
        by simp
      show "\<And>a. C.obj a \<Longrightarrow> D.equivalence_map (\<tau>\<^sub>0 a)"
        using C\<^sub>U.counit.components_are_equivalences preserves_equivalence_maps by blast
      show "\<And>a. C.obj a \<Longrightarrow> \<guillemotleft>\<tau>\<^sub>0 a : src\<^sub>D (EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map a) \<rightarrow>\<^sub>D src\<^sub>D (F a)\<guillemotright>"
      proof -
        fix a
        assume a: "C.obj a"
        show "\<guillemotleft>\<tau>\<^sub>0 a : src\<^sub>D (EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map a) \<rightarrow>\<^sub>D src\<^sub>D (F a)\<guillemotright>"
        proof
          show "D.arr (\<tau>\<^sub>0 a)"
            using a by simp
          show "src\<^sub>D (\<tau>\<^sub>0 a) = src\<^sub>D (EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map a)"
          proof -
            have "D\<^sub>V.arr (F (C\<^sub>U.P a))"
            proof -
              have "src\<^sub>D (F (C\<^sub>U.P a)) \<in> V"
              proof -
                have "src\<^sub>D (F (C\<^sub>U.P a)) = map\<^sub>0 (C\<^sub>U.prj.map\<^sub>0 a)"
                  using a by auto
                moreover have "C.obj (C\<^sub>U.prj.map\<^sub>0 a)"
                  using a C\<^sub>U.obj_char [of "C\<^sub>U.prj.map\<^sub>0 a"] C\<^sub>U.prj.map\<^sub>0_simps(1) by auto
                ultimately show ?thesis
                  using V_def by simp
              qed
              moreover have "trg\<^sub>D (F (C\<^sub>U.P a)) \<in> V"
              proof -
                have "trg\<^sub>D (F (C\<^sub>U.P a)) = map\<^sub>0 (C\<^sub>U.prj.map\<^sub>0 a)"
                  using a by auto
                moreover have "C.obj (C\<^sub>U.prj.map\<^sub>0 a)"
                  using a C\<^sub>U.obj_char [of "C\<^sub>U.prj.map\<^sub>0 a"] C\<^sub>U.prj.map\<^sub>0_simps(1) by auto
                ultimately show ?thesis
                  using V_def by simp
              qed
              ultimately show ?thesis
                using a D\<^sub>V.arr_char by fastforce
            qed
            thus ?thesis
              using a D\<^sub>V.emb.map\<^sub>0_def D\<^sub>V.emb.map_def D\<^sub>V.src_def C.obj_simps(1-2) C\<^sub>U.P_simps\<^sub>B(2)
              by (simp add: C\<^sub>U.P\<^sub>0_props(1))
          qed
          show "trg\<^sub>D (F (C\<^sub>U.d a)) = src\<^sub>D (F a)"
            using a by auto
        qed
      qed
      show "\<And>f. C.ide f \<Longrightarrow>
                   \<guillemotleft>\<tau>\<^sub>1 f : F f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f\<guillemotright>"
      proof -
        fix f
        assume f: "C.ide f"
        show "\<guillemotleft>\<tau>\<^sub>1 f : F f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f\<guillemotright>"
        proof -
          have "D\<^sub>V.arr (F (C\<^sub>U.P f))"
            using f F\<^sub>U\<^sub>V.preserves_arr by auto
          hence "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f = F (C\<^sub>U.P f)"
            using f EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0_def D\<^sub>V.emb.map_def by simp
          thus ?thesis
            using f by auto
        qed
      qed
      show "\<And>f. C.ide f \<Longrightarrow> D.iso (\<tau>\<^sub>1 f)"
        using iso_\<tau>\<^sub>1 by simp
      show "\<And>\<mu>. C.arr \<mu> \<Longrightarrow>
                   \<tau>\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)) =
                   (\<tau>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1 (C.dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "C.arr \<mu>"
        show "\<tau>\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>))
                = (\<tau>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1 (C.dom \<mu>)"
        proof -
          have "\<tau>\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>))
                  = D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P (C.cod \<mu>))) \<cdot>\<^sub>D
                    F (C\<^sub>U.counit\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D
                    \<Phi> (C.cod \<mu>, C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                    (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>))"
            using \<mu> D.comp_assoc by simp
          also have "... = D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P (C.cod \<mu>))) \<cdot>\<^sub>D
                           (F (C\<^sub>U.counit\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D
                           F (\<mu> \<star>\<^sub>C C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>))) \<cdot>\<^sub>D
                           \<Phi> (C.dom \<mu>, C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>))"
            using \<mu> \<Phi>.naturality [of "(\<mu>, C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>))"] D.comp_assoc
                  C.VV.arr_char C.VV.dom_char C.VV.cod_char FF_def
            by simp
          also have "... = (D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P (C.cod \<mu>))) \<cdot>\<^sub>D
                           F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>C C\<^sub>U.EoP.map \<mu>)) \<cdot>\<^sub>D
                           F (C\<^sub>U.counit\<^sub>1 (C.dom \<mu>)) \<cdot>\<^sub>D
                           \<Phi> (C.dom \<mu>, C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>))"
          proof -
            have "F (C\<^sub>U.counit\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D F (\<mu> \<star>\<^sub>C C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>))
                    = F (C\<^sub>U.counit\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>C (\<mu> \<star>\<^sub>C C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>)))"
              using \<mu> by simp
            also have "... = F ((C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>C C\<^sub>U.EoP.map \<mu>) \<cdot>\<^sub>C
                                  C\<^sub>U.counit\<^sub>1 (C.dom \<mu>))"
              using \<mu> C\<^sub>U.counit.naturality [of \<mu>] by simp
            also have "... = F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>C C\<^sub>U.EoP.map \<mu>) \<cdot>\<^sub>D
                             F (C\<^sub>U.counit\<^sub>1 (C.dom \<mu>))"
              using \<mu> by simp
            finally have "F (C\<^sub>U.counit\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D F (\<mu> \<star>\<^sub>C C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>))
                            = F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>C C\<^sub>U.EoP.map \<mu>) \<cdot>\<^sub>D
                              F (C\<^sub>U.counit\<^sub>1 (C.dom \<mu>))"
              by blast
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = (F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>)) \<star>\<^sub>D F (C\<^sub>U.EoP.map \<mu>)) \<cdot>\<^sub>D
                           D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P (C.dom \<mu>))) \<cdot>\<^sub>D
                           F (C\<^sub>U.counit\<^sub>1 (C.dom \<mu>)) \<cdot>\<^sub>D
                           \<Phi> (C.dom \<mu>, C\<^sub>U.counit\<^sub>0 (src\<^sub>C \<mu>))"
          proof -
            have "D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P (C.cod \<mu>))) \<cdot>\<^sub>D
                  F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>C C\<^sub>U.EoP.map \<mu>)
                    = (F (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>)) \<star>\<^sub>D F (C\<^sub>U.EoP.map \<mu>)) \<cdot>\<^sub>D
                      D.inv (\<Phi> (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P (C.dom \<mu>)))"
            proof -
              have "C.VV.arr (C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P \<mu>)"
              proof (unfold C.VV.arr_char, intro conjI)
                show "C.arr (fst (C\<^sub>U.d (trg\<^sub>C \<mu>), C\<^sub>U.P \<mu>))"
                  using \<mu> by simp
                show "C.arr (snd (C\<^sub>U.d (trg\<^sub>C \<mu>), C\<^sub>U.P \<mu>))"
                  using \<mu> by simp
                show "src\<^sub>C (fst (C\<^sub>U.d (trg\<^sub>C \<mu>), C\<^sub>U.P \<mu>)) = trg\<^sub>C (snd (C\<^sub>U.d (trg\<^sub>C \<mu>), C\<^sub>U.P \<mu>))"
                  using \<mu> C\<^sub>U.emb.map\<^sub>0_def C\<^sub>U.emb.map_def apply simp
                  using C\<^sub>U.P\<^sub>0_props(1) C\<^sub>U.P_simps\<^sub>B(3) C\<^sub>U.src_def by fastforce
              qed
              moreover have "C\<^sub>U.EoP.map \<mu> = C\<^sub>U.P \<mu>"
                using \<mu> by (simp add: C\<^sub>U.emb.map_def)
              moreover have "C\<^sub>U.emb.map\<^sub>0 (C\<^sub>U.P\<^sub>0 (trg\<^sub>C \<mu>)) = C\<^sub>U.P\<^sub>0 (trg\<^sub>C \<mu>)"
                using \<mu> C\<^sub>U.P\<^sub>0_props(1) C\<^sub>U.emb.map\<^sub>0_simp by blast
              ultimately show ?thesis
                using \<mu> C.VV.arr_char C.VV.dom_char C.VV.cod_char C.VV.ide_char FF_def
                      \<Phi>.inv_naturality [of "(C\<^sub>U.counit\<^sub>0 (trg\<^sub>C \<mu>), C\<^sub>U.P \<mu>)"]
                by simp
            qed
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = (\<tau>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1 (C.dom \<mu>)"
            using \<mu> F\<^sub>U\<^sub>V.preserves_arr D.comp_assoc D\<^sub>V.emb.map_def C\<^sub>U.emb.map_def by simp
          finally show "\<tau>\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>))
                          = (\<tau>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1 (C.dom \<mu>)"
            by blast
        qed
      qed
      show "\<And>a. C.obj a \<Longrightarrow>
                  (\<tau>\<^sub>0 a \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a] =
                  \<tau>\<^sub>1 a \<cdot>\<^sub>D (unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
      proof -
        fix a
        assume a: "C.obj a"
        have 1: "C\<^sub>U.obj (C\<^sub>U.prj.map\<^sub>0 a)"
          using a C\<^sub>U.prj.map\<^sub>0_simps(1) by simp
        have 2: "\<guillemotleft>C\<^sub>U.prj.unit a : C\<^sub>U.prj.map\<^sub>0 a \<Rightarrow>\<^sub>C C\<^sub>U.P a\<guillemotright>"
          using a C\<^sub>U.in_hom_char by blast
        have 3: "\<guillemotleft>C\<^sub>U.prj.unit a : C\<^sub>U.prj.map\<^sub>0 a \<rightarrow>\<^sub>C C\<^sub>U.prj.map\<^sub>0 a\<guillemotright>"
        proof (intro C.in_hhomI)
          show 4: "C.arr (C\<^sub>U.prj.unit a)"
            using 2 by auto
          show "src\<^sub>C (C\<^sub>U.prj.unit a) = C\<^sub>U.prj.map\<^sub>0 a"
          proof -
            have "src\<^sub>C (C\<^sub>U.prj.unit a) = src\<^sub>C (C\<^sub>U.P a)"
              using 2 4 C.src_cod [of "C\<^sub>U.prj.unit a"] C.vconn_implies_hpar(1,3) by auto
            also have "... = C\<^sub>U.prj.map\<^sub>0 a"
              using a C.obj_simps(1) C\<^sub>U.prj.map\<^sub>0_def [of a] C\<^sub>U.src_def [of "C\<^sub>U.P a"]
              by simp
            finally show ?thesis by blast
          qed
          show "trg\<^sub>C (C\<^sub>U.prj.unit a) = C\<^sub>U.prj.map\<^sub>0 a"
          proof -
            have "trg\<^sub>C (C\<^sub>U.prj.unit a) = trg\<^sub>C (C\<^sub>U.P a)"
              using 2 4 C.trg_cod [of "C\<^sub>U.prj.unit a"] C.vconn_implies_hpar(2,4) by auto
            also have "... = C\<^sub>U.prj.map\<^sub>0 a"
              using a C.obj_simps(1,3) C\<^sub>U.prj.map\<^sub>0_def [of a] C\<^sub>U.trg_def [of "C\<^sub>U.P a"]
              by simp
            finally show ?thesis by blast
          qed
        qed
        have [simp]: "C.dom (C\<^sub>U.prj.unit a) = C\<^sub>U.prj.map\<^sub>0 a"
          using 2 by auto
        have [simp]: "C.arr (C\<^sub>U.prj.unit a)"
          using 2 by auto
        have [simp]: "C.cod (C\<^sub>U.prj.unit a) = C\<^sub>U.P a"
          using 2 by auto
        have [simp]: "src\<^sub>C (C\<^sub>U.prj.unit a) = C\<^sub>U.prj.map\<^sub>0 a"
          using 3 by auto
        have [simp]: "trg\<^sub>C (C\<^sub>U.prj.unit a) = C\<^sub>U.prj.map\<^sub>0 a"
          using 3 by auto
        have [simp]: "C.arr (C\<^sub>U.d a)"
          using a by simp
        have [simp]: "C.ide (C\<^sub>U.d a)"
          using a by simp
        have [simp]: "C.dom (C\<^sub>U.d a) = C\<^sub>U.d a"
          using a by auto
        have [simp]: "C.cod (C\<^sub>U.d a) = C\<^sub>U.d a"
          using a by auto
        have [simp]: "src\<^sub>C (C\<^sub>U.d a) = C\<^sub>U.prj.map\<^sub>0 a"
          using a C\<^sub>U.equivalence_data_simps\<^sub>B(7) by auto
        have [simp]: "trg\<^sub>C (C\<^sub>U.d a) = a"
          using a C\<^sub>U.equivalence_data_simps\<^sub>B(7) by auto

        have seq: "D.seq (F (C\<^sub>U.prj.unit a)) (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
          using a
          apply (intro D.seqI)
          using C\<^sub>U.prj.map\<^sub>0_simps(1) D\<^sub>V.arr_char F\<^sub>U\<^sub>V.unit_simps(1) apply blast
          using C\<^sub>U.prj.unit_simps(1) C\<^sub>U.arr_char apply blast
        proof -
          have "D.dom (F (C\<^sub>U.prj.unit a)) = F (C.dom (C\<^sub>U.prj.unit a))"
            using a C\<^sub>U.prj.unit_simps(1) C\<^sub>U.arr_char by simp
          also have "... = F (C\<^sub>U.prj.map\<^sub>0 a)"
            using a C\<^sub>U.prj.unit_simps [of a] C\<^sub>U.dom_char by simp
          also have "... = D.cod (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
            using a 1 C\<^sub>U.prj.unit_simps [of a] F\<^sub>U\<^sub>V.unit_simps(5) [of "C\<^sub>U.prj.map\<^sub>0 a"] D\<^sub>V.cod_char
            by simp
          finally show "D.dom (F (C\<^sub>U.prj.unit a)) = D.cod (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
            by blast
        qed

        have 4: "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.unit a = F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a)"
        proof -
          have "EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0 a = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)"
            using a EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0_def D\<^sub>V.src_def C.obj_def F\<^sub>U\<^sub>V.preserves_arr by auto
          have seq': "D\<^sub>V.arr (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
          proof -
            have 5: "D.arr (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
              using seq by simp
            moreover have "src\<^sub>D (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a)) \<in> V"
            proof -
              have "src\<^sub>D (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))
                      = map\<^sub>0 (C\<^sub>U.prj.map\<^sub>0 a)"
              proof -
                have "src\<^sub>D (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))
                        = src\<^sub>D (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
                  using 5 D.src_vcomp D.vseq_implies_hpar by simp
                also have "... = map\<^sub>0 (C\<^sub>U.prj.map\<^sub>0 a)"
                  using a F\<^sub>U\<^sub>V.unit_simps(1-2) [of "C\<^sub>U.prj.map\<^sub>0 a"] D\<^sub>V.src_def F\<^sub>U\<^sub>V.map\<^sub>0_def
                  apply simp
                  using a C\<^sub>U.prj.map\<^sub>0_simps(1) F\<^sub>U\<^sub>V.preserves_arr map\<^sub>0_def by force
                finally show ?thesis by blast
              qed
              moreover have "C.obj (C\<^sub>U.prj.map\<^sub>0 a)"
                using a C\<^sub>U.prj.map\<^sub>0_simps(1) C\<^sub>U.obj_char by blast
              ultimately show ?thesis
                using V_def by blast
            qed
            moreover have "trg\<^sub>D (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a)) \<in> V"
            proof -
              have "trg\<^sub>D (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))
                      = map\<^sub>0 (C\<^sub>U.prj.map\<^sub>0 a)"
              proof -
                have "trg\<^sub>D (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a)) =
                      trg\<^sub>D (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
                  using 5 D.trg_vcomp D.vseq_implies_hpar by simp
                also have "... = map\<^sub>0 (C\<^sub>U.prj.map\<^sub>0 a)"
                  using a F\<^sub>U\<^sub>V.unit_simps(1,3) [of "C\<^sub>U.prj.map\<^sub>0 a"] D\<^sub>V.src_def D\<^sub>V.trg_def
                        F\<^sub>U\<^sub>V.map\<^sub>0_def
                  apply simp
                  using a C\<^sub>U.prj.map\<^sub>0_simps(1) F\<^sub>U\<^sub>V.preserves_arr map\<^sub>0_def by force
                finally show ?thesis by blast
              qed
              moreover have "C.obj (C\<^sub>U.prj.map\<^sub>0 a)"
                using a C\<^sub>U.prj.map\<^sub>0_simps(1) C\<^sub>U.obj_char by blast
              ultimately show ?thesis
                using V_def by blast
            qed
            ultimately show ?thesis
              using a D\<^sub>V.arr_char by simp
          qed

          have "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.unit a =
                F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a) \<cdot>\<^sub>D map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)"
          proof -
            have 5: "D\<^sub>V.obj (src\<^sub>D (F (C\<^sub>U.P\<^sub>0 a)))"
              using a C\<^sub>U.P\<^sub>0_props [of a]
              by (metis (no_types, lifting) EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0_simps(1)
                  \<open>EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0 a = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)\<close> map\<^sub>0_def)
            have 6: "D\<^sub>V.emb.unit (map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)) = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)"
              using a 5 D\<^sub>V.emb.unit_char' EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0_simps(1)
                    \<open>EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0 a = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)\<close> map\<^sub>0_def
              by simp
            moreover have "D\<^sub>V.emb.unit (map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)) = map\<^sub>0 (C\<^sub>U.prj.map\<^sub>0 a)"
              using 6 a C.obj_simps C\<^sub>U.equivalence_data_simps\<^sub>B(7) by simp
            moreover have "D\<^sub>V.arr (F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
              using a C.obj_simps seq' by blast
            moreover have "D\<^sub>V.arr (F\<^sub>U\<^sub>V.unit (C\<^sub>U.P\<^sub>0 a))"
              using a 1 by simp
            moreover have "D\<^sub>V.arr (F (C\<^sub>U.prj.unit a))"
              using a F\<^sub>U\<^sub>V.preserves_arr by auto
            moreover have "D\<^sub>V.obj (F\<^sub>U\<^sub>V.map\<^sub>0 (C\<^sub>U.P\<^sub>0 a))"
              using a 1 F\<^sub>U\<^sub>V.map\<^sub>0_simps(1) by auto
            moreover have "F\<^sub>U\<^sub>V.map\<^sub>0 (C\<^sub>U.P\<^sub>0 a) = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)"
              using a \<open>EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.map\<^sub>0 a = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)\<close> map\<^sub>0_def F\<^sub>U\<^sub>V.map\<^sub>0_simps
              by auto
            ultimately show ?thesis
              using a seq EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.unit_char' EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.unit_char'
                    D\<^sub>V.emb.unit_char' D\<^sub>V.emb.map_def D\<^sub>V.seq_char D\<^sub>V.comp_char D.comp_assoc
              by simp
          qed
          also have "... = F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a)"
          proof -
            have "D.dom (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a)) = map\<^sub>0 (C\<^sub>U.P\<^sub>0 a)"
              using a 1 F\<^sub>U\<^sub>V.unit_simps(4) [of "C\<^sub>U.prj.map\<^sub>0 a"] D\<^sub>V.dom_char F\<^sub>U\<^sub>V.map\<^sub>0_def
                    D\<^sub>V.src_def map\<^sub>0_def C.obj_def F\<^sub>U\<^sub>V.preserves_arr
              by simp
            moreover have "D.arr (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))"
              using a \<open>D.seq (F (C\<^sub>U.prj.unit a)) (F\<^sub>U\<^sub>V.unit (C\<^sub>U.prj.map\<^sub>0 a))\<close> by blast
            ultimately show ?thesis
              using a D.comp_arr_dom by auto
          qed
          also have "... = F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a)"
            using a 1 F\<^sub>U\<^sub>V.unit_char' F\<^sub>U.unit_char' by simp
          finally show ?thesis by blast
        qed

        have "(\<tau>\<^sub>0 a \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a] =
              (\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a]"
          using 4 by simp
        also have "(\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a)) \<cdot>\<^sub>D
                   \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a]
                     = (\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D
                       unit (C\<^sub>U.prj.map\<^sub>0 a)) \<cdot>\<^sub>D
                       (\<tau>\<^sub>0 a \<star>\<^sub>D D.inv (unit (src\<^sub>C (C\<^sub>U.d a)))) \<cdot>\<^sub>D
                       D.inv (\<Phi> (C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a))) \<cdot>\<^sub>D
                       F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] \<cdot>\<^sub>D
                       F \<l>\<^sub>C[C\<^sub>U.d a] \<cdot>\<^sub>D
                       \<Phi> (trg\<^sub>C (C\<^sub>U.d a), C\<^sub>U.d a) \<cdot>\<^sub>D
                       (unit (trg\<^sub>C (C\<^sub>U.d a)) \<star>\<^sub>D \<tau>\<^sub>0 a)"
        proof -
          have "\<l>\<^sub>D[\<tau>\<^sub>0 a] = F \<l>\<^sub>C[C\<^sub>U.d a] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C (C\<^sub>U.d a), C\<^sub>U.d a) \<cdot>\<^sub>D
                          (unit (trg\<^sub>C (C\<^sub>U.d a)) \<star>\<^sub>D \<tau>\<^sub>0 a)"
            using a preserves_lunit [of "C\<^sub>U.counit\<^sub>0 a"] C\<^sub>U.counit.ide_map\<^sub>0_obj lunit_coherence
            by blast
          moreover
          have "\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] = (\<tau>\<^sub>0 a \<star>\<^sub>D D.inv (unit (src\<^sub>C (C\<^sub>U.d a)))) \<cdot>\<^sub>D
                            D.inv (\<Phi> (C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a))) \<cdot>\<^sub>D F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a]"
          proof -
            have "F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] =
                  \<Phi> (C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a)) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D unit (src\<^sub>C (C\<^sub>U.d a))) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]"
              using preserves_runit(2) [of "C\<^sub>U.counit\<^sub>0 a"] by simp
            moreover have 1: "D.iso (\<Phi> (C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a)))"
              using a C.VV.ide_char C.VV.arr_char C.obj_src [of "C\<^sub>U.d a"]
                    \<Phi>.components_are_iso [of "(C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a))"]
              by auto
            ultimately have "D.inv (\<Phi> (C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a))) \<cdot>\<^sub>D F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] =
                             (\<tau>\<^sub>0 a \<star>\<^sub>D unit (src\<^sub>C (C\<^sub>U.d a))) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]"
              using D.invert_side_of_triangle(1)
                      [of "F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a]" "\<Phi> (C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a))"
                          "(\<tau>\<^sub>0 a \<star>\<^sub>D unit (src\<^sub>C (C\<^sub>U.d a))) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]"]
              by fastforce
            thus ?thesis
              using D.invert_side_of_triangle(1)
                      [of "D.inv (\<Phi> (C\<^sub>U.d a, src\<^sub>C (C\<^sub>U.d a))) \<cdot>\<^sub>D F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a]"
                          "\<tau>\<^sub>0 a \<star>\<^sub>D unit (src\<^sub>C (C\<^sub>U.d a))" "\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]"]
              using C.obj_src [of "C\<^sub>U.d a"] unit_char(2) by auto
          qed
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 a \<star>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 a \<star>\<^sub>D D.inv (unit (C\<^sub>U.prj.map\<^sub>0 a))))) \<cdot>\<^sub>D
                         D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.prj.map\<^sub>0 a)) \<cdot>\<^sub>D
                         F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] \<cdot>\<^sub>D F \<l>\<^sub>C[C\<^sub>U.d a] \<cdot>\<^sub>D
                         \<Phi> (a, C\<^sub>U.d a) \<cdot>\<^sub>D
                         (unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
        proof -
          have "\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a) =
                (\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a))"
            using 1 seq D.whisker_left [of "\<tau>\<^sub>0 a"]
            by (simp add: F\<^sub>U.unit_char' F\<^sub>U\<^sub>V.unit_char')
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D
                         D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.prj.map\<^sub>0 a))) \<cdot>\<^sub>D
                         F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] \<cdot>\<^sub>D F \<l>\<^sub>C[C\<^sub>U.d a] \<cdot>\<^sub>D
                         \<Phi> (a, C\<^sub>U.d a) \<cdot>\<^sub>D
                         (unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
        proof -
          have "(\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0 a \<star>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a)) \<cdot>\<^sub>D
                (\<tau>\<^sub>0 a \<star>\<^sub>D D.inv (unit (C\<^sub>U.prj.map\<^sub>0 a))))
                  = (\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 a \<star>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a) \<cdot>\<^sub>D
                    D.inv (unit (C\<^sub>U.prj.map\<^sub>0 a)))"
          proof -
            have "D.seq (unit (C\<^sub>U.prj.map\<^sub>0 a)) (D.inv (unit (C\<^sub>U.prj.map\<^sub>0 a)))"
              using a 1 unit_char(1-2) C\<^sub>U.obj_char
              by (intro D.seqI) auto
            thus ?thesis
              using a D.whisker_left [of "\<tau>\<^sub>0 a"] by simp
          qed
          also have "... = (\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.map\<^sub>0 a))"
            using a 1 unit_char(1-2) C\<^sub>U.obj_char unit_simps [of "C\<^sub>U.prj.map\<^sub>0 a"]
            by (simp add: D.comp_arr_inv')
          also have "... = \<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F (C\<^sub>U.prj.map\<^sub>0 a)"
            using seq D.whisker_left by auto
          also have "... = \<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)"
            using D.comp_arr_dom by simp
          finally have "(\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0 a \<star>\<^sub>D unit (C\<^sub>U.prj.map\<^sub>0 a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0 a \<star>\<^sub>D D.inv (unit (C\<^sub>U.prj.map\<^sub>0 a))))
                          = \<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.P a)) \<cdot>\<^sub>D
                         (F (C\<^sub>U.d a \<star>\<^sub>C C\<^sub>U.prj.unit a) \<cdot>\<^sub>D
                         F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] \<cdot>\<^sub>D F \<l>\<^sub>C[C\<^sub>U.d a]) \<cdot>\<^sub>D
                         \<Phi> (a, C\<^sub>U.d a) \<cdot>\<^sub>D
                         (unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
        proof -
          have "(\<tau>\<^sub>0 a \<star>\<^sub>D F (C\<^sub>U.prj.unit a)) \<cdot>\<^sub>D D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.prj.map\<^sub>0 a)) =
                D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.P a)) \<cdot>\<^sub>D F (C\<^sub>U.d a \<star>\<^sub>C C\<^sub>U.prj.unit a)"
          proof -
            have "C.VV.arr (C\<^sub>U.d a, C\<^sub>U.prj.unit a)"
              using a C.VV.arr_char by simp
            thus ?thesis
              using a \<Phi>.inv_naturality [of "(C\<^sub>U.d a, C\<^sub>U.prj.unit a)"] C\<^sub>U.prj.unit_simps [of a]
                    C.VV.arr_char C.VV.dom_char C.VV.cod_char FF_def
              by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.P a)) \<cdot>\<^sub>D
                         F (C\<^sub>U.counit\<^sub>1 a \<cdot>\<^sub>C (a \<star>\<^sub>C C\<^sub>U.d a)) \<cdot>\<^sub>D
                         \<Phi> (a, C\<^sub>U.d a)) \<cdot>\<^sub>D
                         (unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
        proof -
          have "F (C\<^sub>U.d a \<star>\<^sub>C C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] \<cdot>\<^sub>D F \<l>\<^sub>C[C\<^sub>U.d a] =
                F ((C\<^sub>U.d a \<star>\<^sub>C C\<^sub>U.prj.unit a) \<cdot>\<^sub>C \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] \<cdot>\<^sub>C \<l>\<^sub>C[C\<^sub>U.d a])"
            using a by simp
          also have "... = F (C\<^sub>U.counit\<^sub>1 a \<cdot>\<^sub>C (a \<star>\<^sub>C C\<^sub>U.d a))"
          proof -
            have "C\<^sub>U.EoP.unit a = C\<^sub>U.prj.unit a"
              using a 1 C\<^sub>U.emb.map_def C\<^sub>U.EoP.unit_char' C\<^sub>U.emb.unit_char' C.comp_arr_dom
              by simp
            thus ?thesis
              using a C\<^sub>U.counit.respects_unit [of a] C\<^sub>U.I\<^sub>C.unit_char' [of a] by simp
          qed
          finally have "F (C\<^sub>U.d a \<star>\<^sub>C C\<^sub>U.prj.unit a) \<cdot>\<^sub>D F \<r>\<^sub>C\<^sup>-\<^sup>1[C\<^sub>U.d a] \<cdot>\<^sub>D F \<l>\<^sub>C[C\<^sub>U.d a] =
                        F (C\<^sub>U.counit\<^sub>1 a \<cdot>\<^sub>C (a \<star>\<^sub>C C\<^sub>U.d a))"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<tau>\<^sub>1 a \<cdot>\<^sub>D (unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
        proof -
          have "D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.P a)) \<cdot>\<^sub>D F (C\<^sub>U.counit\<^sub>1 a \<cdot>\<^sub>C (a \<star>\<^sub>C C\<^sub>U.d a)) \<cdot>\<^sub>D
                \<Phi> (a, C\<^sub>U.d a)
                  = D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.P a)) \<cdot>\<^sub>D F (C\<^sub>U.counit\<^sub>1 a) \<cdot>\<^sub>D \<Phi> (a, C\<^sub>U.d a)"
            using a C.obj_def' C.comp_arr_dom
            by (metis C\<^sub>U.counit\<^sub>1_simps(1) C\<^sub>U.counit\<^sub>1_simps(4) C.objE)
          also have "... = \<tau>\<^sub>1 a"
            using a by auto
          finally have "D.inv (\<Phi> (C\<^sub>U.d a, C\<^sub>U.P a)) \<cdot>\<^sub>D F (C\<^sub>U.counit\<^sub>1 a \<cdot>\<^sub>C (a \<star>\<^sub>C C\<^sub>U.d a)) \<cdot>\<^sub>D
                        \<Phi> (a, C\<^sub>U.d a)
                          = \<tau>\<^sub>1 a"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        finally show "(\<tau>\<^sub>0 a \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a]
                        = \<tau>\<^sub>1 a \<cdot>\<^sub>D (unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
          by blast
      qed
      show "\<And>f g. \<lbrakk>C.ide f; C.ide g; src\<^sub>C g = trg\<^sub>C f\<rbrakk> \<Longrightarrow>
                     (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp (g, f)) \<cdot>\<^sub>D
                     \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map g,
                        EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f] \<cdot>\<^sub>D
                     (\<tau>\<^sub>1 g \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f) \<cdot>\<^sub>D
                     D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (src\<^sub>C g), EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f] \<cdot>\<^sub>D
                     (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)]
                       = \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))"
      proof -
        fix f g
        assume f: "C.ide f" and g: "C.ide g" and fg: "src\<^sub>C g = trg\<^sub>C f"
        have 1: "C.ide f \<and> C.ide g \<and> C.ide (C\<^sub>U.P f) \<and> C.ide (C\<^sub>U.P g) \<and>
                 C.ide (C\<^sub>U.d (trg\<^sub>C f)) \<and> C.ide (C\<^sub>U.d (trg\<^sub>C g)) \<and>
                 src\<^sub>C (C\<^sub>U.d (trg\<^sub>C f)) = trg\<^sub>C (C\<^sub>U.P f) \<and>
                 src\<^sub>C (C\<^sub>U.d (trg\<^sub>C g)) = trg\<^sub>C (C\<^sub>U.P g) \<and>
                 trg\<^sub>C (C\<^sub>U.d (trg\<^sub>C f)) = src\<^sub>C g"
          using f g fg C\<^sub>U.emb.map\<^sub>0_def C\<^sub>U.emb.map_def C\<^sub>U.obj_char C\<^sub>U.P\<^sub>0_props(1) C.obj_simps(2)
                C\<^sub>U.prj.preserves_ide C\<^sub>U.ide_char
          by auto
        have "\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))
                = (D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                  F ((C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>C
                  \<a>\<^sub>C[C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g, C\<^sub>U.P f] \<cdot>\<^sub>C
                  (C\<^sub>U.counit\<^sub>1 g \<star>\<^sub>C C\<^sub>U.P f) \<cdot>\<^sub>C
                  C.inv \<a>\<^sub>C[g, C\<^sub>U.d (src\<^sub>C g), C\<^sub>U.P f] \<cdot>\<^sub>C
                  (g \<star>\<^sub>C C\<^sub>U.counit\<^sub>1 f) \<cdot>\<^sub>C
                  \<a>\<^sub>C[g, f, C\<^sub>U.d (src\<^sub>C f)]) \<cdot>\<^sub>D
                  \<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                  (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))"
          using f g fg C\<^sub>U.emb.map_def C\<^sub>U.counit.respects_hcomp [of f g] D.comp_arr_dom
          by simp
        also have "... = ((D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                         \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f)))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F (C\<^sub>U.P g), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 g \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (trg\<^sub>C f), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi> (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                         (D.inv (\<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                         \<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                         (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))"
        proof -
          have "F ((C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>C
                   \<a>\<^sub>C[C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g, C\<^sub>U.P f] \<cdot>\<^sub>C
                   (C\<^sub>U.counit\<^sub>1 g \<star>\<^sub>C C\<^sub>U.P f) \<cdot>\<^sub>C
                   C.inv \<a>\<^sub>C[g, C\<^sub>U.d (src\<^sub>C g), C\<^sub>U.P f] \<cdot>\<^sub>C
                   (g \<star>\<^sub>C C\<^sub>U.counit\<^sub>1 f) \<cdot>\<^sub>C
                   \<a>\<^sub>C[g, f, C\<^sub>U.d (src\<^sub>C f)])
                  = F (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>D
                    F \<a>\<^sub>C[C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g, C\<^sub>U.P f] \<cdot>\<^sub>D
                    F (C\<^sub>U.counit\<^sub>1 g \<star>\<^sub>C C\<^sub>U.P f) \<cdot>\<^sub>D
                    F (C.inv \<a>\<^sub>C[g, C\<^sub>U.d (src\<^sub>C g), C\<^sub>U.P f]) \<cdot>\<^sub>D
                    F (g \<star>\<^sub>C C\<^sub>U.counit\<^sub>1 f) \<cdot>\<^sub>D
                    F \<a>\<^sub>C[g, f, C\<^sub>U.d (src\<^sub>C f)]"
          proof -
            have "C.arr ((C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>C
                         \<a>\<^sub>C[C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g, C\<^sub>U.P f] \<cdot>\<^sub>C
                         (C\<^sub>U.counit\<^sub>1 g \<star>\<^sub>C C\<^sub>U.P f) \<cdot>\<^sub>C
                         C.inv \<a>\<^sub>C[g, C\<^sub>U.d (src\<^sub>C g), C\<^sub>U.P f] \<cdot>\<^sub>C
                         (g \<star>\<^sub>C C\<^sub>U.counit\<^sub>1 f) \<cdot>\<^sub>C
                         \<a>\<^sub>C[g, f, C\<^sub>U.d (src\<^sub>C f)])"
             using f g fg 1 C\<^sub>U.emb.map_def C.VV.arr_char C.VV.dom_char C\<^sub>U.EoP.FF_def
             by (intro C.seqI C.hseqI') auto
           thus ?thesis
             using f g fg by fastforce
          qed
          also have "... = \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))) \<cdot>\<^sub>D
                           ((D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))) \<cdot>\<^sub>D
                           \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F (C\<^sub>U.P g), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                           (D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g)) \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                           ((D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<Phi> (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f))) \<cdot>\<^sub>D
                           ((D.inv (\<Phi> (g \<star>\<^sub>C C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<Phi> (g \<star>\<^sub>C C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (\<Phi> (g, C\<^sub>U.d (trg\<^sub>C f)) \<star>\<^sub>D F (C\<^sub>U.P f))) \<cdot>\<^sub>D
                           D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (trg\<^sub>C f), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f))) \<cdot>\<^sub>D
                           ((D.inv (\<Phi> (g, C\<^sub>U.d (trg\<^sub>C f) \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<Phi> (g, C\<^sub>U.d (trg\<^sub>C f) \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D F (C\<^sub>U.counit\<^sub>1 f))) \<cdot>\<^sub>D
                           ((D.inv (\<Phi> (g, f \<star>\<^sub>C C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                           \<Phi> (g, f \<star>\<^sub>C C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D \<Phi> (f, C\<^sub>U.d (src\<^sub>C f)))) \<cdot>\<^sub>D
                           \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                           (D.inv (\<Phi> (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (\<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f)))"
            using 1 f g fg preserves_hcomp preserves_assoc C\<^sub>U.emb.map_def
                  C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def D.comp_assoc
            by simp
          also have "... = \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F (C\<^sub>U.P g), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                           ((D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g)) \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (\<Phi> (g, C\<^sub>U.d (trg\<^sub>C f)) \<star>\<^sub>D F (C\<^sub>U.P f))) \<cdot>\<^sub>D
                           D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (trg\<^sub>C f), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                           ((F g \<star>\<^sub>D D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f))) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D F (C\<^sub>U.counit\<^sub>1 f)) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D \<Phi> (f, C\<^sub>U.d (src\<^sub>C f)))) \<cdot>\<^sub>D
                           \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                           (D.inv (\<Phi> (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (\<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f)))"
          proof -
            have "(D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                          \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                          (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))
                    = \<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"
              using f g fg 1 C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
              by simp
            moreover have "(D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<Phi> (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f))
                             = F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f)"
            proof -
              have "(D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                            \<Phi> (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                            (F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f))
                      = (F (C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.P g) \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                        (F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f))"
                using f g fg 1 C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
                by simp
              also have "... = F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f)"
                using g D.comp_cod_arr f g fg C\<^sub>U.P\<^sub>0_props(1) C\<^sub>U.emb.map_def by simp
              finally show ?thesis by blast
            qed
            moreover have "(D.inv (\<Phi> (g \<star>\<^sub>C C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (\<Phi> (g \<star>\<^sub>C C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f))) \<cdot>\<^sub>D
                           (\<Phi> (g, C\<^sub>U.d (trg\<^sub>C f)) \<star>\<^sub>D F (C\<^sub>U.P f))
                             = (\<Phi> (g, C\<^sub>U.d (trg\<^sub>C f)) \<star>\<^sub>D F (C\<^sub>U.P f))"
              using f g fg 1 C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
              by simp
            moreover have "(D.inv (\<Phi> (g, C\<^sub>U.d (trg\<^sub>C f) \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<Phi> (g, C\<^sub>U.d (trg\<^sub>C f) \<star>\<^sub>C C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D F (C\<^sub>U.counit\<^sub>1 f))
                             = F g \<star>\<^sub>D F (C\<^sub>U.counit\<^sub>1 f)"
              using f g fg 1 C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
              by simp
            moreover have "(D.inv (\<Phi> (g, f \<star>\<^sub>C C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                           \<Phi> (g, f \<star>\<^sub>C C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D \<Phi> (f, C\<^sub>U.d (src\<^sub>C f)))
                             = F g \<star>\<^sub>D \<Phi> (f, C\<^sub>U.d (src\<^sub>C f))"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
              by simp
            ultimately show ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                           \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F (C\<^sub>U.P g), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                           (\<tau>\<^sub>1 g \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                           D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (trg\<^sub>C f), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                           \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                           (D.inv (\<Phi> (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (\<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f)))"
          proof -
            have "(F g \<star>\<^sub>D D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C f), C\<^sub>U.P f))) \<cdot>\<^sub>D
                  (F g \<star>\<^sub>D F (C\<^sub>U.counit\<^sub>1 f)) \<cdot>\<^sub>D
                  (F g \<star>\<^sub>D \<Phi> (f, C\<^sub>U.d (src\<^sub>C f)))
                    = F g \<star>\<^sub>D \<tau>\<^sub>1 f"
              using f g fg 1 D.whisker_left C.VV.arr_char C.VV.dom_char C.VV.cod_char
              by simp
            moreover have "(D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g)) \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (F (C\<^sub>U.counit\<^sub>1 g) \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                           (\<Phi> (g, C\<^sub>U.d (trg\<^sub>C f)) \<star>\<^sub>D F (C\<^sub>U.P f))
                             = \<tau>\<^sub>1 g \<star>\<^sub>D F (C\<^sub>U.P f)"
              using f g fg 1 D.whisker_right C.VV.arr_char C.VV.dom_char C.VV.cod_char
                    C.VV.ide_char \<Phi>.components_are_iso C\<^sub>U.emb.map_def
              by simp
            ultimately show ?thesis
              using D.comp_assoc by simp
          qed
          finally have "F ((C\<^sub>U.d (trg\<^sub>C g) \<star>\<^sub>C C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>C
                        \<a>\<^sub>C[C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P g, C\<^sub>U.P f] \<cdot>\<^sub>C
                        (C\<^sub>U.counit\<^sub>1 g \<star>\<^sub>C C\<^sub>U.P f) \<cdot>\<^sub>C
                        C.inv \<a>\<^sub>C[g, C\<^sub>U.d (src\<^sub>C g), C\<^sub>U.P f] \<cdot>\<^sub>C
                        (g \<star>\<^sub>C C\<^sub>U.counit\<^sub>1 f) \<cdot>\<^sub>C
                        \<a>\<^sub>C[g, f, C\<^sub>U.d (src\<^sub>C f)])
                          = \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                            \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F (C\<^sub>U.P g), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                            (\<tau>\<^sub>1 g \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                            D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (trg\<^sub>C f), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                            (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                            \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                            (D.inv (\<Phi> (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                            D.inv (\<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f)))"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F (C\<^sub>U.P g), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 g \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (trg\<^sub>C f), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)]"
        proof -
          have "(D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f)))
                   = \<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))"
          proof -
            have "(D.inv (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                  \<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                  (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f)))
                    = (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.P (g \<star>\<^sub>C f))) \<cdot>\<^sub>D
                      (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f)))"
            proof -
              have "D.iso (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f)))"
                using f g fg \<Phi>.components_are_iso C.VV.ide_char C.VV.arr_char
                by (metis (no_types, lifting) C\<^sub>U.prj.preserves_ide C\<^sub>U.P_simps\<^sub>B(3) C\<^sub>U.ide_char
                    C\<^sub>U.counit.ide_map\<^sub>0_obj C\<^sub>U.equivalence_data_simps\<^sub>B(7) C.hcomp_simps(2)
                    C.ideD(1) C.ide_hcomp C.obj_trg cmp_components_are_iso)
              moreover have "D.dom (\<Phi> (C\<^sub>U.d (trg\<^sub>C g), C\<^sub>U.P (g \<star>\<^sub>C f))) =
                             \<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.P (g \<star>\<^sub>C f))"
                using f g fg C\<^sub>U.ide_char C\<^sub>U.equivalence_data_simps\<^sub>B(7) C\<^sub>U.prj.preserves_ide
                      cmp_simps(4)
                by simp
              ultimately show ?thesis
                using D.comp_inv_arr' by auto
            qed
            also have "... = \<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.whisker_left [of "\<tau>\<^sub>0 (trg\<^sub>C g)"]
              by simp
            also have "... = \<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_cod_arr
              by simp
            finally show ?thesis by blast
          qed
          moreover have "\<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi> (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                         (D.inv (\<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                         \<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D
                         (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))
                           = \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)]"
          proof -
            have "D.inv (\<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D \<Phi> (g \<star>\<^sub>C f, C\<^sub>U.d (src\<^sub>C f)) =
                    F (g \<star>\<^sub>C f) \<star>\<^sub>D F (C\<^sub>U.d (src\<^sub>C f))"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
              by simp
            moreover have "(F (g \<star>\<^sub>C f) \<star>\<^sub>D F (C\<^sub>U.d (src\<^sub>C f))) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) =
                           \<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
              by simp
            moreover have "(D.inv (\<Phi> (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) =
                           (F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
                    \<Phi>.components_are_iso C.VV.ide_char FF_def
                    D.whisker_right [of "\<tau>\<^sub>0 (src\<^sub>C f)" "D.inv (\<Phi> (g, f))" "\<Phi> (g, f)"]
              by simp
            moreover have "\<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D ((F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) =
                           \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)]"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def D.comp_inv_arr' D.comp_arr_dom D.comp_cod_arr
              by simp
            ultimately show ?thesis by argo
          qed
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>D
                         \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F (C\<^sub>U.P g), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 g \<star>\<^sub>D F (C\<^sub>U.P f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (trg\<^sub>C f), F (C\<^sub>U.P f)] \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)]"
        proof -
          have "(\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f))) \<cdot>\<^sub>D
                (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))
                  = \<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F (C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"
          proof -
            have "D.arr (F (C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char C\<^sub>U.EoP.FF_def
                    C\<^sub>U.emb.map_def
              by (intro D.seqI) auto
            thus ?thesis
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char
                    D.whisker_left [of "\<tau>\<^sub>0 (trg\<^sub>C g)"]
              by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map g,
                            EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 g \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (src\<^sub>C g), EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f] \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)]"
        proof -
          have "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp (g, f) =
                F (C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"
          proof -
            have "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp (g, f) =
                    F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D ((F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (C\<^sub>U.\<Phi>\<^sub>P (g, f))) \<cdot>\<^sub>D
                    \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D D\<^sub>V.\<Phi>\<^sub>E (F (C\<^sub>U.P g), F (C\<^sub>U.P f))"
            proof -
              have 3: "D.arr (F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (C\<^sub>U.\<Phi>\<^sub>P (g, f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))"
                using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char FF_def C\<^sub>U.prj.FF_def
                      C\<^sub>U.\<Phi>\<^sub>P_in_hom [of g f] C\<^sub>U.hcomp_def C\<^sub>U.in_hom_char
                by (intro D.seqI) auto
              have 4: "D\<^sub>V.arr (\<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))"
                using f g fg 1 cmp_in_hom(1) [of "C\<^sub>U.P g" "C\<^sub>U.P f"] C\<^sub>U.prj.map\<^sub>0_simps(1)
                      C\<^sub>U.obj_char D\<^sub>V.arr_char V_def
                by auto
              moreover have 5: "D\<^sub>V.arr (F (C\<^sub>U.\<Phi>\<^sub>P (g, f)))"
                using f g fg 1 C\<^sub>U.\<Phi>\<^sub>P_simps [of g f] F\<^sub>U\<^sub>V.preserves_arr by presburger
              moreover have 6: "D\<^sub>V.arr (F (C\<^sub>U.P (g \<star>\<^sub>C f)))"
                using f g fg C\<^sub>U.P_simps(1) [of "g \<star>\<^sub>C f"] F\<^sub>U\<^sub>V.preserves_arr by simp
              moreover have 7: "D\<^sub>V.arr (F (C\<^sub>U.\<Phi>\<^sub>P (g, f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))"
                using 3 4 5 D\<^sub>V.seq_char [of "F (C\<^sub>U.\<Phi>\<^sub>P (g, f))" "\<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"]
                      D\<^sub>V.comp_char [of "F (C\<^sub>U.\<Phi>\<^sub>P (g, f))" "\<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"]
                by auto
              moreover have "D.seq (F (C\<^sub>U.\<Phi>\<^sub>P (g, f))) (\<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))"
                using 3 by blast
              moreover have "D.seq (F (C\<^sub>U.P (g \<star>\<^sub>C f)))
                                   (F (C\<^sub>U.\<Phi>\<^sub>P (g, f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))"
                using 3 by blast
              moreover have "D\<^sub>V.arr (F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (C\<^sub>U.\<Phi>\<^sub>P (g, f)) \<cdot>\<^sub>D
                                     \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f))"
                using f g fg 3 6 7 D.vseq_implies_hpar D\<^sub>V.arr_char V_def
                by (metis (no_types, lifting) D\<^sub>V.comp_char D\<^sub>V.seq_char)
              ultimately show ?thesis
                using f g fg EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.cmp_def EQ\<^sub>U\<^sub>VoEQ\<^sub>C'.FH.cmp_def
                      C.VV.arr_char C.VV.dom_char C\<^sub>U.VV.arr_char D\<^sub>V.comp_char
                      D\<^sub>V.emb.map_def D.comp_assoc
                by simp
            qed
            also have "... = F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (C\<^sub>U.\<Phi>\<^sub>P (g, f)) \<cdot>\<^sub>D
                             \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f) \<cdot>\<^sub>D D\<^sub>V.\<Phi>\<^sub>E (F (C\<^sub>U.P g), F (C\<^sub>U.P f))"
            proof -
              have "F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (C\<^sub>U.\<Phi>\<^sub>P (g, f)) = F (C\<^sub>U.\<Phi>\<^sub>P (g, f))"
              proof -
                have 1: "C.arr (C\<^sub>U.\<Phi>\<^sub>P (g, f))"
                  using f g fg C.VV.arr_char
                  by (metis (no_types, lifting) C\<^sub>U.prj.preserves_hcomp C\<^sub>U.prj.preserves_ide
                      C\<^sub>U.ide_char C\<^sub>U.seq_char C.ideD(1) C.ideD(3) C.ide_hcomp C.seqE)
                moreover have "C.cod (C\<^sub>U.\<Phi>\<^sub>P (g, f)) = C\<^sub>U.P (g \<star>\<^sub>C f)"
                  using f g fg C.VV.arr_char C\<^sub>U.\<Phi>\<^sub>P_in_hom(2) [of g f]
                        C\<^sub>U.hcomp_def C\<^sub>U.in_hom_char by auto
                ultimately have "D.cod (F (C\<^sub>U.\<Phi>\<^sub>P (g, f))) = F (C\<^sub>U.P (g \<star>\<^sub>C f))"
                  using f g fg C.VV.arr_char preserves_cod [of "C\<^sub>U.\<Phi>\<^sub>P (g, f)"]
                  by simp
                thus ?thesis
                  using 1 f g fg D.comp_cod_arr [of "F (C\<^sub>U.\<Phi>\<^sub>P (g, f))" "F (C\<^sub>U.P (g \<star>\<^sub>C f))"]
                  by simp
              qed
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = F (C\<^sub>U.P (g \<star>\<^sub>C f)) \<cdot>\<^sub>D F (C\<^sub>U.\<Phi>\<^sub>P (g, f)) \<cdot>\<^sub>D
                             F (C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"
            proof -
              have "D\<^sub>V.\<Phi>\<^sub>E (F (C\<^sub>U.P g), F (C\<^sub>U.P f)) = F (C\<^sub>U.P g) \<star>\<^sub>D F (C\<^sub>U.P f)"
                using f g fg D\<^sub>V.emb.cmp_def D\<^sub>V.VV.arr_char D\<^sub>V.src_def D\<^sub>V.trg_def
                      F\<^sub>U\<^sub>V.preserves_arr
                by auto
              moreover have "C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f) = C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f"
                using f g fg C\<^sub>U.VV.arr_char C\<^sub>U.emb.cmp_def by simp
              ultimately
              have "\<Phi> (C\<^sub>U.P g, C\<^sub>U.P f) \<cdot>\<^sub>D D\<^sub>V.\<Phi>\<^sub>E (F (C\<^sub>U.P g), F (C\<^sub>U.P f)) =
                      F (C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"
                using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char FF_def
                      \<Phi>.naturality [of "(C\<^sub>U.P g, C\<^sub>U.P f)"]
                by simp
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = F (C\<^sub>U.P (g \<star>\<^sub>C f) \<cdot>\<^sub>C C\<^sub>U.\<Phi>\<^sub>P (g, f) \<cdot>\<^sub>C C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f)) \<cdot>\<^sub>D
                             \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"
            proof -
              have "C.arr (C\<^sub>U.P (g \<star>\<^sub>C f) \<cdot>\<^sub>C C\<^sub>U.\<Phi>\<^sub>P (g, f) \<cdot>\<^sub>C C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f))"
              proof (intro C.seqI)
                show "C.arr (C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f))"
                  using f g fg by auto
                show 1: "C.arr (C\<^sub>U.\<Phi>\<^sub>P (g, f))"
                  using f g fg C\<^sub>U.arr_char C\<^sub>U.\<Phi>\<^sub>P_simps(1) [of g f] by auto
                show "C.dom (C\<^sub>U.\<Phi>\<^sub>P (g, f)) = C.cod (C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f))"
                proof -
                  have "C.dom (C\<^sub>U.\<Phi>\<^sub>P (g, f)) = C\<^sub>U.hcomp (C\<^sub>U.P g) (C\<^sub>U.P f)"
                    using f g fg C\<^sub>U.VV.arr_char C\<^sub>U.\<Phi>\<^sub>P_simps(4) [of g f]
                          C\<^sub>U.dom_char [of "C\<^sub>U.\<Phi>\<^sub>P (g, f)"]
                    by fastforce
                  also have "... = C\<^sub>U.P g \<star>\<^sub>C (C\<^sub>U.P f)"
                    using f g fg by auto
                  also have "... = C.cod (C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f))"
                    using f g fg C\<^sub>U.emb.cmp_def [of "(C\<^sub>U.P g, C\<^sub>U.P f)"] by auto
                  finally show ?thesis by blast
                qed
                show "C.arr (C\<^sub>U.P (g \<star>\<^sub>C f))"
                  using f g fg by simp
                show "C.dom (C\<^sub>U.P (g \<star>\<^sub>C f)) =
                      C.cod (C\<^sub>U.\<Phi>\<^sub>P (g, f) \<cdot>\<^sub>C C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f))"
                proof -
                  have "C.dom (C\<^sub>U.P (g \<star>\<^sub>C f)) = C\<^sub>U.P (g \<star>\<^sub>C f)"
                    using f g fg by simp
                  also have "... = C.cod (C\<^sub>U.\<Phi>\<^sub>P (g, f))"
                    using f g fg C\<^sub>U.\<Phi>\<^sub>P_simps(5) [of g f] C\<^sub>U.cod_char [of "C\<^sub>U.\<Phi>\<^sub>P (g, f)"]
                    by fastforce
                  also have "... = C.cod (C\<^sub>U.\<Phi>\<^sub>P (g, f) \<cdot>\<^sub>C C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f))"
                  proof -
                    have 2: "C\<^sub>U.hcomp (C\<^sub>U.P g) (C\<^sub>U.P f) = C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f"
                      using f g fg by auto
                    have "C\<^sub>U.arr (C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f)"
                    proof -
                      have "C\<^sub>U.arr (C\<^sub>U.hcomp (C\<^sub>U.P g) (C\<^sub>U.P f))"
                        using f g fg by simp
                      thus ?thesis
                        using 2 by simp
                    qed
                    moreover have "C.dom (C\<^sub>U.\<Phi>\<^sub>P (g, f)) = C\<^sub>U.P g \<star>\<^sub>C C\<^sub>U.P f"
                      using f g fg 2 C\<^sub>U.VV.arr_char C\<^sub>U.\<Phi>\<^sub>P_simps(4) [of g f]
                            C\<^sub>U.dom_char [of "C\<^sub>U.\<Phi>\<^sub>P (g, f)"]
                      by fastforce
                    ultimately have "C.arr (C\<^sub>U.\<Phi>\<^sub>P (g, f) \<cdot>\<^sub>C C\<^sub>U.\<Phi>\<^sub>E (C\<^sub>U.P g, C\<^sub>U.P f))"
                      using f g fg 1 C\<^sub>U.VV.arr_char C\<^sub>U.VV.cod_char C\<^sub>U.hcomp_char
                            C\<^sub>U.emb.map_def
                      by auto
                    thus ?thesis by simp
                  qed
                  finally show ?thesis by blast
                qed
              qed
              thus ?thesis
                using D.comp_assoc by auto
            qed
            also have "... = F (C\<^sub>U.EoP.cmp (g, f)) \<cdot>\<^sub>D \<Phi> (C\<^sub>U.P g, C\<^sub>U.P f)"
              using f g fg C\<^sub>U.EoP.cmp_def C.VV.arr_char C.VV.dom_char C\<^sub>U.emb.map_def
              by simp
            finally show ?thesis by blast
          qed
          moreover have "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map g = F (C\<^sub>U.P g)"
          proof -
            have "D\<^sub>V.arr (F (C\<^sub>U.P g))"
              using g D\<^sub>V.arr_char C\<^sub>U.P_simps(1) C.ideD(1) F\<^sub>U\<^sub>V.preserves_arr by presburger
            thus ?thesis
              using g D\<^sub>V.emb.map_def by simp
          qed
          moreover have "EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f = F (C\<^sub>U.P f)"
          proof -
            have "D\<^sub>V.arr (F (C\<^sub>U.P f))"
              using f D\<^sub>V.arr_char C\<^sub>U.P_simps(1) C.ideD(1) F\<^sub>U\<^sub>V.preserves_arr by presburger
            thus ?thesis
              using f D\<^sub>V.emb.map_def by simp
          qed
          ultimately show ?thesis
            using fg by argo
        qed
        finally show "(\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp (g, f)) \<cdot>\<^sub>D
                      \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map g,
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f] \<cdot>\<^sub>D
                      (\<tau>\<^sub>1 g \<star>\<^sub>D EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f) \<cdot>\<^sub>D
                      D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0 (src\<^sub>C g), EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map f] \<cdot>\<^sub>D
                      (F g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0 (src\<^sub>C f)]
                        = \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))"
          by argo
      qed
    qed

    interpretation EQ: equivalence_of_bicategories_and_pseudonatural_equivalence_left  (* 25 sec *)
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_cmp
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>1
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>1
                         F \<Phi> \<tau>\<^sub>0 \<tau>\<^sub>1
    proof -
      interpret E: equivalence_of_bicategories
                      V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_cmp
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>1
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>1
        using induces_equivalence_of_bicategories by simp
      interpret \<tau>: pseudonatural_equivalence
                      V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                      EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp F \<Phi> \<tau>\<^sub>0 \<tau>\<^sub>1
        ..
      show "equivalence_of_bicategories_and_pseudonatural_equivalence_left
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.left_cmp
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_cmp
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.unit\<^sub>1
                         EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>0 EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.counit\<^sub>1
                         F \<Phi> \<tau>\<^sub>0 \<tau>\<^sub>1"
        ..
    qed

    definition right_map
    where "right_map \<equiv> EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_map"

    definition right_cmp
    where "right_cmp \<equiv> EQ\<^sub>DoEQ\<^sub>U\<^sub>VoEQ\<^sub>C'.right_cmp"

    definition unit\<^sub>0
    where "unit\<^sub>0 \<equiv> EQ.unit.map\<^sub>0"

    definition unit\<^sub>1
    where "unit\<^sub>1 \<equiv> EQ.unit.map\<^sub>1"

    definition counit\<^sub>0
    where "counit\<^sub>0 \<equiv> EQ.counit.map\<^sub>0"

    definition counit\<^sub>1
    where "counit\<^sub>1 \<equiv> EQ.counit.map\<^sub>1"

    theorem extends_to_equivalence_of_bicategories:
    shows "equivalence_of_bicategories V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
             F \<Phi> right_map right_cmp unit\<^sub>0 unit\<^sub>1 counit\<^sub>0 counit\<^sub>1"
      unfolding right_map_def right_cmp_def unit\<^sub>0_def unit\<^sub>1_def counit\<^sub>0_def counit\<^sub>1_def
      ..

  end

  locale converse_equivalence_pseudofunctor =  (* 10 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
  for V\<^sub>C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'd"
  begin

    interpretation E: equivalence_of_bicategories
                        V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                        F \<Phi>\<^sub>F F.right_map F.right_cmp F.unit\<^sub>0 F.unit\<^sub>1 F.counit\<^sub>0 F.counit\<^sub>1
      using F.extends_to_equivalence_of_bicategories by simp
    interpretation E': converse_equivalence_of_bicategories
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                         F \<Phi>\<^sub>F F.right_map F.right_cmp F.unit\<^sub>0 F.unit\<^sub>1 F.counit\<^sub>0 F.counit\<^sub>1
      ..

    sublocale equivalence_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                F.right_map F.right_cmp
      using E'.equivalence_pseudofunctor_left by simp

    lemma is_equivalence_pseudofunctor:
    shows "equivalence_pseudofunctor V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
                F.right_map F.right_cmp"
      ..

  end

  (*
   * TODO: Change the following definition to be based on the existence of an equivalence of
   * bicategories, rather than an equivalence pseudofunctor.  This will require a few changes
   * elsewhere.
   *)

  definition equivalent_bicategories
  where "equivalent_bicategories V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C \<equiv>
         \<exists>F \<Phi>. equivalence_pseudofunctor
                 V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>"

  lemma equivalent_bicategories_reflexive:
  assumes "bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  shows "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  proof -
    interpret bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C
      using assms by simp
    interpret I: identity_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C ..
    show ?thesis
      using I.equivalence_pseudofunctor_axioms equivalent_bicategories_def by blast
  qed

  lemma equivalent_bicategories_symmetric:
  assumes "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
  shows "equivalent_bicategories V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  proof -
    obtain F \<Phi>\<^sub>F where F: "equivalence_pseudofunctor
                            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F"
      using assms equivalent_bicategories_def by blast
    interpret F: equivalence_pseudofunctor
                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
      using F by simp
    interpret G: converse_equivalence_pseudofunctor
                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
      ..
    show ?thesis
      using G.is_equivalence_pseudofunctor equivalent_bicategories_def by blast
  qed

  lemma equivalent_bicategories_transitive:
  assumes "equivalent_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C"
  and "equivalent_bicategories V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
  shows "equivalent_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
  proof -
    obtain F \<Phi>\<^sub>F where F: "equivalence_pseudofunctor
                            V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F"
      using assms(1) equivalent_bicategories_def by blast
    obtain G \<Phi>\<^sub>G where G: "equivalence_pseudofunctor
                            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G"
      using assms(2) equivalent_bicategories_def by blast
    interpret F: equivalence_pseudofunctor
                   V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F
      using F by simp
    interpret G: equivalence_pseudofunctor
                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
      using G by simp
    interpret GF: composite_equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                    V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G ..
    show "equivalent_bicategories V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D"
      using equivalent_bicategories_def GF.equivalence_pseudofunctor_axioms by blast
  qed

end
