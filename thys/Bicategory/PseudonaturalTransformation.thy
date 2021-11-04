(*  Title:       PseudonaturalTransformation
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Pseudonatural Transformations"

theory PseudonaturalTransformation
imports InternalEquivalence InternalAdjunction Pseudofunctor
begin

  subsection "Definition of Pseudonatural Transformation"

  text \<open>
    Pseudonatural transformations are a generalization of natural transformations that is
    appropriate for pseudofunctors.  The ``components'' of a pseudonatural transformation \<open>\<tau>\<close>
    from a pseudofunctor \<open>F\<close> to a pseudofunctor \<open>G\<close> (both from bicategory \<open>C\<close> to \<open>D\<close>),
    are 1-cells \<open>\<guillemotleft>\<tau>\<^sub>0 a : F\<^sub>0 a \<rightarrow>\<^sub>D G\<^sub>0 a\<guillemotright>\<close> associated with the objects of \<open>C\<close>.  Instead of
    ``naturality squares'' that commute on-the-nose, a pseudonatural transformation associates
    an invertible 2-cell \<open>\<guillemotleft>\<tau>\<^sub>1 f : G f \<star>\<^sub>D \<tau>\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0 a' \<star>\<^sub>D F f\<guillemotright>\<close> with each 1-cell \<open>\<guillemotleft>f : a \<rightarrow>\<^sub>C a'\<guillemotright>\<close>
    of \<open>C\<close>.  The 1-cells \<open>\<tau>\<^sub>0 a\<close> and 2-cells \<open>\<tau>\<^sub>1 f\<close> are subject to coherence conditions which
    express that they transform naturally across 2-cells of \<open>C\<close> and behave sensibly with
    respect to objects and horizontal composition.

    In formalizing ordinary natural transformations, we found it convenient to treat them
    similarly to functors in that a natural transformation \<open>\<tau> : C \<rightarrow> D\<close> maps arrows of \<open>C\<close>
    to arrows of \<open>D\<close>; the components \<open>\<tau> a\<close> at objects \<open>a\<close> being merely special cases.
    However, it is not possible to take the same approach for pseudofunctors, because it is
    not possible to treat the components \<open>\<tau>\<^sub>0 a\<close> at objects \<open>a\<close> as a special case of the
    components \<open>\<tau>\<^sub>1 f\<close> at 1-cells \<open>f\<close>.  So we have to regard a pseudonatural transformation \<open>\<tau>\<close>
    as consisting of two separate mappings: a mapping \<open>\<tau>\<^sub>0\<close> from objects of \<open>C\<close> to 1-cells
    of \<open>D\<close> and a mapping \<open>\<tau>\<^sub>1\<close> from 1-cells of \<open>C\<close> to invertible 2-cells of \<open>D\<close>.

    Pseudonatural transformations are themselves a special case of the more general notion
    of ``lax natural transformations'' between pseudofunctors.  For a lax natural transformation
    \<open>\<tau>\<close>, the 2-cells \<open>\<tau>\<^sub>1 f\<close> are not required to be invertible.  This means that there is a
    distinction between a lax natural transformation with \<open>\<guillemotleft>\<tau>\<^sub>1 f : G f \<star>\<^sub>D \<tau>\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0 a' \<star>\<^sub>D F f\<guillemotright>\<close>
    and an ``op-lax'' natural transformation with \<open>\<guillemotleft>\<tau>\<^sub>1 f : \<tau>\<^sub>0 a' \<star>\<^sub>D F f \<Rightarrow>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a\<guillemotright>\<close>.
    There is some variation in the literature on which direction is considered ``lax'' and
    which is ``op-lax'' and this variation extends as well to the special case of pseudofunctors,
    though in that case it does not result in any essential difference in the notion,
    due to the assumed invertibility.  We have chosen the direction that agrees with
    Leinster \cite{leinster-basic-bicategories}, and with the ``nLab'' article
    \cite{nlab-lax-natural-transformation} on lax natural transformations, but note that the
    ``nLab'' article \cite{nlab-pseudonatural-transformation} on pseudonatural transformations
    seems to make the opposite choice.
  \<close>

  locale pseudonatural_transformation =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F +
    G: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
  for V\<^sub>C :: "'c comp"                   (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                   (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'd"
  and G :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>G :: "'c * 'c \<Rightarrow> 'd"
  and \<tau>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<tau>\<^sub>1 :: "'c \<Rightarrow> 'd" +
  assumes map\<^sub>0_in_hhom: "C.obj a \<Longrightarrow> \<guillemotleft>\<tau>\<^sub>0 a : src\<^sub>D (F a) \<rightarrow>\<^sub>D src\<^sub>D (G a)\<guillemotright>"
  and map\<^sub>1_in_vhom: "C.ide f \<Longrightarrow> \<guillemotleft>\<tau>\<^sub>1 f : G f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f\<guillemotright>"
  and ide_map\<^sub>0_obj: "C.obj a \<Longrightarrow> D.ide (\<tau>\<^sub>0 a)"
  and iso_map\<^sub>1_ide: "C.ide f \<Longrightarrow> D.iso (\<tau>\<^sub>1 f)"
  and naturality: "C.arr \<mu> \<Longrightarrow>
                     \<tau>\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)) = (\<tau>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1 (C.dom \<mu>)"
  and respects_unit: "C.obj a \<Longrightarrow>
                        (\<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a] = \<tau>\<^sub>1 a \<cdot>\<^sub>D (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
  and respects_hcomp:
        "\<lbrakk> C.ide f; C.ide g; src\<^sub>C g = trg\<^sub>C f \<rbrakk> \<Longrightarrow>
             (\<tau>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D (\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
             D.inv \<a>\<^sub>D[G g, \<tau>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 (src\<^sub>C f)]
               = \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))"
  begin

    lemma map\<^sub>0_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>\<tau>\<^sub>0 a : F.map\<^sub>0 a \<rightarrow>\<^sub>D G.map\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<tau>\<^sub>0 a : \<tau>\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0 a\<guillemotright>"
      using assms map\<^sub>0_in_hhom [of a]
       apply fastforce
      using assms ide_map\<^sub>0_obj [of a] by fast

    lemma map\<^sub>0_simps [simp]:
    assumes "C.obj a"
    shows "D.ide (\<tau>\<^sub>0 a)"
    and "src\<^sub>D (\<tau>\<^sub>0 a) = F.map\<^sub>0 a" and "trg\<^sub>D (\<tau>\<^sub>0 a) = G.map\<^sub>0 a"
      using assms map\<^sub>0_in_hom iso_map\<^sub>1_ide ide_map\<^sub>0_obj by auto

    lemma map\<^sub>1_in_hom [intro]:
    assumes "C.ide f"
    shows "\<guillemotleft>\<tau>\<^sub>1 f : F.map\<^sub>0 (src\<^sub>C f) \<rightarrow>\<^sub>D G.map\<^sub>0 (trg\<^sub>C f)\<guillemotright>"
    and "\<guillemotleft>\<tau>\<^sub>1 f : G f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f\<guillemotright>"
      using assms map\<^sub>1_in_vhom [of f] D.vconn_implies_hpar(1-2) by auto

    lemma map\<^sub>1_simps [simp]:
    assumes "C.ide f"
    shows "D.arr (\<tau>\<^sub>1 f)"
    and "src\<^sub>D (\<tau>\<^sub>1 f) = F.map\<^sub>0 (src\<^sub>C f)"
    and "trg\<^sub>D (\<tau>\<^sub>1 f) = G.map\<^sub>0 (trg\<^sub>C f)"
    and "D.dom (\<tau>\<^sub>1 f) = G f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)"
    and "D.cod (\<tau>\<^sub>1 f) = \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f"
      using assms map\<^sub>1_in_hom iso_map\<^sub>1_ide by auto

    lemma inv_naturality:
    assumes "C.arr \<mu>"
    shows "(G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 (C.dom \<mu>)) =
           D.inv (\<tau>\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D (\<tau>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>)"
      using assms naturality iso_map\<^sub>1_ide D.invert_opposite_sides_of_square by simp

  end

  subsection "Identity Pseudonatural Transformation"

  locale identity_pseudonatural_transformation =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
  for V\<^sub>C :: "'c comp"                   (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                   (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'd"
  begin

    abbreviation (input) map\<^sub>0
    where "map\<^sub>0 a \<equiv> F.map\<^sub>0 a"

    abbreviation (input) map\<^sub>1
    where "map\<^sub>1 f \<equiv> \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<cdot>\<^sub>D \<r>\<^sub>D[F f]"

    sublocale pseudonatural_transformation
                V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F F \<Phi>\<^sub>F map\<^sub>0 map\<^sub>1
    proof
      show 1: "\<And>a. C.obj a \<Longrightarrow> D.ide (F.map\<^sub>0 a)"
        using F.map\<^sub>0_simps(1) by blast
      show "\<And>f. C.ide f \<Longrightarrow> D.iso (map\<^sub>1 f)"
        by auto
      show "\<And>a. C.obj a \<Longrightarrow> \<guillemotleft>F.map\<^sub>0 a : src\<^sub>D (F a) \<rightarrow>\<^sub>D src\<^sub>D (F a)\<guillemotright>"
        by (metis C.obj_def' D.in_hhomI D.src.preserves_arr F.map\<^sub>0_def F.map\<^sub>0_simps(2)
            F.map\<^sub>0_simps(3) F.preserves_reflects_arr)
      show "\<And>f. C.ide f \<Longrightarrow> \<guillemotleft>map\<^sub>1 f : F f \<star>\<^sub>D F.map\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D F.map\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f\<guillemotright>"
        by simp
      show "\<And>\<mu>. C.arr \<mu> \<Longrightarrow>
                  (map\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D F.map\<^sub>0 (src\<^sub>C \<mu>))
                    = (F.map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D map\<^sub>1 (C.dom \<mu>)"
        by (metis D.comp_assoc D.lunit'_naturality D.runit_naturality F.preserves_arr
            F.preserves_cod F.preserves_dom F.preserves_src F.preserves_trg)
      show "\<And>f g. \<lbrakk>C.ide f; C.ide g; src\<^sub>C g = trg\<^sub>C f\<rbrakk> \<Longrightarrow>
                    (F.map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D[F.map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                    (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<cdot>\<^sub>D \<r>\<^sub>D[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                    D.inv \<a>\<^sub>D[F g, F.map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                    (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<cdot>\<^sub>D \<r>\<^sub>D[F f]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[F g, F f, F.map\<^sub>0 (src\<^sub>C f)]
                      = (\<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D \<r>\<^sub>D[F (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D F.map\<^sub>0 (src\<^sub>C f))"
      proof -
        fix f g
        assume f: "C.ide f" and g: "C.ide g" and fg: "src\<^sub>C g = trg\<^sub>C f"
        have "(F.map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
              \<a>\<^sub>D[F.map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
              (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<cdot>\<^sub>D \<r>\<^sub>D[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
              D.inv \<a>\<^sub>D[F g, F.map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
              (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<cdot>\<^sub>D \<r>\<^sub>D[F f]) \<cdot>\<^sub>D
              \<a>\<^sub>D[F g, F f, F.map\<^sub>0 (src\<^sub>C f)]
                = (F.map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                  (\<a>\<^sub>D[F.map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                  (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                  (\<r>\<^sub>D[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                  (D.inv \<a>\<^sub>D[F g, F.map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                  (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f])) \<cdot>\<^sub>D
                  (F g \<star>\<^sub>D \<r>\<^sub>D[F f]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[F g, F f, F.map\<^sub>0 (src\<^sub>C f)]"
          using f g fg D.whisker_right [of "F f"] D.whisker_left [of "F g"] D.comp_assoc
          by simp
        also have "... = (F.map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<cdot>\<^sub>D
                         ((\<r>\<^sub>D[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                         \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
        proof -
          have "D.inv \<a>\<^sub>D[F g, F.map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]) = \<r>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f"
          proof -
            have "D.inv \<a>\<^sub>D[F g, F.map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]) =
                  D.inv ((F g \<star>\<^sub>D \<l>\<^sub>D[F f]) \<cdot>\<^sub>D \<a>\<^sub>D[F g, F.map\<^sub>0 (src\<^sub>C g), F f])"
              using f g fg 1 D.inv_comp by auto
            also have "... = D.inv (\<r>\<^sub>D[F g] \<star>\<^sub>D F f)"
              using f g fg D.triangle [of "F f" "F g"] by simp
            also have "... = \<r>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f"
              using f g fg by simp
            finally show ?thesis by blast
          qed
          moreover have "(F g \<star>\<^sub>D \<r>\<^sub>D[F f]) \<cdot>\<^sub>D \<a>\<^sub>D[F g, F f, F.map\<^sub>0 (src\<^sub>C f)] = \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
            using f g fg D.runit_hcomp(1) by simp
          moreover have "\<a>\<^sub>D[F.map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f)
                           = \<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f]"
            using f g fg D.lunit_hcomp(4) by simp
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((F.map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f]) \<cdot>\<^sub>D \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
        proof -
          have "((\<r>\<^sub>D[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<r>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f)) \<cdot>\<^sub>D \<r>\<^sub>D[F g \<star>\<^sub>D F f] = \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
          proof -
            have "((\<r>\<^sub>D[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<r>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f)) \<cdot>\<^sub>D \<r>\<^sub>D[F g \<star>\<^sub>D F f] =
                   (\<r>\<^sub>D[F g] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
              using f g fg D.whisker_right by simp
            also have "... = (F g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
              using f g fg D.comp_arr_inv' by simp
            also have "... = \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
              using f g fg D.comp_cod_arr by simp
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D \<Phi>\<^sub>F (g, f) \<cdot>\<^sub>D \<r>\<^sub>D[F g \<star>\<^sub>D F f]"
          using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char F.FF_def
                D.lunit'_naturality [of "\<Phi>\<^sub>F (g, f)"] D.comp_assoc
          by simp
        also have "... = (\<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D \<r>\<^sub>D[F (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D F.map\<^sub>0 (src\<^sub>C f))"
          using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char F.FF_def
                D.runit_naturality [of "\<Phi>\<^sub>F (g, f)"] D.comp_assoc
          by simp
        finally show "(F.map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                      \<a>\<^sub>D[F.map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                      (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<cdot>\<^sub>D \<r>\<^sub>D[F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                      D.inv \<a>\<^sub>D[F g, F.map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                      (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<cdot>\<^sub>D \<r>\<^sub>D[F f]) \<cdot>\<^sub>D
                      \<a>\<^sub>D[F g, F f, F.map\<^sub>0 (src\<^sub>C f)]
                        = (\<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D \<r>\<^sub>D[F (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D F.map\<^sub>0 (src\<^sub>C f))"
          by simp
      qed
      show "\<And>a. C.obj a \<Longrightarrow>
                  (F.map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F.map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[F.map\<^sub>0 a] =
                  map\<^sub>1 a \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D F.map\<^sub>0 a)"
      proof -
        fix a
        assume a: "C.obj a"
        have "(F.map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F.map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[F.map\<^sub>0 a] =
              (F.map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F.map\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[F.map\<^sub>0 a]"
          using a 1 D.unitor_coincidence by simp
        also have "... = ((F.map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F.map\<^sub>0 a]) \<cdot>\<^sub>D \<r>\<^sub>D[F.map\<^sub>0 a]"
          using D.comp_assoc by simp
        also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[F a] \<cdot>\<^sub>D F.unit a \<cdot>\<^sub>D \<r>\<^sub>D[F.map\<^sub>0 a]"
          using a 1 D.lunit'_naturality [of "F.unit a"] D.comp_assoc by simp
        also have "... = map\<^sub>1 a \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D F.map\<^sub>0 a)"
          using a 1 D.runit_naturality [of "F.unit a"] D.comp_assoc by simp
        finally show "(F.map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F.map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[F.map\<^sub>0 a] =
                      map\<^sub>1 a \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D F.map\<^sub>0 a)"
          by blast
      qed
    qed

    lemma is_pseudonatural_transformation:
    shows "pseudonatural_transformation
             V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F F \<Phi>\<^sub>F map\<^sub>0 map\<^sub>1"
      ..

  end

  subsection "Composite Pseudonatural Transformation"

  text \<open>
    A pseudonatural transformation \<open>\<sigma>\<close> from \<open>F\<close> to \<open>G\<close> and a pseudonatural transformation \<open>\<rho>\<close>
    from \<open>G\<close> to \<open>H\<close> can be composed to obtain a pseudonatural transformation \<open>\<tau>\<close> from
    \<open>F\<close> to \<open>H\<close>.  The components at objects are composed via horizontal composition.
    Composing the components at 1-cells is straightforward, but is formally complicated by
    the need for associativities.  The additional complexity leads to somewhat lengthy
    proofs of the coherence conditions.  This issue only gets worse as we consider additional
    constructions on pseudonatural transformations.
  \<close>

  locale composite_pseudonatural_transformation =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F +
    G: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G +
    H: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D H \<Phi>\<^sub>H +
    \<sigma>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<sigma>\<^sub>0 \<sigma>\<^sub>1 +
    \<rho>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G H \<Phi>\<^sub>H \<rho>\<^sub>0 \<rho>\<^sub>1
  for V\<^sub>C :: "'c comp"                   (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                   (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'd"
  and G :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>G :: "'c * 'c \<Rightarrow> 'd"
  and H :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>H :: "'c * 'c \<Rightarrow> 'd"
  and \<sigma>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<sigma>\<^sub>1 :: "'c \<Rightarrow> 'd"
  and \<rho>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<rho>\<^sub>1 :: "'c \<Rightarrow> 'd"
  begin

    definition map\<^sub>0
    where "map\<^sub>0 a = \<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a"

    definition map\<^sub>1
    where "map\<^sub>1 f = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C f), \<sigma>\<^sub>0 (trg\<^sub>C f), F f] \<cdot>\<^sub>D
                    (\<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                    (\<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]"

    sublocale pseudonatural_transformation
      V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F H \<Phi>\<^sub>H map\<^sub>0 map\<^sub>1
    proof
      show "\<And>a. C.obj a \<Longrightarrow> D.ide (map\<^sub>0 a)"
        unfolding map\<^sub>0_def by fastforce
      show "\<And>a. C.obj a \<Longrightarrow> \<guillemotleft>map\<^sub>0 a : src\<^sub>D (F a) \<rightarrow>\<^sub>D src\<^sub>D (H a)\<guillemotright>"
        unfolding map\<^sub>0_def
        using \<rho>.map\<^sub>0_in_hhom \<sigma>.map\<^sub>0_in_hhom by blast
      show "\<And>f. C.ide f \<Longrightarrow> \<guillemotleft>map\<^sub>1 f : H f \<star>\<^sub>D map\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f\<guillemotright>"
        by (unfold map\<^sub>1_def map\<^sub>0_def, intro D.comp_in_homI) auto
      show "\<And>f. C.ide f \<Longrightarrow> D.iso (map\<^sub>1 f)"
        unfolding map\<^sub>1_def
        using \<rho>.ide_map\<^sub>0_obj \<rho>.iso_map\<^sub>1_ide \<sigma>.ide_map\<^sub>0_obj \<sigma>.iso_map\<^sub>1_ide
        by (intro D.isos_compose) auto
      show "\<And>\<mu>. C.arr \<mu> \<Longrightarrow> map\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (H \<mu> \<star>\<^sub>D map\<^sub>0 (src\<^sub>C \<mu>))
                               = (map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D map\<^sub>1 (C.dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "C.arr \<mu>"
        have "map\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (H \<mu> \<star>\<^sub>D map\<^sub>0 (src\<^sub>C \<mu>))
                = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), \<sigma>\<^sub>0 (trg\<^sub>C \<mu>), F (C.cod \<mu>)] \<cdot>\<^sub>D
                  (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), G (C.cod \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)] \<cdot>\<^sub>D
                  (\<rho>\<^sub>1 (C.cod \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[H (C.cod \<mu>), \<rho>\<^sub>0 (src\<^sub>C \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)] \<cdot>\<^sub>D
                  (H \<mu> \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>))"
          unfolding map\<^sub>1_def map\<^sub>0_def
          using \<mu> D.comp_assoc by simp
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), \<sigma>\<^sub>0 (trg\<^sub>C \<mu>), F (C.cod \<mu>)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), G (C.cod \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)] \<cdot>\<^sub>D
                         ((\<rho>\<^sub>1 (C.cod \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                         ((H \<mu> \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C \<mu>)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>))) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (C.dom \<mu>), \<rho>\<^sub>0 (src\<^sub>C \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)]"
          using \<mu> D.assoc'_naturality [of "H \<mu>" "\<rho>\<^sub>0 (src\<^sub>C \<mu>)" "\<sigma>\<^sub>0 (src\<^sub>C \<mu>)"] D.comp_assoc by simp
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), \<sigma>\<^sub>0 (trg\<^sub>C \<mu>), F (C.cod \<mu>)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), G (C.cod \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)] \<cdot>\<^sub>D
                         ((\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>))) \<cdot>\<^sub>D
                         (\<rho>\<^sub>1 (C.dom \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (C.dom \<mu>), \<rho>\<^sub>0 (src\<^sub>C \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)]"
        proof -
          have "(\<rho>\<^sub>1 (C.cod \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D ((H \<mu> \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C \<mu>)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) =
                \<rho>\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (H \<mu> \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C \<mu>)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)"
            using \<mu> D.whisker_right by simp
          also have "... = (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu>) \<cdot>\<^sub>D \<rho>\<^sub>1 (C.dom \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)"
            using \<mu> \<rho>.naturality by simp
          also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                           (\<rho>\<^sub>1 (C.dom \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>))"
            using \<mu> D.whisker_right by simp
          finally have
              "(\<rho>\<^sub>1 (C.cod \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D ((H \<mu> \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C \<mu>)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) =
               ((\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D (\<rho>\<^sub>1 (C.dom \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>))"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), \<sigma>\<^sub>0 (trg\<^sub>C \<mu>), F (C.cod \<mu>)] \<cdot>\<^sub>D
                         ((\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), G (C.dom \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>1 (C.dom \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (C.dom \<mu>), \<rho>\<^sub>0 (src\<^sub>C \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)]"
          using \<mu> D.assoc_naturality [of "\<rho>\<^sub>0 (trg\<^sub>C \<mu>)" "G \<mu>" "\<sigma>\<^sub>0 (src\<^sub>C \<mu>)"] D.comp_assoc
          by simp
        also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), \<sigma>\<^sub>0 (trg\<^sub>C \<mu>), F (C.cod \<mu>)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>)) \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.dom \<mu>)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), G (C.dom \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>1 (C.dom \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (C.dom \<mu>), \<rho>\<^sub>0 (src\<^sub>C \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)]"
        proof -
          have "(\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) =
                \<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (G \<mu> \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>))"
            using \<mu> D.whisker_left by simp
          also have "... = \<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D (\<sigma>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D \<sigma>\<^sub>1 (C.dom \<mu>)"
            using \<mu> \<sigma>.naturality by simp
          also have "... = (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.dom \<mu>))"
            using \<mu> D.whisker_left by simp
          finally have "(\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.cod \<mu>)) \<cdot>\<^sub>D (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) =
                        (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.dom \<mu>))"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C \<mu>)) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), \<sigma>\<^sub>0 (trg\<^sub>C \<mu>), F (C.dom \<mu>)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D \<sigma>\<^sub>1 (C.dom \<mu>)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C \<mu>), G (C.dom \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>1 (C.dom \<mu>) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (C.dom \<mu>), \<rho>\<^sub>0 (src\<^sub>C \<mu>), \<sigma>\<^sub>0 (src\<^sub>C \<mu>)]"
          using \<mu> D.assoc'_naturality [of "\<rho>\<^sub>0 (trg\<^sub>C \<mu>)" "\<sigma>\<^sub>0 (trg\<^sub>C \<mu>)" "F \<mu>"] D.comp_assoc
          by simp
        also have "... = (map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D map\<^sub>1 (C.dom \<mu>)"
          unfolding map\<^sub>1_def map\<^sub>0_def
          using \<mu> by simp
        finally show "map\<^sub>1 (C.cod \<mu>) \<cdot>\<^sub>D (H \<mu> \<star>\<^sub>D map\<^sub>0 (src\<^sub>C \<mu>)) =
                      (map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D map\<^sub>1 (C.dom \<mu>)"
          by blast
      qed
      show "\<And>a. C.obj a \<Longrightarrow> (map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]
                               = map\<^sub>1 a \<cdot>\<^sub>D (H.unit a \<star>\<^sub>D map\<^sub>0 a)"
      proof -
        fix a
        assume a: "C.obj a"
        have "map\<^sub>1 a \<cdot>\<^sub>D (H.unit a \<star>\<^sub>D map\<^sub>0 a)
                = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, \<sigma>\<^sub>0 a, F a] \<cdot>\<^sub>D
                  (\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>1 a) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<rho>\<^sub>0 a, G a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                  (\<rho>\<^sub>1 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[H a, \<rho>\<^sub>0 a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                  (H.unit a \<star>\<^sub>D \<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a)"
          unfolding map\<^sub>1_def map\<^sub>0_def
          using a C.obj_simps D.comp_assoc by simp
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, \<sigma>\<^sub>0 a, F a] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>1 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 a, G a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<rho>\<^sub>1 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         ((H.unit a \<star>\<^sub>D \<rho>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H.map\<^sub>0 a, \<rho>\<^sub>0 a, \<sigma>\<^sub>0 a]"
          using a C.obj_simps D.assoc'_naturality [of "H.unit a" "\<rho>\<^sub>0 a" "\<sigma>\<^sub>0 a"] D.comp_assoc
          by auto
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, \<sigma>\<^sub>0 a, F a] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>1 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<rho>\<^sub>0 a, G a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<rho>\<^sub>0 a \<star>\<^sub>D G.unit a) \<star>\<^sub>D \<sigma>\<^sub>0 a)) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H.map\<^sub>0 a, \<rho>\<^sub>0 a, \<sigma>\<^sub>0 a]"
        proof -
          have "(\<rho>\<^sub>1 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D ((H.unit a \<star>\<^sub>D \<rho>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a)
                   = \<rho>\<^sub>1 a \<cdot>\<^sub>D (H.unit a \<star>\<^sub>D \<rho>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a"
            using a C.obj_simps D.whisker_right
            by (metis C.objE D.hcomp_simps(4) D.hseqI' D.ideD(1) D.ideD(3) D.seqI
                H.unit_simps(1) H.unit_simps(2) H.unit_simps(5)
                \<rho>.ide_map\<^sub>0_obj \<rho>.map\<^sub>0_simps(3) \<rho>.map\<^sub>1_simps(1) \<rho>.map\<^sub>1_simps(4) \<sigma>.ide_map\<^sub>0_obj)
          also have "... = (\<rho>\<^sub>0 a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a"
            using a C.obj_simps \<rho>.respects_unit D.comp_assoc by simp
          also have "... = ((\<rho>\<^sub>0 a \<star>\<^sub>D G.unit a) \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a)"
            using a C.obj_simps D.whisker_right
            by (metis C.objE D.hcomp_simps(4) D.hseqI' D.ideD(1) D.ideD(3) D.seqI D.trg_cod
                H.unit_simps(1-2,5) H.\<i>_simps(1,3,5) \<rho>.ide_map\<^sub>0_obj \<rho>.map\<^sub>0_simps(3)
                \<rho>.map\<^sub>1_simps(1,4) \<rho>.respects_unit \<sigma>.ide_map\<^sub>0_obj)
          finally have "(\<rho>\<^sub>1 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D ((H.unit a \<star>\<^sub>D \<rho>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a) =
                        ((\<rho>\<^sub>0 a \<star>\<^sub>D G.unit a) \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, \<sigma>\<^sub>0 a, F a] \<cdot>\<^sub>D
                         ((\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>1 a) \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<sigma>\<^sub>0 a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H.map\<^sub>0 a, \<rho>\<^sub>0 a, \<sigma>\<^sub>0 a]"
          using a D.assoc_naturality [of "\<rho>\<^sub>0 a" "G.unit a" "\<sigma>\<^sub>0 a"] D.comp_assoc by auto
        also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, \<sigma>\<^sub>0 a, F a] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a \<star>\<^sub>D F.unit a)) \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<sigma>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H.map\<^sub>0 a, \<rho>\<^sub>0 a, \<sigma>\<^sub>0 a]"
        proof -
          have "(\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>1 a) \<cdot>\<^sub>D (\<rho>\<^sub>0 a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<sigma>\<^sub>0 a)
                   = \<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>1 a \<cdot>\<^sub>D (G.unit a \<star>\<^sub>D \<sigma>\<^sub>0 a)"
            using a D.whisker_left [of "\<rho>\<^sub>0 a" "\<sigma>\<^sub>1 a" "G.unit a \<star>\<^sub>D \<sigma>\<^sub>0 a"] by force
          also have "... = \<rho>\<^sub>0 a \<star>\<^sub>D (\<sigma>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<sigma>\<^sub>0 a]"
            using a \<sigma>.respects_unit by simp
          also have "... = (\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D (\<rho>\<^sub>0 a \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<sigma>\<^sub>0 a])"
            using a D.whisker_left C.obj_simps by fastforce
          finally have "(\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>1 a) \<cdot>\<^sub>D (\<rho>\<^sub>0 a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<sigma>\<^sub>0 a) =
                        (\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D (\<rho>\<^sub>0 a \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<sigma>\<^sub>0 a])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, \<sigma>\<^sub>0 a, F.map\<^sub>0 a] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<sigma>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H.map\<^sub>0 a, \<rho>\<^sub>0 a, \<sigma>\<^sub>0 a]"
          using a D.assoc'_naturality [of "\<rho>\<^sub>0 a" "\<sigma>\<^sub>0 a" "F.unit a"] D.comp_assoc
          by fastforce
        also have "... = ((\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, \<sigma>\<^sub>0 a, F.map\<^sub>0 a] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 a])) \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 a \<star>\<^sub>D \<l>\<^sub>D[\<sigma>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H.map\<^sub>0 a, \<rho>\<^sub>0 a, \<sigma>\<^sub>0 a]"
          using a D.whisker_left D.whisker_right D.comp_assoc by simp
        also have "... = ((\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D
                         \<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a)) \<cdot>\<^sub>D
                         \<l>\<^sub>D[\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a]"
          using a D.lunit_hcomp(3) [of "\<rho>\<^sub>0 a" "\<sigma>\<^sub>0 a"] D.runit_hcomp(2) [of "\<rho>\<^sub>0 a" "\<sigma>\<^sub>0 a"]
                D.triangle' [of "\<rho>\<^sub>0 a" "\<sigma>\<^sub>0 a"] D.comp_assoc
          by auto
       also have "... = ((\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a]"
       proof -
         have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a] \<cdot>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 a, G.map\<^sub>0 a, \<sigma>\<^sub>0 a]
                 = (\<rho>\<^sub>0 a \<star>\<^sub>D G.map\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a"
           using a D.comp_inv_arr'
           by (metis C.obj_def' D.comp_assoc_assoc'(2) G.map\<^sub>0_def G.map\<^sub>0_simps(1)
               G.preserves_trg G.weak_arrow_of_homs_axioms \<rho>.ide_map\<^sub>0_obj \<rho>.map\<^sub>0_simps(2)
               \<sigma>.ide_map\<^sub>0_obj \<sigma>.map\<^sub>0_simps(3) horizontal_homs.objE weak_arrow_of_homs_def)
         moreover have "((\<rho>\<^sub>0 a \<star>\<^sub>D G.map\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a)
                          = (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a)"
           using a D.comp_cod_arr D.whisker_right
           by (metis D.runit'_simps(1) D.runit'_simps(5) G.map\<^sub>0_def \<rho>.ide_map\<^sub>0_obj
               \<rho>.map\<^sub>0_simps(2) \<sigma>.ide_map\<^sub>0_obj)
         moreover have "(\<r>\<^sub>D[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D (\<r>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 a] \<star>\<^sub>D \<sigma>\<^sub>0 a) = \<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a"
           using a D.whisker_right D.comp_arr_inv' D.R.components_are_iso
           by (metis D.ideD(1) D.iso_runit D.runit_simps(5) \<rho>.ide_map\<^sub>0_obj \<sigma>.ide_map\<^sub>0_obj)
         moreover have "(\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a) \<cdot>\<^sub>D \<l>\<^sub>D[\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a] = \<l>\<^sub>D[\<rho>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a]"
           using a D.comp_cod_arr \<open>\<And>a. C.obj a \<Longrightarrow> D.ide (map\<^sub>0 a)\<close> map\<^sub>0_def by auto
         ultimately show ?thesis
           using D.comp_assoc by metis
       qed
       also have "... = (map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]"
         unfolding map\<^sub>0_def by simp
       finally show "(map\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]
                       = map\<^sub>1 a \<cdot>\<^sub>D (H.unit a \<star>\<^sub>D map\<^sub>0 a)"
         by simp
     qed
     show "\<And>f g. \<lbrakk>C.ide f; C.ide g; src\<^sub>C g = trg\<^sub>C f\<rbrakk> \<Longrightarrow>
                    (map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                    (map\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
                    D.inv \<a>\<^sub>D[H g, map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                    (H g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[H g, H f, map\<^sub>0 (src\<^sub>C f)]
                      = map\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>C f))"
     proof -
       fix f g
       assume f: "C.ide f" and g: "C.ide g" and fg: "src\<^sub>C g = trg\<^sub>C f"
       have "(map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
             \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
             (map\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
             D.inv \<a>\<^sub>D[H g, map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
             (H g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[H g, H f, map\<^sub>0 (src\<^sub>C f)]
               = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                 \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<cdot>\<^sub>D
                 (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<cdot>\<^sub>D
                  (\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g)) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g)]
                     \<star>\<^sub>D F f) \<cdot>\<^sub>D
                 \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                 (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C f), \<sigma>\<^sub>0 (trg\<^sub>C f), F f] \<cdot>\<^sub>D
                         (\<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                         (\<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
               \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
         unfolding map\<^sub>0_def map\<^sub>1_def
         using f g fg by simp
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C f), \<sigma>\<^sub>0 (trg\<^sub>C f), F f]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
         using f g fg D.whisker_left D.whisker_right D.comp_assoc by fastforce
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (((\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C f), \<sigma>\<^sub>0 (trg\<^sub>C f), F f]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
         using f g fg D.pentagon' D.comp_assoc
               D.invert_side_of_triangle(2)
                 [of "\<a>\<^sub>D\<^sup>-\<^sup>1[H g \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f]"
                     "(\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g), F f]"
                     "H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]"]
         by force
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f] \<cdot>\<^sub>D
                        (((H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C f), \<sigma>\<^sub>0 (trg\<^sub>C f), F f])) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
        proof -
         have "((\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g)) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f)"
           using f g fg D.assoc'_naturality [of "\<rho>\<^sub>1 g" "\<sigma>\<^sub>0 (src\<^sub>C g)" "F f"] by simp
         thus ?thesis
            using D.comp_assoc by simp
       qed
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
      proof -
         have "((H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
               (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C f), \<sigma>\<^sub>0 (trg\<^sub>C f), F f])) \<cdot>\<^sub>D
               (H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f)
                 = H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f"
         proof -
           have "(H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                 (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f])
                   = H g \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f"
           proof -
             have "(H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                   (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f])
                     = H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                       \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (src\<^sub>C g), \<sigma>\<^sub>0 (src\<^sub>C g), F f]"
               using f g fg D.whisker_left by simp
             also have "... = H g \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f"
               using f g fg D.comp_arr_inv' by simp
             finally show ?thesis by simp
           qed
           moreover have "(H g \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                          (H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f)
                            = (H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>1 f)"
             using f g fg D.comp_cod_arr by simp
           ultimately show ?thesis
             using fg by simp
         qed
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>1 f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
         using f g fg D.assoc'_naturality [of "H g" "\<rho>\<^sub>0 (src\<^sub>C g)" "\<sigma>\<^sub>1 f"] D.comp_assoc by simp
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 g \<star>\<^sub>D G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)])) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<rho>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
       proof -
         have "(\<rho>\<^sub>1 g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f) \<cdot>\<^sub>D ((H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>1 f) =
               ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D (\<rho>\<^sub>1 g \<star>\<^sub>D G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
           using f g fg D.interchange D.comp_arr_dom D.comp_cod_arr
           by (metis C.ideD(1) \<rho>.map\<^sub>1_simps(1,5) \<rho>.naturality \<sigma>.map\<^sub>1_simps(1,4)
               \<sigma>.naturality C.ideD(2,3))
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 g \<star>\<^sub>D G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)])) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        ((H g \<star>\<^sub>D \<rho>\<^sub>1 f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
         using f g fg D.comp_assoc D.hcomp_reassoc(2) by simp
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>1 g \<star>\<^sub>D G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((H g \<star>\<^sub>D \<rho>\<^sub>1 f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
       proof -  
         have "(\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
               (H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)])) \<cdot>\<^sub>D
               \<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)]
                 = \<a>\<^sub>D[H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                   (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
         proof -
           have "((H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                 (\<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))
                   = \<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                     \<a>\<^sub>D[H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
             using f g fg D.pentagon D.comp_assoc by simp
           moreover have "D.seq \<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]
                                \<a>\<^sub>D[H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
             using f g fg
             by (intro D.seqI) auto
           ultimately show ?thesis
             using f g fg D.comp_assoc
                   D.invert_opposite_sides_of_square
                     [of "\<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
                         "\<a>\<^sub>D[H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
                         "(H g \<star>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                            \<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
                         "\<a>\<^sub>D[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"]
             by fastforce
         qed
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((H g \<star>\<^sub>D \<rho>\<^sub>1 f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
       proof -
         have "(\<rho>\<^sub>1 g \<star>\<^sub>D G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D \<a>\<^sub>D[H g \<star>\<^sub>D \<rho>\<^sub>0 (trg\<^sub>C f), G f, \<sigma>\<^sub>0 (src\<^sub>C f)] =
               \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D ((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
           using f g fg D.assoc_naturality [of "\<rho>\<^sub>1 g" "G f" "\<sigma>\<^sub>0 (src\<^sub>C f)"] by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)])"
       proof -
         have "((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                 (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                 ((H g \<star>\<^sub>D \<rho>\<^sub>1 f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) =
               (\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<cdot>\<^sub>D (H g \<star>\<^sub>D \<rho>\<^sub>1 f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
           using f g fg D.whisker_right by simp
         also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<cdot>\<^sub>D
                          \<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D
                          (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]
                            \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
         proof -
           have "((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D
                 ((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f] \<cdot>\<^sub>D (H g \<star>\<^sub>D \<rho>\<^sub>1 f))) \<cdot>\<^sub>D
                 \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]
                   = \<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f))"
             using f g fg \<rho>.respects_hcomp D.comp_assoc by simp
           moreover have "D.seq (\<rho>\<^sub>1 (g \<star>\<^sub>C f)) (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f))"
             using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char by auto
           ultimately
           have "(\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D
                 ((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f] \<cdot>\<^sub>D (H g \<star>\<^sub>D \<rho>\<^sub>1 f))
                   = (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]"
             using f g fg D.invert_side_of_triangle(2) by simp
           moreover have "D.seq (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f)))
                                \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]"
             using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def by auto
           ultimately
           have "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D
                 ((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f] \<cdot>\<^sub>D (H g \<star>\<^sub>D \<rho>\<^sub>1 f))
                   = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<cdot>\<^sub>D
                     (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D
                     (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]"
             using f g fg
                   D.invert_side_of_triangle(1)
                     [of "(\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]"
                         "\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)"
                         "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D ((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<cdot>\<^sub>D
                          \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f] \<cdot>\<^sub>D (H g \<star>\<^sub>D \<rho>\<^sub>1 f))"]
             by simp
           hence "(\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f] \<cdot>\<^sub>D (H g \<star>\<^sub>D \<rho>\<^sub>1 f)
                    = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<cdot>\<^sub>D
                      (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D
                      (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]"
             using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
                   D.invert_side_of_triangle(1)
             by simp
           hence "(\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (src\<^sub>C g), G f] \<cdot>\<^sub>D (H g \<star>\<^sub>D \<rho>\<^sub>1 f)
                    = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<cdot>\<^sub>D
                      \<rho>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D
                      (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)]"
             using D.comp_assoc by simp
           thus ?thesis
             using fg by simp
         qed
         also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                          ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                          (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                          ((\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                          (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
           using f g fg D.whisker_right C.VV.arr_char C.VV.dom_char C.VV.cod_char
                 H.FF_def G.FF_def
           by force
         finally have "((\<rho>\<^sub>1 g \<star>\<^sub>D G f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                       (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, \<rho>\<^sub>0 (trg\<^sub>C f), G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                       ((H g \<star>\<^sub>D \<rho>\<^sub>1 f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))
                         = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           ((\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H g \<star>\<^sub>D H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]"
       proof -
         have "((\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
               \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
               (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)])) \<cdot>\<^sub>D
               \<a>\<^sub>D[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[H g \<star>\<^sub>D H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]"
         proof -
           have "(\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                 \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                 (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)])
                   = \<a>\<^sub>D\<^sup>-\<^sup>1[H g \<star>\<^sub>D H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                     \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"
             using f g fg D.pentagon' D.comp_assoc by simp
           moreover have "D.seq (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))
                                (\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                                  (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]))"
             using f g fg by auto
           ultimately show ?thesis
             using f g fg D.comp_assoc
                   D.invert_side_of_triangle(2)
                     [of "(\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f)] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                            \<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                            (H g \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)])"
                         "\<a>\<^sub>D\<^sup>-\<^sup>1[H g \<star>\<^sub>D H f, \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)]"
                         "\<a>\<^sub>D\<^sup>-\<^sup>1[H g, H f, \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)]"]
             by simp
         qed
         thus ?thesis
           using D.comp_assoc by simp
       qed              
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
         using f g fg D.assoc'_naturality [of "\<Phi>\<^sub>H (g, f)" "\<rho>\<^sub>0 (src\<^sub>C f)" "\<sigma>\<^sub>0 (src\<^sub>C f)"]
         by fastforce
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F g, F f] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
         using f g fg D.hcomp_reassoc(1) D.comp_assoc by simp
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F g, F f] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g) \<star>\<^sub>D \<sigma>\<^sub>1 f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
         using f g fg D.comp_assoc D.pentagon
               D.invert_opposite_sides_of_square
                 [of "\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f]"
                     "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g)] \<star>\<^sub>D F f)"
                     "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, \<sigma>\<^sub>0 (src\<^sub>C g) \<star>\<^sub>D F f]"
                     "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f]"]
         by simp
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F g, F f] \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g \<star>\<^sub>D \<sigma>\<^sub>1 f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
         using f g fg D.assoc_naturality [of "\<rho>\<^sub>0 (trg\<^sub>C g)" "G g" "\<sigma>\<^sub>1 f"] D.comp_assoc by simp
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F g, F f] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f])) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
       proof -
         have "(\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
               (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
               (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g \<star>\<^sub>D \<sigma>\<^sub>1 f)
                 = \<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D (\<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<sigma>\<^sub>1 f)"
           using f g fg D.whisker_left by simp
         also have "... = \<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                             (\<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                             \<sigma>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D
                             (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
         proof -
           have "((\<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                 \<a>\<^sub>D[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                 (\<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<sigma>\<^sub>1 f)) \<cdot>\<^sub>D
                 \<a>\<^sub>D[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]
                   = \<sigma>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
             using f g fg \<sigma>.respects_hcomp D.comp_assoc by simp
           hence "(\<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                  (\<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<sigma>\<^sub>1 f)
                    = (\<sigma>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
             using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char D.invert_side_of_triangle(2)
             by simp
           hence "\<a>\<^sub>D[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                  (\<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<sigma>\<^sub>1 f)
                    = (\<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                      (\<sigma>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
             using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char G.FF_def
                   D.invert_side_of_triangle(1)
                     [of "(\<sigma>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
                         "\<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)"
                         "\<a>\<^sub>D[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D (\<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
                            \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<sigma>\<^sub>1 f)"]
             by simp
           hence "(\<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<sigma>\<^sub>1 f)
                    = \<a>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D (\<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                      (\<sigma>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
             using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char G.FF_def F.FF_def
                   D.invert_side_of_triangle(1)
             by simp
           thus ?thesis
             using D.comp_assoc by simp
         qed
         also have "... = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f]) \<cdot>\<^sub>D
                          (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                          (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                          (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                          (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)])"
            using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char F.FF_def G.FF_def
                  D.whisker_left
           by force
         finally have "(\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
                       (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<sigma>\<^sub>0 (src\<^sub>C g), F f]) \<cdot>\<^sub>D
                       (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g \<star>\<^sub>D \<sigma>\<^sub>1 f)
                         = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f]) \<cdot>\<^sub>D
                           (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                           (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                           (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)])"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g \<star>\<^sub>D F f] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f)))) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
         using f g fg D.pentagon' D.comp_assoc
               D.invert_side_of_triangle(1)
                 [of "(\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g] \<star>\<^sub>D F f) \<cdot>\<^sub>D
                      \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D F g, F f] \<cdot>\<^sub>D
                      (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f])"
                     "\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g), F g, F f]"
                     "\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F g \<star>\<^sub>D F f]" ]
         by simp
       also have "... = ((((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f)))) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
           using f g fg D.assoc'_naturality [of "\<rho>\<^sub>0 (trg\<^sub>C g)" "\<sigma>\<^sub>0 (trg\<^sub>C g)" "D.inv (\<Phi>\<^sub>F (g, f))"]
                 D.comp_assoc
           by simp
       also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
       proof -
         have "(((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
               ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f)))) \<cdot>\<^sub>D
               \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)]"
         proof -
           have "((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                 ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f)))
                   = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f))"
             using f g fg D.whisker_left C.VV.arr_char by simp
           also have "... = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D F (g \<star>\<^sub>C f)"
             using f g fg D.comp_arr_inv' F.cmp_components_are_iso by simp
           finally have "((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                         ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D D.inv (\<Phi>\<^sub>F (g, f)))
                           = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D F (g \<star>\<^sub>C f)"
             by blast
           moreover have "((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C g)) \<star>\<^sub>D F (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                          \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)]
                            = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)]"
             using f g fg D.comp_cod_arr by simp
           ultimately show ?thesis by simp
         qed
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
         using f g fg D.pentagon D.comp_assoc
               D.invert_side_of_triangle(1)
                 [of "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
                     "\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
                     "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
               (\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"]
               D.invert_side_of_triangle(2)
                 [of "(\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G g, G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
                     "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)]"
                     "\<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g, G f] \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"]
         by simp
       also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G (g \<star>\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        ((((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
        proof -
         have "(\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
               \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G g \<star>\<^sub>D G f, \<sigma>\<^sub>0 (src\<^sub>C f)]
                 = \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G (g \<star>\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                   ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
           using f g fg D.assoc_naturality [of "\<rho>\<^sub>0 (trg\<^sub>C g)" "\<Phi>\<^sub>G (g, f)" "\<sigma>\<^sub>0 (src\<^sub>C f)"]
           by fastforce
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<rho>\<^sub>0 (trg\<^sub>C g), \<sigma>\<^sub>0 (trg\<^sub>C g), F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D
                        (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<sigma>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<rho>\<^sub>0 (trg\<^sub>C g), G (g \<star>\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[H (g \<star>\<^sub>C f), \<rho>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                        (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D \<rho>\<^sub>0 (src\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))"
       proof -
         have "(((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
               ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))) \<cdot>\<^sub>D
               (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))
                 = \<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
         proof -
           have "((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                 ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))
                   = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                     (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)))
                        \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
             using f g fg C.VV.arr_char D.whisker_right by simp
           also have "... = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
             using f g fg C.VV.arr_char D.whisker_left [of "\<rho>\<^sub>0 (trg\<^sub>C g)"] by simp
           also have "... = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G (g \<star>\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
             using f g fg D.comp_arr_inv' G.cmp_components_are_iso G.cmp_simps(5) by auto
           finally have "((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                         ((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))
                           = (\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G (g \<star>\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
             by blast
           moreover have "((\<rho>\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D G (g \<star>\<^sub>C f)) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                          (\<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f))
                            = \<rho>\<^sub>1 (g \<star>\<^sub>C f) \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)"
             using f g fg D.comp_cod_arr by simp
           ultimately show ?thesis by simp
         qed
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = map\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>C f))"
         unfolding map\<^sub>0_def map\<^sub>1_def
         using f g fg D.comp_assoc by simp
       finally show "(map\<^sub>0 (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                     \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>C g), F g, F f] \<cdot>\<^sub>D
                     (map\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D
                     D.inv \<a>\<^sub>D[H g, map\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D
                     (H g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D
                     \<a>\<^sub>D[H g, H f, map\<^sub>0 (src\<^sub>C f)]
                       = map\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>H (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>C f))"
         using D.comp_assoc by simp
     qed
   qed

   lemma is_pseudonatural_transformation:
   shows "pseudonatural_transformation
            V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F H \<Phi>\<^sub>H map\<^sub>0 map\<^sub>1"
     ..

  end

  subsection "Whiskering of Pseudonatural Transformations"

  text \<open>
    Similarly to ordinary natural transformations, pseudonatural transformations can be whiskered
    with pseudofunctors on the left and the right.
  \<close>

  locale pseudonatural_transformation_whisker_right =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B +
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    \<tau>.F: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F +
    \<tau>.G: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G +
    H: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C H \<Phi>\<^sub>H +
    \<tau>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
  for V\<^sub>B :: "'b comp"                   (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'b comp"                   (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"       ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'b \<Rightarrow> 'b"                   ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'b \<Rightarrow> 'b"
  and trg\<^sub>B :: "'b \<Rightarrow> 'b"
  and V\<^sub>C :: "'c comp"                   (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                   (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'd"
  and G :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>G :: "'c * 'c \<Rightarrow> 'd"
  and H :: "'b \<Rightarrow> 'c"
  and \<Phi>\<^sub>H :: "'b * 'b \<Rightarrow> 'c"
  and \<tau>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<tau>\<^sub>1 :: "'c \<Rightarrow> 'd"
  begin

    interpretation FoH: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D H \<Phi>\<^sub>H F \<Phi>\<^sub>F
      ..
    interpretation GoH: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D H \<Phi>\<^sub>H G \<Phi>\<^sub>G
      ..

    definition map\<^sub>0
    where "map\<^sub>0 a = \<tau>\<^sub>0 (H.map\<^sub>0 a)"

    definition map\<^sub>1
    where "map\<^sub>1 f = \<tau>\<^sub>1 (H f)"

    sublocale pseudonatural_transformation V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          \<open>F o H\<close> FoH.cmp \<open>G o H\<close> GoH.cmp map\<^sub>0 map\<^sub>1
    proof
      show "\<And>a. B.obj a \<Longrightarrow> D.ide (map\<^sub>0 a)"
        using map\<^sub>0_def by simp
      show "\<And>a. B.obj a \<Longrightarrow> \<guillemotleft>map\<^sub>0 a : src\<^sub>D ((F \<circ> H) a) \<rightarrow>\<^sub>D src\<^sub>D ((G \<circ> H) a)\<guillemotright>"
        using map\<^sub>0_def \<tau>.map\<^sub>0_in_hhom B.obj_simps C.obj_simps by simp
      show "\<And>f. B.ide f \<Longrightarrow> D.iso (map\<^sub>1 f)"
        using map\<^sub>1_def \<tau>.iso_map\<^sub>1_ide by simp
      show "\<And>f. B.ide f \<Longrightarrow>
                   \<guillemotleft>map\<^sub>1 f : (G \<circ> H) f \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f) \<Rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>B f) \<star>\<^sub>D (F \<circ> H) f\<guillemotright>"
        using map\<^sub>0_def map\<^sub>1_def by auto
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow>
                   map\<^sub>1 (B.cod \<mu>) \<cdot>\<^sub>D ((G \<circ> H) \<mu> \<star>\<^sub>D map\<^sub>0 (src\<^sub>B \<mu>)) =
                   (map\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>D (F \<circ> H) \<mu>) \<cdot>\<^sub>D map\<^sub>1 (B.dom \<mu>)"
        unfolding map\<^sub>0_def map\<^sub>1_def
        using \<tau>.naturality by force
      show "\<And>a. B.obj a \<Longrightarrow>
                  (map\<^sub>0 a \<star>\<^sub>D FoH.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]
                     = map\<^sub>1 a \<cdot>\<^sub>D (GoH.unit a \<star>\<^sub>D map\<^sub>0 a)"
      proof -
        fix a
        assume a: "B.obj a"
        have "map\<^sub>1 a \<cdot>\<^sub>D (GoH.unit a \<star>\<^sub>D map\<^sub>0 a) =
              \<tau>\<^sub>1 (H a) \<cdot>\<^sub>D (G (H.unit a) \<cdot>\<^sub>D \<tau>.G.unit (H.map\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0 (H.map\<^sub>0 a))"
          unfolding map\<^sub>0_def map\<^sub>1_def
          using a GoH.unit_char' by simp
        also have "... = (\<tau>\<^sub>1 (H a) \<cdot>\<^sub>D (G (H.unit a) \<star>\<^sub>D \<tau>\<^sub>0 (H.map\<^sub>0 a))) \<cdot>\<^sub>D
                         (\<tau>.G.unit (H.map\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0 (H.map\<^sub>0 a))"
          using a D.whisker_right D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0 (H.map\<^sub>0 a) \<star>\<^sub>D F (H.unit a)) \<cdot>\<^sub>D \<tau>\<^sub>1 (H.map\<^sub>0 a) \<cdot>\<^sub>D
                         (\<tau>.G.unit (H.map\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0 (H.map\<^sub>0 a))"
          using a \<tau>.naturality [of "H.unit a"] D.comp_assoc by simp
        also have "... = ((\<tau>\<^sub>0 (H.map\<^sub>0 a) \<star>\<^sub>D F (H.unit a)) \<cdot>\<^sub>D
                          (\<tau>\<^sub>0 (H.map\<^sub>0 a) \<star>\<^sub>D \<tau>.F.unit (H.map\<^sub>0 a))) \<cdot>\<^sub>D
                         \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 (H.map\<^sub>0 a)] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 (H.map\<^sub>0 a)]"
          using a \<tau>.respects_unit D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0 (H.map\<^sub>0 a) \<star>\<^sub>D F (H.unit a) \<cdot>\<^sub>D \<tau>.F.unit (H.map\<^sub>0 a)) \<cdot>\<^sub>D
                         \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 (H.map\<^sub>0 a)] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 (H.map\<^sub>0 a)]"
          using a D.whisker_left by simp
        also have "... = (map\<^sub>0 a \<star>\<^sub>D FoH.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]"
          unfolding map\<^sub>0_def map\<^sub>1_def
          using a FoH.unit_char' by simp
        finally show "(map\<^sub>0 a \<star>\<^sub>D FoH.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]
                        = map\<^sub>1 a \<cdot>\<^sub>D (GoH.unit a \<star>\<^sub>D map\<^sub>0 a)"
          by simp
      qed
      show "\<And>f g. \<lbrakk>B.ide f; B.ide g; src\<^sub>B g = trg\<^sub>B f\<rbrakk> \<Longrightarrow>
                    (map\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>D FoH.cmp (g, f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>B g), (F \<circ> H) g, (F \<circ> H) f] \<cdot>\<^sub>D
                    (map\<^sub>1 g \<star>\<^sub>D (F \<circ> H) f) \<cdot>\<^sub>D
                    D.inv \<a>\<^sub>D[(G \<circ> H) g, map\<^sub>0 (src\<^sub>B g), (F \<circ> H) f] \<cdot>\<^sub>D
                    ((G \<circ> H) g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D
                    \<a>\<^sub>D[(G \<circ> H) g, (G \<circ> H) f, map\<^sub>0 (src\<^sub>B f)]
                      = map\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>D (GoH.cmp (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f))"
      proof -
        fix f g
        assume f: "B.ide f" and g: "B.ide g" and fg: "src\<^sub>B g = trg\<^sub>B f"
        have "map\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>D (GoH.cmp (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f))
                = \<tau>\<^sub>1 (H (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                  (G (H (g \<star>\<^sub>B f)) \<cdot>\<^sub>D G (\<Phi>\<^sub>H (g, f)) \<cdot>\<^sub>D \<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
          unfolding map\<^sub>0_def map\<^sub>1_def
          using f g fg GoH.cmp_def B.VV.arr_char B.VV.dom_char by simp
        also have "... = (\<tau>\<^sub>1 (H (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                         (G (H (g \<star>\<^sub>B f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))) \<cdot>\<^sub>D
                         (G (\<Phi>\<^sub>H (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
          using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char H.FF_def
                C.VV.arr_char C.VV.dom_char C.VV.cod_char D.whisker_right
                D.comp_assoc
          by simp
        also have "... = (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (H (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 (H (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                         (G (\<Phi>\<^sub>H (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
          using f g fg \<tau>.naturality [of "H (g \<star>\<^sub>B f)"] D.comp_assoc by auto
        also have "... = (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (H (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (\<Phi>\<^sub>H (g, f))) \<cdot>\<^sub>D
                         \<tau>\<^sub>1 (H g \<star>\<^sub>C H f) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
          using f g fg \<tau>.naturality [of "\<Phi>\<^sub>H (g, f)"] D.comp_assoc by fastforce
        also have "... = (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (H (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (\<Phi>\<^sub>H (g, f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D \<Phi>\<^sub>F (H g, H f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C (H g)), F (H g), F (H f)] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 (H g) \<star>\<^sub>D F (H f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[G (H g), \<tau>\<^sub>0 (src\<^sub>C (H g)), F (H f)] \<cdot>\<^sub>D
                         (G (H g) \<star>\<^sub>D \<tau>\<^sub>1 (H f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))))"
        proof -
          have "\<tau>\<^sub>1 (H g \<star>\<^sub>C H f) = (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D \<Phi>\<^sub>F (H g, H f)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C (H g)), F (H g), F (H f)] \<cdot>\<^sub>D
                                 (\<tau>\<^sub>1 (H g) \<star>\<^sub>D F (H f)) \<cdot>\<^sub>D
                                 D.inv \<a>\<^sub>D[G (H g), \<tau>\<^sub>0 (src\<^sub>C (H g)), F (H f)] \<cdot>\<^sub>D
                                 (G (H g) \<star>\<^sub>D \<tau>\<^sub>1 (H f)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))] \<cdot>\<^sub>D
                                 D.inv (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
          proof -
            have "\<tau>\<^sub>1 (H g \<star>\<^sub>C H f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))
                    = (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D \<Phi>\<^sub>F (H g, H f)) \<cdot>\<^sub>D
                      \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C (H g)), F (H g), F (H f)] \<cdot>\<^sub>D
                      (\<tau>\<^sub>1 (H g) \<star>\<^sub>D F (H f)) \<cdot>\<^sub>D
                      D.inv \<a>\<^sub>D[G (H g), \<tau>\<^sub>0 (src\<^sub>C (H g)), F (H f)] \<cdot>\<^sub>D
                      (G (H g) \<star>\<^sub>D \<tau>\<^sub>1 (H f)) \<cdot>\<^sub>D
                      \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))]"
              using f g fg \<tau>.respects_hcomp [of "H f" "H g"] by simp
            moreover have "D.seq (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D \<Phi>\<^sub>F (H g, H f))
                                 (\<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C (H g)), F (H g), F (H f)] \<cdot>\<^sub>D
                                 (\<tau>\<^sub>1 (H g) \<star>\<^sub>D F (H f)) \<cdot>\<^sub>D
                                 D.inv \<a>\<^sub>D[G (H g), \<tau>\<^sub>0 (src\<^sub>C (H g)), F (H f)] \<cdot>\<^sub>D
                                 (G (H g) \<star>\<^sub>D \<tau>\<^sub>1 (H f)) \<cdot>\<^sub>D
                                 \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))])"
              using f g fg C.obj_simps C.VV.arr_char C.VV.dom_char C.VV.cod_char \<tau>.F.FF_def
              by simp
            moreover have "D.iso (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
              using f g fg \<tau>.G.cmp_components_are_iso [of "H g" "H f"] by simp
            ultimately
            have "\<tau>\<^sub>1 (H g \<star>\<^sub>C H f) = ((\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D \<Phi>\<^sub>F (H g, H f)) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C (H g)), F (H g), F (H f)] \<cdot>\<^sub>D
                                   (\<tau>\<^sub>1 (H g) \<star>\<^sub>D F (H f)) \<cdot>\<^sub>D
                                   D.inv \<a>\<^sub>D[G (H g), \<tau>\<^sub>0 (src\<^sub>C (H g)), F (H f)] \<cdot>\<^sub>D
                                   (G (H g) \<star>\<^sub>D \<tau>\<^sub>1 (H f)) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))]) \<cdot>\<^sub>D
                                   D.inv (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
            using D.invert_side_of_triangle(2) by blast
            thus ?thesis
              using D.comp_assoc by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (H (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (\<Phi>\<^sub>H (g, f))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D \<Phi>\<^sub>F (H g, H f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C (H g)), F (H g), F (H f)] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 (H g) \<star>\<^sub>D F (H f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[G (H g), \<tau>\<^sub>0 (src\<^sub>C (H g)), F (H f)] \<cdot>\<^sub>D
                         (G (H g) \<star>\<^sub>D \<tau>\<^sub>1 (H f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))]"
        proof -
          have "(D.inv (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))) \<cdot>\<^sub>D
                (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))))
                  = (G (H g) \<star>\<^sub>D G (H f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))"
          proof -
            have "(D.inv (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))) \<cdot>\<^sub>D
                  (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))))
                    = (D.inv (\<Phi>\<^sub>G (H g, H f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))) \<cdot>\<^sub>D
                      (\<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f)))"
              using f g fg by simp
            also have "... = D.inv (\<Phi>\<^sub>G (H g, H f)) \<cdot>\<^sub>D \<Phi>\<^sub>G (H g, H f) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))"
              using f g fg D.whisker_right C.VV.arr_char by simp
            also have "... = (G (H g) \<star>\<^sub>D G (H f)) \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C (H f))"
              using f g fg D.comp_inv_arr' \<tau>.G.cmp_components_are_iso by simp
            finally show ?thesis by blast
          qed
          moreover have "\<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))] \<cdot>\<^sub>D ...
                           = \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))]"
            using f g fg D.comp_arr_dom by simp
          ultimately show ?thesis by simp
        qed
        also have "... = (\<tau>\<^sub>0 (trg\<^sub>C (H g)) \<star>\<^sub>D F (H (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                                            F (\<Phi>\<^sub>H (g, f)) \<cdot>\<^sub>D
                                            \<Phi>\<^sub>F (H g, H f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C (H g)), F (H g), F (H f)] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 (H g) \<star>\<^sub>D F (H f)) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[G (H g), \<tau>\<^sub>0 (src\<^sub>C (H g)), F (H f)] \<cdot>\<^sub>D
                         (G (H g) \<star>\<^sub>D \<tau>\<^sub>1 (H f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[G (H g), G (H f), \<tau>\<^sub>0 (src\<^sub>C (H f))]"
          using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char
                B.VV.arr_char B.VV.dom_char B.VV.cod_char H.FF_def
                D.whisker_left C.VV.arr_char B.VV.arr_char D.comp_assoc
          by auto
        also have "... = (map\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>D FoH.cmp (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>B g), (F \<circ> H) g, (F \<circ> H) f] \<cdot>\<^sub>D
                         (map\<^sub>1 g \<star>\<^sub>D (F \<circ> H) f) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[(G \<circ> H) g, map\<^sub>0 (src\<^sub>B g), (F \<circ> H) f] \<cdot>\<^sub>D
                         ((G \<circ> H) g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[(G \<circ> H) g, (G \<circ> H) f, map\<^sub>0 (src\<^sub>B f)]"
          unfolding map\<^sub>0_def map\<^sub>1_def
          using f g fg FoH.cmp_def B.VV.arr_char B.VV.dom_char by simp
        finally show "(map\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>D FoH.cmp (g, f)) \<cdot>\<^sub>D
                      \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>B g), (F \<circ> H) g, (F \<circ> H) f] \<cdot>\<^sub>D
                      (map\<^sub>1 g \<star>\<^sub>D (F \<circ> H) f) \<cdot>\<^sub>D
                      D.inv \<a>\<^sub>D[(G \<circ> H) g, map\<^sub>0 (src\<^sub>B g), (F \<circ> H) f] \<cdot>\<^sub>D
                      ((G \<circ> H) g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D
                      \<a>\<^sub>D[(G \<circ> H) g, (G \<circ> H) f, map\<^sub>0 (src\<^sub>B f)]
                        = map\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>D (GoH.cmp (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f))"
          by simp
      qed
    qed

    lemma is_pseudonatural_transformation:
    shows "pseudonatural_transformation V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          (F o H) FoH.cmp (G o H) GoH.cmp map\<^sub>0 map\<^sub>1"
      ..

  end

  locale pseudonatural_transformation_whisker_left =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B +
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    \<tau>.F: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F +
    \<tau>.G: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G +
    H: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D H \<Phi>\<^sub>H +
    \<tau>: pseudonatural_transformation
         V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
  for V\<^sub>B :: "'b comp"                   (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'b comp"                   (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"       ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'b \<Rightarrow> 'b"                   ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'b \<Rightarrow> 'b"
  and trg\<^sub>B :: "'b \<Rightarrow> 'b"
  and V\<^sub>C :: "'c comp"                   (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                   (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'b \<Rightarrow> 'c"
  and \<Phi>\<^sub>F :: "'b * 'b \<Rightarrow> 'c"
  and G :: "'b \<Rightarrow> 'c"
  and \<Phi>\<^sub>G :: "'b * 'b \<Rightarrow> 'c"
  and H :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>H :: "'c * 'c \<Rightarrow> 'd"
  and \<tau>\<^sub>0 :: "'b \<Rightarrow> 'c"
  and \<tau>\<^sub>1 :: "'b \<Rightarrow> 'c"
  begin

    interpretation HoF: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F H \<Phi>\<^sub>H
      ..
    interpretation HoG: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G H \<Phi>\<^sub>H
      ..

    definition map\<^sub>0
    where "map\<^sub>0 a = H (\<tau>\<^sub>0 a)"

    definition map\<^sub>1
    where "map\<^sub>1 f = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B f), F f)) \<cdot>\<^sub>D H (\<tau>\<^sub>1 f) \<cdot>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f))"

    sublocale pseudonatural_transformation V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                HoF.map HoF.cmp HoG.map HoG.cmp map\<^sub>0 map\<^sub>1
    proof
      show "\<And>a. B.obj a \<Longrightarrow> D.ide (map\<^sub>0 a)"
        using map\<^sub>0_def by simp
      show "\<And>f. B.ide f \<Longrightarrow> D.iso (map\<^sub>1 f)"
      proof -
        fix f
        assume f: "B.ide f"
        have "D.seq (H (\<tau>\<^sub>1 f)) (\<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f)))"
          using f by (intro D.seqI) auto
        moreover have "D.seq (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B f), F f)))
                             (H (\<tau>\<^sub>1 f) \<cdot>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f)))"
          using f \<tau>.map\<^sub>1_in_hom [of f] calculation by (intro D.seqI) auto
        ultimately show "D.iso (map\<^sub>1 f)"
          using f map\<^sub>1_def H.preserves_iso \<tau>.iso_map\<^sub>1_ide H.cmp_components_are_iso
                C.VV.arr_char D.isos_compose
          by auto
      qed
      show "\<And>a. B.obj a \<Longrightarrow> \<guillemotleft>map\<^sub>0 a : src\<^sub>D ((H \<circ> F) a) \<rightarrow>\<^sub>D src\<^sub>D ((H \<circ> G) a)\<guillemotright>"
        using map\<^sub>0_def by fastforce
      show "\<And>f. B.ide f \<Longrightarrow>
                   \<guillemotleft>map\<^sub>1 f : (H \<circ> G) f \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f) \<Rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>B f) \<star>\<^sub>D (H \<circ> F) f\<guillemotright>"
        using map\<^sub>0_def map\<^sub>1_def by fastforce
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow>
                   map\<^sub>1 (B.cod \<mu>) \<cdot>\<^sub>D ((H \<circ> G) \<mu> \<star>\<^sub>D map\<^sub>0 (src\<^sub>B \<mu>))
                     = (map\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>D (H \<circ> F) \<mu>) \<cdot>\<^sub>D map\<^sub>1 (B.dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "B.arr \<mu>"
        have "(map\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>D (H \<circ> F) \<mu>) \<cdot>\<^sub>D map\<^sub>1 (B.dom \<mu>)
                = (H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>)) \<star>\<^sub>D (H \<circ> F) \<mu>) \<cdot>\<^sub>D
                  D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B (B.dom \<mu>)), F (B.dom \<mu>))) \<cdot>\<^sub>D
                  H (\<tau>\<^sub>1 (B.dom \<mu>)) \<cdot>\<^sub>D \<Phi>\<^sub>H (G (B.dom \<mu>), \<tau>\<^sub>0 (src\<^sub>B (B.dom \<mu>)))"
          unfolding map\<^sub>0_def map\<^sub>1_def
          using \<mu> by simp
        also have "... = ((H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>)) \<star>\<^sub>D H (F \<mu>)) \<cdot>\<^sub>D
                         D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.dom \<mu>)))) \<cdot>\<^sub>D
                H (\<tau>\<^sub>1 (B.dom \<mu>)) \<cdot>\<^sub>D \<Phi>\<^sub>H (G (B.dom \<mu>), \<tau>\<^sub>0 (src\<^sub>B \<mu>))"
          using \<mu> D.comp_assoc by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>C F \<mu>) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 (B.dom \<mu>))) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G (B.dom \<mu>), \<tau>\<^sub>0 (src\<^sub>B (B.dom \<mu>)))"
        proof -
          have "\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>)) \<cdot>\<^sub>D (H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>)) \<star>\<^sub>D H (F \<mu>))
                  = H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>C F \<mu>) \<cdot>\<^sub>D \<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.dom \<mu>))"
            using \<mu> H.\<Phi>.naturality [of "(\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F \<mu>)"]
                  C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
            by simp
          moreover have "D.seq (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>))) (H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>)) \<star>\<^sub>D H (F \<mu>))"
            using \<mu>
            by (intro D.seqI D.hseqI') auto
          moreover have "D.iso (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>)))"
            using \<mu> H.cmp_components_are_iso by simp
          moreover have "D.iso (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.dom \<mu>)))"
            using \<mu> H.cmp_components_are_iso by simp
          ultimately
          have "(H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>)) \<star>\<^sub>D H (F \<mu>)) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.dom \<mu>)))
                = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>))) \<cdot>\<^sub>D H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>C F \<mu>)"
            using \<mu> H.cmp_components_are_iso C.VV.arr_char D.invert_opposite_sides_of_square
            by blast
          thus ?thesis
            using \<mu> D.comp_assoc by simp
        qed
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>))) \<cdot>\<^sub>D
                         H ((\<tau>\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>C F \<mu>) \<cdot>\<^sub>C \<tau>\<^sub>1 (B.dom \<mu>)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G (B.dom \<mu>), \<tau>\<^sub>0 (src\<^sub>B (B.dom \<mu>)))"
          using \<mu> by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>))) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 (B.cod \<mu>) \<cdot>\<^sub>C (G \<mu> \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B \<mu>))) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G (B.dom \<mu>), \<tau>\<^sub>0 (src\<^sub>B (B.dom \<mu>)))"
          using \<mu> \<tau>.naturality by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>))) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 (B.cod \<mu>)) \<cdot>\<^sub>D
                         H (G \<mu> \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B \<mu>)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G (B.dom \<mu>), \<tau>\<^sub>0 (src\<^sub>B (B.dom \<mu>)))"
          using \<mu> D.comp_assoc by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B \<mu>), F (B.cod \<mu>))) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 (B.cod \<mu>)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G (B.cod \<mu>), \<tau>\<^sub>0 (src\<^sub>B (B.cod \<mu>))) \<cdot>\<^sub>D
                         (H (G \<mu>) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B \<mu>)))"
          using \<mu> H.\<Phi>.naturality [of "(G \<mu>, \<tau>\<^sub>0 (src\<^sub>B \<mu>))"]
                C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
          by force
        also have "... = map\<^sub>1 (B.cod \<mu>) \<cdot>\<^sub>D ((H \<circ> G) \<mu> \<star>\<^sub>D map\<^sub>0 (src\<^sub>B \<mu>))"
          unfolding map\<^sub>0_def map\<^sub>1_def
          using \<mu> D.comp_assoc by simp
        finally show "map\<^sub>1 (B.cod \<mu>) \<cdot>\<^sub>D ((H \<circ> G) \<mu> \<star>\<^sub>D map\<^sub>0 (src\<^sub>B \<mu>))
                        = (map\<^sub>0 (trg\<^sub>B \<mu>) \<star>\<^sub>D (H \<circ> F) \<mu>) \<cdot>\<^sub>D map\<^sub>1 (B.dom \<mu>)"
          by simp
      qed
      show "\<And>a. B.obj a \<Longrightarrow> (map\<^sub>0 a \<star>\<^sub>D HoF.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]
                               = map\<^sub>1 a \<cdot>\<^sub>D (HoG.unit a \<star>\<^sub>D map\<^sub>0 a)"
      proof -
        fix a
        assume a: "B.obj a"
        have "map\<^sub>1 a \<cdot>\<^sub>D (HoG.unit a \<star>\<^sub>D map\<^sub>0 a)
                = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<cdot>\<^sub>D
                  H (\<tau>\<^sub>1 a) \<cdot>\<^sub>D
                  \<Phi>\<^sub>H (G a, \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                  (H (\<tau>.G.unit a) \<cdot>\<^sub>D H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
          unfolding map\<^sub>0_def map\<^sub>1_def
          using a HoG.unit_char' D.comp_assoc by auto
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 a) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G a, \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (H (\<tau>.G.unit a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
          using a D.whisker_right D.comp_assoc by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 a) \<cdot>\<^sub>D
                         H (\<tau>.G.unit a \<star>\<^sub>C \<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
          using a H.\<Phi>.naturality [of "(\<tau>.G.unit a, \<tau>\<^sub>0 a)"] D.comp_assoc
                C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
          by auto
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 a \<cdot>\<^sub>C (\<tau>.G.unit a \<star>\<^sub>C \<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
        proof -
          have "C.arr (\<tau>\<^sub>1 a \<cdot>\<^sub>C (\<tau>.G.unit a \<star>\<^sub>C \<tau>\<^sub>0 a))"
            using a by force
         hence "H (\<tau>\<^sub>1 a) \<cdot>\<^sub>D H (\<tau>.G.unit a \<star>\<^sub>C \<tau>\<^sub>0 a) = H (\<tau>\<^sub>1 a \<cdot>\<^sub>C (\<tau>.G.unit a \<star>\<^sub>C \<tau>\<^sub>0 a))"
            using a by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<cdot>\<^sub>D
                         H ((\<tau>\<^sub>0 a \<star>\<^sub>C \<tau>.F.unit a) \<cdot>\<^sub>C \<r>\<^sub>C\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>C \<l>\<^sub>C[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
          using a \<tau>.respects_unit by simp
        also have "... = (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>0 a \<star>\<^sub>C \<tau>.F.unit a)) \<cdot>\<^sub>D
                         H (\<r>\<^sub>C\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         H (\<l>\<^sub>C[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
          using a D.comp_assoc B.obj_simps by simp
        also have "... = (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H (\<tau>.F.unit a)) \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, \<tau>.F.map\<^sub>0 a)) \<cdot>\<^sub>D
                         H (\<r>\<^sub>C\<^sup>-\<^sup>1[\<tau>\<^sub>0 a])) \<cdot>\<^sub>D
                         H (\<l>\<^sub>C[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<cdot>\<^sub>D H (\<tau>\<^sub>0 a \<star>\<^sub>C \<tau>.F.unit a)
                  = (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H (\<tau>.F.unit a)) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, \<tau>.F.map\<^sub>0 a))"
          proof -
            have "D.seq (H (\<tau>\<^sub>0 a \<star>\<^sub>C \<tau>.F.unit a)) (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, \<tau>.F.map\<^sub>0 a))"
              using a C.VV.arr_char C.VV.dom_char C.VV.cod_char C.obj_simps by auto
            moreover have "D.iso (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)) \<and> D.iso (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, \<tau>.F.map\<^sub>0 a))"
            proof -
              have "C.ide (F a) \<and> src\<^sub>C (\<tau>\<^sub>0 a) = trg\<^sub>C (F a) \<and> src\<^sub>C (\<tau>\<^sub>0 a) = trg\<^sub>C (\<tau>.F.map\<^sub>0 a)"
                using a by auto
              moreover have "C.ide (\<tau>.F.map\<^sub>0 a)"
              proof -
                (* TODO: I still haven't been able to configure the simps to do this. *)
                have "C.obj (\<tau>.F.map\<^sub>0 a)"
                  using a by simp
                thus ?thesis by auto
              qed
              ultimately show ?thesis
                using a H.cmp_components_are_iso B.obj_simps by auto
            qed
            ultimately show ?thesis
              using a H.\<Phi>.naturality [of "(\<tau>\<^sub>0 a, \<tau>.F.unit a)"]
                    C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
                    D.invert_opposite_sides_of_square
                      [of "\<Phi>\<^sub>H (\<tau>\<^sub>0 a, F a)" "H (\<tau>\<^sub>0 a) \<star>\<^sub>D H (\<tau>.F.unit a)"
                          "H (\<tau>\<^sub>0 a \<star>\<^sub>C \<tau>.F.unit a)" "\<Phi>\<^sub>H (\<tau>\<^sub>0 a, \<tau>.F.map\<^sub>0 a)"]
              by auto
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H (\<tau>.F.unit a)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H.unit (\<tau>.F.map\<^sub>0 a)) \<cdot>\<^sub>D
                         \<r>\<^sub>D\<^sup>-\<^sup>1[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D
                         (H (\<l>\<^sub>C[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 a, \<tau>.F.map\<^sub>0 a)) \<cdot>\<^sub>D H (\<r>\<^sub>C\<^sup>-\<^sup>1[\<tau>\<^sub>0 a])
                  = (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H.unit (\<tau>.F.map\<^sub>0 a)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[H (\<tau>\<^sub>0 a)]"
            using a H.preserves_runit(2) [of "\<tau>\<^sub>0 a"] D.comp_assoc
            by (metis C.ideD(1) C.runit'_simps(1) C.src.preserves_ide C.trg_src
                D.invert_side_of_triangle(1) \<tau>.F.map\<^sub>0_def H.cmp_components_are_iso
                H.preserves_reflects_arr \<tau>.ide_map\<^sub>0_obj \<tau>.map\<^sub>0_simps(2))
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H (\<tau>.F.unit a)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H.unit (\<tau>.F.map\<^sub>0 a)) \<cdot>\<^sub>D
                         \<r>\<^sub>D\<^sup>-\<^sup>1[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D
                         \<l>\<^sub>D[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D
                         (D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                         (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
        proof -
          have "H (\<l>\<^sub>C[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a)
                  = \<l>\<^sub>D[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D (D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                    D.inv (\<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a)) \<cdot>\<^sub>D \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a)"
            using a H.preserves_lunit(1) D.comp_assoc by auto
          also have "... = \<l>\<^sub>D[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D (D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
          proof - 
            have "D.inv (\<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a)) \<cdot>\<^sub>D \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a)
                    = H (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a)"
              using a H.cmp_components_are_iso D.comp_inv_arr'
              by (metis C.isomorphic_implies_hpar(1) \<tau>.G.map\<^sub>0_simps(2) \<tau>.G.weakly_preserves_objects
                  H.cmp_simps(4) \<tau>.ide_map\<^sub>0_obj \<tau>.map\<^sub>0_simps(3))
            moreover have "(D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                           (H (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))
                             = (D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
              using a H.unit_char(2) D.comp_arr_dom
              by (metis D.arr_inv D.dom_inv D.whisker_right \<tau>.G.map\<^sub>0_simps(1) H.unit_simps(5)
                  H.preserves_ide \<tau>.ide_map\<^sub>0_obj)
            ultimately show ?thesis by simp
          qed
          finally have "H (\<l>\<^sub>C[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D \<Phi>\<^sub>H (\<tau>.G.map\<^sub>0 a, \<tau>\<^sub>0 a)
                          = \<l>\<^sub>D[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D (D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a))"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((H (\<tau>\<^sub>0 a) \<star>\<^sub>D H (\<tau>.F.unit a)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 a) \<star>\<^sub>D H.unit (\<tau>.F.map\<^sub>0 a))) \<cdot>\<^sub>D
                         \<r>\<^sub>D\<^sup>-\<^sup>1[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D
                         \<l>\<^sub>D[H (\<tau>\<^sub>0 a)]"
        proof -
          have "(D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))
                  = D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<cdot>\<^sub>D H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a)"
            using a D.whisker_right H.unit_char(2) by simp
          also have "... = H.map\<^sub>0 (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a)"
            using a H.unit_char(1-2) [of "\<tau>.G.map\<^sub>0 a"] D.comp_inv_arr' by simp
          finally have "(D.inv (H.unit (\<tau>.G.map\<^sub>0 a)) \<star>\<^sub>D H (\<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                        (H.unit (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a))
                          = H.map\<^sub>0 (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a)"
            by blast
          moreover have "\<l>\<^sub>D[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D (H.map\<^sub>0 (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a)) = \<l>\<^sub>D[H (\<tau>\<^sub>0 a)]"
            using a D.comp_arr_dom [of "\<l>\<^sub>D[H (\<tau>\<^sub>0 a)]" "H.map\<^sub>0 (\<tau>.G.map\<^sub>0 a) \<star>\<^sub>D H (\<tau>\<^sub>0 a)"]
            by auto
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 a) \<star>\<^sub>D HoF.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[H (\<tau>\<^sub>0 a)] \<cdot>\<^sub>D \<l>\<^sub>D[H (\<tau>\<^sub>0 a)]"
          using a HoF.unit_char' D.whisker_left [of "H (\<tau>\<^sub>0 a)"] by simp
        also have "... = (map\<^sub>0 a \<star>\<^sub>D HoF.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a]"
          unfolding map\<^sub>0_def by simp
        finally show "(map\<^sub>0 a \<star>\<^sub>D HoF.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[map\<^sub>0 a] =
                      map\<^sub>1 a \<cdot>\<^sub>D (HoG.unit a \<star>\<^sub>D map\<^sub>0 a)"
          by simp
      qed
      show "\<And>f g. \<lbrakk>B.ide f; B.ide g; src\<^sub>B g = trg\<^sub>B f\<rbrakk> \<Longrightarrow>
                    (map\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>D HoF.cmp (g, f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>B g), (H \<circ> F) g, (H \<circ> F) f] \<cdot>\<^sub>D
                    (map\<^sub>1 g \<star>\<^sub>D (H \<circ> F) f) \<cdot>\<^sub>D
                    D.inv \<a>\<^sub>D[(H \<circ> G) g, map\<^sub>0 (src\<^sub>B g), (H \<circ> F) f] \<cdot>\<^sub>D
                    ((H \<circ> G) g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[(H \<circ> G) g, (H \<circ> G) f, map\<^sub>0 (src\<^sub>B f)]
                      = map\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>D (HoG.cmp (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f))"
      proof -
        fix f g 
        assume f: "B.ide f" and g: "B.ide g" and fg: "src\<^sub>B g = trg\<^sub>B f"
        have "map\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>D (HoG.cmp (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f))
                = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                  H (\<tau>\<^sub>1 (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                  \<Phi>\<^sub>H (G (g \<star>\<^sub>B f), \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                  (H (G (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                  H (\<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                  \<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
          unfolding map\<^sub>0_def map\<^sub>1_def HoG.cmp_def
          using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char D.comp_assoc by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G (g \<star>\<^sub>B f), \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         ((H (G (g \<star>\<^sub>B f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         (H (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
          using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char
                C.VV.arr_char C.VV.dom_char C.VV.cod_char \<tau>.G.FF_def
                D.comp_assoc D.whisker_right
          by auto
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G (g \<star>\<^sub>B f), \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (H (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
        proof -
          have "(H (G (g \<star>\<^sub>B f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D (H (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))
                  = H (G (g \<star>\<^sub>B f)) \<cdot>\<^sub>D H (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))"
            using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char D.whisker_right
            by simp
          also have "... = H (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))"
            using f g fg D.comp_cod_arr [of "H (\<Phi>\<^sub>G (g, f))" "H (G (g \<star>\<^sub>B f))"]
                  B.VV.arr_char B.VV.dom_char B.VV.cod_char
            by simp
          finally have "(H (G (g \<star>\<^sub>B f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                        (H (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))
                          = H (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                         H (\<Phi>\<^sub>G (g, f) \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
          using f g fg H.\<Phi>.naturality [of "(\<Phi>\<^sub>G (g, f), \<tau>\<^sub>0 (src\<^sub>B f))"]
                B.VV.arr_char B.VV.dom_char B.VV.cod_char \<tau>.G.FF_def
                C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
                D.comp_assoc
          by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>C (\<Phi>\<^sub>G (g, f) \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
          using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char D.comp_assoc by simp
        also have "... = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         H ((\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>C
                            \<a>\<^sub>C[\<tau>\<^sub>0 (trg\<^sub>B g), F g, F f] \<cdot>\<^sub>C
                            (\<tau>\<^sub>1 g \<star>\<^sub>C F f) \<cdot>\<^sub>C
                            \<a>\<^sub>C\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>B g), F f] \<cdot>\<^sub>C
                            (G g \<star>\<^sub>C \<tau>\<^sub>1 f) \<cdot>\<^sub>C
                            \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)]) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
          using f g fg \<tau>.respects_hcomp by simp
        also have "... = (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C \<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[\<tau>\<^sub>0 (trg\<^sub>B g), F g, F f] \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 g \<star>\<^sub>C F f) \<cdot>\<^sub>D
                         H (\<a>\<^sub>C\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>B g), F f]) \<cdot>\<^sub>D
                         H (G g \<star>\<^sub>C \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)] \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
          using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char \<tau>.F.FF_def D.comp_assoc
          by simp
        also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f)) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[\<tau>\<^sub>0 (trg\<^sub>B g), F g, F f]) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 g \<star>\<^sub>C F f) \<cdot>\<^sub>D
                         H (\<a>\<^sub>C\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>B g), F f]) \<cdot>\<^sub>D
                         H (G g \<star>\<^sub>C \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)] \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<cdot>\<^sub>D H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C \<Phi>\<^sub>F (g, f))
                  = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f))"
          proof -
            have "\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f)) \<cdot>\<^sub>D (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) =
                  H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f)"
              using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char
                    C.VV.arr_char C.VV.dom_char C.VV.cod_char \<tau>.F.FF_def H.FF_def
                    H.\<Phi>.naturality [of "(\<tau>\<^sub>0 (trg\<^sub>B g), \<Phi>\<^sub>F (g, f))"]
              by auto
            moreover have "D.seq (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f)))"
              using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char
                    C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
              by auto
            moreover have "D.iso (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F (g \<star>\<^sub>B f))) \<and>
                           D.iso (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f))"
              using f g fg H.cmp_components_are_iso by simp
            ultimately show ?thesis
            using f g fg D.invert_opposite_sides_of_square by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f)) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 g \<star>\<^sub>C F f)) \<cdot>\<^sub>D
                         H (\<a>\<^sub>C\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>B g), F f]) \<cdot>\<^sub>D
                         H (G g \<star>\<^sub>C \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)] \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f)) \<cdot>\<^sub>D H \<a>\<^sub>C[\<tau>\<^sub>0 (trg\<^sub>B g), F g, F f]
                  = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                    (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                    D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f))"
          proof -
            have "D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f)) \<cdot>\<^sub>D H \<a>\<^sub>C[\<tau>\<^sub>0 (trg\<^sub>B g), F g, F f]
                    = ((D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f)) \<cdot>\<^sub>D
                      \<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g \<star>\<^sub>C F f)) \<cdot>\<^sub>D
                      (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f))) \<cdot>\<^sub>D
                      \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                      (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                      D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f))"
              using f g fg H.preserves_assoc(1) D.comp_assoc by simp
            also have "... = ((H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (F g \<star>\<^sub>C F f)) \<cdot>\<^sub>D
                             (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f))) \<cdot>\<^sub>D
                             \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f))"
              using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char
                    H.FF_def D.comp_assoc D.comp_inv_arr' H.cmp_components_are_iso
              by simp
            also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                             (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f))"
              using f g fg C.VV.arr_char H.cmp_simps(5) D.comp_cod_arr D.comp_assoc by auto
            finally show ?thesis by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D
                         H (\<a>\<^sub>C\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>B g), F f])) \<cdot>\<^sub>D
                         H (G g \<star>\<^sub>C \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)] \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f)) \<cdot>\<^sub>D H (\<tau>\<^sub>1 g \<star>\<^sub>C F f)
                  = (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f))"
          proof -
            have "\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f) \<cdot>\<^sub>D (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f))
                    = H (\<tau>\<^sub>1 g \<star>\<^sub>C F f) \<cdot>\<^sub>D \<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)"
              using f g fg H.\<Phi>.naturality [of "(\<tau>\<^sub>1 g, F f)"]
                    C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
              by simp
            moreover have "D.seq (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f))
                                 (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f))"
              using f g fg by fastforce
            moreover have "D.iso (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>C F g, F f)) \<and>
                           D.iso (\<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f))"
              using f g fg H.cmp_components_are_iso by simp
            ultimately show ?thesis
              using f g fg D.invert_opposite_sides_of_square by metis
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g) \<star>\<^sub>C F f)) \<cdot>\<^sub>D
                         H (G g \<star>\<^sub>C \<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)] \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D H (\<a>\<^sub>C\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>B g), F f])
                  = (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                    (H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                    D.inv (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g) \<star>\<^sub>C F f))"
          proof -
            have "D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D H (\<a>\<^sub>C\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>B g), F f])
                    = ((D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D
                      \<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D
                      (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f))) \<cdot>\<^sub>D
                      \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                      (H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                      D.inv (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g) \<star>\<^sub>C F f))"
              using f g fg H.preserves_assoc(2) D.comp_assoc by simp
            also have "... = (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                             (H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                             D.inv (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g) \<star>\<^sub>C F f))"
            proof -
              have "D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D \<Phi>\<^sub>H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g), F f)
                      = H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)"
                using f g fg H.cmp_components_are_iso D.comp_inv_arr' H.FF_def
                      C.VV.arr_char C.VV.dom_char C.VV.cod_char
                by simp
              moreover have "(H (G g \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f))
                               = (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f))"
                using f g fg D.comp_cod_arr C.VV.arr_char C.VV.dom_char C.VV.cod_char
                by simp
              ultimately show ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D H (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)]) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g) \<star>\<^sub>C F f)) \<cdot>\<^sub>D H (G g \<star>\<^sub>C \<tau>\<^sub>1 f)
                  = (H (G g) \<star>\<^sub>D H (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f)))"
          proof -
            have "\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (trg\<^sub>B f) \<star>\<^sub>C F f) \<cdot>\<^sub>D (H (G g) \<star>\<^sub>D H (\<tau>\<^sub>1 f))
                    = H (G g \<star>\<^sub>C \<tau>\<^sub>1 f) \<cdot>\<^sub>D \<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))"
              using f g fg H.\<Phi>.naturality [of "(G g, \<tau>\<^sub>1 f)"]
                    C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
              by simp
            thus ?thesis
              using f g fg H.cmp_components_are_iso
                    C.VV.arr_char C.VV.dom_char C.VV.cod_char
                    D.invert_opposite_sides_of_square
                      [of "\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (trg\<^sub>B f) \<star>\<^sub>C F f)" "H (G g) \<star>\<^sub>D H (\<tau>\<^sub>1 f)"
                          "H (G g \<star>\<^sub>C \<tau>\<^sub>1 f)" "\<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))"]
              by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D H (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (G g), H (G f), H (\<tau>\<^sub>0 (src\<^sub>B f))] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (G g, G f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))"
        proof -
          have "D.inv (\<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)]
                  = (H (G g) \<star>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                    \<a>\<^sub>D[H (G g), H (G f), H (\<tau>\<^sub>0 (src\<^sub>B f))] \<cdot>\<^sub>D
                    (D.inv (\<Phi>\<^sub>H (G g, G f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                    D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)))"
          proof -
            have "D.inv (\<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D H \<a>\<^sub>C[G g, G f, \<tau>\<^sub>0 (src\<^sub>B f)]
                    = ((D.inv (\<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                      \<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                      (H (G g) \<star>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>D
                      \<a>\<^sub>D[H (G g), H (G f), H (\<tau>\<^sub>0 (src\<^sub>B f))] \<cdot>\<^sub>D
                      (D.inv (\<Phi>\<^sub>H (G g, G f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                      D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f)))"
              using f g fg H.preserves_assoc(1)
                    H.cmp_components_are_iso C.VV.arr_char C.VV.dom_char C.VV.cod_char
                    D.comp_assoc
              by simp
            moreover have "D.inv (\<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>H (G g, G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))
                             = H (G g) \<star>\<^sub>D H (G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))"
              using f g fg H.cmp_components_are_iso C.VV.arr_char C.VV.dom_char C.VV.cod_char
                    D.comp_inv_arr' H.FF_def
              by simp
            moreover have "(H (G g) \<star>\<^sub>D H (G f \<star>\<^sub>C \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                           (H (G g) \<star>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f)))
                             = H (G g) \<star>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f))"
              using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char
                    D.whisker_left D.comp_cod_arr
              by simp
            ultimately show ?thesis by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                         ((D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f))) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                         ((H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D H (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f)))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (G g), H (G f), H (\<tau>\<^sub>0 (src\<^sub>B f))]"
        proof - 
          have "\<a>\<^sub>D[H (G g), H (G f), H (\<tau>\<^sub>0 (src\<^sub>B f))] \<cdot>\<^sub>D
                (D.inv (\<Phi>\<^sub>H (G g, G f)) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                (D.inv (\<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                \<Phi>\<^sub>H (G g \<star>\<^sub>C G f, \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                (\<Phi>\<^sub>H (G g, G f) \<star>\<^sub>D H (\<tau>\<^sub>0 (src\<^sub>B f)))
                  = \<a>\<^sub>D[H (G g), H (G f), H (\<tau>\<^sub>0 (src\<^sub>B f))]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.whisker_right [of "H (\<tau>\<^sub>0 (src\<^sub>B f))" "D.inv (\<Phi>\<^sub>H (G g, G f))" "\<Phi>\<^sub>H (G g, G f)"]
                  D.comp_inv_arr' C.VV.arr_char C.VV.dom_char C.VV.cod_char H.FF_def
                  H.cmp_components_are_iso
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (F (g \<star>\<^sub>B f)) \<cdot>\<^sub>D
                         H (\<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (F g, F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (\<tau>\<^sub>0 (trg\<^sub>B g)), H (F g), H (F f)] \<cdot>\<^sub>D
                         (D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 g) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[H (G g), H (\<tau>\<^sub>0 (src\<^sub>B g)), H (F f)] \<cdot>\<^sub>D
                         (H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D
                         H (\<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[H (G g), H (G f), H (\<tau>\<^sub>0 (src\<^sub>B f))]"
        proof -
          have "(H (G g) \<star>\<^sub>D D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f))) \<cdot>\<^sub>D
                (H (G g) \<star>\<^sub>D H (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                (H (G g) \<star>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f)))
                  = H (G g) \<star>\<^sub>D
                      D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (src\<^sub>B g), F f)) \<cdot>\<^sub>D H (\<tau>\<^sub>1 f) \<cdot>\<^sub>D \<Phi>\<^sub>H (G f, \<tau>\<^sub>0 (src\<^sub>B f))"
            using f g fg C.VV.arr_char C.VV.dom_char C.VV.cod_char D.whisker_left
                  H.cmp_components_are_iso
            by simp
          moreover have "(H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f))
                           = H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D
                               H (F (g \<star>\<^sub>B f)) \<cdot>\<^sub>D H (\<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<Phi>\<^sub>H (F g, F f)"
          proof -
            have "(H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D (H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D \<Phi>\<^sub>H (F g, F f))
                    = H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D H (\<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<Phi>\<^sub>H (F g, F f)"
            proof -
              have "D.arr (H (\<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<Phi>\<^sub>H (F g, F f))"
                using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char \<tau>.F.FF_def
                by (intro D.seqI) auto
              thus ?thesis
                using f g fg D.whisker_left C.VV.arr_char by simp
            qed
            also have "... = H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D
                               (H (F (g \<star>\<^sub>B f) \<cdot>\<^sub>C \<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D \<Phi>\<^sub>H (F g, F f)"
              using f g fg C.comp_cod_arr B.VV.arr_char \<tau>.F.cmp_simps(5) by auto
            also have "... = H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D
                               (H (F (g \<star>\<^sub>B f)) \<cdot>\<^sub>D H (\<Phi>\<^sub>F (g, f))) \<cdot>\<^sub>D \<Phi>\<^sub>H (F g, F f)"
              using f g fg B.VV.arr_char \<tau>.F.cmp_simps(5) by auto
            also have "... = H (\<tau>\<^sub>0 (trg\<^sub>B g)) \<star>\<^sub>D
                               H (F (g \<star>\<^sub>B f)) \<cdot>\<^sub>D H (\<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<Phi>\<^sub>H (F g, F f)"
              using D.comp_assoc by simp
            finally show ?thesis by simp
          qed
          moreover have "(D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (H (\<tau>\<^sub>1 g) \<star>\<^sub>D H (F f)) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f))
                           = D.inv (\<Phi>\<^sub>H (\<tau>\<^sub>0 (trg\<^sub>B g), F g)) \<cdot>\<^sub>D
                             H (\<tau>\<^sub>1 g) \<cdot>\<^sub>D \<Phi>\<^sub>H (G g, \<tau>\<^sub>0 (src\<^sub>B g)) \<star>\<^sub>D H (F f)"
            using f g fg D.whisker_right C.VV.arr_char C.VV.dom_char C.VV.cod_char
            by simp
          ultimately show ?thesis
            by simp
        qed
        also have "... = (map\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>D HoF.cmp (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>B g), (H \<circ> F) g, (H \<circ> F) f] \<cdot>\<^sub>D
                         (map\<^sub>1 g \<star>\<^sub>D (H \<circ> F) f) \<cdot>\<^sub>D
                         D.inv \<a>\<^sub>D[(H \<circ> G) g, map\<^sub>0 (src\<^sub>B g), (H \<circ> F) f] \<cdot>\<^sub>D
                         ((H \<circ> G) g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[(H \<circ> G) g, (H \<circ> G) f, map\<^sub>0 (src\<^sub>B f)]"
          unfolding map\<^sub>0_def map\<^sub>1_def HoF.cmp_def
          using f g fg B.VV.arr_char B.VV.dom_char B.VV.cod_char by simp
        finally show "(map\<^sub>0 (trg\<^sub>B g) \<star>\<^sub>D HoF.cmp (g, f)) \<cdot>\<^sub>D
                      \<a>\<^sub>D[map\<^sub>0 (trg\<^sub>B g), (H \<circ> F) g, (H \<circ> F) f] \<cdot>\<^sub>D
                      (map\<^sub>1 g \<star>\<^sub>D (H \<circ> F) f) \<cdot>\<^sub>D
                      D.inv \<a>\<^sub>D[(H \<circ> G) g, map\<^sub>0 (src\<^sub>B g), (H \<circ> F) f] \<cdot>\<^sub>D
                      ((H \<circ> G) g \<star>\<^sub>D map\<^sub>1 f) \<cdot>\<^sub>D \<a>\<^sub>D[(H \<circ> G) g, (H \<circ> G) f, map\<^sub>0 (src\<^sub>B f)]
                        = map\<^sub>1 (g \<star>\<^sub>B f) \<cdot>\<^sub>D (HoG.cmp (g, f) \<star>\<^sub>D map\<^sub>0 (src\<^sub>B f))"
          by simp
      qed
    qed

    lemma is_pseudonatural_transformation:
    shows "pseudonatural_transformation V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             HoF.map HoF.cmp HoG.map HoG.cmp map\<^sub>0 map\<^sub>1"
      ..

  end

  subsection "Pseudonatural Equivalences"

  text \<open>
    A \emph{pseudonatural equivalence} is a pseudonatural transformation whose components
    at objects are equivalence maps.  Pseudonatural equivalences between pseudofunctors
    generalize natural isomorphisms between ordinary functors.
  \<close>

  locale pseudonatural_equivalence =
    pseudonatural_transformation +
  assumes components_are_equivalences: "C.obj a \<Longrightarrow> D.equivalence_map (\<tau>\<^sub>0 a)"

  subsubsection "Identity Transformations are Pseudonatural Equivalences"

  sublocale identity_pseudonatural_transformation \<subseteq>
            pseudonatural_equivalence V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
              F \<Phi>\<^sub>F F \<Phi>\<^sub>F map\<^sub>0 map\<^sub>1
    by unfold_locales (simp add: D.obj_is_equivalence_map)

  subsubsection "Composition of Pseudonatural Equivalences"

  locale composite_pseudonatural_equivalence =
    composite_pseudonatural_transformation +
    \<sigma>: pseudonatural_equivalence V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
         F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<sigma>\<^sub>0 \<sigma>\<^sub>1 +
    \<rho>: pseudonatural_equivalence V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
         G \<Phi>\<^sub>G H \<Phi>\<^sub>H \<rho>\<^sub>0 \<rho>\<^sub>1
  begin

    sublocale pseudonatural_equivalence V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                F \<Phi>\<^sub>F H \<Phi>\<^sub>H map\<^sub>0 map\<^sub>1
      apply unfold_locales
      by (metis D.equivalence_maps_compose D.hcomp_in_hhomE \<rho>.components_are_equivalences
          \<sigma>.components_are_equivalences map\<^sub>0_def map\<^sub>0_in_hom(1))

    lemma is_pseudonatural_equivalence:
    shows "pseudonatural_equivalence V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             F \<Phi>\<^sub>F H \<Phi>\<^sub>H map\<^sub>0 map\<^sub>1"
      ..

  end

  locale pseudonatural_equivalence_whisker_right =
    pseudonatural_transformation_whisker_right +
    \<tau>: pseudonatural_equivalence
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
  begin

    interpretation FoH: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D H \<Phi>\<^sub>H F \<Phi>\<^sub>F
      ..
    interpretation GoH: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D H \<Phi>\<^sub>H G \<Phi>\<^sub>G
      ..

    sublocale pseudonatural_equivalence V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          \<open>F o H\<close> FoH.cmp \<open>G o H\<close> GoH.cmp map\<^sub>0 map\<^sub>1
      using map\<^sub>0_def \<tau>.components_are_equivalences
      by unfold_locales simp

    lemma is_pseudonatural_equivalence:
    shows "pseudonatural_equivalence V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          (F o H) FoH.cmp (G o H) GoH.cmp map\<^sub>0 map\<^sub>1"
      ..

  end

  locale pseudonatural_equivalence_whisker_left =
    pseudonatural_transformation_whisker_left +
    \<tau>: pseudonatural_equivalence
         V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
  begin

    interpretation HoF: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F H \<Phi>\<^sub>H
      ..
    interpretation HoG: composite_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G H \<Phi>\<^sub>H
      ..

    sublocale pseudonatural_equivalence V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          \<open>H o F\<close> HoF.cmp \<open>H o G\<close> HoG.cmp map\<^sub>0 map\<^sub>1
      using map\<^sub>0_def \<tau>.components_are_equivalences H.preserves_equivalence_maps
      by unfold_locales simp

    lemma is_pseudonatural_equivalence:
    shows "pseudonatural_equivalence V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                          (H o F) HoF.cmp (H o G) HoG.cmp map\<^sub>0 map\<^sub>1"
      ..

  end

  subsubsection "Converse of a Pseudonatural Equivalence"

  text \<open>
    It is easy to see that natural isomorphism between ordinary functors is a symmetric
    relation because a unique inverse to a natural isomorphism is obtained merely by inverting
    the components.  However the situation is more difficult for pseudonatural equivalences
    because they do not have unique inverses.  Instead, we have to choose a quasi-inverse for
    each of the components.  In order to satisfy the required coherence conditions,
    it is necessary for these quasi-inverses to be part of chosen adjoint equivalences.
    Some long calculations to establish the coherence conditions seem unavoidable.
    The purpose of this section is to carry out the construction, given a pseudonatural
    equivalence, of a ``converse'' pseudonatural equivalence in the opposite direction.
  \<close>

  locale converse_pseudonatural_equivalence =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F +
    G: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G +
    \<tau>: pseudonatural_equivalence
  begin

    abbreviation (input) F\<^sub>0
    where "F\<^sub>0 \<equiv> F.map\<^sub>0"

    abbreviation (input) G\<^sub>0
    where "G\<^sub>0 \<equiv> G.map\<^sub>0"

    definition map\<^sub>0
    where "map\<^sub>0 a = (SOME g. \<exists>\<eta> \<epsilon>. adjoint_equivalence_in_bicategory
                                     V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (\<tau>\<^sub>0 a) g \<eta> \<epsilon>)"

    abbreviation (input) \<tau>\<^sub>0'
    where "\<tau>\<^sub>0' \<equiv> map\<^sub>0"

    definition unit
    where "unit a = (SOME \<eta>. \<exists>\<epsilon>. adjoint_equivalence_in_bicategory
                                   V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (\<tau>\<^sub>0 a) (\<tau>\<^sub>0' a) \<eta> \<epsilon>)"

    abbreviation (input) \<eta>
    where "\<eta> \<equiv> unit"

    definition counit
    where "counit a = (SOME \<epsilon>. adjoint_equivalence_in_bicategory
                                 V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (\<tau>\<^sub>0 a) (\<tau>\<^sub>0' a) (\<eta> a) \<epsilon>)"

    abbreviation (input) \<epsilon>
    where "\<epsilon> \<equiv> counit"

    lemma chosen_adjoint_equivalence:
    assumes "C.obj a"
    shows "adjoint_equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (\<tau>\<^sub>0 a) (\<tau>\<^sub>0' a) (\<eta> a) (\<epsilon> a)"
      using assms \<tau>.components_are_equivalences map\<^sub>0_def unit_def counit_def
            D.obj_is_equivalence_map D.equivalence_map_extends_to_adjoint_equivalence
            someI_ex [of "\<lambda>g. \<exists>\<eta> \<epsilon>. adjoint_equivalence_in_bicategory
                                      V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (\<tau>\<^sub>0 a) g \<eta> \<epsilon>"]
            someI_ex [of "\<lambda>\<eta>. \<exists>\<epsilon>. adjoint_equivalence_in_bicategory
                                    V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (\<tau>\<^sub>0 a) (\<tau>\<^sub>0' a) \<eta> \<epsilon>"]
            someI_ex [of "\<lambda>\<epsilon>. adjoint_equivalence_in_bicategory
                                    V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (\<tau>\<^sub>0 a) (\<tau>\<^sub>0' a) (\<eta> a) \<epsilon>"]
      by simp

    lemma map\<^sub>0_in_hhom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>\<tau>\<^sub>0' a : G\<^sub>0 a \<rightarrow>\<^sub>D F\<^sub>0 a\<guillemotright>"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis
        using assms \<tau>.map\<^sub>0_in_hhom [of a] antipar by auto
    qed

    lemma map\<^sub>0_simps [simp]:
    assumes "C.obj a"
    shows "D.ide (\<tau>\<^sub>0' a)" and "src\<^sub>D (\<tau>\<^sub>0' a) = G\<^sub>0 a" and "trg\<^sub>D (\<tau>\<^sub>0' a) = F\<^sub>0 a"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show "D.ide (\<tau>\<^sub>0' a)"
        by simp
      show "src\<^sub>D (\<tau>\<^sub>0' a) = G\<^sub>0 a"
        using assms map\<^sub>0_in_hhom by blast
      show "trg\<^sub>D (\<tau>\<^sub>0' a) = F\<^sub>0 a"
        using assms map\<^sub>0_in_hhom by blast
    qed

    lemma equivalence_map_map\<^sub>0 [simp]:
    assumes "C.obj a"
    shows "D.equivalence_map (\<tau>\<^sub>0' a)"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show "D.equivalence_map (\<tau>\<^sub>0' a)"
        using D.equivalence_map_def adjoint_equivalence_in_bicategory_axioms
              dual_equivalence
        by blast
    qed

    lemma unit_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>\<eta> a : F\<^sub>0 a \<rightarrow>\<^sub>D F\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<eta> a : F\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a\<guillemotright>"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show "\<guillemotleft>\<eta> a : F\<^sub>0 a \<rightarrow>\<^sub>D F\<^sub>0 a\<guillemotright>"
        using assms unit_in_hom antipar(1) by auto
      show "\<guillemotleft>\<eta> a : F\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a\<guillemotright>"
        using assms unit_in_hom antipar(1) by auto
    qed

    lemma unit_simps [simp]:
    assumes "C.obj a"
    shows "D.iso (\<eta> a)" and "D.arr (\<eta> a)"
    and "src\<^sub>D (\<eta> a) = F\<^sub>0 a" and "trg\<^sub>D (\<eta> a) = F\<^sub>0 a"
    and "D.dom (\<eta> a) = F\<^sub>0 a" and "D.cod (\<eta> a) = \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show "D.iso (\<eta> a)" and "D.arr (\<eta> a)"
      and "src\<^sub>D (\<eta> a) = F\<^sub>0 a" and "trg\<^sub>D (\<eta> a) = F\<^sub>0 a"
      and "D.dom (\<eta> a) = F\<^sub>0 a" and "D.cod (\<eta> a) = \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a"
        using assms by auto
    qed

    lemma iso_unit:
    assumes "C.obj a"
    shows "D.iso (\<eta> a)"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis by simp
    qed

    lemma counit_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>\<epsilon> a : G\<^sub>0 a \<rightarrow>\<^sub>D G\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<epsilon> a : \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a \<Rightarrow>\<^sub>D G\<^sub>0 a\<guillemotright>"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show "\<guillemotleft>\<epsilon> a : G\<^sub>0 a \<rightarrow>\<^sub>D G\<^sub>0 a\<guillemotright>"
        using assms counit_in_hom antipar(2) by auto
      show " \<guillemotleft>\<epsilon> a : \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a \<Rightarrow>\<^sub>D G\<^sub>0 a\<guillemotright>"
        using assms counit_in_hom antipar(2) by simp
    qed

    lemma counit_simps [simp]:
    assumes "C.obj a"
    shows "D.iso (\<epsilon> a)" and "D.arr (\<epsilon> a)"
    and "src\<^sub>D (\<epsilon> a) = G\<^sub>0 a" and "trg\<^sub>D (\<epsilon> a) = G\<^sub>0 a"
    and "D.dom (\<epsilon> a) = \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a" and "D.cod (\<epsilon> a) = G\<^sub>0 a"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show "D.iso (\<epsilon> a)" and "D.arr (\<epsilon> a)"
      and "src\<^sub>D (\<epsilon> a) = G\<^sub>0 a" and "trg\<^sub>D (\<epsilon> a) = G\<^sub>0 a"
      and "D.dom (\<epsilon> a) = \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a" and "D.cod (\<epsilon> a) = G\<^sub>0 a"
        using assms by auto
    qed

    lemma iso_counit:
    assumes "C.obj a"
    shows "D.iso (\<epsilon> a)"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show ?thesis by simp
    qed

    lemma quasi_inverts_components:
    assumes "C.obj a"
    shows "D.isomorphic (\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) (F\<^sub>0 a)"
    and "D.isomorphic (\<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) (G\<^sub>0 a)"
    and "D.quasi_inverses (\<tau>\<^sub>0 a) (\<tau>\<^sub>0' a)"
    proof -
      interpret adjoint_equivalence_in_bicategory
                  V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
        using assms chosen_adjoint_equivalence by simp
      show "D.isomorphic (\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) (F\<^sub>0 a)"
        using assms D.isomorphic_def D.isomorphic_symmetric unit_is_iso by blast
      show "D.isomorphic (\<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) (G\<^sub>0 a)"
        using assms D.isomorphic_def counit_is_iso by blast
      show "D.quasi_inverses (\<tau>\<^sub>0 a) (\<tau>\<^sub>0' a)"
        using D.quasi_inverses_def equivalence_in_bicategory_axioms by auto
    qed

    definition map\<^sub>1
    where "map\<^sub>1 f = (\<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> (src\<^sub>C f)) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 (src\<^sub>C f), \<tau>\<^sub>0' (src\<^sub>C f)]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' (trg\<^sub>C f), G f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f), \<tau>\<^sub>0' (src\<^sub>C f)] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f)) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' (trg\<^sub>C f), \<tau>\<^sub>0 (trg\<^sub>C f), F f] \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f)) \<cdot>\<^sub>D
                    ((\<eta> (trg\<^sub>C f) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f)) \<cdot>\<^sub>D
                    (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f))"

    abbreviation (input) \<tau>\<^sub>1'
    where "\<tau>\<^sub>1' \<equiv> map\<^sub>1"

    lemma map\<^sub>1_in_hom [intro]:
    assumes "C.ide f"
    shows "\<guillemotleft>\<tau>\<^sub>1' f : G\<^sub>0 (src\<^sub>C f) \<rightarrow>\<^sub>D F\<^sub>0 (trg\<^sub>C f)\<guillemotright>"
    and "\<guillemotleft>\<tau>\<^sub>1' f : F f \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D G f\<guillemotright>"
    proof -
      show "\<guillemotleft>\<tau>\<^sub>1' f : F f \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D G f\<guillemotright>"
        using assms \<tau>.iso_map\<^sub>1_ide \<tau>.map\<^sub>1_in_vhom
        by (unfold map\<^sub>1_def, intro D.comp_in_homI) auto
      thus "\<guillemotleft>\<tau>\<^sub>1' f : G\<^sub>0 (src\<^sub>C f) \<rightarrow>\<^sub>D F\<^sub>0 (trg\<^sub>C f)\<guillemotright>"
        using assms D.vconn_implies_hpar(1-2) by auto
    qed

    lemma map\<^sub>1_simps [simp]:
    assumes "C.ide f"
    shows "D.arr (\<tau>\<^sub>1' f)"
    and "src\<^sub>D (\<tau>\<^sub>1' f) = G\<^sub>0 (src\<^sub>C f)" and "trg\<^sub>D (\<tau>\<^sub>1' f) = F\<^sub>0 (trg\<^sub>C f)"
    and "D.dom (\<tau>\<^sub>1' f) = F f \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f)" and "D.cod (\<tau>\<^sub>1' f) = \<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D G f"
      using assms map\<^sub>1_in_hom by auto
    
    lemma iso_map\<^sub>1_ide:
    assumes "C.ide f"
    shows "D.iso (\<tau>\<^sub>1' f)"
    proof -
      interpret src: adjoint_equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        \<open>\<tau>\<^sub>0 (src\<^sub>C f)\<close> \<open>\<tau>\<^sub>0' (src\<^sub>C f)\<close> \<open>\<eta> (src\<^sub>C f)\<close> \<open>\<epsilon> (src\<^sub>C f)\<close>
        using assms chosen_adjoint_equivalence by simp
      interpret trg: adjoint_equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                        \<open>\<tau>\<^sub>0 (trg\<^sub>C f)\<close> \<open>\<tau>\<^sub>0' (trg\<^sub>C f)\<close> \<open>\<eta> (trg\<^sub>C f)\<close> \<open>\<epsilon> (trg\<^sub>C f)\<close>

        using assms chosen_adjoint_equivalence by simp
      show ?thesis
        unfolding map\<^sub>1_def
        using assms \<tau>.iso_map\<^sub>1_ide
        by (intro D.isos_compose) auto
    qed

    interpretation EV: self_evaluation_map V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D ..
    notation EV.eval ("\<lbrace>_\<rbrace>")

    sublocale pseudonatural_equivalence
                     V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G F \<Phi>\<^sub>F \<tau>\<^sub>0' \<tau>\<^sub>1'
    proof
      show "\<And>a. C.obj a \<Longrightarrow> D.ide (\<tau>\<^sub>0' a)"
        using map\<^sub>0_simps(1) by simp
      show "\<And>f. C.ide f \<Longrightarrow> D.iso (\<tau>\<^sub>1' f)"
        using iso_map\<^sub>1_ide by simp
      show "\<And>a. C.obj a \<Longrightarrow> \<guillemotleft>\<tau>\<^sub>0' a : src\<^sub>D (G a) \<rightarrow>\<^sub>D src\<^sub>D (F a)\<guillemotright>"
        by fastforce
      show "\<And>f. C.ide f \<Longrightarrow> \<guillemotleft>\<tau>\<^sub>1' f : F f \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f) \<Rightarrow>\<^sub>D \<tau>\<^sub>0' (trg\<^sub>C f) \<star>\<^sub>D G f\<guillemotright>"
        by auto
      show "\<And>a. C.obj a \<Longrightarrow> D.equivalence_map (\<tau>\<^sub>0' a)"
        by simp
      show "\<And>\<mu>. C.arr \<mu> \<Longrightarrow> \<tau>\<^sub>1' (C.cod \<mu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C \<mu>))
                               = (\<tau>\<^sub>0' (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1' (C.dom \<mu>)"
      proof -
        fix \<mu>
        assume \<mu>: "C.arr \<mu>"
        let ?a = "src\<^sub>C \<mu>"
        let ?b = "trg\<^sub>C \<mu>"
        let ?f = "C.dom \<mu>"
        let ?g = "C.cod \<mu>"
        have "\<tau>\<^sub>1' (C.cod \<mu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                       = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?g \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?g] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?g) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?g] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          unfolding map\<^sub>1_def
          using \<mu> D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?g \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?g] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<eta> ?b \<star>\<^sub>D F ?g) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((trg\<^sub>D (F \<mu>) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          using \<mu> D.whisker_right D.lunit'_naturality [of "F \<mu>"] D.comp_assoc
                D.whisker_right [of "\<tau>\<^sub>0' ?a" "trg\<^sub>D (F \<mu>) \<star>\<^sub>D F \<mu>" "\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f]"]
          by simp
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?g \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?g] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "((\<eta> ?b \<star>\<^sub>D F ?g) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((trg\<^sub>D (F \<mu>) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          proof -
            have "((\<eta> ?b \<star>\<^sub>D F ?g) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((trg\<^sub>D (F \<mu>) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                    = (\<eta> ?b \<star>\<^sub>D F ?g) \<cdot>\<^sub>D (trg\<^sub>D (F \<mu>) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
              using \<mu> D.whisker_right D.obj_simps by simp
            also have "... = (\<eta> ?b \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
              using \<mu> D.interchange [of "\<eta> ?b" "trg\<^sub>D (F \<mu>)" "F ?g" "F \<mu>"]
                    D.comp_arr_dom D.comp_cod_arr
              by simp
            also have "... = ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D (\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
              using \<mu> D.interchange [of "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b" "\<eta> ?b" "F \<mu>" "F ?f"]
                    D.comp_arr_dom D.comp_cod_arr
              by simp
            also have "... = (((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
              using \<mu> D.whisker_right by simp
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?g \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?g] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?g] \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using \<mu> D.whisker_right by simp
          also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using \<mu> D.assoc_naturality [of "\<tau>\<^sub>0' ?b" "\<tau>\<^sub>0 ?b" "F \<mu>"] by simp
          also have "... = ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using \<mu> D.whisker_right by simp
          finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?g] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?g \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g)) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using \<mu> \<tau>.iso_map\<^sub>1_ide D.whisker_right by simp
          also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g) \<cdot>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using \<mu> \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
          also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using \<mu> \<tau>.iso_map\<^sub>1_ide \<tau>.naturality
                  D.invert_opposite_sides_of_square
                    [of "\<tau>\<^sub>1 ?g" "G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a" "\<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>" "\<tau>\<^sub>1 ?f"]
            by simp
          also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using \<mu> \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
          also have "... = ((\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using \<mu> \<tau>.iso_map\<^sub>1_ide D.whisker_right by simp
          finally have "((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?g)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F \<mu>) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          using \<mu> D.assoc_naturality [of "\<tau>\<^sub>0' ?b" "G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a" "\<tau>\<^sub>0' ?a"] D.comp_assoc
          by simp
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D ((G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using \<mu> D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D[G ?f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using \<mu> D.assoc_naturality [of "G \<mu>" "\<tau>\<^sub>0 ?a" "\<tau>\<^sub>0' ?a"] by simp
          also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
            using \<mu> D.whisker_left by simp
          finally have "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?g, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D G\<^sub>0 ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<tau>\<^sub>0' ?b \<star>\<^sub>D (G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using \<mu> D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<epsilon> ?a"
            using \<mu> D.interchange [of "G ?g" "G \<mu>" "\<epsilon> ?a" "\<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                  D.comp_arr_dom D.comp_cod_arr
            by simp
          also have "... = \<tau>\<^sub>0' ?b \<star>\<^sub>D (G \<mu> \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D (G ?f \<star>\<^sub>D \<epsilon> ?a)"
            using \<mu> D.interchange [of "G \<mu>" "G ?f" "G\<^sub>0 ?a" "\<epsilon> ?a"]
                  D.comp_arr_dom D.comp_cod_arr
            by simp
          also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?f \<star>\<^sub>D \<epsilon> ?a)"
            using \<mu> D.whisker_left D.obj_simps by auto
          finally have "(\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?g \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?f \<star>\<^sub>D \<epsilon> ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu>) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?f]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D G ?f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G ?f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G ?f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?b \<star>\<^sub>D F ?f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D G\<^sub>0 ?a)
                  = \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g] \<cdot>\<^sub>D (G \<mu> \<star>\<^sub>D G\<^sub>0 ?a)"
            using \<mu> D.whisker_left D.obj_simps by simp
          also have "... = \<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<cdot>\<^sub>D \<r>\<^sub>D[G ?f]"
            using \<mu> D.runit_naturality [of "G \<mu>"] by simp
          also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu>) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?f])"
            using \<mu> D.whisker_left by simp
          finally have "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?g]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu> \<star>\<^sub>D G\<^sub>0 ?a)
                          = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu>) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G ?f])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1' ?f"
          unfolding map\<^sub>1_def
          using \<mu> D.comp_assoc by simp
        finally show "\<tau>\<^sub>1' ?g \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D \<tau>\<^sub>0' ?a) = (\<tau>\<^sub>0' ?b \<star>\<^sub>D G \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1' ?f"
          by blast
      qed
      show "\<And>a. C.obj a \<Longrightarrow>
                  (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0' a] = \<tau>\<^sub>1' a \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D \<tau>\<^sub>0' a)"
      proof -
        fix a
        assume "C.obj a"
        hence a: "C.obj a \<and> C.arr a \<and> C.ide a \<and> src\<^sub>C a = a \<and> trg\<^sub>C a = a"
          by auto
        have 1: "D.ide (F\<^sub>0 a)"
          using a F.map\<^sub>0_simps(1) by blast
        have 2: "D.ide (G\<^sub>0 a)"
          using a G.map\<^sub>0_simps(1) by blast
        have "\<tau>\<^sub>1' a \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D \<tau>\<^sub>0' a)
                       = (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (F.unit a \<star>\<^sub>D \<tau>\<^sub>0' a)"
          unfolding map\<^sub>1_def
          using a D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (((\<eta> a \<star>\<^sub>D F a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((F\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D \<tau>\<^sub>0' a) = \<l>\<^sub>D\<^sup>-\<^sup>1[F a] \<cdot>\<^sub>D F.unit a \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.whisker_right by simp
          also have "... = (F\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.lunit'_naturality [of "F.unit a"] by simp
          also have "... = ((F\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a 1 D.whisker_right by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D \<tau>\<^sub>0' a) =
                        ((F\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "((\<eta> a \<star>\<^sub>D F a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D ((F\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = (\<eta> a \<star>\<^sub>D F a) \<cdot>\<^sub>D (F\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a 1 D.whisker_right by simp
          also have "... = (\<eta> a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.interchange [of "\<eta> a" "F\<^sub>0 a" "F a" "F.unit a"]
                  D.comp_cod_arr D.comp_arr_dom
            by simp
          also have "... = ((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D (\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.interchange [of "\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a" "\<eta> a" "F.unit a" "F\<^sub>0 a"]
                  D.comp_cod_arr D.comp_arr_dom
            by simp
          also have "... = (((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a 1 D.whisker_right by simp
          finally have "((\<eta> a \<star>\<^sub>D F a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D ((F\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                          = (((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "(\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F a] \<cdot>\<^sub>D ((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.whisker_right by simp
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.assoc_naturality [of "\<tau>\<^sub>0' a" "\<tau>\<^sub>0 a" "F.unit a"] by simp
          also have "... = ((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                             (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a 1 D.whisker_right by simp
          finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                          = ((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, G a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "((\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D ((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = (\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a)) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a \<tau>.iso_map\<^sub>1_ide D.whisker_right by simp
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D F.unit a)) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a"
          proof -
            have "(\<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a] = \<tau>\<^sub>1 a \<cdot>\<^sub>D (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a)"
              using a \<tau>.respects_unit by simp
            hence "D.inv (\<tau>\<^sub>1 a) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0 a]
                     = G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a"
              using a \<tau>.iso_map\<^sub>1_ide D.invert_side_of_triangle(1) by simp
            hence "D.inv (\<tau>\<^sub>1 a) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]
                     = (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]"
              using a D.iso_lunit D.invert_side_of_triangle(2) D.comp_assoc by simp
            hence "D.inv (\<tau>\<^sub>1 a) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D F.unit a)
                     = (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]"
              using a D.iso_runit D.comp_assoc
                    D.invert_side_of_triangle(2)
                      [of "(G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]" "D.inv (\<tau>\<^sub>1 a) \<cdot>\<^sub>D (\<tau>\<^sub>0 a \<star>\<^sub>D F.unit a)"
                          "\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]"]
              by simp
            thus ?thesis by simp
          qed
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.whisker_left by simp
          also have "... = ((\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a D.whisker_right by simp
          finally have "((\<tau>\<^sub>0' a \<star>\<^sub>D D.inv (\<tau>\<^sub>1 a)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D F.unit a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                          = ((\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
          using a D.assoc_naturality [of "\<tau>\<^sub>0' a" "G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a" "\<tau>\<^sub>0' a"] D.comp_assoc
          by simp
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "(\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D ((G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' a \<star>\<^sub>D (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
            using a D.assoc_naturality [of "G.unit a" "\<tau>\<^sub>0 a" "\<tau>\<^sub>0' a"] by simp
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a])"
            using a 2 D.whisker_left [of "\<tau>\<^sub>0' a"] by simp
          finally have "(\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' a \<star>\<^sub>D (G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                          = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D G\<^sub>0 a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "(\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<epsilon> a"
            using a D.whisker_left D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "G a" "G.unit a" "\<epsilon> a" "\<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a"]
            by simp
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D G\<^sub>0 a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a)"
            using a 2 D.whisker_left D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "G.unit a" "G\<^sub>0 a" "G\<^sub>0 a" "\<epsilon> a"]
            by simp
          finally have "(\<tau>\<^sub>0' a \<star>\<^sub>D G a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a)
                          = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D G\<^sub>0 a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, G\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "(\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D G\<^sub>0 a)
                  = \<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a] \<cdot>\<^sub>D (G.unit a \<star>\<^sub>D G\<^sub>0 a)"
            using a 2 D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<cdot>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]"
            using a D.runit_naturality [of "G.unit a"] by simp
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a])"
            using a 2 D.whisker_left by simp
          finally have "(\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a \<star>\<^sub>D G\<^sub>0 a)
                          = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' a, G\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<r>\<^sub>D[\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
          using a 1 D.whisker_right D.runit_hcomp(1) D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D[\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
          using a D.assoc_naturality [of "\<tau>\<^sub>0' a" "\<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a]" "\<tau>\<^sub>0' a"] D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a])) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D[\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
          using a 2 D.whisker_left D.lunit_hcomp(4) D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<r>\<^sub>D[\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "(\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a])
                  = \<tau>\<^sub>0' a \<star>\<^sub>D (G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a]"
            using a 2 D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a] \<cdot>\<^sub>D \<epsilon> a"
            using a D.lunit'_naturality [of "\<epsilon> a"] by simp
          also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<epsilon> a)"
            using a 2 D.whisker_left by simp
          finally have "(\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a])
                          = (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<epsilon> a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<eta> a \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<r>\<^sub>D[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          have "(\<r>\<^sub>D[\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<r>\<^sub>D[\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<cdot>\<^sub>D (\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a 1 D.whisker_right by simp
          also have "... = \<eta> a \<cdot>\<^sub>D \<r>\<^sub>D[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a"
            using a D.runit_naturality [of "\<eta> a"] by simp
          also have "... = (\<eta> a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (\<r>\<^sub>D[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a 1 D.whisker_right by simp
          finally have "(\<r>\<^sub>D[\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D ((\<eta> a \<star>\<^sub>D F\<^sub>0 a) \<star>\<^sub>D \<tau>\<^sub>0' a)
                          = (\<eta> a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (\<r>\<^sub>D[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D
                         \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<l>\<^sub>D[\<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<r>\<^sub>D[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a)"
        proof -
          interpret adjoint_equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                      \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
            using a chosen_adjoint_equivalence by simp
          have "(\<tau>\<^sub>0' a \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' a, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (\<eta> a \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0' a]"
            using triangle_right by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0' a]"
        proof -
          have "\<l>\<^sub>D[\<tau>\<^sub>0' a] \<cdot>\<^sub>D (\<r>\<^sub>D[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a) = \<l>\<^sub>D[\<tau>\<^sub>0' a]"
          proof -
            have "D.seq \<r>\<^sub>D[F\<^sub>0 a] \<l>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 a]"
              using a 1 by auto
            thus ?thesis
              using a D.unitor_coincidence [of "F\<^sub>0 a"] D.comp_arr_dom D.whisker_right
              by (metis D.comp_arr_inv' D.iso_runit D.lunit_simps(1,4)
                  D.objE D.runit_simps(5) F.map\<^sub>0_simps(1) map\<^sub>0_simps(1,3))
          qed
          moreover have "(\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a]
                           = \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a]"
          proof -
            have "(\<tau>\<^sub>0' a \<star>\<^sub>D \<r>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a] =
                  ((\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D[G\<^sub>0 a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a])) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a]"
              using a D.unitor_coincidence D.comp_assoc by simp
            also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D \<l>\<^sub>D[G\<^sub>0 a] \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G\<^sub>0 a]) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a]"
              using a 2 D.whisker_left by simp
            also have "... = (\<tau>\<^sub>0' a \<star>\<^sub>D G\<^sub>0 a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a]"
              using a 2 D.comp_arr_inv' by simp
            also have "... = \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a]"
              using a 2 D.comp_cod_arr by simp
            finally show ?thesis by blast
          qed
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        finally show "(\<tau>\<^sub>0' a \<star>\<^sub>D G.unit a) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' a] \<cdot>\<^sub>D \<l>\<^sub>D[\<tau>\<^sub>0' a]
                         = \<tau>\<^sub>1' a \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D \<tau>\<^sub>0' a)"
          by simp
      qed
      show "\<And>f g. \<lbrakk>C.ide f; C.ide g; src\<^sub>C g = trg\<^sub>C f\<rbrakk> \<Longrightarrow>
                     (\<tau>\<^sub>0' (trg\<^sub>C g) \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                     \<a>\<^sub>D[\<tau>\<^sub>0' (trg\<^sub>C g), G g, G f] \<cdot>\<^sub>D
                     (\<tau>\<^sub>1' g \<star>\<^sub>D G f) \<cdot>\<^sub>D
                     D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0' (src\<^sub>C g), G f] \<cdot>\<^sub>D
                     (F g \<star>\<^sub>D \<tau>\<^sub>1' f) \<cdot>\<^sub>D
                     \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' (src\<^sub>C f)]
                       = \<tau>\<^sub>1' (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' (src\<^sub>C f))"
      proof -
        fix f g
        assume f: "C.ide f" and g: "C.ide g" and fg: "src\<^sub>C g = trg\<^sub>C f"
        let ?a = "src\<^sub>C f"
        let ?b = "trg\<^sub>C f"
        let ?c = "trg\<^sub>C g"
        (*
         * TODO: The following are extremely problematic.
         * I don't think all the cases are used, but they don't get discovered by auto
         * and sledgehammer doesn't find them, either.  Note that the same issue occurred
         * for the previous subgoal, where I needed D.ide (F\<^sub>0 a) and D.ide (G\<^sub>0 a).
         *)
        have *: "D.ide (G\<^sub>0 ?a) \<and> D.ide (G\<^sub>0 ?b) \<and> D.ide (G\<^sub>0 ?b) \<and> D.ide (G\<^sub>0 ?c)"
          using f g C.ideD(1) G.map\<^sub>0_simps(1) by blast
        have **: "D.ide (F\<^sub>0 ?a) \<and> D.ide (F\<^sub>0 ?b) \<and> D.ide (F\<^sub>0 ?b) \<and> D.ide (F\<^sub>0 ?c)"
          using f g C.ideD(1) F.map\<^sub>0_simps(1) by blast
        have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
              \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
              (\<tau>\<^sub>1' g \<star>\<^sub>D G f) \<cdot>\<^sub>D
              D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0' (src\<^sub>C g), G f] \<cdot>\<^sub>D
              (F g \<star>\<^sub>D \<tau>\<^sub>1' f) \<cdot>\<^sub>D
              \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]
                        = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                          \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                          ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D
                           \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                           (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b)
                              \<star>\<^sub>D G f) \<cdot>\<^sub>D
                           D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                           (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                                   (\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                                   (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                   \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                   ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                                   (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                                   ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                                   (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
          unfolding map\<^sub>1_def
          using f g fg D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F g, \<tau>\<^sub>0' ?b, G f]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b)
                   \<star>\<^sub>D G f
                  = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f)"
          proof -
            have 1: "D.arr ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D
                            \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b))"
              using f g fg \<tau>.iso_map\<^sub>1_ide by auto
            thus ?thesis
              using f g fg D.whisker_right [of "G f"]
              by (metis D.seqE G.preserves_ide)
          qed
          moreover have "F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                                (\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                                (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                                (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                                ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                                (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                           = (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                             (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                             (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          proof -
            have 1: "D.arr ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a))"
              using f g fg \<tau>.iso_map\<^sub>1_ide map\<^sub>1_def map\<^sub>1_simps(1) by presburger
            thus ?thesis
              using f g fg D.whisker_left [of "F g"]
              by (metis D.seqE F.preserves_ide)
          qed
          ultimately show ?thesis
            using f g fg D.comp_assoc by simp
        qed
        (*
         * Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] and \<l>\<^sub>D\<^sup>-\<^sup>1[F f] to the bottom, followed by \<eta> ?c and D.inv (\<tau>\<^sub>1 g).
         * Move \<epsilon> ?b down across D.inv (\<tau>\<^sub>1 g) to meet \<eta> ?b, where they can be canceled.
         *)
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F g, \<tau>\<^sub>0' ?b, G f]
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f)"
            using f g fg D.assoc'_naturality [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "\<tau>\<^sub>0' ?b" "G f"] by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f" "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]"]
            by simp
          also have "... = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                           (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a"]
            by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])
                          = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"]
            by simp
          also have "... = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                             (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                          = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (F g \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                          = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                          = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
         proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "(\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "(\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (F g \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (F g \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (F g \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D\<^sup>-\<^sup>1[F g] down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (F g \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F g" "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         ((((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f]
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                    ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f)"
            using f g fg D.assoc'_naturality [of "\<eta> ?c \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b" "G f"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f) \<cdot>\<^sub>D ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])
                  = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f" "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<eta> ?c \<star>\<^sub>D F g"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]" "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a"]
            by simp
          finally have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                  = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<eta> ?c \<star>\<^sub>D F g"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a" "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                  = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<eta> ?c \<star>\<^sub>D F g"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
                                    "\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                  = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<eta> ?c \<star>\<^sub>D F g"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<eta> ?c \<star>\<^sub>D F g"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g"
                                    "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<eta> ?c \<star>\<^sub>D F g"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?c down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g"
                                    "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f \<star>\<^sub>D G\<^sub>0 ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f] \<cdot>\<^sub>D
              (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<r>\<^sub>D[G f])
                 = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                   \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f \<star>\<^sub>D G\<^sub>0 ?a]"
            using f g fg D.assoc'_naturality [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b" "\<r>\<^sub>D[G f]"]
            by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f \<star>\<^sub>D G\<^sub>0 ?a] \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                 = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                   \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
           using f g fg D.assoc'_naturality [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b" "G f \<star>\<^sub>D \<epsilon> ?a"]
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                 = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                 \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
           using f g fg
                 D.assoc'_naturality [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                   ((\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"
           using f g fg \<tau>.iso_map\<^sub>1_ide
                 D.assoc_naturality [of "\<tau>\<^sub>0' ?b" "D.inv (\<tau>\<^sub>1 f)" "\<tau>\<^sub>0' ?a"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
         finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                       (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "\<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                   \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.assoc'_naturality
                   [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<tau>\<^sub>0' ?b" "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
               ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                 = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f" "\<r>\<^sub>D[G f]"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                          ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<r>\<^sub>D[G f]" "G f \<star>\<^sub>D G\<^sub>0 ?a"]
           by simp
         finally have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                       ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                           ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
               ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                 = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f \<star>\<^sub>D G\<^sub>0 ?a" "G f \<star>\<^sub>D \<epsilon> ?a"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                          ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f \<star>\<^sub>D \<epsilon> ?a" "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                       ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                           ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                 = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                          ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
                                   "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                 = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f" "\<r>\<^sub>D[G f]"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                          (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<r>\<^sub>D[G f]" "G f \<star>\<^sub>D G\<^sub>0 ?a"]
           by simp
         finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                       (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                 = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f \<star>\<^sub>D G\<^sub>0 ?a" "G f \<star>\<^sub>D \<epsilon> ?a"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                          (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f \<star>\<^sub>D \<epsilon> ?a" "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                       (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                 = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                          (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]" "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                   "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                   (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.assoc'_naturality [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]" "\<tau>\<^sub>0' ?b"
                                         "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])
                 = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g"
                                   "\<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"]
           by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                          (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g" "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"
                                   "(\<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])
                         = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g"
                                   "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g" "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                   ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide
                 D.assoc'_naturality
                   [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)" "\<tau>\<^sub>0' ?b" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)" "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g"
                                   "\<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"]
           by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                          ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b" "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"
                                   "(\<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<tau>\<^sub>0' ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])
                         = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move D.inv (\<tau>\<^sub>1 g) down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)" "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g"
                                   "(\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b" "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)"
                                   "\<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move \<eta> ?b up. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<cdot>\<^sub>D (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D
                   (((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]" "\<eta> ?c \<star>\<^sub>D F g"
                                   "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                   "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<cdot>\<^sub>D (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.comp_cod_arr by simp
         also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<cdot>\<^sub>D (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D
                          ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.comp_arr_dom by simp
         also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          using f g fg ** D.interchange by auto
         finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move \<eta> ?b up. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_cod_arr
                 D.interchange
                   [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)" "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]"
                       "((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom
                 D.interchange
                   [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)" "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]"
                       "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D ((\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move \<epsilon> ?b down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
               (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f"
           using f g fg D.whisker_right by simp
         also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
                          (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f"
           using f g fg D.pentagon
                 D.invert_side_of_triangle(2)
                   [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                        "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                        "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b"]
                 D.comp_assoc
           by simp
         also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                          (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                          ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f)"
           using f g fg D.whisker_right by simp
         finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                       (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)
                         = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                           ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move \<epsilon> ?b down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f"
           using f g fg D.whisker_right [of "G f"] by simp
         also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f"
           using f g fg D.assoc_naturality [of "\<tau>\<^sub>0' ?c" "G g" "\<epsilon> ?b"] by simp
         also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f)"
           using f g fg * D.whisker_right [of "G f"] by simp
         finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                       (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)
                         = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Prepare to move \<epsilon> ?b down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
               (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b)
                 = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
           using f g fg D.pentagon by simp
         hence "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b)"
           using f g fg D.comp_assoc D.invert_side_of_triangle(1) by simp
         hence "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b)
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
           using f g fg D.comp_assoc
                 D.invert_side_of_triangle(2)
                   [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                       "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D
                          \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                       "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b"]
           by simp
         hence "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f"
           using f g fg D.whisker_right by simp
         hence "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f)
                  = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)"
           using f g fg D.whisker_right by simp
        thus ?thesis
          using D.comp_assoc by simp
       qed
       (* Move \<epsilon> ?b down *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
               (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)
                 = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f"
           using f g fg D.whisker_right by simp
         also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f"
           using f g fg D.assoc'_naturality [of "\<tau>\<^sub>0' ?c" "G g" "\<epsilon> ?b"] by simp
         also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f)"
           using f g fg * D.whisker_right by simp
         finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                       (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f)
                         = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* There is a cancellation of associativities here. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f)
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f"
           using f g fg * D.comp_arr_inv' D.whisker_right
           by (metis C.ideD(1) C.obj_trg D.comp_assoc_assoc'(1) D.hcomp_simps(2) D.hseqI'
               D.ideD(1) G.map\<^sub>0_simps(3) G.preserves_ide G.preserves_src G.preserves_trg
               map\<^sub>0_simps(1-2))
         moreover have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f)
                          = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f"
           using f g fg D.comp_cod_arr by simp
         ultimately have "((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                          (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f)) \<cdot>\<^sub>D
                          ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f)
                            = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f"
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move \<r>\<^sub>D[G f] up. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D \<r>\<^sub>D[G f]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f" "\<r>\<^sub>D[G f]"]
            by simp
          also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "\<r>\<^sub>D[G f]" "G f \<star>\<^sub>D G\<^sub>0 ?a"]
            by simp
          finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                          = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            by blast
          thus ?thesis
            using f g fg D.comp_assoc by simp
        qed
        (* Move \<r>\<^sub>D[G f] up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D \<r>\<^sub>D[G f]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f" "\<r>\<^sub>D[G f]"]
            by simp
          also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "\<r>\<^sub>D[G f]" "G f \<star>\<^sub>D G\<^sub>0 ?a"]
            by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                          = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<r>\<^sub>D[G f] up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b" "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f" "\<r>\<^sub>D[G f]"]
            by simp
          also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b" "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b"
                                    "\<r>\<^sub>D[G f]" "G f \<star>\<^sub>D G\<^sub>0 ?a"]
            by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                          = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<epsilon> ?a up. The useful effect is on the associativity part of the term. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f \<star>\<^sub>D G\<^sub>0 ?a" "G f \<star>\<^sub>D \<epsilon> ?a"]
            by simp
          also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "G f \<star>\<^sub>D \<epsilon> ?a" "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                          = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<epsilon> ?a up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f \<star>\<^sub>D G\<^sub>0 ?a" "G f \<star>\<^sub>D \<epsilon> ?a"]
            by simp
          also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "G f \<star>\<^sub>D \<epsilon> ?a" "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                          = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<epsilon> ?a up and \<epsilon> ?b down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b"
                                    "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f \<star>\<^sub>D G\<^sub>0 ?a" "G f \<star>\<^sub>D \<epsilon> ?a"]
            by simp
          also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b"
                                    "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b"
                                    "G f \<star>\<^sub>D \<epsilon> ?a" "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                          = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Prepare to move \<epsilon> ?b down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          proof -
            have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
                  (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b)
                    = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
              using f g fg D.pentagon by simp
            hence "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]
                     = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
                       (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b)"
              using f g fg D.comp_assoc
                    D.invert_side_of_triangle(2)
                      [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                          "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                          "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b"]
              by simp
            hence "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]
                       \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a
                     = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<cdot>\<^sub>D
                       (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b)
                           \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"
              by simp
            thus ?thesis
              using f g fg D.whisker_right by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<epsilon> ?b down. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b]
                        \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.whisker_right by simp
          also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b)
                              \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.assoc_naturality [of "\<tau>\<^sub>0' ?c" "G g" "\<epsilon> ?b"] by simp
          also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg * D.whisker_right by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Prepare to move D.inv (\<tau>\<^sub>1 f) up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                  = ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]" "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                          = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Prepare to move D.inv (\<tau>\<^sub>1 f) up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]" "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Prepare to move D.inv (\<tau>\<^sub>1 f) up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                  = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b"
                                    "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]" "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move D.inv (\<tau>\<^sub>1 f) up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move D.inv (\<tau>\<^sub>1 f) up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b]"
                                    "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move D.inv (\<tau>\<^sub>1 f) up across \<epsilon> ?b. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b"
                                    "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b"
                                    "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<eta> ?b up. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                  = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b" "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)"
                                    "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (*
         * Introduce associativities to align (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) with
         * (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) in the middle.
         *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
          proof -
            have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                    = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                      (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
              using f g fg D.comp_arr_dom by simp
            also have "... = ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                      = \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                         ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]\<rbrace>"
                using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                      D.VV.ide_char D.VV.arr_char
                by simp
              also have "... =
                         \<lbrace>((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>) \<^bold>\<star> (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<rbrace>"
                using f g fg by (intro EV.eval_eqI, auto)
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                      D.VV.ide_char D.VV.arr_char
                by simp
              finally have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                              = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                      = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg
                      D.assoc'_naturality [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g" "\<epsilon> ?b" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by auto
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                      = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"
                using f g fg * D.comp_arr_dom D.comp_cod_arr D.whisker_left
                      D.interchange [of "\<epsilon> ?b" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b)" "(\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                        "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"]
                by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg * D.comp_arr_dom D.comp_cod_arr D.whisker_left
                      D.interchange [of "G\<^sub>0 ?b" "\<epsilon> ?b" "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"
                                        "\<tau>\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by simp
              finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                              = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                      = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D
                          (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg D.whisker_left by simp
              also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D
                                 \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                 ((\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg D.assoc_naturality [of "\<epsilon> ?b" "\<tau>\<^sub>0 ?b" "F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg * D.whisker_left by simp
              finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                              = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            finally show ?thesis by simp
          qed
          moreover
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                  = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"
          proof -
            have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                    = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                      ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
              using f g fg ** D.comp_arr_dom by simp
            also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"

            proof -
              have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                      = \<lbrace>(\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                         ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                         \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                         (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>])\<rbrace>"
                using f g fg ** D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                      D.VV.ide_char D.VV.arr_char
                by simp
              also have "... = \<lbrace>(\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>) \<^bold>\<star> (\<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<rbrace>"
                using f g fg by (intro EV.eval_eqI, auto)
              also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                using f g fg ** D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                      D.VV.ide_char D.VV.arr_char
                by simp
              finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                            (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                              = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                    = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D
                        ((\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"
                using f g fg ** D.comp_arr_dom D.comp_cod_arr
                      D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b" "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b]"
                                        "(\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"]
                by simp
              also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D
                                 \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                 (\<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg ** D.assoc'_naturality [of "\<eta> ?b" "F f" "\<tau>\<^sub>0' ?a"]
                by simp
              also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                               (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg ** D.comp_arr_dom D.comp_cod_arr
                      D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b]" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b"
                                        "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"
                                        "\<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by simp
              finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D (\<eta> ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                              = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"
            proof -
              have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                      = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg D.assoc'_naturality [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g" "\<tau>\<^sub>0 ?b"
                                                     "\<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by force
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                      = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D
                          (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg ** D.whisker_left by auto
              also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D
                                  \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                  ((\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg ** D.assoc_naturality [of "\<tau>\<^sub>0 ?b" "\<eta> ?b" "F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by auto
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg ** D.whisker_left by auto
              finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                              = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            finally show ?thesis by blast
          qed
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        (* Cancel out all the intervening associativities. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"
          proof -
            have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  (\<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b] \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                  ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<tau>\<^sub>0' ?b) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                  (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (\<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                    = \<lbrace>((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       (\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                       ((\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>) \<^bold>\<star> (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                       \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                       (\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                        \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, (\<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>])\<rbrace>"
              using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by simp
            also have "... =
                       \<lbrace>(\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<rbrace>"
              using f g fg by (intro EV.eval_eqI, auto)
            also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"
              using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by simp
            finally show ?thesis
              using D.comp_assoc by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Hooray!  We can finally cancel \<eta> ?b with \<epsilon> ?b using the triangle identity. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 ?b] \<star>\<^sub>D (F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D
                      ((\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                      (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                      ((\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.whisker_left by simp
          also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D
                              (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b] \<cdot>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b)
                                 \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.whisker_right by simp
          also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 ?b] \<star>\<^sub>D (F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          proof -
            interpret adjoint_equivalence_in_bicategory
                         V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 ?b\<close> \<open>\<tau>\<^sub>0' ?b\<close> \<open>\<eta> ?b\<close> \<open>\<epsilon> ?b\<close>
              using f chosen_adjoint_equivalence by simp
            show ?thesis
              using fg triangle_left by simp
          qed
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<epsilon> ?b \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, \<tau>\<^sub>0' ?b, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D \<eta> ?b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 ?b] \<star>\<^sub>D (F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Simplify some more canonical arrows. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 ?b] \<star>\<^sub>D (F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                  = (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          proof -
            have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, G\<^sub>0 ?b, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G\<^sub>0 ?b, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 ?b] \<star>\<^sub>D (F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F\<^sub>0 ?b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                    = \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>G\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>G\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>G\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> \<^bold>\<r>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> (\<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>)) \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>])\<rbrace>"
              using f g fg * ** D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char D.\<ll>_ide_simp D.\<rr>_ide_simp
              by simp
            also have "... = \<lbrace>(\<^bold>\<r>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                              ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<l>\<^bold>[\<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                              \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, (\<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                              (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> (\<^bold>\<langle>F\<^sub>0 ?b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>)\<rbrace>"
              using f g fg by (intro EV.eval_eqI, auto)
            also have "... = (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
              using f g fg * ** D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char D.\<ll>_ide_simp D.\<rr>_ide_simp
              by simp
            finally show ?thesis by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D G f) \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<r>\<^sub>D[G f])
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]" "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b" "G f" "\<r>\<^sub>D[G f]"]
            by simp
          moreover have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                           = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
            using f g fg * D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b]" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b"
                                    "G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
            by simp
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        (*
         * Move \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] and \<l>\<^sub>D[F f] outside, to get rid of
         * G\<^sub>0 ?b and F\<^sub>0 ?b.
         *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.assoc_naturality [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g" "\<tau>\<^sub>0 ?b" "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b" "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b]"
                                     "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b]" "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b"
                                    "F f \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b" "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)"
                                    "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)" "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g"
                                    "F f \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<tau>\<^sub>0 ?b) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                  = \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b" "\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g]"
                                    "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"]
            by simp
          also have "... = (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g]" "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g" "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
                                    "(D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]"]
                  D.whisker_left
            by simp (* 12 sec *)
          finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                          = (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Introduce associativities to achieve (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) and (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)). *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
          proof -
            have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                    = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                      ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
              using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom by simp
            also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                      = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                  \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left D.comp_assoc by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                               (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_inv' by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                               \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_cod_arr by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_inv_arr' by simp
              finally show ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                      = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg \<tau>.iso_map\<^sub>1_ide
                      D.assoc'_naturality [of "\<tau>\<^sub>0' ?c" "G g" "D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by simp
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])
                      = \<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
              also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                        ((G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.assoc_naturality [of "G g" "D.inv (\<tau>\<^sub>1 f)" "\<tau>\<^sub>0' ?a"]
                by simp
              also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                               (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
              finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a])
                              = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            finally show ?thesis by simp
          qed
          moreover have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a
                           = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
          proof -
            have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a
                    = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                      ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
              using f g fg \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom by auto
            also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                      = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                  \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg D.whisker_left D.comp_assoc by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                               (\<tau>\<^sub>0' ?c \<star>\<^sub>D (\<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg D.comp_arr_inv' by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                               \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
                using f g fg D.comp_cod_arr by simp
              also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg D.comp_inv_arr' by simp
              finally show ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g)) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                      = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg \<tau>.iso_map\<^sub>1_ide
                      D.assoc'_naturality [of "\<tau>\<^sub>0' ?c" "D.inv (\<tau>\<^sub>1 g)" "F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                by simp
              thus ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
            proof -
              have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a])
                      = \<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
              also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                        ((D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.assoc_naturality [of "D.inv (\<tau>\<^sub>1 g)" "F f" "\<tau>\<^sub>0' ?a"]
                by simp
              also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                               (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
              finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a])
                              = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                                (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
                by blast
              thus ?thesis
                using D.comp_assoc by simp
            qed
            finally show ?thesis
              by simp
          qed
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        (* Cancel intervening associativities. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                  = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
          proof -
            have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, (\<tau>\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g, \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, \<tau>\<^sub>0 ?b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D \<tau>\<^sub>0 ?b, F f, \<tau>\<^sub>0' ?a])
                    = \<lbrace>(\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, (\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       ((\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G g\<^bold>\<rangle>,\<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                       \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>G g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       (\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>G g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>])\<rbrace>"
              using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by simp
            also have "... = \<lbrace>\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>G g\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<rbrace>"
              using f g fg by (intro EV.eval_eqI, auto)
            also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
              using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by simp
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Apply "respects composition". *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<tau>\<^sub>0' ?c \<star>\<^sub>D ((G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (\<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             ((D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D
                             (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f)
                               \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_right by simp
          also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D
                               \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<cdot>\<^sub>D
                               (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D
                               D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D
                               ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f])
                                  \<star>\<^sub>D \<tau>\<^sub>0' ?a"
          proof -
            have 1: "(\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f)
                       = D.inv ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f]) \<cdot>\<^sub>D
                         \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a]"
            proof -
              have "((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<cdot>\<^sub>D
                    (\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a]
                      = \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a)"
                using f g fg \<tau>.respects_hcomp D.comp_assoc by simp
              hence "((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f]) \<cdot>\<^sub>D
                     (\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f)
                       = \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a]"
                using f g fg D.comp_assoc
                      D.invert_side_of_triangle(2)
                        [of "\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a)"
                            "(\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<cdot>\<^sub>D
                             (\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f)"
                            "\<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a]"]
                by fastforce
              moreover have "D.iso ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f])"
                using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_simp F.cmp_components_are_iso
                      F.FF_def
                by (intro D.isos_compose D.seqI D.hseqI') auto
              moreover have "D.seq (\<tau>\<^sub>1 (g \<star>\<^sub>C f))
                                   ((\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a])"
                using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_simp G.FF_def
                by (intro D.seqI) auto
              ultimately show ?thesis
                using f g fg \<tau>.iso_map\<^sub>1_ide
                      D.invert_side_of_triangle(1)
                        [of "\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a]"
                            "(\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f]"
                            "(\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f)"]
                by simp
            qed
            have "(G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f)
                    = D.inv ((\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f))"
            proof -
              have "D.inv ((\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f))
                      = D.inv (\<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f)) \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 g \<star>\<^sub>D F f)"
              proof -
                have "D.iso ((\<tau>\<^sub>1 g \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f))"
                  using f g fg \<tau>.iso_map\<^sub>1_ide
                  by (intro D.isos_compose) auto
                moreover have "D.iso (\<tau>\<^sub>1 g \<star>\<^sub>D F f)"
                  using f g fg \<tau>.iso_map\<^sub>1_ide by auto
                ultimately show ?thesis
                  using \<tau>.iso_map\<^sub>1_ide D.inv_comp_left by simp
              qed
              also have "... = ((G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f]) \<cdot>\<^sub>D
                               (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f)"
              proof -
                have "D.iso (\<a>\<^sub>D\<^sup>-\<^sup>1[G g, \<tau>\<^sub>0 (src\<^sub>C g), F f] \<cdot>\<^sub>D (G g \<star>\<^sub>D \<tau>\<^sub>1 f))"
                  using f g fg \<tau>.iso_map\<^sub>1_ide
                  by (intro D.isos_compose) auto
                thus ?thesis
                  using f g fg \<tau>.iso_map\<^sub>1_ide D.inv_comp_left by simp
              qed
              finally show ?thesis
                using D.comp_assoc by simp
            qed
            also have "... = D.inv (D.inv ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f]) \<cdot>\<^sub>D
                                    \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D
                                    (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a])"
              using 1 by simp
            also have "... = D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D
                                    \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a]) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f])"
            proof -
              have 2: "D.iso ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f])"
                 using f g fg \<tau>.iso_map\<^sub>1_ide C.VV.arr_char C.VV.dom_simp F.cmp_components_are_iso
                       F.FF_def
                 by (intro D.isos_compose) auto
              moreover have "D.iso (D.inv ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f]) \<cdot>\<^sub>D
                                    \<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a])"
                 using 2 f g fg \<tau>.iso_map\<^sub>1_ide C.VV.arr_char C.VV.dom_simp
                       C.VV.cod_simp F.FF_def G.FF_def D.inv_comp_left
                 by (intro D.isos_compose) auto (* 10 sec *)
              ultimately show ?thesis
                using D.inv_comp_left
                        [of "D.inv ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f])"
                            "\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a]"]
                      D.inv_inv D.iso_inv_iso
                by metis
            qed
            also have "... = \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<cdot>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D
                             D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f])"
            proof -
              have "D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a])
                      = \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<cdot>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D
                        D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f))"
              proof -
                have 2: "D.iso (\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a])"
                   using f g fg \<tau>.iso_map\<^sub>1_ide C.VV.arr_char C.VV.dom_simp
                         C.VV.cod_simp G.FF_def
                   by (intro D.isos_compose D.seqI D.hseqI') auto
                have "D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a])
                        = D.inv ((\<Phi>\<^sub>G (g, f) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G g, G f, \<tau>\<^sub>0 ?a]) \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f))"
                  using 2 f g fg * \<tau>.iso_map\<^sub>1_ide G.cmp_components_are_iso C.VV.arr_char
                        C.VV.dom_simp C.VV.cod_simp G.FF_def D.inv_comp_left
                  by simp
                also have "... = (\<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<cdot>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a)) \<cdot>\<^sub>D
                                 D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f))"
                  using 2 f g fg * \<tau>.iso_map\<^sub>1_ide G.cmp_components_are_iso C.VV.arr_char
                        C.VV.dom_simp C.VV.cod_simp G.FF_def D.inv_comp_left
                  by simp
                also have "... = \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<cdot>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D
                                 D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f))"
                  using D.comp_assoc by simp
                finally show ?thesis
                  using D.comp_assoc by simp
              qed
              thus ?thesis
                using D.comp_assoc by simp
            qed
            finally have "(G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f)
                            = \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<cdot>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D
                              D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<cdot>\<^sub>D (\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f]"
              by blast
            thus ?thesis by simp
          qed
          also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D
                             (\<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             ((D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                             (((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                             (\<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_right
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_simp G.cmp_components_are_iso
                  F.FF_def G.FF_def
            by simp
          also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide D.whisker_left
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_simp G.cmp_components_are_iso
                  F.FF_def G.FF_def
            by simp
          finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, \<tau>\<^sub>0 ?b, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<tau>\<^sub>1 g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move \<l>\<^sub>D[F f] down, where it will cancel. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g" "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]"
                                    "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                  D.whisker_right
            by simp
          also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]" "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g"
                                    "F f \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
                  D.whisker_right
            by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
         thus ?thesis
            using D.comp_assoc by simp
       qed
       (* Move \<l>\<^sub>D[F f] down. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
               ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = (\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g" "\<eta> ?c \<star>\<^sub>D F g"
                                   "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a" "(F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.comp_arr_dom D.comp_cod_arr
                 D.interchange [of "\<eta> ?c \<star>\<^sub>D F g" "F\<^sub>0 ?c \<star>\<^sub>D F g" "F f \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D (F\<^sub>0 ?b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Cancel \<l>\<^sub>D[F f] and \<l>\<^sub>D\<^sup>-\<^sup>1[F f]. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) =
               \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D (\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.comp_cod_arr
                 D.interchange [of "F\<^sub>0 ?c \<star>\<^sub>D F g" "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "\<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a" "\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D[F f] \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           using f g fg D.whisker_right by simp
         also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           using f D.comp_arr_inv' by simp
         finally have "((F\<^sub>0 ?c \<star>\<^sub>D F g) \<star>\<^sub>D \<l>\<^sub>D[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                       (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move \<r>\<^sub>D\<^sup>-\<^sup>1[G g] up, where it will cancel. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
               (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           using f g fg * D.comp_arr_dom
                 D.interchange [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b]" "\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g]"
                                   "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]" "(G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
           by simp
         also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           using f g fg D.runit_hcomp(4) [of "\<tau>\<^sub>0' ?c" "G g"] by simp
         finally have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G\<^sub>0 ?b] \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                       (\<r>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D G g] \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move \<r>\<^sub>D\<^sup>-\<^sup>1[G g] up. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
               ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D (G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           using f g fg D.comp_cod_arr
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b" "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]"
                                   "G f \<star>\<^sub>D \<epsilon> ?a" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
           by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                          ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
           using f g fg D.comp_arr_dom
                 D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]" "\<tau>\<^sub>0' ?c \<star>\<^sub>D G g" "G f \<star>\<^sub>D \<epsilon> ?a"
                                   "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
           by simp
         finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G\<^sub>0 ?b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                       ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])
                         = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Cancel \<r>\<^sub>D\<^sup>-\<^sup>1[G g] and \<r>\<^sub>D[G g]. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f] \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> ?a)"
           using f g fg D.interchange by simp
         also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g] \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f] \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> ?a)"
           using f g fg D.whisker_left by simp
         also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f] \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> ?a)"
           using g D.comp_arr_inv' by simp
         also have "... = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)"
           using f g fg D.whisker_left by simp
         finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g]) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                       ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[G g]) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)
                         = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
               \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, (G f \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                   (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
           using f g fg
                 D.assoc'_naturality [of "\<tau>\<^sub>0' ?c" "G g" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"]
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
               (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
               (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = \<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                            \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                            (\<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg D.whisker_left by simp
         also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                                   \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           using f g fg D.pentagon by simp
         also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                          (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
           using f g fg D.whisker_left by simp
         finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                       (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                       (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        (((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f \<star>\<^sub>D G\<^sub>0 ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f \<star>\<^sub>D G\<^sub>0 ?a] \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a)"
           using f g fg D.assoc'_naturality [of "\<tau>\<^sub>0' ?c" "G g" "G f \<star>\<^sub>D \<epsilon> ?a"]
           by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Move associativity to where it can be canceled. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D
                        \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f \<star>\<^sub>D G\<^sub>0 ?a]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<r>\<^sub>D[G f])"
           using f g fg D.assoc'_naturality [of "\<tau>\<^sub>0' ?c" "G g" "\<r>\<^sub>D[G f]"] by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Cancel associativities. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a])) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c, G g, G f]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<r>\<^sub>D[G f])
                 = (\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<r>\<^sub>D[G f])"
           using f g fg D.comp_arr_inv' D.comp_cod_arr by simp
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Permute associativity to continue forming G g \<star>\<^sub>D G f. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, G\<^sub>0 ?a])) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                 = \<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a]"
           using f g fg D.whisker_left by simp
         also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, G\<^sub>0 ?a] \<cdot>\<^sub>D ((G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a)"
           using f g fg D.assoc_naturality [of "G g" "G f" "\<epsilon> ?a"] by simp
         also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, G\<^sub>0 ?a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a)"
           using f g fg * D.whisker_left by simp
         finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D G g \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                       (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a])
                         = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g, G f, G\<^sub>0 ?a]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a)"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
       qed
       (* Form \<r>\<^sub>D[G g \<star>\<^sub>D G f]. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g \<star>\<^sub>D G f]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
         using f g fg * D.runit_hcomp D.whisker_left D.comp_assoc by simp
       (* Move D.inv (\<Phi>\<^sub>G (g, f)) to the top and cancel with its inverse. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g \<star>\<^sub>D G f]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
       proof -
         have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
               (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                 = \<tau>\<^sub>0' ?c \<star>\<^sub>D
                      \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                      ((D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
           using f g fg G.cmp_components_are_iso D.whisker_left by simp
         also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D
                            (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]"
           using f g fg G.cmp_components_are_iso
                 D.assoc_naturality [of "D.inv (\<Phi>\<^sub>G (g, f))" "\<tau>\<^sub>0 ?a" "\<tau>\<^sub>0' ?a"]
           by simp
         also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                          (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
           using f g fg G.cmp_components_are_iso D.whisker_left by simp
         finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G g \<star>\<^sub>D G f, \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                       (\<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                         = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a])"
           by blast
         thus ?thesis
           using D.comp_assoc by simp
        qed
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g \<star>\<^sub>D G f]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D G\<^sub>0 ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<tau>\<^sub>0' ?c \<star>\<^sub>D ((G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg G.cmp_components_are_iso D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<epsilon> ?a)"
            using f g fg * D.comp_arr_dom D.comp_cod_arr
                   D.interchange [of "G g \<star>\<^sub>D G f" "D.inv (\<Phi>\<^sub>G (g, f))" "\<epsilon> ?a" "\<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a"]
            by simp
          also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D (G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a)"
            using f g fg * D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "D.inv (\<Phi>\<^sub>G (g, f))" "G (g \<star>\<^sub>C f)" "G\<^sub>0 ?a" "\<epsilon> ?a"]
            by simp
          also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a)"
            using f g fg * G.cmp_components_are_iso D.whisker_left by simp
          finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D (G g \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D \<tau>\<^sub>0 ?a \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D G\<^sub>0 ?a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
       also have "... = (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)))) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)])) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g \<star>\<^sub>D G f]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D G\<^sub>0 ?a)
                  = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g \<star>\<^sub>D G f] \<cdot>\<^sub>D (D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D G\<^sub>0 ?a)"
            using f g fg * G.cmp_components_are_iso D.whisker_left by simp
          also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]"
            using f g fg * G.cmp_components_are_iso D.runit_naturality [of "D.inv (\<Phi>\<^sub>G (g, f))"]
            by simp
          also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D  \<r>\<^sub>D[G (g \<star>\<^sub>C f)])"
            using f g fg * G.cmp_components_are_iso D.whisker_left by simp
          finally have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G g \<star>\<^sub>D G f]) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)) \<star>\<^sub>D G\<^sub>0 ?a) =
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D  \<r>\<^sub>D[G (g \<star>\<^sub>C f)])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)))) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)])
                  = \<tau>\<^sub>0' ?c \<star>\<^sub>D (\<Phi>\<^sub>G (g, f) \<cdot>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f))) \<cdot>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]"
            using f g fg D.whisker_left G.cmp_components_are_iso
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
            by simp
          also have "... = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]"
            using f g fg G.cmp_components_are_iso D.comp_arr_inv' D.comp_cod_arr by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<Phi>\<^sub>G (g, f)))) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)])
                          = \<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Perform similar manipulations on the bottom part. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[F\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          using f g fg D.assoc_naturality [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F g]" "F f" "\<tau>\<^sub>0' ?a"] D.comp_assoc by simp
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D \<a>\<^sub>D[F\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]
                  = \<a>\<^sub>D[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg **
                  D.assoc_naturality [of "\<eta> ?c \<star>\<^sub>D F g" "F f" "\<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                \<a>\<^sub>D[(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg D.assoc_naturality [of "\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g]" "F f" "\<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Replace \<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f by \<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)]. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[trg\<^sub>D (F g), F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                   = \<a>\<^sub>D\<^sup>-\<^sup>1[trg\<^sub>D (F g), F g, F f] \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.lunit_hcomp(2) [of "F g" "F f"] by simp
          also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[trg\<^sub>D (F g), F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg ** D.whisker_right [of "\<tau>\<^sub>0' ?a"] by simp
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a
                          = (\<a>\<^sub>D\<^sup>-\<^sup>1[trg\<^sub>D (F g), F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Move the associativity up to the big block of associativities. *)
       also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                        ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<a>\<^sub>D\<^sup>-\<^sup>1[trg\<^sub>D (F g), F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = ((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[trg\<^sub>D (F g), F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg ** D.whisker_right by simp
          also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c, F g, F f] \<cdot>\<^sub>D (\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg ** D.assoc'_naturality [of "\<eta> ?c" "F g" "F f"] by simp
          also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg ** D.whisker_right by simp    
          finally have "(((\<eta> ?c \<star>\<^sub>D F g) \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D\<^sup>-\<^sup>1[trg\<^sub>D (F g), F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Simplify the block of associativities. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          proof -
            have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                  (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f \<star>\<^sub>D \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D F g, F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                  ((\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g] \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                  (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c, F g, F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                    = \<lbrace>(\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle>, \<^bold>\<langle>F g\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                       (\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F g\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F g\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F g\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                       ((\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle>, \<^bold>\<langle>F g\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>) \<^bold>\<cdot>
                       (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle>, \<^bold>\<langle>F g\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>)\<rbrace>"
              using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by simp
            also have "... = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>,  \<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                              (\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' ?c\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 ?c\<^bold>\<rangle>, \<^bold>\<langle>F g\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' ?a\<^bold>\<rangle>)\<rbrace>"
              using f g fg by (intro EV.eval_eqI, auto)
            also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                             (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
              using f g fg D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by simp
            finally show ?thesis by simp
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* Permute \<Phi>\<^sub>F (g, f) to the bottom. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F (g \<star>\<^sub>C f), \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D ((\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F g \<star>\<^sub>D F f, \<tau>\<^sub>0' ?a]
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F (g \<star>\<^sub>C f), \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def
                  D.assoc_naturality [of "\<tau>\<^sub>0' ?c" "\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)" "\<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F (g \<star>\<^sub>C f), \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D (\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f))) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def
                  D.whisker_right
            by simp
          also have "... = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def
                  D.assoc_naturality [of "\<tau>\<^sub>0' ?c" "\<tau>\<^sub>0 ?c" "\<Phi>\<^sub>F (g, f)"]
            by simp
          also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                           (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def
                  D.whisker_right
            by simp
          finally have "((\<tau>\<^sub>0' ?c \<star>\<^sub>D (\<tau>\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f))) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                            (((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F (g \<star>\<^sub>C f), \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((F\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = ((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D (\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def D.whisker_right
            by simp
          also have "... = (\<eta> ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def
                  D.interchange [of "\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c" "\<eta> ?c" "\<Phi>\<^sub>F (g, f)" "F g \<star>\<^sub>D F f"]
            by simp
          also have "... = (\<eta> ?c \<star>\<^sub>D F (g \<star>\<^sub>C f)) \<cdot>\<^sub>D (F\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg D.comp_arr_dom D.comp_cod_arr
                  C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def
                  D.interchange [of "\<eta> ?c" "F\<^sub>0 ?c" "F (g \<star>\<^sub>C f)" "\<Phi>\<^sub>F (g, f)"]
            by simp
          also have "... = ((\<eta> ?c \<star>\<^sub>D F (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((F\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg ** C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def D.whisker_right
            by simp
          finally have "(((\<tau>\<^sub>0' ?c \<star>\<^sub>D \<tau>\<^sub>0 ?c) \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                        ((\<eta> ?c \<star>\<^sub>D F g \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = ((\<eta> ?c \<star>\<^sub>D F (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D ((F\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F (g \<star>\<^sub>C f), \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "((F\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                  = (F\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg ** C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def D.whisker_right
            by simp
          also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<cdot>\<^sub>D \<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' ?a"
            using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def
                  D.lunit'_naturality [of "\<Phi>\<^sub>F (g, f)"]
            by simp
          also have "... = (\<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg C.VV.arr_char C.VV.dom_simp C.VV.cod_char F.FF_def D.whisker_right
            by simp
          finally have "((F\<^sub>0 ?c \<star>\<^sub>D \<Phi>\<^sub>F (g, f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F g \<star>\<^sub>D F f] \<star>\<^sub>D \<tau>\<^sub>0' ?a)
                          = (\<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        (* One more associativity to move to its final position. *)
        also have "... = (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<r>\<^sub>D[G (g \<star>\<^sub>C f)]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D G (g \<star>\<^sub>C f) \<star>\<^sub>D \<epsilon> ?a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' ?c \<star>\<^sub>D \<a>\<^sub>D[G (g \<star>\<^sub>C f), \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G (g \<star>\<^sub>C f) \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f))) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c, F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         ((\<eta> ?c \<star>\<^sub>D F (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F (g \<star>\<^sub>C f)] \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                         (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
        proof -
          have "(\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f)) \<star>\<^sub>D \<tau>\<^sub>0' ?a) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' ?c, \<tau>\<^sub>0 ?c \<star>\<^sub>D F (g \<star>\<^sub>C f), \<tau>\<^sub>0' ?a]
                  = \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G (g \<star>\<^sub>C f) \<star>\<^sub>D \<tau>\<^sub>0 ?a, \<tau>\<^sub>0' ?a] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' ?c \<star>\<^sub>D D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f))) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
            using f g fg \<tau>.iso_map\<^sub>1_ide
                  D.assoc_naturality [of "\<tau>\<^sub>0' ?c" "D.inv (\<tau>\<^sub>1 (g \<star>\<^sub>C f))" "\<tau>\<^sub>0' ?a"]
            by simp
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<tau>\<^sub>1' (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          unfolding map\<^sub>1_def
          using f g fg D.comp_assoc by simp
        finally show "(\<tau>\<^sub>0' ?c \<star>\<^sub>D \<Phi>\<^sub>G (g, f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' ?c, G g, G f] \<cdot>\<^sub>D (\<tau>\<^sub>1' g \<star>\<^sub>D G f) \<cdot>\<^sub>D
                      D.inv \<a>\<^sub>D[F g, \<tau>\<^sub>0' (src\<^sub>C g), G f] \<cdot>\<^sub>D (F g \<star>\<^sub>D \<tau>\<^sub>1' f) \<cdot>\<^sub>D \<a>\<^sub>D[F g, F f, \<tau>\<^sub>0' ?a]
                        = \<tau>\<^sub>1' (g \<star>\<^sub>C f) \<cdot>\<^sub>D (\<Phi>\<^sub>F (g, f) \<star>\<^sub>D \<tau>\<^sub>0' ?a)"
          by blast
      qed
    qed

    lemma is_pseudonatural_equivalence:
    shows "pseudonatural_equivalence
             V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G F \<Phi>\<^sub>F \<tau>\<^sub>0' \<tau>\<^sub>1'"
      ..

  end

  subsection "Pseudonaturally Equivalent Pseudofunctors"

  text \<open>
    Pseudofunctors \<open>F\<close> and \<open>G\<close> are \emph{pseudonaturally equivalent} if there is a
    pseudonatural equivalence between them.
  \<close>

  definition pseudonaturally_equivalent
  where "pseudonaturally_equivalent
           V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<equiv>
         \<exists>\<tau>\<^sub>0 \<tau>\<^sub>1. pseudonatural_equivalence
                  V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1"

  lemma pseudonaturally_equivalent_reflexive:
  assumes "pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F"
  shows "pseudonaturally_equivalent
           V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F F \<Phi>\<^sub>F"
  proof -
    interpret F: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F
      using assms by simp
    interpret identity_pseudonatural_transformation
                V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F
      ..
    show ?thesis
      using pseudonatural_equivalence_axioms pseudonaturally_equivalent_def by blast
  qed

  lemma pseudonaturally_equivalent_symmetric:
  assumes "pseudonaturally_equivalent
             V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G"
  shows "pseudonaturally_equivalent
             V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G F \<Phi>\<^sub>F"
  proof -
    obtain \<tau>\<^sub>0 \<tau>\<^sub>1 where \<tau>: "pseudonatural_equivalence
                           V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1"
      using assms pseudonaturally_equivalent_def by blast
    interpret \<tau>: pseudonatural_equivalence
                    V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      using \<tau> by simp
    interpret \<sigma>: converse_pseudonatural_equivalence
                    V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      ..
    show ?thesis
      using \<sigma>.is_pseudonatural_equivalence pseudonaturally_equivalent_def by blast
  qed

  lemma pseudonaturally_equivalent_transitive:
  assumes "pseudonaturally_equivalent
             V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G"
  and "pseudonaturally_equivalent
         V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G H \<Phi>\<^sub>H"
  shows "pseudonaturally_equivalent
           V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F H \<Phi>\<^sub>H"
  proof -
    obtain \<tau>\<^sub>0 \<tau>\<^sub>1 where \<tau>: "pseudonatural_equivalence
                            V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1"
      using assms pseudonaturally_equivalent_def by blast
    interpret \<tau>: pseudonatural_equivalence
                   V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      using \<tau> by simp
    obtain \<sigma>\<^sub>0 \<sigma>\<^sub>1 where \<sigma>: "pseudonatural_equivalence
                             V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G H \<Phi>\<^sub>H \<sigma>\<^sub>0 \<sigma>\<^sub>1"
      using assms pseudonaturally_equivalent_def by blast
    interpret \<sigma>: pseudonatural_equivalence
                   V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G H \<Phi>\<^sub>H \<sigma>\<^sub>0 \<sigma>\<^sub>1
      using \<sigma> by simp
    interpret \<sigma>\<tau>: composite_pseudonatural_equivalence V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                    V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G H \<Phi>\<^sub>H \<tau>\<^sub>0 \<tau>\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1
      ..
    show ?thesis
      using \<sigma>\<tau>.pseudonatural_equivalence_axioms pseudonaturally_equivalent_def by blast
  qed

  text \<open>
    If \<open>\<tau>\<close> is a pseudonatural equivalence from pseudofunctor \<open>F\<close> to pseudofunctor \<open>G\<close>
    and \<open>\<sigma>\<close> is the converse equivalence, then \<open>F\<close> is locally naturally isomorphic to
    the functor that takes a 2-cell \<open>\<mu>\<close> of \<open>C\<close> to \<open>\<sigma>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)\<close>
    and symmetrically for \<open>G\<close>.  Here we just establish the naturality property and
    and that each 1-cell \<open>\<guillemotleft>g : a \<rightarrow>\<^sub>C a'\<guillemotright>\<close> is isomorphic to \<open>\<tau>\<^sub>0 a' \<star>\<^sub>D (\<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a\<close>.
    We ultimately need these results to prove that a pseudofunctor extends to an
    equivalence of bicategories if and only if it is an equivalence pseudofunctor.
  \<close>

  context pseudonatural_equivalence
  begin

    interpretation \<sigma>: converse_pseudonatural_equivalence
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      ..

    abbreviation (input) \<sigma>\<^sub>0
    where "\<sigma>\<^sub>0 \<equiv> \<sigma>.map\<^sub>0"

    definition \<phi>
    where "\<phi> f \<equiv> \<a>\<^sub>D[\<tau>\<^sub>0 (trg\<^sub>C f), F f, \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                 (\<tau>\<^sub>1 f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)) \<cdot>\<^sub>D
                 \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 (src\<^sub>C f), \<sigma>\<^sub>0 (src\<^sub>C f)] \<cdot>\<^sub>D
                 (G f \<star>\<^sub>D D.inv (\<sigma>.\<epsilon> (src\<^sub>C f))) \<cdot>\<^sub>D
                 \<r>\<^sub>D\<^sup>-\<^sup>1[G f]"

    lemma \<phi>_in_hom [intro]:
    assumes "C.ide f"
    shows "\<guillemotleft>\<phi> f : G f \<Rightarrow>\<^sub>D \<tau>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D F f \<star>\<^sub>D \<sigma>\<^sub>0 (src\<^sub>C f)\<guillemotright>"
      unfolding \<phi>_def
      using assms by (intro D.comp_in_homI' D.hseqI') auto

    lemma iso_\<phi>:
    assumes "C.ide f"
    shows "D.iso (\<phi> f)"
      unfolding \<phi>_def
      using assms iso_map\<^sub>1_ide
      by (intro D.isos_compose) auto

    definition \<psi>
    where "\<psi> f \<equiv> (\<sigma>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<sigma>\<^sub>0 (trg\<^sub>C f), \<tau>\<^sub>0 (trg\<^sub>C f), F f] \<cdot>\<^sub>D
                  (\<sigma>.\<eta> (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                  \<l>\<^sub>D\<^sup>-\<^sup>1[F f]"

    lemma \<psi>_in_hom [intro]:
    assumes "C.ide f"
    shows "\<guillemotleft>\<psi> f : F f \<Rightarrow>\<^sub>D \<sigma>\<^sub>0 (trg\<^sub>C f) \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)\<guillemotright>"
      unfolding \<psi>_def
      using assms iso_map\<^sub>1_ide
      by (intro D.comp_in_homI' D.hseqI') auto

    lemma iso_\<psi>:
    assumes "C.ide f"
    shows "D.iso (\<psi> f)"
      unfolding \<psi>_def
      using assms iso_map\<^sub>1_ide
      by (intro D.isos_compose) auto

    lemma \<psi>_naturality:
    assumes "C.arr \<mu>"
    shows "(\<sigma>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D \<psi> (C.dom \<mu>) = \<psi> (C.cod \<mu>) \<cdot>\<^sub>D F \<mu>"
    and "D.inv (\<psi> (C.cod \<mu>)) \<cdot>\<^sub>D (\<sigma>\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D \<psi> (C.dom \<mu>) = F \<mu>"
    proof -
      let ?a = "src\<^sub>C \<mu>" and ?a' = "trg\<^sub>C \<mu>"
      let ?f = "C.dom \<mu>" and ?f' = "C.cod \<mu>"
      have "(\<sigma>\<^sub>0 ?a' \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<psi> (C.dom \<mu>)
              = ((\<sigma>\<^sub>0 ?a' \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D
                (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f))) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<sigma>\<^sub>0 ?a', \<tau>\<^sub>0 ?a', F ?f] \<cdot>\<^sub>D
                (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f) \<cdot>\<^sub>D
                \<l>\<^sub>D\<^sup>-\<^sup>1[F ?f]"
        unfolding \<psi>_def       
        using assms D.comp_assoc by simp
      also have "... = (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f')) \<cdot>\<^sub>D
                       ((\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D
                       \<a>\<^sub>D[\<sigma>\<^sub>0 ?a', \<tau>\<^sub>0 ?a', F ?f]) \<cdot>\<^sub>D
                       (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f) \<cdot>\<^sub>D
                       \<l>\<^sub>D\<^sup>-\<^sup>1[F ?f]"            
      proof -
        have "(\<sigma>\<^sub>0 ?a' \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f))
                = \<sigma>\<^sub>0 ?a' \<star>\<^sub>D (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)"
          using assms D.whisker_left iso_map\<^sub>1_ide by simp
        also have "... = \<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f') \<cdot>\<^sub>D (\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>)"
          using assms naturality iso_map\<^sub>1_ide
                D.invert_opposite_sides_of_square
                   [of "\<tau>\<^sub>1 ?f'" "G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a" "\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>" "\<tau>\<^sub>1 ?f"]
          by simp
        also have "... = (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f')) \<cdot>\<^sub>D (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>)"
          using assms D.whisker_left iso_map\<^sub>1_ide by simp
        finally have "(\<sigma>\<^sub>0 ?a' \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f))
                        = (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f')) \<cdot>\<^sub>D (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>)"
          by blast
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f')) \<cdot>\<^sub>D
                       \<a>\<^sub>D[\<sigma>\<^sub>0 ?a', \<tau>\<^sub>0 ?a', F ?f'] \<cdot>\<^sub>D
                       (((\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a') \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D
                       (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f)) \<cdot>\<^sub>D
                       \<l>\<^sub>D\<^sup>-\<^sup>1[F ?f]"            
      proof -
        have "(\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D \<a>\<^sub>D[\<sigma>\<^sub>0 ?a', \<tau>\<^sub>0 ?a', F ?f]
                = \<a>\<^sub>D[\<sigma>\<^sub>0 ?a', \<tau>\<^sub>0 ?a', F ?f'] \<cdot>\<^sub>D ((\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a') \<star>\<^sub>D F \<mu>)"
          using assms D.assoc_naturality [of "\<sigma>\<^sub>0 ?a'" "\<tau>\<^sub>0 ?a'" "F \<mu>"] by simp
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D D.inv (\<tau>\<^sub>1 ?f')) \<cdot>\<^sub>D
                       \<a>\<^sub>D[\<sigma>\<^sub>0 ?a', \<tau>\<^sub>0 ?a', F ?f'] \<cdot>\<^sub>D
                       (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f') \<cdot>\<^sub>D
                       (F.map\<^sub>0 ?a' \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D
                       \<l>\<^sub>D\<^sup>-\<^sup>1[F ?f]"            
      proof -
        have "((\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a') \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f)
                = (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a') \<cdot>\<^sub>D \<sigma>.\<eta> ?a' \<star>\<^sub>D F \<mu> \<cdot>\<^sub>D F ?f"
          using assms D.interchange [of "\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a'" "\<sigma>.\<eta> ?a'" "F \<mu>" "F ?f"]
          by simp
        also have "... = \<sigma>.\<eta> ?a' \<cdot>\<^sub>D F.map\<^sub>0 ?a' \<star>\<^sub>D F ?f' \<cdot>\<^sub>D F \<mu>"
          using assms D.comp_arr_dom D.comp_cod_arr by simp
        also have "... = (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f') \<cdot>\<^sub>D (F.map\<^sub>0 ?a' \<star>\<^sub>D F \<mu>)"
          using assms D.interchange [of "\<sigma>.\<eta> ?a'" "F.map\<^sub>0 ?a'" "F ?f'" "F \<mu>"]
                \<sigma>.unit_in_hom [of ?a']
          by fastforce
        finally have "((\<sigma>\<^sub>0 ?a' \<star>\<^sub>D \<tau>\<^sub>0 ?a') \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f)
                        = (\<sigma>.\<eta> ?a' \<star>\<^sub>D F ?f') \<cdot>\<^sub>D (F.map\<^sub>0 ?a' \<star>\<^sub>D F \<mu>)"
          by blast
        thus ?thesis
          using D.comp_assoc by simp
      qed
      also have "... = \<psi> ?f' \<cdot>\<^sub>D F \<mu>"            
      proof -
        have "(F.map\<^sub>0 ?a' \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F ?f] = \<l>\<^sub>D\<^sup>-\<^sup>1[F ?f'] \<cdot>\<^sub>D F \<mu>"
          using assms D.lunit'_naturality [of "F \<mu>"] by simp
        thus ?thesis
        unfolding \<psi>_def       
          using assms D.comp_assoc by simp
      qed
      finally show "(\<sigma>\<^sub>0 ?a' \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<psi> (C.dom \<mu>) = \<psi> ?f' \<cdot>\<^sub>D F \<mu>"
        by blast
      thus "D.inv (\<psi> ?f') \<cdot>\<^sub>D (\<sigma>\<^sub>0 ?a' \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<psi> (C.dom \<mu>) = F \<mu>"
        using assms \<psi>_in_hom iso_\<psi>
        by (metis C.ide_cod D.in_homE D.invert_side_of_triangle(1) D.seqI
            F.preserves_arr F.preserves_cod)
    qed

    lemma isomorphic_expansion:
    assumes "C.obj a" and "C.obj a'" and "\<guillemotleft>g : G.map\<^sub>0 a \<rightarrow>\<^sub>D G.map\<^sub>0 a'\<guillemotright>" and "D.ide g"
    shows "D.isomorphic (\<tau>\<^sub>0 a' \<star>\<^sub>D (\<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a) g"
    proof -
      let ?g' = "\<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<tau>\<^sub>0 a"
      have g': "\<guillemotleft>?g' : F.map\<^sub>0 a \<rightarrow>\<^sub>D F.map\<^sub>0 a'\<guillemotright>"
        using assms ide_map\<^sub>0_obj \<sigma>.map\<^sub>0_simps(3) C.obj_simps
        by (intro D.in_hhomI D.hseqI') auto
      have ide_g': "D.ide ?g'"
        using assms g' \<sigma>.ide_map\<^sub>0_obj ide_map\<^sub>0_obj by blast
      let ?\<psi> = "(\<sigma>\<^sub>0 a' \<star>\<^sub>D \<r>\<^sub>D[g]) \<cdot>\<^sub>D (\<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<sigma>.\<epsilon> a) \<cdot>\<^sub>D
                (\<sigma>\<^sub>0 a' \<star>\<^sub>D \<a>\<^sub>D[g, \<tau>\<^sub>0 a, \<sigma>\<^sub>0 a]) \<cdot>\<^sub>D \<a>\<^sub>D[\<sigma>\<^sub>0 a', g \<star>\<^sub>D \<tau>\<^sub>0 a, \<sigma>\<^sub>0 a]"
      have \<psi>: "\<guillemotleft>?\<psi> : ?g' \<star>\<^sub>D \<sigma>\<^sub>0 a \<Rightarrow>\<^sub>D \<sigma>\<^sub>0 a' \<star>\<^sub>D g\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>\<a>\<^sub>D[\<sigma>\<^sub>0 a', g \<star>\<^sub>D \<tau>\<^sub>0 a, \<sigma>\<^sub>0 a] :
                 (\<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a \<Rightarrow>\<^sub>D \<sigma>\<^sub>0 a' \<star>\<^sub>D (g \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a\<guillemotright>"
          using assms g' by fastforce
        show "\<guillemotleft>\<sigma>\<^sub>0 a' \<star>\<^sub>D \<a>\<^sub>D[g, \<tau>\<^sub>0 a, \<sigma>\<^sub>0 a] :
                 \<sigma>\<^sub>0 a' \<star>\<^sub>D (g \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<sigma>\<^sub>0 a \<Rightarrow>\<^sub>D \<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a\<guillemotright>"
          using assms g' by fastforce
        show "\<guillemotleft>\<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<sigma>.\<epsilon> a :
                 \<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<sigma>\<^sub>0 a \<Rightarrow>\<^sub>D \<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D G.map\<^sub>0 a\<guillemotright>"
          using assms C.obj_simps
          by (intro D.hcomp_in_vhom) auto
        show "\<guillemotleft>\<sigma>\<^sub>0 a' \<star>\<^sub>D \<r>\<^sub>D[g] : \<sigma>\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D G.map\<^sub>0 a \<Rightarrow>\<^sub>D \<sigma>\<^sub>0 a' \<star>\<^sub>D g\<guillemotright>"
          using assms
          apply (intro D.hcomp_in_vhom)
            apply auto
          by fastforce
      qed
      have iso_\<psi>: "D.iso ?\<psi>"
        using assms g' \<psi> ide_g' ide_map\<^sub>0_obj C.obj_simps
        by (intro D.isos_compose) auto
      let ?\<phi> = "\<l>\<^sub>D[g] \<cdot>\<^sub>D (\<sigma>.\<epsilon> a' \<star>\<^sub>D g) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a', \<sigma>\<^sub>0 a', g] \<cdot>\<^sub>D (\<tau>\<^sub>0 a' \<star>\<^sub>D ?\<psi>)"
      have \<phi>: "\<guillemotleft>?\<phi> : \<tau>\<^sub>0 a' \<star>\<^sub>D ?g' \<star>\<^sub>D \<sigma>\<^sub>0 a \<Rightarrow>\<^sub>D g\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>\<tau>\<^sub>0 a' \<star>\<^sub>D ?\<psi> : \<tau>\<^sub>0 a' \<star>\<^sub>D ?g' \<star>\<^sub>D \<sigma>\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0 a' \<star>\<^sub>D \<sigma>\<^sub>0 a' \<star>\<^sub>D g\<guillemotright>"
          using assms g' \<psi> C.obj_simps
          by (intro D.hcomp_in_vhom) auto
        show "\<guillemotleft>\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a', \<sigma>\<^sub>0 a', g] : \<tau>\<^sub>0 a' \<star>\<^sub>D \<sigma>\<^sub>0 a' \<star>\<^sub>D g \<Rightarrow>\<^sub>D (\<tau>\<^sub>0 a' \<star>\<^sub>D \<sigma>\<^sub>0 a') \<star>\<^sub>D g\<guillemotright>"
        proof -
          have "src\<^sub>D (\<tau>\<^sub>0 a') = trg\<^sub>D (\<sigma>\<^sub>0 a')"
            using assms by auto
          moreover have "src\<^sub>D (\<sigma>\<^sub>0 a') = trg\<^sub>D g"
            using assms by auto
          ultimately show ?thesis
            using assms ide_map\<^sub>0_obj \<sigma>.ide_map\<^sub>0_obj by auto
        qed
        show "\<guillemotleft>\<sigma>.\<epsilon> a' \<star>\<^sub>D g : (\<tau>\<^sub>0 a' \<star>\<^sub>D \<sigma>\<^sub>0 a') \<star>\<^sub>D g \<Rightarrow>\<^sub>D G.map\<^sub>0 a' \<star>\<^sub>D g\<guillemotright>"
          using assms by fastforce
        show "\<guillemotleft>\<l>\<^sub>D[g] : G.map\<^sub>0 a' \<star>\<^sub>D g \<Rightarrow>\<^sub>D g\<guillemotright>"
          using assms by auto
      qed
      have iso_\<phi>: "D.iso ?\<phi>"
        using assms g' \<phi> \<psi> iso_\<psi> ide_map\<^sub>0_obj iso_map\<^sub>1_ide \<sigma>.ide_map\<^sub>0_obj
        apply (intro D.isos_compose)
              apply (meson D.arrI D.hseqE D.ide_is_iso D.iso_hcomp D.seqE)
             apply (metis D.hseqE D.in_hhomE D.iso_assoc' D.trg_hcomp F.map\<^sub>0_def map\<^sub>0_simps(2))
        by auto
      show ?thesis
        using \<phi> iso_\<phi> D.isomorphic_def by auto
    qed

  end

  text \<open>
    Here we show that pseudonatural equivalence respects equivalence pseudofunctors,
    in the sense that a pseudofunctor \<open>G\<close>, pseudonaturally equivalent to an
    equivalence pseudofunctor \<open>F\<close>, is itself an equivalence pseudofunctor.
  \<close>

  locale pseudofunctor_pseudonaturally_equivalent_to_equivalence_pseudofunctor =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F +
    pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G +
    \<tau>: pseudonatural_equivalence V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
  for V\<^sub>C :: "'c comp"                   (infixr "\<cdot>\<^sub>C" 55)
  and H\<^sub>C :: "'c comp"                   (infixr "\<star>\<^sub>C" 53)
  and \<a>\<^sub>C :: "'c \<Rightarrow> 'c \<Rightarrow> 'c \<Rightarrow> 'c"       ("\<a>\<^sub>C[_, _, _]")
  and \<i>\<^sub>C :: "'c \<Rightarrow> 'c"                   ("\<i>\<^sub>C[_]")
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and V\<^sub>D :: "'d comp"                   (infixr "\<cdot>\<^sub>D" 55)
  and H\<^sub>D :: "'d comp"                   (infixr "\<star>\<^sub>D" 53)
  and \<a>\<^sub>D :: "'d \<Rightarrow> 'd \<Rightarrow> 'd \<Rightarrow> 'd"       ("\<a>\<^sub>D[_, _, _]")
  and \<i>\<^sub>D :: "'d \<Rightarrow> 'd"                   ("\<i>\<^sub>D[_]")
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>F :: "'c * 'c \<Rightarrow> 'd"
  and G :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>G :: "'c * 'c \<Rightarrow> 'd"
  and \<tau>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<tau>\<^sub>1 :: "'c \<Rightarrow> 'd"
  begin

    interpretation \<sigma>': converse_pseudonatural_equivalence
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      ..

    sublocale G: equivalence_pseudofunctor
                   V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
    proof
      show "\<And>\<mu> \<mu>'. \<lbrakk>C.par \<mu> \<mu>'; G \<mu> = G \<mu>'\<rbrakk> \<Longrightarrow> \<mu> = \<mu>'"
      proof -
        fix \<mu> \<mu>'
        assume par: "C.par \<mu> \<mu>'" and eq: "G \<mu> = G \<mu>'"
        let ?a = "src\<^sub>C \<mu>" and ?a' = "trg\<^sub>C \<mu>"
        let ?f = "C.dom \<mu>" and ?f' = "C.cod \<mu>"
        have "\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu> = (\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1 ?f \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)"
          using par \<tau>.ide_map\<^sub>0_obj \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_arr_inv'
                \<tau>.map\<^sub>1_in_hom [of \<mu>]
          by (metis C.dom_trg C.ide_dom C.obj_trg C.trg.preserves_dom D.whisker_left
              F.is_natural_2 F.naturality F.preserves_arr \<tau>.map\<^sub>1_simps(5))
        also have "... = ((\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>) \<cdot>\<^sub>D \<tau>\<^sub>1 ?f) \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)"
          using D.comp_assoc by simp
        also have "... = ((\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>') \<cdot>\<^sub>D \<tau>\<^sub>1 ?f) \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)"
          using eq par \<tau>.naturality [of \<mu>] \<tau>.naturality [of \<mu>'] C.src_cod C.trg_cod by metis
        also have 1: "... = (\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>') \<cdot>\<^sub>D \<tau>\<^sub>1 ?f \<cdot>\<^sub>D D.inv (\<tau>\<^sub>1 ?f)"
          using D.comp_assoc by blast
        also have "... = \<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>'"
          using par \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_arr_inv' \<tau>.map\<^sub>1_in_hom [of \<mu>']
          by (metis 1 C.ide_dom C.trg_cod D.hseqE D.hseqI' D.hseq_char' D.seqE
              F.preserves_arr F.preserves_trg calculation)
        finally have "\<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu> = \<tau>\<^sub>0 ?a' \<star>\<^sub>D F \<mu>'"
          by blast
        hence "F \<mu> = F \<mu>'"
          using par \<tau>.components_are_equivalences
                D.equivalence_cancel_left [of "\<tau>\<^sub>0 ?a'" "F \<mu>" "F \<mu>'"]
          by simp
        thus "\<mu> = \<mu>'"
          using par F.is_faithful by blast
      qed
      show "\<And>b. D.obj b \<Longrightarrow> \<exists>a. C.obj a \<and> D.equivalent_objects (map\<^sub>0 a) b"
      proof -
        fix b
        assume b: "D.obj b"
        obtain a where a: "C.obj a \<and> D.equivalent_objects (F.map\<^sub>0 a) b"
          using b F.biessentially_surjective_on_objects by blast
        have "D.equivalent_objects (F.map\<^sub>0 a) (map\<^sub>0 a)"
          using a \<tau>.components_are_equivalences D.equivalent_objects_def
          by (metis F.map\<^sub>0_def map\<^sub>0_def \<tau>.map\<^sub>0_in_hhom)
        hence "D.equivalent_objects (map\<^sub>0 a) b"
          using a D.equivalent_objects_symmetric D.equivalent_objects_transitive by blast
        thus "\<exists>a. C.obj a \<and> D.equivalent_objects (map\<^sub>0 a) b"
          using a by auto
      qed
      show "\<And>a a' g. \<lbrakk>C.obj a; C.obj a'; \<guillemotleft>g : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>; D.ide g\<rbrakk>
                       \<Longrightarrow> \<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>C a'\<guillemotright> \<and> C.ide f \<and> D.isomorphic (G f) g"
      proof -
        fix a a' g
        assume a: "C.obj a" and a': "C.obj a'"
        assume g: "\<guillemotleft>g : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>" and ide_g: "D.ide g"
        interpret \<sigma>: converse_pseudonatural_equivalence
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
          ..
        interpret \<sigma>: pseudonatural_equivalence
                       V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                       G \<Phi>\<^sub>G F \<Phi>\<^sub>F \<sigma>'.map\<^sub>0 \<sigma>'.map\<^sub>1
          using \<sigma>'.is_pseudonatural_equivalence by simp
        let ?g' = "\<sigma>'.map\<^sub>0 a' \<star>\<^sub>D g \<star>\<^sub>D \<tau>\<^sub>0 a"
        have g': "\<guillemotleft>?g' : F.map\<^sub>0 a \<rightarrow>\<^sub>D F.map\<^sub>0 a'\<guillemotright>"
          using a a' g \<tau>.ide_map\<^sub>0_obj \<sigma>'.map\<^sub>0_simps(3) C.obj_simps
          by (intro D.in_hhomI D.hseqI') auto
        have ide_g': "D.ide ?g'"
          using a a' g g' ide_g
          by (meson D.hcomp_in_hhomE D.hseqE D.ide_hcomp \<sigma>'.ide_map\<^sub>0_obj \<tau>.ide_map\<^sub>0_obj)
        obtain f where f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C a'\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) ?g'"
          using a a' g g' ide_g' F.locally_essentially_surjective [of a a' ?g'] by auto
        obtain \<xi> where \<xi>: "\<guillemotleft>\<xi> : F f \<Rightarrow>\<^sub>D ?g'\<guillemotright> \<and> D.iso \<xi>"
          using f D.isomorphic_def by blast
        have "D.isomorphic (G f) g"
        proof -
          have "D.isomorphic (G f) (\<tau>\<^sub>0 a' \<star>\<^sub>D F f \<star>\<^sub>D \<sigma>'.map\<^sub>0 a)"
            using a a' f \<tau>.iso_\<phi> D.isomorphic_def by blast
          also have "D.isomorphic ... (\<tau>\<^sub>0 a' \<star>\<^sub>D ?g' \<star>\<^sub>D \<sigma>'.map\<^sub>0 a)"
            using a a' g' \<xi> D.isomorphic_def
            by (metis D.hcomp_ide_isomorphic D.hcomp_isomorphic_ide D.hseqE D.ideD(1)
                D.isomorphic_implies_ide(2) \<sigma>'.ide_map\<^sub>0_obj calculation \<tau>.ide_map\<^sub>0_obj)
          also have "D.isomorphic ... g"
            using a a' g ide_g \<tau>.isomorphic_expansion by simp
          finally show ?thesis by blast
        qed
        thus "\<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>C a'\<guillemotright> \<and> C.ide f \<and> D.isomorphic (G f) g"
          using f by auto
      qed
      show "\<And>f f' \<nu>. \<lbrakk>C.ide f; C.ide f'; src\<^sub>C f = src\<^sub>C f'; trg\<^sub>C f = trg\<^sub>C f'; \<guillemotleft>\<nu> : G f \<Rightarrow>\<^sub>D G f'\<guillemotright>\<rbrakk>
                         \<Longrightarrow> \<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C f'\<guillemotright> \<and> G \<mu> = \<nu>"
      proof -
        fix f f' \<nu>
        assume f: "C.ide f" and f': "C.ide f'"
        and eq_src: "src\<^sub>C f = src\<^sub>C f'" and eq_trg: "trg\<^sub>C f = trg\<^sub>C f'"
        and \<nu>: "\<guillemotleft>\<nu> : G f \<Rightarrow>\<^sub>D G f'\<guillemotright>"
        let ?a = "src\<^sub>C f" and ?a' = "trg\<^sub>C f"
        let ?\<nu>' = "D.inv (\<tau>.\<psi> f') \<cdot>\<^sub>D (\<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<tau>.\<psi> f"
        have \<nu>': "\<guillemotleft>?\<nu>' : F f \<Rightarrow>\<^sub>D F f'\<guillemotright>"
        proof (intro D.comp_in_homI)
          show "\<guillemotleft>\<tau>.\<psi> f : F f \<Rightarrow>\<^sub>D \<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a\<guillemotright>"
            using f \<tau>.\<psi>_in_hom [of f] by blast
          show "\<guillemotleft>\<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a :
                   \<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 ?a \<Rightarrow>\<^sub>D \<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D G f' \<star>\<^sub>D \<tau>\<^sub>0 ?a\<guillemotright>"
            using f \<nu> by (intro D.hcomp_in_vhom) auto
          show "\<guillemotleft>D.inv (\<tau>.\<psi> f') : \<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D G f' \<star>\<^sub>D \<tau>\<^sub>0 ?a \<Rightarrow>\<^sub>D F f'\<guillemotright>"
            using f' \<tau>.iso_\<psi> eq_src eq_trg by auto
        qed
        obtain \<mu> where \<mu>: "\<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C f'\<guillemotright> \<and> F \<mu> = ?\<nu>'"
          using f f' eq_src eq_trg \<nu>' F.locally_full [of f f' ?\<nu>'] by blast
        have "G \<mu> = \<nu>"
        proof -
          have "D.inv (\<tau>.\<psi> f') \<cdot>\<^sub>D (\<sigma>'.map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D \<tau>.\<psi> f =
                D.inv (\<tau>.\<psi> f') \<cdot>\<^sub>D (\<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<tau>.\<psi> f"
            using \<mu> \<tau>.\<psi>_naturality [of \<mu>] by auto
          hence "\<sigma>'.map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>) = \<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a"
            using f f' \<nu>' \<tau>.iso_\<psi>
                  D.iso_cancel_left
                    [of "D.inv (\<tau>.\<psi> f')" "(\<sigma>'.map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)) \<cdot>\<^sub>D \<tau>.\<psi> f"
                        "(\<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a) \<cdot>\<^sub>D \<tau>.\<psi> f"]
                  D.iso_cancel_right
                    [of "\<tau>.\<psi> f" "\<sigma>'.map\<^sub>0 (trg\<^sub>C \<mu>) \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C \<mu>)" "\<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a"]
            by auto
          hence "\<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a = \<sigma>'.map\<^sub>0 ?a' \<star>\<^sub>D \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a"
            using \<mu> by auto
          moreover have "D.par (G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f)) (\<nu> \<star>\<^sub>D \<tau>\<^sub>0 (src\<^sub>C f))"
            using f \<mu> \<nu> \<nu>'
            apply (intro conjI D.hseqI')
                   apply (auto simp add: D.vconn_implies_hpar(1))
             apply fastforce
            by (metis C.ideD(1) C.vconn_implies_hpar(1) D.hcomp_simps(4) D.hseqE D.hseqI'
                D.seqE D.vconn_implies_hpar(1) preserves_arr preserves_cod preserves_src
                weak_arrow_of_homs_axioms category.in_homE horizontal_homs_def
                weak_arrow_of_homs_def)
          ultimately have "G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a = \<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a"
            using f f' \<mu> \<nu> \<tau>.ide_map\<^sub>0_obj \<sigma>'.ide_map\<^sub>0_obj
                  D.equivalence_cancel_left [of "\<sigma>'.map\<^sub>0 ?a'" "G \<mu> \<star>\<^sub>D \<tau>\<^sub>0 ?a" "\<nu> \<star>\<^sub>D \<tau>\<^sub>0 ?a"]
                  \<sigma>'.components_are_equivalences
            by auto
          moreover have "D.par (G \<mu>) \<nu>"
            using f f' \<mu> \<nu> by fastforce
          ultimately show ?thesis
            using f f' \<mu> \<nu> \<tau>.ide_map\<^sub>0_obj
                  D.equivalence_cancel_right [of "\<tau>\<^sub>0 ?a" "G \<mu>" "\<nu>"] \<tau>.components_are_equivalences
            by auto
        qed
        thus "\<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C f'\<guillemotright> \<and> G \<mu> = \<nu>"
          using \<mu> by auto
      qed
    qed

    lemma is_equivalence_pseudofunctor:
    shows "equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G"
      ..

  end

  lemma pseudonaturally_equivalent_respects_equivalence_pseudofunctor:
  assumes "pseudonaturally_equivalent
             V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G"
  and "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F"
  shows "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G"
  proof -
    obtain \<tau>\<^sub>0 \<tau>\<^sub>1 where \<tau>: "pseudonatural_equivalence
                            V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1"
      using assms pseudonaturally_equivalent_def by blast
    interpret F: equivalence_pseudofunctor
                   V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F
      using assms by simp
    interpret G: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G
      using assms \<tau>
      by (simp add: pseudonatural_equivalence_def pseudonatural_transformation_def)
    interpret \<tau>: pseudonatural_equivalence
                   V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      using \<tau> by simp
    interpret G: pseudofunctor_pseudonaturally_equivalent_to_equivalence_pseudofunctor
                   V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
      ..
    show "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C G \<Phi>\<^sub>G"
      using G.is_equivalence_pseudofunctor by simp
  qed

end
