(*  Title:       Pseudofunctor
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2019
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Pseudofunctors"

theory Pseudofunctor
imports MonoidalCategory.MonoidalFunctor Bicategory Subbicategory InternalEquivalence Coherence
begin

  text \<open>
    The traditional definition of a pseudofunctor \<open>F : C \<rightarrow> D\<close> between bicategories \<open>C\<close> and \<open>D\<close>
    is in terms of two maps: an ``object map'' \<open>F\<^sub>o\<close> that takes objects of \<open>C\<close> to objects of \<open>D\<close>
    and an ``arrow map'' \<open>F\<^sub>a\<close> that assigns to each pair of objects \<open>a\<close> and \<open>b\<close> of \<open>C\<close>
    a functor \<open>F\<^sub>a a b\<close> from the hom-category \<open>hom\<^sub>C a b\<close> to the hom-category \<open>hom\<^sub>D (F\<^sub>o a) (F\<^sub>o b)\<close>.
    In addition, there is assigned to each object \<open>a\<close> of \<open>C\<close> an invertible 2-cell
    \<open>\<guillemotleft>\<Psi> a : F\<^sub>o a \<Rightarrow>\<^sub>D (F\<^sub>a a a) a\<guillemotright>\<close>, and to each pair \<open>(f, g)\<close> of composable 1-cells of C there
    is assigned an invertible 2-cell \<open>\<guillemotleft>\<Phi> (f, g) : F g \<star> F f \<Rightarrow> F (g \<star> f)\<guillemotright>\<close>, all subject to
    naturality and coherence conditions.

    In keeping with the ``object-free'' style in which we have been working, we do not wish
    to adopt a definition of pseudofunctor that distinguishes between objects and other
    arrows.  Instead, we would like to understand a pseudofunctor as an ordinary functor between
    (vertical) categories that weakly preserves horizontal composition in a suitable sense.
    So, we take as a starting point that a pseudofunctor \<open>F : C \<rightarrow> D\<close> is a functor from
    \<open>C\<close> to \<open>D\<close>, when these are regarded as ordinary categories with respect to vertical
    composition.  Next, \<open>F\<close> should preserve source and target, but only ``weakly''
    (up to isomorphism, rather than ``on the nose'').
    Weak preservation of horizontal composition is expressed by specifying, for each horizontally
    composable pair of vertical identities \<open>(f, g)\<close> of \<open>C\<close>, a ``compositor''
    \<open>\<guillemotleft>\<Phi> (f, g) : F g \<star> F f \<Rightarrow> F (g \<star> f)\<guillemotright>\<close> in \<open>D\<close>, such that the \<open>\<Phi> (f, g)\<close> are the components
    of a natural isomorphism.
    Associators must also be weakly preserved by F; this is expressed by a coherence
    condition that relates an associator \<open>\<a>\<^sub>C[f, g, h]\<close> in \<open>C\<close>, its image \<open>F \<a>\<^sub>C[f, g, h]\<close>,
    the associator \<open>\<a>\<^sub>D[F f, F g, F h]\<close> in \<open>D\<close> and compositors involving \<open>f\<close>, \<open>g\<close>, and \<open>h\<close>.
    As regards the weak preservation of unitors, just as for monoidal functors,
    which are in fact pseudofunctors between one-object bicategories, it is only necessary
    to assume that \<open>F \<i>\<^sub>C[a]\<close> and \<open>\<i>\<^sub>D[F a]\<close> are isomorphic in \<open>D\<close> for each object \<open>a\<close> of \<open>C\<close>,
    for there is then a canonical way to obtain, for each \<open>a\<close>, an isomorphism
    \<open>\<guillemotleft>\<Psi> a : src (F a) \<rightarrow> F a\<guillemotright>\<close> that satisfies the usual coherence conditions relating the
    unitors and the associators.  Note that the map \<open>a \<mapsto> src (F a)\<close> amounts to the traditional
    ``object map'' \<open>F\<^sub>o\<close>, so that this becomes a derived notion, rather than a primitive one.
  \<close>

  subsection "Weak Arrows of Homs"

  text \<open>
    We begin with a locale that defines a functor between ``horizontal homs'' that preserves
    source and target up to isomorphism.
  \<close>

  locale weak_arrow_of_homs =
    C: horizontal_homs C src\<^sub>C trg\<^sub>C +
    D: horizontal_homs D src\<^sub>D trg\<^sub>D +
    "functor" C D F
  for C :: "'c comp"                    (infixr "\<cdot>\<^sub>C" 55)
  and src\<^sub>C :: "'c \<Rightarrow> 'c"
  and trg\<^sub>C :: "'c \<Rightarrow> 'c"
  and D :: "'d comp"                    (infixr "\<cdot>\<^sub>D" 55)
  and src\<^sub>D :: "'d \<Rightarrow> 'd"
  and trg\<^sub>D :: "'d \<Rightarrow> 'd"
  and F :: "'c \<Rightarrow> 'd" +
  assumes weakly_preserves_src: "\<And>\<mu>. C.arr \<mu> \<Longrightarrow> D.isomorphic (F (src\<^sub>C \<mu>)) (src\<^sub>D (F \<mu>))"
  and weakly_preserves_trg: "\<And>\<mu>. C.arr \<mu> \<Longrightarrow> D.isomorphic (F (trg\<^sub>C \<mu>)) (trg\<^sub>D (F \<mu>))"
  begin

    lemma isomorphic_src:
    assumes "C.obj a"
    shows "D.isomorphic (src\<^sub>D (F a)) (F a)"
      using assms weakly_preserves_src [of a] D.isomorphic_symmetric by auto

    lemma isomorphic_trg:
    assumes "C.obj a"
    shows "D.isomorphic (trg\<^sub>D (F a)) (F a)"
      using assms weakly_preserves_trg [of a] D.isomorphic_symmetric by auto

    abbreviation (input) hseq\<^sub>C
    where "hseq\<^sub>C \<mu> \<nu> \<equiv> C.arr \<mu> \<and> C.arr \<nu> \<and> src\<^sub>C \<mu> = trg\<^sub>C \<nu>"

    abbreviation (input) hseq\<^sub>D
    where "hseq\<^sub>D \<mu> \<nu> \<equiv> D.arr \<mu> \<and> D.arr \<nu> \<and> src\<^sub>D \<mu> = trg\<^sub>D \<nu>"

    lemma preserves_hseq:
    assumes "hseq\<^sub>C \<mu> \<nu>"
    shows "hseq\<^sub>D (F \<mu>) (F \<nu>)"
    proof -
      have "src\<^sub>C \<mu> = trg\<^sub>C \<nu>"
        using assms by auto
      hence "D.isomorphic (F (src\<^sub>C \<mu>)) (trg\<^sub>D (F \<nu>))"
        using assms weakly_preserves_trg by auto
      moreover have "D.isomorphic (src\<^sub>D (F \<mu>)) (F (src\<^sub>C \<mu>))"
        using assms weakly_preserves_src D.isomorphic_symmetric by blast
      ultimately have "D.isomorphic (src\<^sub>D (F \<mu>)) (trg\<^sub>D (F \<nu>))"
        using D.isomorphic_transitive by blast
      hence "src\<^sub>D (F \<mu>) = trg\<^sub>D (F \<nu>)"
        using assms D.isomorphic_objects_are_equal by auto
      thus ?thesis
        using assms by auto
    qed

    text \<open>
      Though \<open>F\<close> does not preserve objects ``on the nose'', we can recover from it the
      usual ``object map'', which does.
      It is slightly confusing at first to get used to the idea that applying the
      object map of a weak arrow of homs to an object does not give the same thing
      as applying the underlying functor, but rather only something isomorphic to it.

      The following defines the object map associated with \<open>F\<close>.
    \<close>

    definition map\<^sub>0
    where "map\<^sub>0 a \<equiv> src\<^sub>D (F a)"

    lemma map\<^sub>0_simps [simp]:
    assumes "C.obj a"
    shows "D.obj (map\<^sub>0 a)"
    and "src\<^sub>D (map\<^sub>0 a) = map\<^sub>0 a" and "trg\<^sub>D (map\<^sub>0 a) = map\<^sub>0 a"
    and "D.dom (map\<^sub>0 a) = map\<^sub>0 a" and "D.cod (map\<^sub>0 a) = map\<^sub>0 a"
      using assms map\<^sub>0_def by auto

    lemma preserves_src [simp]:
    assumes "C.arr \<mu>"
    shows "src\<^sub>D (F \<mu>) = map\<^sub>0 (src\<^sub>C \<mu>)"
      using assms
      by (metis C.src.preserves_arr C.src_src C.trg_src map\<^sub>0_def preserves_hseq)

    lemma preserves_trg [simp]:
    assumes "C.arr \<mu>"
    shows "trg\<^sub>D (F \<mu>) = map\<^sub>0 (trg\<^sub>C \<mu>)"
      using assms map\<^sub>0_def preserves_hseq C.src_trg C.trg.preserves_arr by presburger

    lemma preserves_hhom [intro]:
    assumes "C.arr \<mu>"
    shows "D.in_hhom (F \<mu>) (map\<^sub>0 (src\<^sub>C \<mu>)) (map\<^sub>0 (trg\<^sub>C \<mu>))"
      using assms by simp

    text \<open>
      We define here the lifting of \<open>F\<close> to a functor \<open>FF: CC \<rightarrow> DD\<close>.
      We need this to define the domains and codomains of the compositors.
    \<close>

    definition FF
    where "FF \<equiv> \<lambda>\<mu>\<nu>. if C.VV.arr \<mu>\<nu> then (F (fst \<mu>\<nu>), F (snd \<mu>\<nu>)) else D.VV.null"

    sublocale FF: "functor" C.VV.comp D.VV.comp FF
    proof -
      have 1: "\<And>\<mu>\<nu>. C.VV.arr \<mu>\<nu> \<Longrightarrow> D.VV.arr (FF \<mu>\<nu>)"
        unfolding FF_def using C.VV.arr_char D.VV.arr_char preserves_hseq by simp
      show "functor C.VV.comp D.VV.comp FF"
      proof
        fix \<mu>\<nu>
        show "\<not> C.VV.arr \<mu>\<nu> \<Longrightarrow> FF \<mu>\<nu> = D.VV.null"
          using FF_def by simp
        show "C.VV.arr \<mu>\<nu> \<Longrightarrow> D.VV.arr (FF \<mu>\<nu>)"
          using 1 by simp
        assume \<mu>\<nu>: "C.VV.arr \<mu>\<nu>"
        show "D.VV.dom (FF \<mu>\<nu>) = FF (C.VV.dom \<mu>\<nu>)"
          using \<mu>\<nu> 1 FF_def C.VV.arr_char D.VV.arr_char C.VV.dom_simp D.VV.dom_simp
          by simp
        show "D.VV.cod (FF \<mu>\<nu>) = FF (C.VV.cod \<mu>\<nu>)"
          using \<mu>\<nu> 1 FF_def C.VV.arr_char D.VV.arr_char C.VV.cod_simp D.VV.cod_simp
          by simp
        next
        fix \<mu>\<nu> \<tau>\<pi>
        assume 2: "C.VV.seq \<mu>\<nu> \<tau>\<pi>"
        show "FF (C.VV.comp \<mu>\<nu> \<tau>\<pi>) = D.VV.comp (FF \<mu>\<nu>) (FF \<tau>\<pi>)"
        proof -
          have "FF (C.VV.comp \<mu>\<nu> \<tau>\<pi>) = (F (fst \<mu>\<nu>) \<cdot>\<^sub>D F (fst \<tau>\<pi>), F (snd \<mu>\<nu>) \<cdot>\<^sub>D F (snd \<tau>\<pi>))"
            using 1 2 FF_def C.VV.comp_char C.VxV.comp_char C.VV.arr_char
            by (metis (no_types, lifting) C.VV.seq_char C.VxV.seqE fst_conv preserves_comp_2
                snd_conv)
          also have "... = D.VV.comp (FF \<mu>\<nu>) (FF \<tau>\<pi>)"
            using 1 2 FF_def D.VV.comp_char D.VxV.comp_char C.VV.arr_char D.VV.arr_char
                  C.VV.seq_char C.VxV.seqE preserves_seq
            by (simp, meson)
          finally show ?thesis by simp
        qed
      qed
    qed

    lemma functor_FF:
    shows "functor C.VV.comp D.VV.comp FF"
      ..

  end

  subsection "Definition of Pseudofunctors"

  text \<open>
    I don't much like the term "pseudofunctor", which is suggestive of something that
    is ``not really'' a functor.  In the development here we can see that a pseudofunctor
    is really a \emph{bona fide} functor with respect to vertical composition,
    which happens to have in addition a weak preservation property with respect to
    horizontal composition.
    This weak preservation of horizontal composition is captured by extra structure,
    the ``compositors'', which are the components of a natural transformation.
    So ``pseudofunctor'' is really a misnomer; it's an actual functor that has been equipped
    with additional structure relating to horizontal composition.  I would use the term
    ``bifunctor'' for such a thing, but it seems to not be generally accepted and also tends
    to conflict with the usage of that term to refer to an ordinary functor of two
    arguments; which I have called a ``binary functor''.  Sadly, there seem to be no other
    plausible choices of terminology, other than simply ``functor''
    (recommended on n-Lab @{url \<open>https://ncatlab.org/nlab/show/pseudofunctor\<close>}),
    but that is not workable here because we need a name that does not clash with that
    used for an ordinary functor between categories.
  \<close>

  locale pseudofunctor =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    weak_arrow_of_homs V\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D src\<^sub>D trg\<^sub>D F +
    FoH\<^sub>C: composite_functor C.VV.comp V\<^sub>C V\<^sub>D \<open>\<lambda>\<mu>\<nu>. H\<^sub>C (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> F +
    H\<^sub>DoFF: composite_functor C.VV.comp D.VV.comp V\<^sub>D
             FF \<open>\<lambda>\<mu>\<nu>. H\<^sub>D (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> +
    \<Phi>: natural_isomorphism C.VV.comp V\<^sub>D H\<^sub>DoFF.map FoH\<^sub>C.map \<Phi>
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
  and \<Phi> :: "'c * 'c \<Rightarrow> 'd" +
  assumes assoc_coherence:
            "\<lbrakk> C.ide f; C.ide g; C.ide h; src\<^sub>C f = trg\<^sub>C g; src\<^sub>C g = trg\<^sub>C h \<rbrakk> \<Longrightarrow>
               F \<a>\<^sub>C[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) =
               \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
  begin

    no_notation C.in_hom                  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    no_notation D.in_hom                  ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")
    notation C.in_hhom                    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation C.in_hom                     ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hhom                    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")
    notation D.in_hom                     ("\<guillemotleft>_ : _ \<Rightarrow>\<^sub>D _\<guillemotright>")

    notation C.lunit                      ("\<l>\<^sub>C[_]")
    notation C.runit                      ("\<r>\<^sub>C[_]")
    notation C.lunit'                     ("\<l>\<^sub>C\<^sup>-\<^sup>1[_]")
    notation C.runit'                     ("\<r>\<^sub>C\<^sup>-\<^sup>1[_]")
    notation C.\<a>'                         ("\<a>\<^sub>C\<^sup>-\<^sup>1[_, _, _]")
    notation D.lunit                      ("\<l>\<^sub>D[_]")
    notation D.runit                      ("\<r>\<^sub>D[_]")
    notation D.lunit'                     ("\<l>\<^sub>D\<^sup>-\<^sup>1[_]")
    notation D.runit'                     ("\<r>\<^sub>D\<^sup>-\<^sup>1[_]")
    notation D.\<a>'                         ("\<a>\<^sub>D\<^sup>-\<^sup>1[_, _, _]")

    lemma weakly_preserves_objects:
    assumes "C.obj a"
    shows "D.isomorphic (map\<^sub>0 a) (F a)"
      using assms weakly_preserves_src [of a] D.isomorphic_symmetric by auto

    lemma cmp_in_hom [intro]:
    assumes "C.ide a" and "C.ide b" and "src\<^sub>C a = trg\<^sub>C b"
    shows "\<guillemotleft>\<Phi> (a, b) : map\<^sub>0 (src\<^sub>C b) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C a)\<guillemotright>"
    and "\<guillemotleft>\<Phi> (a, b) : F a \<star>\<^sub>D F b \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C b)\<guillemotright>"
    proof -
      show "\<guillemotleft>\<Phi> (a, b) : F a \<star>\<^sub>D F b \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C b)\<guillemotright>"
      proof -
        have "H\<^sub>DoFF.map (a, b) = F a \<star>\<^sub>D F b"
          using assms C.VV.ide_char FF_def by auto
        moreover have "FoH\<^sub>C.map (a, b) = F (a \<star>\<^sub>C b)"
          using assms C.VV.ide_char by simp
        ultimately show ?thesis
          using assms C.VV.ide_char \<Phi>.preserves_hom
          apply simp
          by (metis (no_types, lifting) C.VV.ideI C.VV.ide_in_hom C.VxV.ide_Ide C.ideD(1)
              fst_conv snd_conv)
      qed
      show "\<guillemotleft>\<Phi> (a, b) : map\<^sub>0 (src\<^sub>C b) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C a)\<guillemotright>"
      proof -
        have "C.hseq a b"
          by (simp add: assms(1-3))
        thus ?thesis
          by (metis C.src_hcomp C.trg_hcomp D.in_hhom_def D.in_homE D.src_cod D.trg_cod
              \<open>\<guillemotleft>\<Phi> (a, b) : F a \<star>\<^sub>D F b \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C b)\<guillemotright>\<close> preserves_src preserves_trg)
      qed
    qed

    lemma cmp_simps [simp]:
    assumes "C.ide f" and "C.ide g" and "src\<^sub>C f = trg\<^sub>C g"
    shows "D.arr (\<Phi> (f, g))"
    and "src\<^sub>D (\<Phi> (f, g)) = src\<^sub>D (F g)" and "trg\<^sub>D (\<Phi> (f, g)) = trg\<^sub>D (F f)"
    and "D.dom (\<Phi> (f, g)) = F f \<star>\<^sub>D F g" and "D.cod (\<Phi> (f, g)) = F (f \<star>\<^sub>C g)"
    proof -
      show "D.arr (\<Phi> (f, g))"
        using assms cmp_in_hom by auto
      show "src\<^sub>D (\<Phi> (f, g)) = src\<^sub>D (F g)"
        using assms cmp_in_hom by auto
      show "trg\<^sub>D (\<Phi> (f, g)) = trg\<^sub>D (F f)"
        using assms cmp_in_hom by auto
      show "D.dom (\<Phi> (f, g)) = F f \<star>\<^sub>D F g"
        using assms cmp_in_hom by blast
      show "D.cod (\<Phi> (f, g)) = F (f \<star>\<^sub>C g)"
        using assms cmp_in_hom by blast
    qed

    lemma cmp_in_hom':
    assumes "C.arr \<mu>" and "C.arr \<nu>" and "src\<^sub>C \<mu> = trg\<^sub>C \<nu>"
    shows "\<guillemotleft>\<Phi> (\<mu>, \<nu>) : map\<^sub>0 (src\<^sub>C \<nu>) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C \<mu>)\<guillemotright>"
    and "\<guillemotleft>\<Phi> (\<mu>, \<nu>) : F (C.dom \<mu>) \<star>\<^sub>D F (C.dom \<nu>) \<Rightarrow>\<^sub>D F (C.cod \<mu> \<star>\<^sub>C C.cod \<nu>)\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>\<Phi> (\<mu>, \<nu>) : F (C.dom \<mu>) \<star>\<^sub>D F (C.dom \<nu>) \<Rightarrow>\<^sub>D F (C.cod \<mu> \<star>\<^sub>C C.cod \<nu>)\<guillemotright>"
        using assms C.VV.arr_char \<Phi>.preserves_hom FF_def C.VV.dom_simp C.VV.cod_simp
        by auto
      show "\<guillemotleft>\<Phi> (\<mu>, \<nu>) : map\<^sub>0 (src\<^sub>C \<nu>) \<rightarrow>\<^sub>D map\<^sub>0 (trg\<^sub>C \<mu>)\<guillemotright>"
        using assms 1 D.src_dom [of "\<Phi> (\<mu>, \<nu>)"] D.trg_dom [of "\<Phi> (\<mu>, \<nu>)"]
              C.VV.dom_simp C.VV.cod_simp
        by auto
    qed

    lemma cmp_simps':
    assumes "C.arr \<mu>" and "C.arr \<nu>" and "src\<^sub>C \<mu> = trg\<^sub>C \<nu>"
    shows "D.arr (\<Phi> (\<mu>, \<nu>))"
    and "src\<^sub>D (\<Phi> (\<mu>, \<nu>)) = map\<^sub>0 (src\<^sub>C \<nu>)" and "trg\<^sub>D (\<Phi> (\<mu>, \<nu>)) = map\<^sub>0 (trg\<^sub>C \<mu>)"
    and "D.dom (\<Phi> (\<mu>, \<nu>)) = F (C.dom \<mu>) \<star>\<^sub>D F (C.dom \<nu>)"
    and "D.cod (\<Phi> (\<mu>, \<nu>)) = F (C.cod \<mu> \<star>\<^sub>C C.cod \<nu>)"
    proof -
      show "D.arr (\<Phi> (\<mu>, \<nu>))"
        using assms cmp_in_hom by auto
      show "src\<^sub>D (\<Phi> (\<mu>, \<nu>)) = map\<^sub>0 (src\<^sub>C \<nu>)"
        using assms cmp_in_hom' by auto
      show "trg\<^sub>D (\<Phi> (\<mu>, \<nu>)) = map\<^sub>0 (trg\<^sub>C \<mu>)"
        using assms cmp_in_hom' by auto
      show "D.dom (\<Phi> (\<mu>, \<nu>)) = F (C.dom \<mu>) \<star>\<^sub>D F (C.dom \<nu>)"
        using assms cmp_in_hom' by blast
      show "D.cod (\<Phi> (\<mu>, \<nu>)) = F (C.cod \<mu> \<star>\<^sub>C C.cod \<nu>)"
        using assms cmp_in_hom' by blast
    qed

    lemma cmp_components_are_iso [simp]:
    assumes "C.ide f" and "C.ide g" and "src\<^sub>C f = trg\<^sub>C g"
    shows "D.iso (\<Phi> (f, g))"
      using assms C.VV.ide_char C.VV.arr_char by simp

    lemma weakly_preserves_hcomp:
    assumes "C.ide f" and "C.ide g" and "src\<^sub>C f = trg\<^sub>C g"
    shows "D.isomorphic (F f \<star>\<^sub>D F g) (F (f \<star>\<^sub>C g))"
      using assms D.isomorphic_def by auto

  end

  context pseudofunctor
  begin

    text \<open>
      The following defines the image of the unit isomorphism \<open>\<i>\<^sub>C[a]\<close> under \<open>F\<close>.
      We will use \<open>(F a, \<i>[a])\<close> as an ``alternate unit'', to substitute for
      \<open>(src\<^sub>D (F a), \<i>\<^sub>D[src\<^sub>D (F a)])\<close>.
    \<close>

    abbreviation (input) \<i>  ("\<i>[_]")
    where "\<i>[a] \<equiv> F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a)"

    lemma \<i>_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a) : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>\<i>[a] : F a \<star>\<^sub>D F a \<Rightarrow>\<^sub>D F a\<guillemotright>"
    proof (unfold map\<^sub>0_def)
      show "\<guillemotleft>F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a) : F a \<star>\<^sub>D F a \<Rightarrow>\<^sub>D F a\<guillemotright>"
        using assms preserves_hom cmp_in_hom
        by (intro D.comp_in_homI, auto)
      show "\<guillemotleft>F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a) : src\<^sub>D (F a) \<rightarrow>\<^sub>D src\<^sub>D (F a)\<guillemotright>"
        using assms C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
        by (intro D.vcomp_in_hhom D.seqI, auto)
    qed

    lemma \<i>_simps [simp]:
    assumes "C.obj a"
    shows "D.arr (\<i> a)"
    and "src\<^sub>D \<i>[a] = map\<^sub>0 a" and "trg\<^sub>D \<i>[a] = map\<^sub>0 a"
    and "D.dom \<i>[a] = F a \<star>\<^sub>D F a" and "D.cod \<i>[a] = F a"
    proof -
      show "src\<^sub>D \<i>[a] = map\<^sub>0 a"
        unfolding map\<^sub>0_def
        using assms \<i>_in_hom D.src_cod [of "F a"]
        by (metis C.unit_simps(1) C.unit_simps(5) D.arrI D.src_vcomp D.vseq_implies_hpar(1)
            is_natural_2 preserves_arr)
      show "trg\<^sub>D \<i>[a] = map\<^sub>0 a"
        unfolding map\<^sub>0_def
        using assms \<i>_in_hom D.trg_cod [of "F a"]
        by (metis C.obj_def C.unit_simps(1) C.unit_simps(3) D.arrI D.trg_vcomp preserves_hseq)
      show "D.arr \<i>[a]"
        using assms \<i>_in_hom by auto
      show "D.dom \<i>[a] = F a \<star>\<^sub>D F a"
        using assms \<i>_in_hom by auto
      show "D.cod \<i>[a] = F a"
        using assms \<i>_in_hom by auto
    qed

    lemma iso_\<i>:
    assumes "C.obj a"
    shows "D.iso \<i>[a]"
    proof -
      have "D.iso (\<Phi> (a, a))"
        using assms by auto
      moreover have "D.iso (F \<i>\<^sub>C[a])"
        using assms C.iso_unit by simp
      moreover have "D.seq (F \<i>\<^sub>C[a]) (\<Phi> (a, a))"
        using assms C.obj_self_composable(1) C.seq_if_composable by simp
      ultimately show ?thesis by auto
    qed

    text \<open>
      If \<open>a\<close> is an object of \<open>C\<close> and we have an isomorphism \<open>\<guillemotleft>\<Phi> (a, a) : F a \<star>\<^sub>D F a \<Rightarrow>\<^sub>D F (a \<star>\<^sub>C a)\<guillemotright>\<close>,
      then there is a canonical way to define a compatible isomorphism \<open>\<guillemotleft>\<Psi> a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>\<close>.
      Specifically, we take \<open>\<Psi> a\<close> to be the unique isomorphism \<open>\<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>\<close> such that
      \<open>\<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)\<close>.
    \<close>

    definition unit
    where "unit a \<equiv> THE \<psi>. \<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<psi> \<and>
                         \<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)"

    lemma unit_char:
    assumes "C.obj a"
    shows "\<guillemotleft>unit a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>" and "D.iso (unit a)"
    and "unit a \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (unit a \<star>\<^sub>D unit a)"
    and "\<exists>!\<psi>. \<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)"
    proof -
      let ?P = "\<lambda>\<psi>. \<guillemotleft>\<psi> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<psi> \<and> \<psi> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<psi> \<star>\<^sub>D \<psi>)"
      show "\<exists>!\<psi>. ?P \<psi>"
      proof -
        have "D.obj (map\<^sub>0 a)"
          using assms by simp
        moreover have "D.isomorphic (map\<^sub>0 a) (F a)"
          unfolding map\<^sub>0_def
          using assms isomorphic_src by simp
        ultimately show ?thesis
          using assms D.unit_unique_upto_unique_iso \<Phi>.preserves_hom \<i>_in_hom iso_\<i> by simp
      qed
      hence 1: "?P (unit a)"
        using assms unit_def the1I2 [of ?P ?P] by simp
      show "\<guillemotleft>unit a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>" using 1 by simp
      show "D.iso (unit a)" using 1 by simp
      show "unit a \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (unit a \<star>\<^sub>D unit a)"
        using 1 by simp
    qed

    lemma unit_simps [simp]:
    assumes "C.obj a"
    shows "D.arr (unit a)"
    and "src\<^sub>D (unit a) = map\<^sub>0 a" and "trg\<^sub>D (unit a) = map\<^sub>0 a"
    and "D.dom (unit a) = map\<^sub>0 a" and "D.cod (unit a) = F a"
    proof -
      show "D.arr (unit a)"
        using assms unit_char(1) by auto
      show 1: "D.dom (unit a) = map\<^sub>0 a"
        using assms unit_char(1) by auto
      show 2: "D.cod (unit a) = F a"
        using assms unit_char(1) by auto
      show "src\<^sub>D (unit a) = map\<^sub>0 a"
        using assms 1 D.src_dom
        unfolding map\<^sub>0_def
        by (metis C.obj_def D.arr_dom_iff_arr D.src.preserves_reflects_arr D.src_src preserves_arr)
      show "trg\<^sub>D (unit a) = map\<^sub>0 a"
        unfolding map\<^sub>0_def
        using assms 2 unit_char
        by (metis "1" D.trg_dom map\<^sub>0_def map\<^sub>0_simps(3) \<open>D.arr (unit a)\<close>)
    qed

    lemma unit_in_hom [intro]:
    assumes "C.obj a"
    shows "\<guillemotleft>unit a : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a\<guillemotright>"
    and "\<guillemotleft>unit a : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>"
      using assms by auto

    lemma unit_eqI:
    assumes "C.obj a" and "\<guillemotleft>\<mu>: map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright>" and "D.iso \<mu>"
    and "\<mu> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i> a \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D \<mu>)"
    shows "\<mu> = unit a"
      using assms unit_def unit_char
            the1_equality [of "\<lambda>\<mu>. \<guillemotleft>\<mu> : map\<^sub>0 a \<Rightarrow>\<^sub>D F a\<guillemotright> \<and> D.iso \<mu> \<and>
                                   \<mu> \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = \<i>[a] \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D \<mu>)" \<mu>]
      by simp

    text \<open>
      The following defines the unique isomorphism satisfying the characteristic conditions
      for the left unitor \<open>\<l>\<^sub>D[trg\<^sub>D (F f)]\<close>, but using the ``alternate unit'' \<open>\<i>[trg\<^sub>C f]\<close>
      instead of \<open>\<i>\<^sub>D[trg\<^sub>D (F f)]\<close>, which is used to define \<open>\<l>\<^sub>D[trg\<^sub>D (F f)]\<close>.
    \<close>

    definition lF
    where "lF f \<equiv> THE \<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<and>
                         F (trg\<^sub>C f) \<star>\<^sub>D \<mu> =(\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"

    lemma lF_char:
    assumes "C.ide f"
    shows "\<guillemotleft>lF f : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright>"
    and "F (trg\<^sub>C f) \<star>\<^sub>D lF f = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
    and "\<exists>!\<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<and>
                   F (trg\<^sub>C f) \<star>\<^sub>D \<mu> = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
    proof -
      let ?P = "\<lambda>\<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<and>
                     F (trg\<^sub>C f) \<star>\<^sub>D \<mu> = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
      show "\<exists>!\<mu>. ?P \<mu>"
      proof -
        interpret Df: prebicategory \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D
          using D.is_prebicategory by simp
        interpret S: subcategory \<open>(\<cdot>\<^sub>D)\<close> \<open>Df.left (F (trg\<^sub>C f))\<close>
          using assms Df.left_hom_is_subcategory by simp
        interpret Df: left_hom \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<open>F (trg\<^sub>C f)\<close>
          using assms D.weak_unit_char
          apply unfold_locales by simp
        interpret Df: left_hom_with_unit \<open>(\<cdot>\<^sub>D)\<close> \<open>(\<star>\<^sub>D)\<close> \<a>\<^sub>D \<open>\<i>[trg\<^sub>C f]\<close> \<open>F (trg\<^sub>C f)\<close>
        proof
          show "Df.weak_unit (F (trg\<^sub>C f))"
            using assms D.weak_unit_char
            by (metis C.ideD(1) C.trg.preserves_reflects_arr C.trg_trg weakly_preserves_trg)
          show "\<guillemotleft>\<i>[trg\<^sub>C f] : F (trg\<^sub>C f) \<star>\<^sub>D F (trg\<^sub>C f) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
            using assms \<i>_in_hom by simp
          show "D.iso \<i>[trg\<^sub>C f]"
            using assms iso_\<i> by simp
        qed
        have "\<exists>!\<mu>. \<guillemotleft>\<mu> : Df.L (F f) \<Rightarrow>\<^sub>S F f\<guillemotright> \<and>
                   Df.L \<mu> = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>S \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
        proof -
          have "Df.left (F (trg\<^sub>C f)) (F f)"
            using assms weakly_preserves_src D.isomorphic_def D.hseq_char D.hseq_char'
                  Df.left_def
            by fastforce
          thus ?thesis
            using assms Df.lunit_char(3) S.ide_char S.arr_char by simp
        qed
        moreover have "Df.L (F f) = F (trg\<^sub>C f) \<star>\<^sub>D F f"
          using assms by (simp add: Df.H\<^sub>L_def)
        moreover have "\<And>\<mu>. Df.L \<mu> = F (trg\<^sub>C f) \<star>\<^sub>D \<mu>"
          using Df.H\<^sub>L_def by simp
        moreover have "(\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>S \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f] =
                       (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
          by (metis (no_types, lifting) D.assoc'_eq_inv_assoc D.ext D.hseqE D.seqE
              D.vconn_implies_hpar(1) D.vconn_implies_hpar(3) Df.characteristic_iso(4)
              Df.equivalence_functor_L Df.iso_unit(2) S.comp_simp S.ext S.ide_char
              S.in_hom_char S.iso_is_arr S.null_char calculation(1) category.ide_cod
              category.in_homE equivalence_functor_def)
        moreover have "\<And>\<mu>. \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright> \<longleftrightarrow>
                            \<guillemotleft>\<mu> : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>S F f\<guillemotright>"
          using assms S.in_hom_char S.arr_char
          by (metis D.in_homE Df.hom_connected(2) Df.left_def calculation(1) calculation(2))
        ultimately show ?thesis by simp
      qed
      hence 1: "?P (lF f)"
        using lF_def the1I2 [of ?P ?P] by simp
      show "\<guillemotleft>lF f : F (trg\<^sub>C f) \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F f\<guillemotright>"
        using 1 by simp
      show "F (trg\<^sub>C f) \<star>\<^sub>D lF f = (\<i>[trg\<^sub>C f] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F (trg\<^sub>C f), F (trg\<^sub>C f), F f]"
        using 1 by simp
    qed

    lemma lF_simps [simp]:
    assumes "C.ide f"
    shows "D.arr (lF f)"
    and "src\<^sub>D (lF f) = map\<^sub>0 (src\<^sub>C f)" and "trg\<^sub>D (lF f) = map\<^sub>0 (trg\<^sub>C f)"
    and "D.dom (lF f) = F (trg\<^sub>C f) \<star>\<^sub>D F f" and "D.cod (lF f) = F f"
    proof -
      show "D.arr (lF f)"
        using assms lF_char(1) by auto
      show "D.dom (lF f) = F (trg\<^sub>C f) \<star>\<^sub>D F f"
        using assms lF_char(1) by auto
      show "D.cod (lF f) = F f"
        using assms lF_char(1) by auto
      show "src\<^sub>D (lF f) = map\<^sub>0 (src\<^sub>C f)"
        unfolding map\<^sub>0_def
        using assms \<open>D.arr (lF f)\<close> \<open>D.cod (lF f) = F f\<close> D.src_cod by fastforce
      show "trg\<^sub>D (lF f) = map\<^sub>0 (trg\<^sub>C f)"
        using assms \<open>D.arr (lF f)\<close> \<open>D.cod (lF f) = F f\<close> D.trg_cod by fastforce
    qed

    text \<open>
      \sloppypar
      The next two lemmas generalize the eponymous results from
      @{theory MonoidalCategory.MonoidalFunctor}.  See the proofs of those results for diagrams.
    \<close>

    lemma lunit_coherence1:
    assumes "C.ide f"
    shows "\<l>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (unit (trg\<^sub>C f) \<star>\<^sub>D F f) = lF f"
    proof -
      let ?b = "trg\<^sub>C f"
      have 1: "trg\<^sub>D (F f) = map\<^sub>0 ?b"
        using assms by simp
      have "lF f \<cdot>\<^sub>D (unit ?b \<star>\<^sub>D F f) = \<l>\<^sub>D[F f]"
      proof -
        have "D.par (lF f \<cdot>\<^sub>D (unit ?b \<star>\<^sub>D F f)) \<l>\<^sub>D[F f]"
          using assms 1 D.lunit_in_hom unit_char(1-2) lF_char(1) D.ideD(1) by auto
        moreover have "map\<^sub>0 ?b \<star>\<^sub>D (lF f \<cdot>\<^sub>D (unit ?b \<star>\<^sub>D F f)) = map\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f]"
        proof -
          have "map\<^sub>0 ?b \<star>\<^sub>D (lF f \<cdot>\<^sub>D (unit ?b \<star>\<^sub>D F f)) =
                (map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (map\<^sub>0 ?b \<star>\<^sub>D unit ?b \<star>\<^sub>D F f)"
            using assms D.objE [of "map\<^sub>0 (trg\<^sub>C f)"]
                  D.whisker_left [of "map\<^sub>0 ?b" "lF f" "unit ?b \<star>\<^sub>D F f"]
            by auto
          also have "... = (map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D
                             (D.inv (unit ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D (unit ?b \<star>\<^sub>D unit ?b \<star>\<^sub>D F f)"
          proof -
            have "(D.inv (unit ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D (unit ?b \<star>\<^sub>D unit ?b \<star>\<^sub>D F f) =
                  D.inv (unit ?b) \<cdot>\<^sub>D unit ?b \<star>\<^sub>D F ?b \<cdot>\<^sub>D unit ?b \<star>\<^sub>D F f \<cdot>\<^sub>D F f"
              using assms unit_char(1-2)
                    D.interchange [of "F ?b" "unit ?b" "F f" "F f"]
                    D.interchange [of "D.inv (unit ?b)" "unit ?b" "F ?b \<star>\<^sub>D F f" "unit ?b \<star>\<^sub>D F f"]
              by simp
            also have "... = map\<^sub>0 ?b \<star>\<^sub>D unit ?b \<star>\<^sub>D F f"
              using assms unit_char(1-2) [of ?b] D.comp_arr_dom D.comp_cod_arr D.comp_inv_arr
              by (simp add: D.inv_is_inverse)
            finally show ?thesis by simp
          qed
          also have "... =
                     (D.inv (unit ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (unit ?b \<star>\<^sub>D unit ?b \<star>\<^sub>D F f)"
          proof -
            have "(map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (D.inv (unit ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) =
                  (D.inv (unit ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
            proof -
              have "(map\<^sub>0 ?b \<star>\<^sub>D lF f) \<cdot>\<^sub>D (D.inv (unit ?b) \<star>\<^sub>D F ?b \<star>\<^sub>D F f) =
                    D.inv (unit ?b) \<star>\<^sub>D lF f"
                using assms unit_char(1-2) lF_char(1) D.comp_arr_dom D.comp_cod_arr
                      D.interchange [of "map\<^sub>0 ?b" "D.inv (unit ?b)" "lF f" "F ?b \<star>\<^sub>D F f"]
                by simp
              also have "... = D.inv (unit ?b) \<cdot>\<^sub>D F ?b \<star>\<^sub>D F f \<cdot>\<^sub>D lF f"
                using assms unit_char(1-2) lF_char(1) D.comp_arr_dom D.comp_cod_arr
                      D.inv_in_hom
                by auto
              also have "... = (D.inv (unit ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
                using assms unit_char(1-2) lF_char(1) D.inv_in_hom
                      D.interchange [of "D.inv (unit ?b)" "F ?b" "F f" "lF f"]
                by simp
              finally show ?thesis by simp
            qed
            thus ?thesis
              using assms unit_char(1-2) D.inv_in_hom D.comp_assoc by metis
          qed
          also have "... = (D.inv (unit ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f] \<cdot>\<^sub>D
                           (unit ?b \<star>\<^sub>D unit ?b \<star>\<^sub>D F f)"
            using assms unit_char(1-2) lF_char(2) D.comp_assoc by auto
          also have "... = ((D.inv (unit ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D
                           ((unit ?b \<star>\<^sub>D unit ?b) \<star>\<^sub>D F f)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 ?b, map\<^sub>0 ?b, F f]"
            using assms unit_char(1-2) D.assoc'_naturality [of "unit ?b" "unit ?b" "F f"] D.comp_assoc
            by (simp add: \<open>trg\<^sub>D (F f) = map\<^sub>0 (trg\<^sub>C f)\<close>)
          also have "... = (\<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[map\<^sub>0 ?b, map\<^sub>0 ?b, F f]"
          proof -
            have "((D.inv (unit ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D ((unit ?b \<star>\<^sub>D unit ?b) \<star>\<^sub>D F f)) =
                  \<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f"
            proof -
              have "((D.inv (unit ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D ((unit ?b \<star>\<^sub>D unit ?b) \<star>\<^sub>D F f)) =
                    D.inv (unit ?b) \<cdot>\<^sub>D unit ?b \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f"
                using assms 1 D.unit_in_hom D.whisker_right [of "F f"] unit_char(2-3)
                      D.invert_side_of_triangle(1)
                by (metis C.ideD(1) C.obj_trg D.seqI' map\<^sub>0_simps(1) unit_in_hom(2) preserves_ide)
              also have "... = \<i>\<^sub>D[map\<^sub>0 ?b] \<star>\<^sub>D F f"
              proof -
                have "(D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D unit (trg\<^sub>C f)) \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 ?b] = \<i>\<^sub>D[map\<^sub>0 ?b]"
                  by (simp add: D.comp_cod_arr D.comp_inv_arr D.inv_is_inverse unit_char(2)
                      assms)
                thus ?thesis
                  by (simp add: D.comp_assoc)
              qed
              finally show ?thesis by blast
            qed
            thus ?thesis by simp
          qed
          also have "... = map\<^sub>0 ?b \<star>\<^sub>D \<l>\<^sub>D[F f]"
            using assms D.lunit_char [of "F f"] \<open>trg\<^sub>D (F f) = map\<^sub>0 ?b\<close> by simp
          finally show ?thesis by blast
        qed
        ultimately show ?thesis
          using assms D.L.is_faithful
          by (metis D.trg_cod D.trg_vcomp D.vseq_implies_hpar(2) lF_simps(3))
      qed
      thus ?thesis
        using assms 1 unit_char(1-2) C.ideD(1) C.obj_trg D.inverse_arrows_hcomp(1)
              D.invert_side_of_triangle(2) D.lunit_simps(1) unit_simps(2) preserves_ide
              D.iso_hcomp components_are_iso
        by metis
    qed

    lemma lunit_coherence2:
    assumes "C.ide f"
    shows "lF f = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)"
    proof -
      let ?b = "trg\<^sub>C f"
      have "D.par (F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (?b, f)) (lF f)"
        using assms cmp_in_hom [of ?b f] lF_simps by auto
      moreover have "F ?b \<star>\<^sub>D F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (?b, f) = F ?b \<star>\<^sub>D lF f"
      proof -
        have "F ?b \<star>\<^sub>D F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (?b, f) = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D \<Phi> (?b, f))"
          using assms cmp_in_hom D.whisker_left [of "F ?b" "F \<l>\<^sub>C[f]" "\<Phi> (?b, f)"]
          by (simp add: calculation)
        also have "... = F ?b \<star>\<^sub>D lF f"
        proof -
          have "(F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D \<Phi> (?b, f))
                  = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D
                    \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
          proof -
            have 1: "D.seq (F \<a>\<^sub>C[trg\<^sub>C f, trg\<^sub>C f, f])
                           (\<Phi> (trg\<^sub>C f \<star>\<^sub>C trg\<^sub>C f, f) \<cdot>\<^sub>D (\<Phi> (trg\<^sub>C f, trg\<^sub>C f) \<star>\<^sub>D F f))"
              using assms by fastforce
            hence 2: "D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D
                         (\<Phi> (?b, ?b) \<star>\<^sub>D F f)
                        = (F ?b \<star>\<^sub>D \<Phi> (?b, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F ?b, F ?b, F f]"
              using assms cmp_in_hom assoc_coherence cmp_components_are_iso
                    D.invert_side_of_triangle(1)
                      [of "F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f)"
                          "\<Phi> (?b, ?b \<star>\<^sub>C f)"
                          "(F ?b \<star>\<^sub>D \<Phi> (?b, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F ?b, F ?b, F f]"]
                    C.ideD(1) C.ide_hcomp C.trg_hcomp C.trg_trg C.src_trg C.trg.preserves_ide
              by metis
            hence "F ?b \<star>\<^sub>D \<Phi> (?b, f)
                      = (D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D
                        (\<Phi> (?b, ?b) \<star>\<^sub>D F f)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            proof -
              have "D.seq (D.inv (\<Phi> (trg\<^sub>C f, trg\<^sub>C f \<star>\<^sub>C f)))
                          (F \<a>\<^sub>C[trg\<^sub>C f, trg\<^sub>C f, f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f \<star>\<^sub>C trg\<^sub>C f, f) \<cdot>\<^sub>D
                             (\<Phi> (trg\<^sub>C f, trg\<^sub>C f) \<star>\<^sub>D F f))"
                using assms 1 D.hseq_char by auto
              moreover have "(F (trg\<^sub>C f) \<star>\<^sub>D \<Phi> (trg\<^sub>C f, f)) \<cdot>\<^sub>D \<a>\<^sub>D[F (trg\<^sub>C f), F (trg\<^sub>C f), F f] =
                             D.inv (\<Phi> (trg\<^sub>C f, trg\<^sub>C f \<star>\<^sub>C f)) \<cdot>\<^sub>D
                               F \<a>\<^sub>C[trg\<^sub>C f, trg\<^sub>C f, f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f \<star>\<^sub>C trg\<^sub>C f, f) \<cdot>\<^sub>D
                               (\<Phi> (trg\<^sub>C f, trg\<^sub>C f) \<star>\<^sub>D F f)"
                using assms 2 by simp
              ultimately show ?thesis
                using assms
                      D.invert_side_of_triangle(2)
                        [of "D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D
                             (\<Phi> (?b, ?b) \<star>\<^sub>D F f)"
                            "F ?b \<star>\<^sub>D \<Phi> (?b, f)" "\<a>\<^sub>D[F ?b, F ?b, F f]"]
                by fastforce
            qed
            thus ?thesis
              using D.comp_assoc by simp
          qed
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           (D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D F (\<i>\<^sub>C[?b] \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           \<Phi> (?b \<star>\<^sub>C ?b, f) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
          proof -
            have 1: "F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) = F (\<i>\<^sub>C[?b] \<star>\<^sub>C f) \<cdot>\<^sub>D D.inv (F \<a>\<^sub>C[?b, ?b, f])"
              using assms C.lunit_char(1-2) C.unit_in_hom preserves_inv by auto
            have "F \<a>\<^sub>C[?b, ?b, f] = D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D F (\<i>\<^sub>C[?b] \<star>\<^sub>C f)"
            proof -
              have "F \<a>\<^sub>C[?b, ?b, f] \<cdot>\<^sub>D D.inv (F (\<i>\<^sub>C[?b] \<star>\<^sub>C f)) =
                    D.inv (F (\<i>\<^sub>C[?b] \<star>\<^sub>C f) \<cdot>\<^sub>D D.inv (F \<a>\<^sub>C[?b, ?b, f]))"
                using assms by (simp add: C.iso_unit D.inv_comp)
              thus ?thesis
                using assms 1 D.invert_side_of_triangle D.iso_inv_iso
                by (metis C.iso_hcomp C.ideD(1) C.ide_is_iso C.iso_lunit C.iso_unit
                    C.lunit_simps(3) C.obj_trg C.src_trg C.trg.components_are_iso
                    C.unit_simps(2) D.arr_inv D.inv_inv preserves_iso)
            qed
            thus ?thesis by argo
          qed
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D (F (\<i>\<^sub>C[?b] \<star>\<^sub>C f) \<cdot>\<^sub>D \<Phi> (?b \<star>\<^sub>C ?b, f)) \<cdot>\<^sub>D
                           (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using D.comp_assoc by auto
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D (\<Phi> (?b, f) \<cdot>\<^sub>D (F \<i>\<^sub>C[?b] \<star>\<^sub>D F f)) \<cdot>\<^sub>D
                           (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using assms \<Phi>.naturality [of "(\<i>\<^sub>C[?b], f)"] FF_def C.VV.arr_char C.VV.cod_char
                  C.VV.dom_char
            by simp
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f) \<cdot>\<^sub>D
                           ((F \<i>\<^sub>C[?b] \<star>\<^sub>D F f)) \<cdot>\<^sub>D (\<Phi> (?b, ?b) \<star>\<^sub>D F f) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using D.comp_assoc by auto
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D
                           D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f) \<cdot>\<^sub>D (\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D
                           \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f]"
            using assms by (simp add: D.comp_assoc D.whisker_right)
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D
                           (D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f)) \<cdot>\<^sub>D
                           (F ?b \<star>\<^sub>D lF f)"
          proof -
            have "(\<i> ?b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F ?b, F ?b, F f] = F ?b \<star>\<^sub>D lF f"
              using assms lF_char by auto
            thus ?thesis
              using assms D.inv_is_inverse \<i>_in_hom cmp_in_hom D.invert_side_of_triangle(2)
              by (simp add: D.comp_assoc)
          qed
          also have "... = (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
          proof -
            have "D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) =
                  D.inv (((F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f))) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
              using assms D.comp_inv_arr D.comp_inv_arr' cmp_simps(4)
                    D.comp_arr_dom D.comp_assoc
              by simp
            also have "... = D.inv (D.inv (\<Phi> (?b, f)) \<cdot>\<^sub>D F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
            proof -
              have 1: "\<Phi> (?b, f) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) = F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f)"
                using assms \<Phi>.naturality [of "(?b, \<l>\<^sub>C[f])"] FF_def C.VV.arr_char
                      C.VV.cod_char D.VV.null_char C.VV.dom_simp
                by simp
              have "(F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) =
                    D.inv (\<Phi> (?b, f)) \<cdot>\<^sub>D F (?b \<star>\<^sub>C \<l>\<^sub>C[f])"
              proof -
                have "D.seq (\<Phi> (?b, f)) (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f])"
                  using assms cmp_in_hom(2) [of ?b f] by auto
                moreover have "D.iso (\<Phi> (?b, f)) \<and> D.iso (\<Phi> (?b, ?b \<star>\<^sub>C f))"
                  using assms by simp
                ultimately show ?thesis
                using 1 D.invert_opposite_sides_of_square by simp
              qed
              thus ?thesis
                using D.comp_assoc by auto
            qed
            also have "... = D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D \<Phi> (?b, f)"
            proof -
              have "D.iso (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
                using assms D.isos_compose C.VV.arr_char C.iso_lunit C.VV.dom_simp
                      C.VV.cod_simp
                by simp
              moreover have "D.iso (D.inv (\<Phi> (?b, f)))"
                using assms by simp
              moreover have "D.seq (D.inv (\<Phi> (?b, f))) (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f))"
                using assms C.VV.arr_char C.VV.dom_simp C.VV.cod_simp by simp
              ultimately show ?thesis
                using assms D.inv_comp by simp
            qed
            also have "... = D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f)"
            proof -
              have "D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]) \<cdot>\<^sub>D \<Phi> (?b, ?b \<star>\<^sub>C f)) =
                    D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f]))"
                using assms D.isos_compose C.VV.arr_char C.iso_lunit D.inv_comp
                      C.VV.dom_simp C.VV.cod_simp
                by simp
              thus ?thesis using D.comp_assoc by simp
            qed
            finally have "D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f])
                            = D.inv (\<Phi> (?b, ?b \<star>\<^sub>C f)) \<cdot>\<^sub>D D.inv (F (?b \<star>\<^sub>C \<l>\<^sub>C[f])) \<cdot>\<^sub>D \<Phi> (?b, f)"
              by blast
            thus ?thesis by argo
          qed
          also have "... = ((F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]) \<cdot>\<^sub>D D.inv (F ?b \<star>\<^sub>D F \<l>\<^sub>C[f])) \<cdot>\<^sub>D (F ?b \<star>\<^sub>D lF f)"
            using D.comp_assoc by simp
          also have "... = F ?b \<star>\<^sub>D lF f"
            using assms D.comp_arr_inv' [of "F ?b \<star>\<^sub>D F \<l>\<^sub>C[f]"] D.comp_cod_arr by simp
          finally show ?thesis by simp
        qed
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis
        using assms D.L.is_faithful
        by (metis D.in_homI lF_char(2-3) lF_simps(4-5))
    qed

    lemma lunit_coherence:
    assumes "C.ide f"
    shows "\<l>\<^sub>D[F f] = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f)"
    proof -
      have 1: "\<l>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (unit (trg\<^sub>C f) \<star>\<^sub>D F f) = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)"
        using assms lunit_coherence1 lunit_coherence2 by simp
      have "\<l>\<^sub>D[F f] = (F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f)"
      proof -
        have "D.seq (F \<l>\<^sub>C[f]) (\<Phi> (trg\<^sub>C f, f))"
          using assms cmp_in_hom [of "trg\<^sub>C f" f] C.unit_in_vhom by auto
        moreover have "D.iso (D.inv (unit (trg\<^sub>C f) \<star>\<^sub>D F f))"
          using assms unit_char unit_char(1-2)
          by (simp add: preserves_hseq)
        ultimately show ?thesis
          using assms 1 unit_char(2) cmp_in_hom D.inv_inv
                D.invert_side_of_triangle(2)
                  [of "F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f)" "\<l>\<^sub>D[F f]" "D.inv (unit (trg\<^sub>C f) \<star>\<^sub>D F f)"]
          by auto
      qed
      thus ?thesis
        using assms unit_char(1) D.comp_assoc by auto
    qed

    text \<open>
      We postpone proving the dual version of this result until after we have developed
      the notion of the ``op bicategory'' in the next section.
    \<close>

  end

  subsection "Pseudofunctors and Opposite Bicategories"

  text \<open>
    There are three duals to a bicategory:
    \begin{enumerate}
      \item ``op'': sources and targets are exchanged;
      \item ``co'': domains and codomains are exchanged;
      \item ``co-op'': both sources and targets and domains and codomains are exchanged.
    \end{enumerate}
    Here we consider the "op" case.
  \<close>

  locale op_bicategory =
    B: bicategory V H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
  for V :: "'a comp"               (infixr "\<cdot>" 55)
  and H\<^sub>B :: "'a comp"              (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'a \<Rightarrow> 'a"              ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'a \<Rightarrow> 'a"
  and trg\<^sub>B :: "'a \<Rightarrow> 'a"
  begin

    abbreviation H  (infixr "\<star>" 53)
    where "H f g \<equiv> H\<^sub>B g f"

    abbreviation \<i>   ("\<i>[_]")
    where "\<i> \<equiv> \<i>\<^sub>B"

    abbreviation src
    where "src \<equiv> trg\<^sub>B"

    abbreviation trg
    where "trg \<equiv> src\<^sub>B"

    interpretation horizontal_homs V src trg
      by (unfold_locales, auto)

    interpretation H: "functor" VV.comp V \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close>
      using VV.arr_char VV.dom_simp VV.cod_simp
      apply unfold_locales
          apply (metis (no_types, lifting) B.hseqE B.hseq_char')
         apply auto[3]
      using VV.comp_char VV.seq_char VV.arr_char B.VxV.comp_char B.interchange
      by (metis (no_types, lifting) B.VxV.seqE fst_conv snd_conv)

    interpretation horizontal_composition V H src trg
      by (unfold_locales, auto)

    abbreviation UP
    where "UP \<mu>\<nu>\<tau> \<equiv> if B.VVV.arr \<mu>\<nu>\<tau> then
                       (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)
                    else VVV.null"

    abbreviation DN
    where "DN \<mu>\<nu>\<tau> \<equiv> if VVV.arr \<mu>\<nu>\<tau> then
                         (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)
                      else B.VVV.null"

    lemma VVV_arr_char:
    shows "VVV.arr \<mu>\<nu>\<tau> \<longleftrightarrow> B.VVV.arr (DN \<mu>\<nu>\<tau>)"
      using VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char B.VVV.not_arr_null
      by auto

    lemma VVV_ide_char:
    shows "VVV.ide \<mu>\<nu>\<tau> \<longleftrightarrow> B.VVV.ide (DN \<mu>\<nu>\<tau>)"
    proof -
      have "VVV.ide \<mu>\<nu>\<tau> \<longleftrightarrow> VVV.arr \<mu>\<nu>\<tau> \<and> B.VxVxV.ide \<mu>\<nu>\<tau>"
        using VVV.ide_char by simp
      also have "... \<longleftrightarrow> B.VVV.arr (DN \<mu>\<nu>\<tau>) \<and> B.VxVxV.ide (DN \<mu>\<nu>\<tau>)"
        using VVV_arr_char B.VxVxV.ide_char by auto
      also have "... \<longleftrightarrow> B.VVV.ide (DN \<mu>\<nu>\<tau>)"
        using B.VVV.ide_char [of "DN \<mu>\<nu>\<tau>"] by blast
      finally show ?thesis by fast
    qed

    lemma VVV_dom_char:
    shows "VVV.dom \<mu>\<nu>\<tau> = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
    proof (cases "VVV.arr \<mu>\<nu>\<tau>")
      show "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.dom \<mu>\<nu>\<tau> = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
        using VVV.dom_def VVV.has_domain_iff_arr VVV_arr_char B.VVV.dom_null
        by auto
      show "VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.dom \<mu>\<nu>\<tau> = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
      proof -
        assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
        have "VVV.dom \<mu>\<nu>\<tau> =
              (B.dom (fst \<mu>\<nu>\<tau>), B.dom (fst (snd \<mu>\<nu>\<tau>)), B.dom (snd (snd \<mu>\<nu>\<tau>)))"
          using \<mu>\<nu>\<tau> VVV.dom_char VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char
          by simp
        also have "... = UP (B.dom (snd (snd \<mu>\<nu>\<tau>)), B.dom (fst (snd \<mu>\<nu>\<tau>)), B.dom (fst \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> VVV_arr_char B.VV.arr_char B.VVV.arr_char B.arr_dom_iff_arr src_dom
                trg_dom
          apply simp
          by (metis (no_types, lifting) src_dom trg_dom VV.arrE VVV.arrE)
        also have "... = UP (B.VVV.dom (DN \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> B.VVV.dom_char B.VVV.arr_char B.VV.arr_char VVV.arr_char VV.arr_char
          by simp
        finally show ?thesis by blast
      qed
    qed

    lemma VVV_cod_char:
    shows "VVV.cod \<mu>\<nu>\<tau> = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
    proof (cases "VVV.arr \<mu>\<nu>\<tau>")
      show "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.cod \<mu>\<nu>\<tau> = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
        using VVV.cod_def VVV.has_codomain_iff_arr VVV_arr_char B.VVV.cod_null
        by auto
      show "VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> VVV.cod \<mu>\<nu>\<tau> = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
      proof -
        assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
        have "VVV.cod \<mu>\<nu>\<tau> = (B.cod (fst \<mu>\<nu>\<tau>), B.cod (fst (snd \<mu>\<nu>\<tau>)), B.cod (snd (snd \<mu>\<nu>\<tau>)))"
          using \<mu>\<nu>\<tau> VVV.cod_char VVV.arr_char VV.arr_char B.VVV.arr_char B.VV.arr_char
          by simp
        also have "... = UP (B.cod (snd (snd \<mu>\<nu>\<tau>)), B.cod (fst (snd \<mu>\<nu>\<tau>)), B.cod (fst \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> VVV_arr_char B.VV.arr_char B.VVV.arr_char
          apply simp
          by (metis (no_types, lifting) B.arr_cod_iff_arr src_cod trg_cod VV.arrE VVV.arrE)
        also have "... = UP (B.VVV.cod (DN \<mu>\<nu>\<tau>))"
          using \<mu>\<nu>\<tau> B.VVV.cod_char B.VVV.arr_char B.VV.arr_char VVV.arr_char VV.arr_char
          by simp
        finally show ?thesis by blast
      qed
    qed

    lemma HoHV_char:
    shows "HoHV \<mu>\<nu>\<tau> = B.HoVH (DN \<mu>\<nu>\<tau>)"
     using HoHV_def B.HoVH_def VVV_arr_char by simp

    lemma HoVH_char:
    shows "HoVH \<mu>\<nu>\<tau> = B.HoHV (DN \<mu>\<nu>\<tau>)"
      using HoVH_def B.HoHV_def VVV_arr_char by simp

    definition \<a>   ("\<a>[_, _, _]")
    where "\<a>[\<mu>, \<nu>, \<tau>] \<equiv> B.\<alpha>' (DN (\<mu>, \<nu>, \<tau>))"

    interpretation natural_isomorphism VVV.comp \<open>(\<cdot>)\<close> HoHV HoVH
                     \<open>\<lambda>\<mu>\<nu>\<tau>. \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]\<close>
    proof
      fix \<mu>\<nu>\<tau>
      show "\<not> VVV.arr \<mu>\<nu>\<tau> \<Longrightarrow> \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)] = B.null"
        using VVV.arr_char B.VVV.arr_char \<a>_def B.\<alpha>'.is_extensional by auto
      assume \<mu>\<nu>\<tau>: "VVV.arr \<mu>\<nu>\<tau>"
      show "B.dom \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)] = HoHV (VVV.dom \<mu>\<nu>\<tau>)"
        using \<mu>\<nu>\<tau> \<a>_def HoHV_def B.\<alpha>'.preserves_dom VVV.arr_char VVV.dom_char VV.arr_char
              B.HoVH_def B.VVV.arr_char B.VV.arr_char B.VVV.dom_char
        by auto
      show "B.cod \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)] = HoVH (VVV.cod \<mu>\<nu>\<tau>)"
        using \<mu>\<nu>\<tau> \<a>_def HoVH_def B.\<alpha>'.preserves_cod VVV.arr_char VVV.cod_char VV.arr_char
              B.HoHV_def B.VVV.arr_char B.VV.arr_char B.VVV.cod_char
        by auto
      show "HoVH \<mu>\<nu>\<tau> \<cdot>
              \<a>[fst (VVV.dom \<mu>\<nu>\<tau>), fst (snd (VVV.dom \<mu>\<nu>\<tau>)), snd (snd (VVV.dom \<mu>\<nu>\<tau>))] =
            \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
      proof -
        have "HoVH \<mu>\<nu>\<tau> \<cdot>
                \<a>[fst (VVV.dom \<mu>\<nu>\<tau>), fst (snd (VVV.dom \<mu>\<nu>\<tau>)), snd (snd (VVV.dom \<mu>\<nu>\<tau>))] =
              HoVH \<mu>\<nu>\<tau> \<cdot> B.\<alpha>' (B.VVV.dom (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>))"
          unfolding \<a>_def
          using \<mu>\<nu>\<tau> VVV.arr_char VV.arr_char VVV.dom_char B.VVV.arr_char B.VVV.dom_char
          by auto
        also have "... = B.\<alpha>' (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)"
          using B.\<alpha>'.is_natural_1 VVV_arr_char \<mu>\<nu>\<tau> HoVH_char by presburger
        also have "... = \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
          using \<mu>\<nu>\<tau> \<a>_def by simp
        finally show ?thesis by blast
      qed
      show "\<a>[fst (VVV.cod \<mu>\<nu>\<tau>), fst (snd (VVV.cod \<mu>\<nu>\<tau>)), snd (snd (VVV.cod \<mu>\<nu>\<tau>))] \<cdot>
              HoHV \<mu>\<nu>\<tau> =
            \<a> (fst \<mu>\<nu>\<tau>) (fst (snd \<mu>\<nu>\<tau>)) (snd (snd \<mu>\<nu>\<tau>))"
      proof -
        have "\<a>[fst (VVV.cod \<mu>\<nu>\<tau>), fst (snd (VVV.cod \<mu>\<nu>\<tau>)), snd (snd (VVV.cod \<mu>\<nu>\<tau>))] \<cdot>
                HoHV \<mu>\<nu>\<tau> =
              B.\<alpha>' (B.VVV.cod (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)) \<cdot> HoHV \<mu>\<nu>\<tau>"
          unfolding \<a>_def
          using \<mu>\<nu>\<tau> VVV.arr_char VV.arr_char VVV.cod_char B.VVV.arr_char B.VVV.cod_char
          by auto
        also have "... = B.\<alpha>' (snd (snd \<mu>\<nu>\<tau>), fst (snd \<mu>\<nu>\<tau>), fst \<mu>\<nu>\<tau>)"
          using B.\<alpha>'.is_natural_2 VVV_arr_char \<mu>\<nu>\<tau> HoHV_char by presburger
        also have "... = \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
          using \<mu>\<nu>\<tau> \<a>_def by simp
        finally show ?thesis by blast
      qed
      next
      fix \<mu>\<nu>\<tau>
      assume \<mu>\<nu>\<tau>: "VVV.ide \<mu>\<nu>\<tau>"
      show "B.iso \<a>[fst \<mu>\<nu>\<tau>, fst (snd \<mu>\<nu>\<tau>), snd (snd \<mu>\<nu>\<tau>)]"
      proof -
        have "B.VVV.ide (DN \<mu>\<nu>\<tau>)"
          using \<mu>\<nu>\<tau> VVV_ide_char by blast
        thus ?thesis
          using \<mu>\<nu>\<tau> \<a>_def B.\<alpha>'.components_are_iso by force
      qed
    qed

    sublocale bicategory V H \<a> \<i> src trg
    proof
      show "\<And>a. obj a \<Longrightarrow> \<guillemotleft>\<i> a : H a a \<rightarrow>\<^sub>B a\<guillemotright>"
        using obj_def objE B.obj_def B.objE B.unit_in_hom by meson
      show "\<And>a. obj a \<Longrightarrow> B.iso (\<i> a)"
        using obj_def objE B.obj_def B.objE B.iso_unit by meson
      show "\<And>f g h k. \<lbrakk> B.ide f; B.ide g; B.ide h; B.ide k;
                        src f = trg g; src g = trg h; src h = trg k \<rbrakk> \<Longrightarrow>
              (f \<star> \<a>[g, h, k]) \<cdot> \<a>[f, g \<star> h, k] \<cdot> (\<a>[f, g, h] \<star> k) = \<a>[f, g, h \<star> k] \<cdot> \<a>[f \<star> g, h, k]"
        unfolding \<a>_def
        using B.\<a>'_def B.comp_assoc B.pentagon' VVV.arr_char VV.arr_char by simp
    qed

    proposition is_bicategory:
    shows "bicategory V H \<a> \<i> src trg"
      ..

    lemma assoc_ide_simp:
    assumes "B.ide f" and "B.ide g" and "B.ide h"
    and "src f = trg g" and "src g = trg h"
    shows "\<a>[f, g, h] = B.\<a>' h g f"
      using assms \<a>_def B.\<a>'_def by fastforce

    lemma lunit_ide_simp:
    assumes "B.ide f"
    shows "lunit f = B.runit f"
    proof (intro B.runit_eqI)
      show "B.ide f" by fact
      show "\<guillemotleft>lunit f : H (trg f) f \<rightarrow>\<^sub>B f\<guillemotright>"
        using assms by simp
      show "trg f \<star> lunit f = (\<i>[trg f] \<star> f) \<cdot> \<a>\<^sub>B[f, trg f, trg f]"
      proof -
        have "trg f \<star> lunit f = (\<i>[trg f] \<star> f) \<cdot> \<a>' (trg f) (trg f) f"
          using assms lunit_char(1-2) [of f] by simp
        moreover have "\<a>' (trg f) (trg f) f = \<a>\<^sub>B[f, trg f, trg f]"
        proof (unfold \<a>'_def)
          have 1: "VVV.ide (trg f, trg f, f)"
            using assms VVV.ide_char VVV.arr_char VV.arr_char by simp
          have "\<alpha>' (trg f, trg f, f) = B.inv \<a>[trg f, trg f, f]"
            using 1 B.\<alpha>'.inverts_components by simp
          also have "... = B.inv (B.\<alpha>' (f, trg f, trg f))"
            unfolding \<a>_def using 1 by simp
          also have "... = \<a>\<^sub>B[f, trg f, trg f]"
            using 1 B.VVV.ide_char B.VVV.arr_char B.VV.arr_char VVV.ide_char
                  VVV.arr_char VV.arr_char B.\<alpha>'.inverts_components B.\<alpha>_def
            by force
          finally show "\<alpha>' (trg f, trg f, f) = \<a>\<^sub>B[f, trg f, trg f]"
            by blast
        qed
        ultimately show ?thesis by simp
      qed
    qed

    lemma runit_ide_simp:
    assumes "B.ide f"
    shows "runit f = B.lunit f"
      using assms runit_char(1-2) [of f] B.\<a>'_def assoc_ide_simp
      by (intro B.lunit_eqI) auto

  end

  context pseudofunctor
  begin

    interpretation C': op_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C ..
    interpretation D': op_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D ..

    notation C'.H  (infixr "\<star>\<^sub>C\<^sup>o\<^sup>p" 53)
    notation D'.H  (infixr "\<star>\<^sub>D\<^sup>o\<^sup>p" 53)

    interpretation F': weak_arrow_of_homs V\<^sub>C C'.src C'.trg V\<^sub>D D'.src D'.trg F
      apply unfold_locales
      using weakly_preserves_src weakly_preserves_trg by simp_all
    interpretation H\<^sub>D'oFF: composite_functor C'.VV.comp D'.VV.comp V\<^sub>D F'.FF
                             \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D\<^sup>o\<^sup>p snd \<mu>\<nu>\<close> ..
    interpretation FoH\<^sub>C': composite_functor C'.VV.comp V\<^sub>C V\<^sub>D
                             \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>C\<^sup>o\<^sup>p snd \<mu>\<nu>\<close> F
      ..
    interpretation \<Phi>': natural_isomorphism C'.VV.comp V\<^sub>D H\<^sub>D'oFF.map FoH\<^sub>C'.map
                                           \<open>\<lambda>f. \<Phi> (snd f, fst f)\<close>
      using C.VV.arr_char C'.VV.arr_char C'.VV.ide_char C.VV.ide_char FF_def F'.FF_def
            \<Phi>.is_extensional \<Phi>.is_natural_1 \<Phi>.is_natural_2
            C.VV.dom_simp C.VV.cod_simp C'.VV.dom_simp C'.VV.cod_simp
      apply unfold_locales by auto
    interpretation F': pseudofunctor V\<^sub>C C'.H C'.\<a> \<i>\<^sub>C C'.src C'.trg
                                     V\<^sub>D D'.H D'.\<a> \<i>\<^sub>D D'.src D'.trg
                                     F \<open>\<lambda>f. \<Phi> (snd f, fst f)\<close>
    proof
      fix f g h
      assume f: "C.ide f" and g: "C.ide g" and h: "C.ide h"
      and fg: "C'.src f = C'.trg g" and gh: "C'.src g = C'.trg h"
      show "F (C'.\<a> f g h) \<cdot>\<^sub>D \<Phi> (snd (f \<star>\<^sub>C\<^sup>o\<^sup>p g, h), fst (f \<star>\<^sub>C\<^sup>o\<^sup>p g, h)) \<cdot>\<^sub>D
              (\<Phi> (snd (f, g), fst (f, g)) \<star>\<^sub>D\<^sup>o\<^sup>p F h) =
            \<Phi> (snd (f, g \<star>\<^sub>C\<^sup>o\<^sup>p h), fst (f, g \<star>\<^sub>C\<^sup>o\<^sup>p h)) \<cdot>\<^sub>D (F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (snd (g, h), fst (g, h))) \<cdot>\<^sub>D
              D'.\<a> (F f) (F g) (F h)"
        using f g h fg gh C.VV.in_hom_char FF_def C.VV.arr_char C.VV.dom_simp C.VV.cod_simp
              C'.assoc_ide_simp D'.assoc_ide_simp preserves_inv assoc_coherence
              D.invert_opposite_sides_of_square
                [of "F (\<a>\<^sub>C h g f)" "\<Phi> (g \<star>\<^sub>C\<^sup>o\<^sup>p h, f) \<cdot>\<^sub>D (F f \<star>\<^sub>D\<^sup>o\<^sup>p \<Phi> (h, g))"
                    "\<Phi> (h, f \<star>\<^sub>C\<^sup>o\<^sup>p g) \<cdot>\<^sub>D (\<Phi> (g, f) \<star>\<^sub>D\<^sup>o\<^sup>p F h)" "\<a>\<^sub>D (F h) (F g) (F f)"]
              D.comp_assoc
        by auto
    qed

    lemma induces_pseudofunctor_between_opposites:
    shows "pseudofunctor (\<cdot>\<^sub>C) (\<star>\<^sub>C\<^sup>o\<^sup>p) C'.\<a> \<i>\<^sub>C C'.src C'.trg
                         (\<cdot>\<^sub>D) (\<star>\<^sub>D\<^sup>o\<^sup>p) D'.\<a> \<i>\<^sub>D D'.src D'.trg
                         F (\<lambda>f. \<Phi> (snd f, fst f))"
      ..

    text \<open>
      It is now easy to dualize the coherence condition for \<open>F\<close> with respect to
      left unitors to obtain the corresponding condition for right unitors.
    \<close>

    lemma runit_coherence:
    assumes "C.ide f"
    shows "\<r>\<^sub>D[F f] = F \<r>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f))"
    proof -
      have "C'.lunit f = \<r>\<^sub>C[f]"
        using assms C'.lunit_ide_simp by simp
      moreover have "D'.lunit (F f) = \<r>\<^sub>D[F f]"
        using assms D'.lunit_ide_simp by simp
      moreover have "F'.unit (src\<^sub>C f) = unit (src\<^sub>C f)"
        using assms F'.unit_char F'.preserves_trg
        by (intro unit_eqI, auto)
      moreover have "D'.lunit (F f) =
                     F (C'.lunit f) \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D F'.unit (src\<^sub>C f))"
        using assms F'.lunit_coherence by simp
      ultimately show ?thesis by simp
    qed

  end

  subsection "Preservation Properties"

  text \<open>
    The objective of this section is to establish explicit formulas for the result
    of applying a pseudofunctor to expressions of various forms.
  \<close>

  context pseudofunctor
  begin

    lemma preserves_lunit:
    assumes "C.ide f"
    shows "F \<l>\<^sub>C[f] = \<l>\<^sub>D[F f] \<cdot>\<^sub>D (D.inv (unit (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f))"
    and "F \<l>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]"
    proof -
      have "\<l>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f)) = F \<l>\<^sub>C[f]"
      proof -
        have "D.arr \<l>\<^sub>D[F f]"
          using assms by simp
        moreover have "\<l>\<^sub>D[F f] = F \<l>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f)"
          using assms lunit_coherence by simp
        moreover have "D.iso (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f))"
          using assms unit_char cmp_components_are_iso
          by (intro D.isos_compose D.seqI) auto
        ultimately show ?thesis
          using assms D.invert_side_of_triangle(2) by metis
      qed
      moreover have "D.inv (\<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f)) =
                      (D.inv (unit (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f))"
        using assms C.VV.arr_char unit_char FF_def D.inv_comp C.VV.dom_simp by simp
      ultimately show "F \<l>\<^sub>C[f] =
                       \<l>\<^sub>D[F f] \<cdot>\<^sub>D (D.inv (unit (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f))"
        by simp
      hence "F \<l>\<^sub>C\<^sup>-\<^sup>1[f] =
             D.inv (\<l>\<^sub>D[F f] \<cdot>\<^sub>D (D.inv (unit (trg\<^sub>C f)) \<star>\<^sub>D F f) \<cdot>\<^sub>D D.inv (\<Phi> (trg\<^sub>C f, f)))"
        using assms preserves_inv by simp
      also have "... = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]"
        using assms unit_char D.comp_assoc D.isos_compose
        by (auto simp add: D.inv_comp)
      finally show "F \<l>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (trg\<^sub>C f, f) \<cdot>\<^sub>D (unit (trg\<^sub>C f) \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f]"
        by simp
    qed

    lemma preserves_runit:
    assumes "C.ide f"
    shows "F \<r>\<^sub>C[f] = \<r>\<^sub>D[F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (unit (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
    and "F \<r>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f]"
    proof -
      have "F \<r>\<^sub>C[f] = \<r>\<^sub>D[F f] \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f)))"
      proof -
        have "\<r>\<^sub>D[F f] = F \<r>\<^sub>C[f] \<cdot>\<^sub>D \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f))"
          using assms runit_coherence by simp
        moreover have "D.iso (\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f)))"
          using assms unit_char D.iso_hcomp FF_def
          apply (intro D.isos_compose D.seqI) by auto
        moreover have "D.arr \<r>\<^sub>D[F f]"
          using assms by simp
        ultimately show ?thesis
          using assms D.invert_side_of_triangle(2) by metis
      qed
      moreover have "D.inv (\<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f))) =
                      (F f \<star>\<^sub>D D.inv (unit (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
        using assms C.VV.arr_char unit_char D.iso_hcomp FF_def D.inv_comp C.VV.dom_simp
        by simp
      ultimately show "F \<r>\<^sub>C[f] =
                       \<r>\<^sub>D[F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (unit (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f))"
        by simp
      hence "F \<r>\<^sub>C\<^sup>-\<^sup>1[f] =
             D.inv (\<r>\<^sub>D[F f] \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv (unit (src\<^sub>C f))) \<cdot>\<^sub>D D.inv (\<Phi> (f, src\<^sub>C f)))"
        using assms preserves_inv C.iso_runit by simp
      also have "... = \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f]"
        using assms unit_char D.comp_assoc D.isos_compose
        by (auto simp add: D.inv_comp)
      finally show "F \<r>\<^sub>C\<^sup>-\<^sup>1[f] = \<Phi> (f, src\<^sub>C f) \<cdot>\<^sub>D (F f \<star>\<^sub>D unit (src\<^sub>C f)) \<cdot>\<^sub>D \<r>\<^sub>D\<^sup>-\<^sup>1[F f]"
        by simp
    qed

    lemma preserves_assoc:
    assumes "C.ide f" and "C.ide g" and "C.ide h"
    and "src\<^sub>C f = trg\<^sub>C g" and "src\<^sub>C g = trg\<^sub>C h"
    shows "F \<a>\<^sub>C[f, g, h] = \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h] \<cdot>\<^sub>D
                            (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
    and "F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, h] = \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F h] \<cdot>\<^sub>D
                            (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
    proof -
      have "F \<a>\<^sub>C[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) =
            \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
        using assms assoc_coherence [of f g h] by simp
      moreover have "D.seq (\<Phi> (f, g \<star>\<^sub>C h)) ((F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h])"
        using assms C.VV.arr_char FF_def C.VV.dom_simp C.VV.cod_simp by auto
      moreover have 1: "D.iso (\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h))"
        using assms C.VV.arr_char FF_def C.VV.dom_simp C.VV.cod_simp by auto
      moreover have "D.inv (\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h)) =
                    (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
        using assms 1 C.VV.arr_char FF_def D.inv_comp C.VV.dom_simp C.VV.cod_simp
        by simp
      ultimately show 1: "F \<a>\<^sub>C[f, g, h] =
                          \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h] \<cdot>\<^sub>D
                            (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h))"
        using D.invert_side_of_triangle(2)
                [of "\<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
                    "F \<a>\<^sub>C[f, g, h]" "\<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h)"]
              D.comp_assoc
        by simp
      hence "F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, h] =
             D.inv (\<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h] \<cdot>\<^sub>D
               (D.inv (\<Phi> (f, g)) \<star>\<^sub>D F h) \<cdot>\<^sub>D D.inv (\<Phi> (f \<star>\<^sub>C g, h)))"
        using assms preserves_inv by simp
      also have "... = \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F h] \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
      proof -
        have "\<guillemotleft>\<Phi> (f, g \<star>\<^sub>C h) : F f \<star>\<^sub>D F (g \<star>\<^sub>C h) \<Rightarrow>\<^sub>D F (f \<star>\<^sub>C g \<star>\<^sub>C h)\<guillemotright> \<and> D.iso (\<Phi> (f, g \<star>\<^sub>C h))"
          using assms by auto
        moreover have "\<guillemotleft>F f \<star>\<^sub>D \<Phi> (g, h) : F f \<star>\<^sub>D F g \<star>\<^sub>D F h \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F (g \<star>\<^sub>C h)\<guillemotright> \<and>
                       D.iso (F f \<star>\<^sub>D \<Phi> (g, h))"
          using assms
          by (intro conjI D.hcomp_in_vhom, auto)
        ultimately show ?thesis
          using assms D.isos_compose D.comp_assoc
          by (elim conjE D.in_homE) (auto simp add: D.inv_comp)
      qed
      finally show "F \<a>\<^sub>C\<^sup>-\<^sup>1[f, g, h] =
                    \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, F g, F h] \<cdot>\<^sub>D
                      (F f \<star>\<^sub>D D.inv (\<Phi> (g, h))) \<cdot>\<^sub>D D.inv (\<Phi> (f, g \<star>\<^sub>C h))"
        by simp
    qed

    lemma preserves_hcomp:
    assumes "C.hseq \<mu> \<nu>"
    shows "F (\<mu> \<star>\<^sub>C \<nu>) =
           \<Phi> (C.cod \<mu>, C.cod \<nu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D F \<nu>) \<cdot>\<^sub>D D.inv (\<Phi> (C.dom \<mu>, C.dom \<nu>))"
    proof -
      have "F (\<mu> \<star>\<^sub>C \<nu>) \<cdot>\<^sub>D \<Phi> (C.dom \<mu>, C.dom \<nu>) = \<Phi> (C.cod \<mu>, C.cod \<nu>) \<cdot>\<^sub>D (F \<mu> \<star>\<^sub>D F \<nu>)"
        using assms \<Phi>.naturality C.VV.arr_char C.VV.cod_char FF_def C.VV.dom_simp
        by auto
      thus ?thesis
        by (metis (no_types) assms C.hcomp_simps(3) C.hseqE C.ide_dom C.src_dom C.trg_dom
            D.comp_arr_inv' D.comp_assoc cmp_components_are_iso cmp_simps(5) is_natural_1)
    qed

    lemma preserves_adjunction_data:
    assumes "adjunction_data_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    shows "adjunction_data_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             (F f) (F g) (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f))
             (D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    proof
      interpret adjunction_data_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using assms by auto
      show "D.ide (F f)"
        using preserves_ide by simp
      show "D.ide (F g)"
        using preserves_ide by simp
      show "\<guillemotleft>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f) : src\<^sub>D (F f) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F f\<guillemotright>"
        using antipar C.VV.ide_char C.VV.arr_char cmp_in_hom(2) unit_in_hom FF_def by auto
      show "\<guillemotleft>D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) : F f \<star>\<^sub>D F g \<Rightarrow>\<^sub>D src\<^sub>D (F g)\<guillemotright>"
        using antipar C.VV.ide_char C.VV.arr_char FF_def cmp_in_hom(2) unit_in_hom(2)
              unit_char(2)
        by auto
    qed

    lemma preserves_equivalence:
    assumes "equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    shows "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             (F f) (F g) (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f))
             (D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    proof -
      interpret equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using assms by auto
      show "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
             (F f) (F g) (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f))
             (D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
        using antipar unit_is_iso preserves_iso unit_char(2) C.VV.ide_char C.VV.arr_char
              FF_def D.isos_compose
        by (unfold_locales) auto
    qed

    lemma preserves_equivalence_maps:
    assumes "C.equivalence_map f"
    shows "D.equivalence_map (F f)"
    proof -
      obtain g \<eta> \<epsilon> where E: "equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
        using assms C.equivalence_map_def by auto
      interpret E: equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>
        using E by auto
      show ?thesis
        using E preserves_equivalence C.equivalence_map_def D.equivalence_map_def map\<^sub>0_simps
        by blast
    qed

    lemma preserves_equivalent_objects:
    assumes "C.equivalent_objects a b"
    shows "D.equivalent_objects (map\<^sub>0 a) (map\<^sub>0 b)"
      using assms D.equivalent_objects_def preserves_equivalence_maps
      unfolding C.equivalent_objects_def by fast

    lemma preserves_isomorphic:
    assumes "C.isomorphic f g"
    shows "D.isomorphic (F f) (F g)"
      using assms C.isomorphic_def D.isomorphic_def preserves_iso by auto

    lemma preserves_quasi_inverses:
    assumes "C.quasi_inverses f g"
    shows "D.quasi_inverses (F f) (F g)"
      using assms C.quasi_inverses_def D.quasi_inverses_def preserves_equivalence by blast

    lemma preserves_quasi_inverse:
    assumes "C.equivalence_map f"
    shows "D.isomorphic (F (C.some_quasi_inverse f)) (D.some_quasi_inverse (F f))"
      using assms preserves_quasi_inverses C.quasi_inverses_some_quasi_inverse
            D.quasi_inverse_unique D.quasi_inverses_some_quasi_inverse
            preserves_equivalence_maps
      by blast

  end

  subsection "Identity Pseudofunctors"

  locale identity_pseudofunctor =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
  for V\<^sub>B :: "'b comp"                    (infixr "\<cdot>\<^sub>B" 55)
  and H\<^sub>B :: "'b comp"                   (infixr "\<star>\<^sub>B" 53)
  and \<a>\<^sub>B :: "'b \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b"       ("\<a>\<^sub>B[_, _, _]")
  and \<i>\<^sub>B :: "'b \<Rightarrow> 'b"                   ("\<i>\<^sub>B[_]")
  and src\<^sub>B :: "'b \<Rightarrow> 'b"
  and trg\<^sub>B :: "'b \<Rightarrow> 'b"
  begin

    text\<open>
      The underlying vertical functor is just the identity functor on the vertical category,
      which is already available as \<open>B.map\<close>.
    \<close>

    abbreviation map
    where "map \<equiv> B.map"

    interpretation I: weak_arrow_of_homs V\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B src\<^sub>B trg\<^sub>B map
    proof
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> B.isomorphic (map (src\<^sub>B \<mu>)) (src\<^sub>B (map \<mu>))"
        by (simp add: B.isomorphic_reflexive)
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> B.isomorphic (map (trg\<^sub>B \<mu>)) (trg\<^sub>B (map \<mu>))"
        by (simp add: B.isomorphic_reflexive)
    qed

    interpretation II: "functor" B.VV.comp B.VV.comp I.FF
      using I.functor_FF by simp

    interpretation H\<^sub>BoII: composite_functor B.VV.comp B.VV.comp V\<^sub>B I.FF
                            \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close>
      ..
    interpretation IoH\<^sub>B: composite_functor B.VV.comp V\<^sub>B V\<^sub>B \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close> map
      ..

    text\<open>
      The horizontal composition provides the compositor.
    \<close>

    abbreviation cmp
    where "cmp \<equiv> \<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>"

    interpretation cmp: natural_transformation B.VV.comp V\<^sub>B H\<^sub>BoII.map IoH\<^sub>B.map cmp
      using B.VV.arr_char B.VV.dom_simp B.VV.cod_simp B.H.is_natural_1 B.H.is_natural_2
            I.FF_def
      apply unfold_locales
          apply auto
      by (meson B.hseqE B.hseq_char')+

    interpretation cmp: natural_isomorphism B.VV.comp V\<^sub>B H\<^sub>BoII.map IoH\<^sub>B.map cmp
      by unfold_locales simp

    sublocale pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B map cmp
      apply unfold_locales
      by (metis B.assoc_is_natural_2 B.assoc_naturality B.assoc_simps(1) B.comp_ide_self
          B.hcomp_simps(1) B.ide_char B.ide_hcomp B.map_simp fst_conv snd_conv)

    lemma is_pseudofunctor:
    shows "pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B map cmp"
      ..

    lemma unit_char':
    assumes "B.obj a"
    shows "unit a = a"
    proof -
      have "src\<^sub>B a = a \<and> B.ide a"
        using assms by auto
      hence "a = unit a"
        using assms B.comp_arr_dom B.comp_cod_arr I.map\<^sub>0_def map_def
              B.ide_in_hom(2) B.objE [of a] B.ide_is_iso [of a]
        by (intro unit_eqI) auto
      thus ?thesis by simp
    qed

  end

  lemma (in identity_pseudofunctor) map\<^sub>0_simp [simp]:
  assumes "B.obj a"
  shows "map\<^sub>0 a = a"
    using assms map\<^sub>0_def by auto
    (* TODO: Does not recognize map\<^sub>0_def unless the context is closed, then re-opened. *)

  subsection "Embedding Pseudofunctors"

  text \<open>
    In this section, we construct the embedding pseudofunctor of a sub-bicategory
    into the ambient bicategory.
  \<close>

  locale embedding_pseudofunctor =
    B: bicategory V H \<a>\<^sub>B \<i> src\<^sub>B trg\<^sub>B +
    S: subbicategory
  begin

    no_notation B.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")
    notation B.in_hhom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    definition map
    where "map \<mu> = (if S.arr \<mu> then \<mu> else B.null)"

    lemma map_in_hom [intro]:
    assumes "S.arr \<mu>"
    shows "\<guillemotleft>map \<mu> : src\<^sub>B (map (S.src \<mu>)) \<rightarrow>\<^sub>B src\<^sub>B (map (S.trg \<mu>))\<guillemotright>"
    and "\<guillemotleft>map \<mu> : map (S.dom \<mu>) \<Rightarrow>\<^sub>B map (S.cod \<mu>)\<guillemotright>"
    proof -
      show 1: "\<guillemotleft>map \<mu> : map (S.dom \<mu>) \<Rightarrow>\<^sub>B map (S.cod \<mu>)\<guillemotright>"
        using assms map_def S.in_hom_char by fastforce
      show "\<guillemotleft>map \<mu> : src\<^sub>B (map (S.src \<mu>)) \<rightarrow>\<^sub>B src\<^sub>B (map (S.trg \<mu>))\<guillemotright>"
        using assms 1 map_def S.arr_char S.src_def S.trg_def S.obj_char S.obj_src S.obj_trg
        by auto
    qed

    lemma map_simps [simp]:
    assumes "S.arr \<mu>"
    shows "B.arr (map \<mu>)"
    and "src\<^sub>B (map \<mu>) = src\<^sub>B (map (S.src \<mu>))" and "trg\<^sub>B (map \<mu>) = src\<^sub>B (map (S.trg \<mu>))"
    and "B.dom (map \<mu>) = map (S.dom \<mu>)" and "B.cod (map \<mu>) = map (S.cod \<mu>)"
      using assms map_in_hom by blast+

    interpretation "functor" S.comp V map
      apply unfold_locales
          apply auto
      using map_def S.comp_char S.seq_char S.arr_char
       apply auto[1]
      using map_def S.comp_simp by auto

    interpretation weak_arrow_of_homs S.comp S.src S.trg V src\<^sub>B trg\<^sub>B map
      using S.arr_char map_def S.src_def S.trg_def S.src_closed S.trg_closed B.isomorphic_reflexive
            preserves_ide S.ide_src S.ide_trg
      apply unfold_locales
      by presburger+

    interpretation HoFF: composite_functor S.VV.comp B.VV.comp V FF
                           \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close>
      ..
    interpretation FoH: composite_functor S.VV.comp S.comp V \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star> snd \<mu>\<nu>\<close> map
      ..

    no_notation B.in_hom ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    definition cmp
    where "cmp \<mu>\<nu> = (if S.VV.arr \<mu>\<nu> then fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu> else B.null)"

    lemma cmp_in_hom [intro]:
    assumes "S.VV.arr \<mu>\<nu>"
    shows "\<guillemotleft>cmp \<mu>\<nu> : src\<^sub>B (snd \<mu>\<nu>) \<rightarrow>\<^sub>B trg\<^sub>B (fst \<mu>\<nu>)\<guillemotright>"
    and "\<guillemotleft>cmp \<mu>\<nu> : map (S.dom (fst \<mu>\<nu>)) \<star>\<^sub>B map (S.dom (snd \<mu>\<nu>))
                     \<Rightarrow>\<^sub>B map (S.cod (fst \<mu>\<nu>) \<star> S.cod (snd \<mu>\<nu>))\<guillemotright>"
    proof -
      show "\<guillemotleft>cmp \<mu>\<nu> : map (S.dom (fst \<mu>\<nu>)) \<star>\<^sub>B map (S.dom (snd \<mu>\<nu>))
                        \<Rightarrow>\<^sub>B map (S.cod (fst \<mu>\<nu>) \<star> S.cod (snd \<mu>\<nu>))\<guillemotright>"
      proof
        show 1: "B.arr (cmp \<mu>\<nu>)"
          unfolding cmp_def
          using assms S.arr_char S.VV.arr_char S.inclusion S.src_def S.trg_def by auto
        show "B.dom (cmp \<mu>\<nu>) = map (S.dom (fst \<mu>\<nu>)) \<star>\<^sub>B map (S.dom (snd \<mu>\<nu>))"
          unfolding cmp_def map_def
          using assms 1 cmp_def S.dom_simp S.cod_simp S.VV.arr_char S.arr_char S.hcomp_def
                S.inclusion S.dom_closed
          by auto
        show "B.cod (cmp \<mu>\<nu>) = map (S.cod (fst \<mu>\<nu>) \<star> S.cod (snd \<mu>\<nu>))"
          unfolding cmp_def map_def
          using assms 1 cmp_def S.dom_simp S.cod_simp S.VV.arr_char S.arr_char S.hcomp_def
                S.inclusion S.cod_closed
          apply auto
          using S.hcomp_closed apply auto[1]
          by (metis (no_types, lifting) B.VV.arrE)
      qed
      thus "\<guillemotleft>cmp \<mu>\<nu> : src\<^sub>B (snd \<mu>\<nu>) \<rightarrow>\<^sub>B trg\<^sub>B (fst \<mu>\<nu>)\<guillemotright>"
        using cmp_def by auto
    qed

    lemma cmp_simps [simp]:
    assumes "S.VV.arr \<mu>\<nu>"
    shows "B.arr (cmp \<mu>\<nu>)"
    and "src\<^sub>B (cmp \<mu>\<nu>) = S.src (snd \<mu>\<nu>)" and "trg\<^sub>B (cmp \<mu>\<nu>) = S.trg (fst \<mu>\<nu>)"
    and "B.dom (cmp \<mu>\<nu>) = map (S.dom (fst \<mu>\<nu>)) \<star>\<^sub>B map (S.dom (snd \<mu>\<nu>))"
    and "B.cod (cmp \<mu>\<nu>) = map (S.cod (fst \<mu>\<nu>) \<star> S.cod (snd \<mu>\<nu>))"
      using assms cmp_in_hom S.src_def S.trg_def S.VV.arr_char
      by simp_all blast+

    lemma iso_cmp:
    assumes "S.VV.ide \<mu>\<nu>"
    shows "B.iso (cmp \<mu>\<nu>)"
      using assms S.VV.ide_char S.VV.arr_char S.arr_char cmp_def S.ide_char S.src_def S.trg_def
      by auto

    interpretation \<Phi>\<^sub>E: natural_isomorphism S.VV.comp V HoFF.map FoH.map cmp
    proof
      show "\<And>\<mu>\<nu>. \<not> S.VV.arr \<mu>\<nu> \<Longrightarrow> cmp \<mu>\<nu> = B.null"
        using cmp_def by simp
      fix \<mu>\<nu>
      assume \<mu>\<nu>: "S.VV.arr \<mu>\<nu>"
      have 1: "S.arr (fst \<mu>\<nu>) \<and> S.arr (snd \<mu>\<nu>) \<and> S.src (fst \<mu>\<nu>) = S.trg (snd \<mu>\<nu>)"
        using \<mu>\<nu> S.VV.arr_char by simp
      show "B.dom (cmp \<mu>\<nu>) = HoFF.map (S.VV.dom \<mu>\<nu>)"
        using \<mu>\<nu> FF_def S.VV.arr_char S.VV.dom_char S.arr_dom S.src_def S.trg_def
              S.dom_char S.src.preserves_dom S.trg.preserves_dom
        apply simp
        by (metis (no_types, lifting))
      show "B.cod (cmp \<mu>\<nu>) = FoH.map (S.VV.cod \<mu>\<nu>)"
        using \<mu>\<nu> 1 map_def S.hseq_char S.hcomp_def S.cod_char S.arr_cod S.VV.cod_simp
        by simp
      show "cmp (S.VV.cod \<mu>\<nu>) \<cdot>\<^sub>B HoFF.map \<mu>\<nu> = cmp \<mu>\<nu>"
        using \<mu>\<nu> 1 cmp_def S.VV.arr_char S.VV.cod_char FF_def S.arr_cod S.cod_simp
              S.src_def S.trg_def map_def
        apply simp
        by (metis (no_types, lifting) B.comp_cod_arr B.hcomp_simps(4) B.hseqE B.src_cod
            B.trg_cod cmp_simps(1) \<mu>\<nu>)
      show "FoH.map \<mu>\<nu> \<cdot>\<^sub>B cmp (S.VV.dom \<mu>\<nu>) = cmp \<mu>\<nu>"
        unfolding cmp_def map_def
        using \<mu>\<nu> S.VV.arr_char B.VV.arr_char S.VV.dom_char S.VV.cod_char B.comp_arr_dom
              S.hcomp_def
        apply simp
        by (metis (no_types, lifting) B.hcomp_simps(3) cmp_def cmp_simps(1) S.arr_char
            S.dom_char S.hcomp_closed S.src_def S.trg_def)
      next
      show "\<And>fg. S.VV.ide fg \<Longrightarrow> B.iso (cmp fg)"
        using iso_cmp by simp
    qed

    sublocale pseudofunctor S.comp S.hcomp S.\<a> \<i> S.src S.trg V H \<a>\<^sub>B \<i> src\<^sub>B trg\<^sub>B map cmp
    proof
      fix f g h
      assume f: "S.ide f" and g: "S.ide g" and h: "S.ide h"
      and fg: "S.src f = S.trg g" and gh: "S.src g = S.trg h"
      have 1: "B.ide f \<and> B.ide g \<and> B.ide h \<and> src\<^sub>B f = trg\<^sub>B g \<and> src\<^sub>B g = trg\<^sub>B h"
        using f g h fg gh S.ide_char S.arr_char S.src_def S.trg_def by simp
      show "map (S.\<a> f g h) \<cdot>\<^sub>B cmp (f \<star> g, h) \<cdot>\<^sub>B cmp (f, g) \<star>\<^sub>B map h =
            cmp (f, g \<star> h) \<cdot>\<^sub>B (map f \<star>\<^sub>B cmp (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[map f, map g, map h]"
      proof -
        have "map (S.\<a> f g h) \<cdot>\<^sub>B cmp (f \<star> g, h) \<cdot>\<^sub>B cmp (f, g) \<star>\<^sub>B map h =
              \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B h) \<cdot>\<^sub>B ((f \<star>\<^sub>B g) \<star>\<^sub>B h)"
          unfolding map_def cmp_def
          using 1 f g h fg gh S.VVV.arr_char S.VV.arr_char B.VVV.arr_char B.VV.arr_char
                B.comp_arr_dom S.arr_char S.comp_char S.hcomp_closed S.hcomp_def
                S.ideD(1) S.src_def
          by (simp add: S.assoc_closed)
        also have "... = cmp (f, g \<star> h) \<cdot>\<^sub>B (map f \<star>\<^sub>B cmp (g, h)) \<cdot>\<^sub>B \<a>\<^sub>B[map f, map g, map h]"
          unfolding cmp_def map_def
          using 1 f g h fg gh S.VV.arr_char B.VVV.arr_char B.VV.arr_char
                B.comp_arr_dom B.comp_cod_arr S.hcomp_def S.comp_char
                S.arr_char S.assoc_closed S.hcomp_closed S.ideD(1) S.trg_def
          by auto
        finally show ?thesis by blast
      qed
    qed

    lemma is_pseudofunctor:
    shows "pseudofunctor S.comp S.hcomp S.\<a> \<i> S.src S.trg V H \<a>\<^sub>B \<i> src\<^sub>B trg\<^sub>B map cmp"
      ..

    lemma map\<^sub>0_simp [simp]:
    assumes "S.obj a"
    shows "map\<^sub>0 a = a"
      using assms map\<^sub>0_def map_def S.obj_char by auto

    lemma unit_char':
    assumes "S.obj a"
    shows "unit a = a"
    proof -
      have a: "S.arr a"
        using assms by auto
      have 1: "B.ide a"
        using assms S.obj_char by auto
      have 2: "src\<^sub>B a = a"
        using assms S.obj_char by auto
      have "a = unit a"
      proof (intro unit_eqI)
        show "S.obj a" by fact
        show "\<guillemotleft>a : map\<^sub>0 a \<Rightarrow>\<^sub>B map a\<guillemotright>"
          using assms a 2 map\<^sub>0_def map_def S.src_def S.dom_char S.cod_char S.obj_char
          by auto
        show "B.iso a"
          using assms 1 by simp
        show "a \<cdot>\<^sub>B \<i>[map\<^sub>0 a] = (map \<i>[a] \<cdot>\<^sub>B cmp (a, a)) \<cdot>\<^sub>B (a \<star>\<^sub>B a)"
        proof -
          have "a \<cdot>\<^sub>B \<i>[a] = \<i>[a] \<cdot>\<^sub>B cmp (a, a) \<cdot>\<^sub>B (a \<star>\<^sub>B a)"
          proof -
            have "a \<cdot>\<^sub>B \<i>[a] = \<i>[a]"
              using assms 1 2 S.comp_cod_arr S.unitor_coincidence S.lunit_in_hom
                    S.obj_char S.comp_simp
              by auto
            moreover have "(a \<star>\<^sub>B a) \<cdot>\<^sub>B (a \<star>\<^sub>B a) = a \<star>\<^sub>B a"
              using assms S.obj_char S.comp_ide_self by auto
            moreover have "B.dom \<i>[a] = a \<star>\<^sub>B a"
              using assms S.obj_char by simp
            moreover have "\<i>[a] \<cdot>\<^sub>B (a \<star>\<^sub>B a) = \<i>[a]"
              using assms S.obj_char B.comp_arr_dom by simp
            ultimately show ?thesis
              using assms cmp_def S.VV.arr_char by auto
          qed
          thus ?thesis
            using assms a 2 map\<^sub>0_def map_def S.src_def B.comp_assoc by simp
        qed
      qed
      thus ?thesis by simp
    qed

  end

  subsection "Composition of Pseudofunctors"

  text \<open>
    In this section, we show how pseudofunctors may be composed.  The main work is to
    establish the coherence condition for associativity.
  \<close>

  locale composite_pseudofunctor =
    B: bicategory V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B +
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F +
    G: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
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
  and F :: "'b \<Rightarrow> 'c"
  and \<Phi>\<^sub>F :: "'b * 'b \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<Phi>\<^sub>G :: "'c * 'c \<Rightarrow> 'd"
  begin

    sublocale composite_functor V\<^sub>B V\<^sub>C V\<^sub>D F G ..

    sublocale weak_arrow_of_homs V\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D src\<^sub>D trg\<^sub>D \<open>G o F\<close>
    proof
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> D.isomorphic ((G o F) (src\<^sub>B \<mu>)) (src\<^sub>D ((G o F) \<mu>))"
      proof -
        fix \<mu>
        assume \<mu>: "B.arr \<mu>"
        show "D.isomorphic ((G o F) (src\<^sub>B \<mu>)) (src\<^sub>D ((G o F) \<mu>))"
        proof -
          have "(G o F) (src\<^sub>B \<mu>) = G (F (src\<^sub>B \<mu>))"
            using \<mu> by simp
          also have "D.isomorphic ... (G (src\<^sub>C (F \<mu>)))"
            using \<mu> F.weakly_preserves_src G.preserves_iso
            by (meson C.isomorphicE D.isomorphic_def G.preserves_hom)
          also have "D.isomorphic ... (src\<^sub>D (G (F \<mu>)))"
            using \<mu> G.weakly_preserves_src by blast
          also have "... = src\<^sub>D ((G o F) \<mu>)"
            by simp
          finally show ?thesis by blast
        qed
      qed
      show "\<And>\<mu>. B.arr \<mu> \<Longrightarrow> D.isomorphic ((G o F) (trg\<^sub>B \<mu>)) (trg\<^sub>D ((G o F) \<mu>))"
      proof -
        fix \<mu>
        assume \<mu>: "B.arr \<mu>"
        show "D.isomorphic ((G o F) (trg\<^sub>B \<mu>)) (trg\<^sub>D ((G o F) \<mu>))"
        proof -
          have "(G o F) (trg\<^sub>B \<mu>) = G (F (trg\<^sub>B \<mu>))"
            using \<mu> by simp
          also have "D.isomorphic ... (G (trg\<^sub>C (F \<mu>)))"
            using \<mu> F.weakly_preserves_trg G.preserves_iso
            by (meson C.isomorphicE D.isomorphic_def G.preserves_hom)
          also have "D.isomorphic ... (trg\<^sub>D (G (F \<mu>)))"
            using \<mu> G.weakly_preserves_trg by blast
          also have "... = trg\<^sub>D ((G o F) \<mu>)"
            by simp
          finally show ?thesis by blast
        qed
      qed
    qed

    interpretation H\<^sub>DoGF_GF: composite_functor B.VV.comp D.VV.comp V\<^sub>D FF
                               \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D snd \<mu>\<nu>\<close>
      ..
    interpretation GFoH\<^sub>B: composite_functor B.VV.comp V\<^sub>B V\<^sub>D \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>\<close>
                               \<open>G o F\<close>
      ..

    definition cmp
    where "cmp \<mu>\<nu> = (if B.VV.arr \<mu>\<nu> then
                      G (F (H\<^sub>B (fst \<mu>\<nu>) (snd \<mu>\<nu>))) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D
                        \<Phi>\<^sub>G (F (B.dom (fst \<mu>\<nu>)), F (B.dom (snd \<mu>\<nu>)))
                   else D.null)"

    lemma cmp_in_hom [intro]:
    assumes "B.VV.arr \<mu>\<nu>"
    shows "\<guillemotleft>cmp \<mu>\<nu> : H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>) \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)\<guillemotright>"
    proof -
      have "cmp \<mu>\<nu> = G (F (H\<^sub>B (fst \<mu>\<nu>) (snd \<mu>\<nu>))) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D
                     \<Phi>\<^sub>G (F (B.dom (fst \<mu>\<nu>)), F (B.dom (snd \<mu>\<nu>)))"
        using assms cmp_def by simp
      moreover have "\<guillemotleft> ... : H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>)
                                \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>\<Phi>\<^sub>G (F (B.dom (fst \<mu>\<nu>)), F (B.dom (snd \<mu>\<nu>))) :
                 H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>)
                   \<Rightarrow>\<^sub>D G (F (B.dom (fst \<mu>\<nu>)) \<star>\<^sub>C F (B.dom (snd \<mu>\<nu>)))\<guillemotright>"
          using assms F.FF_def FF_def B.VV.arr_char B.VV.dom_simp by auto
        show "\<guillemotleft>G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) :
                 G (F (B.dom (fst \<mu>\<nu>)) \<star>\<^sub>C F (B.dom (snd \<mu>\<nu>)))
                   \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.dom \<mu>\<nu>)\<guillemotright>"
          using assms B.VV.arr_char F.FF_def B.VV.dom_simp B.VV.cod_simp by auto
        show "\<guillemotleft>G (F (fst \<mu>\<nu> \<star>\<^sub>B snd \<mu>\<nu>)) :
                 GFoH\<^sub>B.map (B.VV.dom \<mu>\<nu>) \<Rightarrow>\<^sub>D GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)\<guillemotright>"
        proof -
          have "B.VV.in_hom \<mu>\<nu> (B.VV.dom \<mu>\<nu>) (B.VV.cod \<mu>\<nu>)"
            using assms by auto
          thus ?thesis by auto
        qed
      qed
      ultimately show ?thesis by argo
    qed

    lemma cmp_simps [simp]:
    assumes "B.VV.arr \<mu>\<nu>"
    shows "D.arr (cmp \<mu>\<nu>)"
    and "D.dom (cmp \<mu>\<nu>) = H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>)"
    and "D.cod (cmp \<mu>\<nu>) = GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)"
      using assms cmp_in_hom by blast+

    interpretation \<Phi>: natural_transformation
                        B.VV.comp V\<^sub>D H\<^sub>DoGF_GF.map GFoH\<^sub>B.map cmp
    proof
      show "\<And>\<mu>\<nu>. \<not> B.VV.arr \<mu>\<nu> \<Longrightarrow> cmp \<mu>\<nu> = D.null"
        unfolding cmp_def by simp
      fix \<mu>\<nu>
      assume \<mu>\<nu>: "B.VV.arr \<mu>\<nu>"
      show "D.dom (cmp \<mu>\<nu>) = H\<^sub>DoGF_GF.map (B.VV.dom \<mu>\<nu>)"
        using \<mu>\<nu> cmp_in_hom by blast
      show "D.cod (cmp \<mu>\<nu>) = GFoH\<^sub>B.map (B.VV.cod \<mu>\<nu>)"
        using \<mu>\<nu> cmp_in_hom by blast
      show "GFoH\<^sub>B.map \<mu>\<nu> \<cdot>\<^sub>D cmp (B.VV.dom \<mu>\<nu>) = cmp \<mu>\<nu>"
        unfolding cmp_def
        using \<mu>\<nu> B.VV.ide_char B.VV.arr_char D.comp_ide_arr B.VV.dom_char D.comp_assoc
              is_natural_1
        apply simp
        by (metis (no_types, lifting) B.H.preserves_arr B.hcomp_simps(3))
      show "cmp (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>D H\<^sub>DoGF_GF.map \<mu>\<nu> = cmp \<mu>\<nu>"
      proof -
        have "cmp (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>D H\<^sub>DoGF_GF.map \<mu>\<nu> =
              (G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                  \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>)))) \<cdot>\<^sub>D
                    (fst (FF \<mu>\<nu>) \<star>\<^sub>D snd (FF \<mu>\<nu>))"
          unfolding cmp_def
          using \<mu>\<nu> B.VV.arr_char B.VV.dom_simp B.VV.cod_simp by simp
        also have "... = (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>)))) \<cdot>\<^sub>D
                               (fst (FF \<mu>\<nu>) \<star>\<^sub>D snd (FF \<mu>\<nu>))"
        proof -
          have "D.ide (G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))))"
            using \<mu>\<nu> B.VV.arr_char by simp
          moreover have "D.seq (G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))))
                               (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                                  \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))))"
            using \<mu>\<nu> B.VV.arr_char B.VV.dom_char B.VV.cod_char F.FF_def
            apply (intro D.seqI)
                apply auto
          proof -
            show "G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>))) =
                  D.cod (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                    \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))))"
            proof -
              have "D.seq (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))))
                          (\<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))))"
                using \<mu>\<nu> B.VV.arr_char F.FF_def B.VV.arr_char B.VV.dom_char B.VV.cod_char
                by (intro D.seqI) auto
              thus ?thesis 
                using \<mu>\<nu> B.VV.arr_char B.VV.cod_simp by simp
            qed
          qed
          ultimately show ?thesis
            using \<mu>\<nu> D.comp_ide_arr [of "G (F (B.cod (fst \<mu>\<nu>) \<star>\<^sub>B B.cod (snd \<mu>\<nu>)))"
                                        "G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                                           \<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>)))"]
            by simp
        qed
        also have "... = G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                            (\<Phi>\<^sub>G (F (B.cod (fst \<mu>\<nu>)), F (B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                               (fst (FF \<mu>\<nu>) \<star>\<^sub>D snd (FF \<mu>\<nu>)))"
          using D.comp_assoc by simp
        also have "... = G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (C.VV.cod (F.FF \<mu>\<nu>)) \<cdot>\<^sub>D G.H\<^sub>DoFF.map (F.FF \<mu>\<nu>)"
          using \<mu>\<nu> B.VV.arr_char F.FF_def G.FF_def FF_def C.VV.cod_simp by auto
        also have "... = G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                           G.FoH\<^sub>C.map (F.FF \<mu>\<nu>) \<cdot>\<^sub>D \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
          using \<mu>\<nu> B.VV.arr_char G.\<Phi>.naturality C.VV.dom_simp C.VV.cod_simp by simp
        also have "... = (G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D
                           G.FoH\<^sub>C.map (F.FF \<mu>\<nu>)) \<cdot>\<^sub>D \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
          using D.comp_assoc by simp
        also have "... = (G (\<Phi>\<^sub>F (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C F.H\<^sub>DoFF.map \<mu>\<nu>)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
        proof -
          have "(B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>)) = B.VV.cod \<mu>\<nu>"
            using \<mu>\<nu> B.VV.arr_char B.VV.cod_simp by simp
          moreover have "G.FoH\<^sub>C.map (F.FF \<mu>\<nu>) = G (F.H\<^sub>DoFF.map \<mu>\<nu>)"
            using \<mu>\<nu> F.FF_def by simp
          moreover have "G (\<Phi>\<^sub>F (B.cod (fst \<mu>\<nu>), B.cod (snd \<mu>\<nu>))) \<cdot>\<^sub>D G (F.H\<^sub>DoFF.map \<mu>\<nu>) =
                         G (\<Phi>\<^sub>F (B.VV.cod \<mu>\<nu>) \<cdot>\<^sub>C F.H\<^sub>DoFF.map \<mu>\<nu>)"
            using \<mu>\<nu> B.VV.arr_char
            by (metis (no_types, lifting) F.\<Phi>.is_natural_2 F.\<Phi>.preserves_reflects_arr
                G.preserves_comp calculation(1))
          ultimately show ?thesis by argo
        qed
        also have "... = G (F.FoH\<^sub>C.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
          using \<mu>\<nu> F.\<Phi>.naturality [of \<mu>\<nu>] F.FF_def by simp
        also have "... = G (F.FoH\<^sub>C.map \<mu>\<nu>) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) \<cdot>\<^sub>D
                         \<Phi>\<^sub>G (C.VV.dom (F.FF \<mu>\<nu>))"
        proof -
          have "G (F.FoH\<^sub>C.map \<mu>\<nu> \<cdot>\<^sub>C \<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>)) =
                G (F.FoH\<^sub>C.map \<mu>\<nu>) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom \<mu>\<nu>))"
            using \<mu>\<nu>
            by (metis (mono_tags, lifting) F.\<Phi>.is_natural_1 F.\<Phi>.preserves_reflects_arr
                G.preserves_comp)
          thus ?thesis
            using \<mu>\<nu> D.comp_assoc by simp
        qed
        also have "... = cmp \<mu>\<nu>"
          using \<mu>\<nu> B.VV.arr_char cmp_def F.FF_def F.FF.preserves_dom B.VV.dom_simp
          by auto
        finally show ?thesis by simp
      qed
    qed

    interpretation \<Phi>: natural_isomorphism B.VV.comp V\<^sub>D H\<^sub>DoGF_GF.map GFoH\<^sub>B.map cmp
    proof
      show "\<And>hk. B.VV.ide hk \<Longrightarrow> D.iso (cmp hk)"
      proof -
        fix hk
        assume hk: "B.VV.ide hk"
        have "D.iso (G (F (fst hk \<star>\<^sub>B snd hk)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (B.VV.dom hk)) \<cdot>\<^sub>D
                       \<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
        proof (intro D.isos_compose)
          show "D.iso (\<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
            using hk G.\<Phi>.components_are_iso [of "(F (B.dom (fst hk)), F (B.dom (snd hk)))"]
                  C.VV.ide_char B.VV.arr_char B.VV.dom_char
            by (metis (no_types, lifting) B.VV.ideD(1) B.VV.ideD(2) B.VxV.dom_char
                F.FF_def F.FF.components_are_iso G.\<Phi>.preserves_iso fst_conv snd_conv)
          show "D.iso (G (\<Phi>\<^sub>F (B.VV.dom hk)))"
            using hk F.\<Phi>.components_are_iso B.VV.arr_char B.VV.dom_char B.VV.ideD(2)
            by auto
          show "D.seq (G (\<Phi>\<^sub>F (B.VV.dom hk))) (\<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
            using hk B.VV.arr_char B.VV.ide_char B.VV.dom_char C.VV.arr_char F.FF_def
                  C.VV.dom_simp C.VV.cod_simp
            by auto
          show "D.iso (G (F (fst hk \<star>\<^sub>B snd hk)))"
            using hk F.\<Phi>.components_are_iso B.VV.arr_char by simp
          show "D.seq (G (F (fst hk \<star>\<^sub>B snd hk)))
                      (G (\<Phi>\<^sub>F (B.VV.dom hk)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (B.dom (fst hk)), F (B.dom (snd hk))))"
            using hk B.VV.arr_char B.VV.dom_char
            by (metis (no_types, lifting) B.VV.ideD(1) cmp_def cmp_simps(1))
        qed
        thus "D.iso (cmp hk)"
          unfolding cmp_def using hk by simp
      qed
    qed

    sublocale pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>G o F\<close> cmp
    proof
      fix f g h
      assume f: "B.ide f" and g: "B.ide g" and h: "B.ide h"
      assume fg: "src\<^sub>B f = trg\<^sub>B g" and gh: "src\<^sub>B g = trg\<^sub>B h"
      show "map \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>D cmp (f \<star>\<^sub>B g, h) \<cdot>\<^sub>D (cmp (f, g) \<star>\<^sub>D map h) =
            cmp (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (map f \<star>\<^sub>D cmp (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[map f, map g, map h]"
      proof -
        have "map \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>D cmp (f \<star>\<^sub>B g, h) \<cdot>\<^sub>D (cmp (f, g) \<star>\<^sub>D map h) =
              G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D
                (G (F ((f \<star>\<^sub>B g) \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h)) \<cdot>\<^sub>D
                  (G (F (f \<star>\<^sub>B g)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          unfolding cmp_def
          using f g h fg gh B.VV.arr_char B.VV.dom_simp by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D
                          (G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h)) \<cdot>\<^sub>D
                            (G (F (f \<star>\<^sub>B g)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh D.comp_ide_arr D.comp_assoc
          by (metis B.ideD(1) B.ide_hcomp B.src_hcomp F.cmp_simps(1) F.cmp_simps(5)
              G.is_natural_2)
        also have "... = G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D
                          (G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h)) \<cdot>\<^sub>D
                            (G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g fg
          by (metis (no_types) D.comp_assoc F.cmp_simps(1) F.cmp_simps(5) G.is_natural_2)
        also have "... = (G (F \<a>\<^sub>B[f, g, h]) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f \<star>\<^sub>B g, h))) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char B.VV.cod_simp by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                            \<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<star>\<^sub>D G (F h)) \<cdot>\<^sub>D
                              (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char C.VV.arr_char F.FF_def D.whisker_right
                B.VV.dom_simp C.VV.cod_simp
          by auto
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                          (\<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g)) \<star>\<^sub>D G (F h))) \<cdot>\<^sub>D
                            (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D
                          (G (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h)) \<cdot>\<^sub>D
                            (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
        proof -
          have "\<Phi>\<^sub>G (F (f \<star>\<^sub>B g), F h) = \<Phi>\<^sub>G (C.VV.cod (\<Phi>\<^sub>F (f, g), F h))"
            using f g h fg gh B.VV.arr_char C.VV.arr_char B.VV.cod_simp C.VV.cod_simp
            by simp
          moreover have "G (\<Phi>\<^sub>F (f, g)) \<star>\<^sub>D G (F h) = G.H\<^sub>DoFF.map (\<Phi>\<^sub>F (f, g), F h)"
            using f g h fg gh B.VV.arr_char C.VV.arr_char G.FF_def by simp
          moreover have "G.FoH\<^sub>C.map (\<Phi>\<^sub>F (f, g), F h) = G (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h)"
            using f g h fg gh B.VV.arr_char by simp
          moreover have "\<Phi>\<^sub>G (C.VV.dom (\<Phi>\<^sub>F (f, g), F h)) = \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h)"
            using f g h fg gh C.VV.arr_char F.cmp_in_hom [of f g] C.VV.dom_simp by auto
          ultimately show ?thesis
            using f g h fg gh B.VV.arr_char G.\<Phi>.naturality
            by (metis (mono_tags, lifting) C.VV.arr_cod_iff_arr C.VV.arr_dom_iff_arr
                G.FoH\<^sub>C.is_extensional G.H\<^sub>DoFF.is_extensional G.\<Phi>.is_extensional)
        qed
        also have "... = (G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>D (G (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G ((F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h)) \<cdot>\<^sub>C (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h)) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char F.FF_def B.VV.dom_simp B.VV.cod_simp by auto
        also have "... = G (F \<a>\<^sub>B[f, g, h] \<cdot>\<^sub>C \<Phi>\<^sub>F (f \<star>\<^sub>B g, h) \<cdot>\<^sub>C (\<Phi>\<^sub>F (f, g) \<star>\<^sub>C F h)) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using C.comp_assoc by simp
        also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>C \<a>\<^sub>C[F f, F g, F h]) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh F.assoc_coherence [of f g h] by simp
        also have "... = G ((\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>C \<a>\<^sub>C[F f, F g, F h]) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using C.comp_assoc by simp
        also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D G \<a>\<^sub>C[F f, F g, F h]) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using f g h fg gh B.VV.arr_char F.FF_def B.VV.dom_simp B.VV.cod_simp by auto
        also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                           G \<a>\<^sub>C[F f, F g, F h] \<cdot>\<^sub>D \<Phi>\<^sub>G (F f \<star>\<^sub>C F g, F h) \<cdot>\<^sub>D
                           (\<Phi>\<^sub>G (F f, F g) \<star>\<^sub>D G (F h))"
          using D.comp_assoc by simp
        also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h)) \<cdot>\<^sub>D
                             \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
          using f g h fg gh G.assoc_coherence [of "F f" "F g" "F h"] by simp
        also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                           \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))) \<cdot>\<^sub>D
                             \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
          using D.comp_assoc by simp
        also have "... = (cmp (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D cmp (g, h))) \<cdot>\<^sub>D
                           \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
        proof -
          have "G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                  \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h)) =
                cmp (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D cmp (g, h))"
          proof -
            have "cmp (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D cmp (g, h)) =
                  (G (F (f \<star>\<^sub>B g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h))) \<cdot>\<^sub>D
                    (G (F f) \<star>\<^sub>D G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              unfolding cmp_def
              using f g h fg gh B.VV.arr_char B.VV.dom_simp B.VV.cod_simp by simp
            also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h))) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
            proof -
              have "G (F (f \<star>\<^sub>B g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h))"
                using f g h fg gh B.VV.arr_char D.comp_ide_arr B.VV.dom_simp B.VV.cod_simp
                by simp
              thus ?thesis
                using D.comp_assoc by metis
            qed
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using D.comp_assoc by simp
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
            proof -
              have "G (F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (g, h)) = G (\<Phi>\<^sub>F (g, h))"
                using f g h fg gh B.VV.arr_char D.comp_ide_arr B.VV.dom_simp B.VV.cod_simp
                by simp
              thus ?thesis
                using D.comp_assoc by metis
            qed
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using f g h fg gh
                    D.whisker_left [of "G (F f)" "G (\<Phi>\<^sub>F (g, h))" "\<Phi>\<^sub>G (F g, F h)"]
              by fastforce
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (\<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h)) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h)))) \<cdot>\<^sub>D
                                 (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using D.comp_assoc by simp
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D
                               (G (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h)) \<cdot>\<^sub>D
                                 (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
            proof -
              have "\<Phi>\<^sub>G (C.VV.cod (F f, \<Phi>\<^sub>F (g, h))) = \<Phi>\<^sub>G (F f, F (g \<star>\<^sub>B h))"
                using f g h fg gh B.VV.arr_char C.VV.cod_char B.VV.dom_simp B.VV.cod_simp
                by auto
              moreover have "G.H\<^sub>DoFF.map (F f, \<Phi>\<^sub>F (g, h)) = G (F f) \<star>\<^sub>D G (\<Phi>\<^sub>F (g, h))"
                using f g h fg gh B.VV.arr_char G.FF_def by auto
              moreover have "G.FoH\<^sub>C.map (F f, \<Phi>\<^sub>F (g, h)) = G (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))"
                using f g h fg gh B.VV.arr_char C.VV.arr_char by simp
              moreover have "C.VV.dom (F f, \<Phi>\<^sub>F (g, h)) = (F f, F g \<star>\<^sub>C F h)"
                using f g h fg gh B.VV.arr_char C.VV.arr_char C.VV.dom_char
                      F.cmp_in_hom [of g h]
                by auto
              ultimately show ?thesis
                using f g h fg gh B.VV.arr_char C.VV.arr_char
                      G.\<Phi>.naturality [of "(F f, \<Phi>\<^sub>F (g, h))"]
                by simp
            qed
            also have "... = (G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h)) \<cdot>\<^sub>D (G (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h)))) \<cdot>\<^sub>D
                               \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using D.comp_assoc by simp
            also have "... = G (\<Phi>\<^sub>F (f, g \<star>\<^sub>B h) \<cdot>\<^sub>C (F f \<star>\<^sub>C \<Phi>\<^sub>F (g, h))) \<cdot>\<^sub>D
                               \<Phi>\<^sub>G (F f, F g \<star>\<^sub>C F h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D \<Phi>\<^sub>G (F g, F h))"
              using f g h fg gh B.VV.arr_char
              by (metis (no_types, lifting) B.assoc_simps(1) C.comp_assoc C.seqE
                  F.preserves_assoc(1) F.preserves_reflects_arr G.preserves_comp)
            finally show ?thesis by simp
          qed
          thus ?thesis by simp
        qed
        also have "... = cmp (f, g \<star>\<^sub>B h) \<cdot>\<^sub>D (G (F f) \<star>\<^sub>D cmp (g, h)) \<cdot>\<^sub>D
                           \<a>\<^sub>D[G (F f), G (F g), G (F h)]"
          using D.comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma is_pseudofunctor:
    shows "pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (G o F) cmp"
      ..

    lemma map\<^sub>0_simp [simp]:
    assumes "B.obj a"
    shows "map\<^sub>0 a = G.map\<^sub>0 (F.map\<^sub>0 a)"
      using assms map\<^sub>0_def by auto

    lemma unit_char':
    assumes "B.obj a"
    shows "unit a = G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a)"
    proof -
      have "G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a) = unit a"
      proof (intro unit_eqI [of a "G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a)"])
        show "B.obj a" by fact
        show "\<guillemotleft>G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a) : map\<^sub>0 a \<Rightarrow>\<^sub>D map a\<guillemotright>"
          using assms by auto
        show "D.iso (G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a))"
          by (simp add: D.isos_compose F.unit_char(2) G.unit_char(2) assms)
        show "(G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a)) \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] =
              (map \<i>\<^sub>B[a] \<cdot>\<^sub>D cmp (a, a)) \<cdot>\<^sub>D
                (G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a) \<star>\<^sub>D G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a))"
        proof -
          have 1: "cmp (a, a) = G (\<Phi>\<^sub>F (a, a)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F a, F a)"
           proof -
            have "cmp (a, a) = (G (F (a \<star>\<^sub>B a)) \<cdot>\<^sub>D G (\<Phi>\<^sub>F (a, a))) \<cdot>\<^sub>D \<Phi>\<^sub>G (F a, F a)"
              using assms cmp_def B.VV.ide_char B.VV.arr_char B.VV.dom_char B.VV.cod_char
                    B.VxV.dom_char B.objE D.comp_assoc B.obj_simps
              by simp
            also have "... = G (\<Phi>\<^sub>F (a, a)) \<cdot>\<^sub>D \<Phi>\<^sub>G (F a, F a)"
              using assms D.comp_cod_arr B.VV.arr_char B.VV.ide_char by auto
            finally show ?thesis by blast
          qed
          have "(map \<i>\<^sub>B[a] \<cdot>\<^sub>D cmp (a, a)) \<cdot>\<^sub>D
                  (G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a) \<star>\<^sub>D G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a)) =
                map \<i>\<^sub>B[a] \<cdot>\<^sub>D G (\<Phi>\<^sub>F (a, a)) \<cdot>\<^sub>D
                    (\<Phi>\<^sub>G (F a, F a) \<cdot>\<^sub>D (G (F.unit a) \<star>\<^sub>D G (F.unit a))) \<cdot>\<^sub>D
                    (G.unit (F.map\<^sub>0 a) \<star>\<^sub>D G.unit (F.map\<^sub>0 a))"
            using assms 1 D.comp_assoc D.interchange by simp
          also have "... = (map \<i>\<^sub>B[a] \<cdot>\<^sub>D G (\<Phi>\<^sub>F (a, a)) \<cdot>\<^sub>D G (F.unit a \<star>\<^sub>C F.unit a)) \<cdot>\<^sub>D
                             \<Phi>\<^sub>G (F.map\<^sub>0 a, F.map\<^sub>0 a) \<cdot>\<^sub>D
                             (G.unit (F.map\<^sub>0 a) \<star>\<^sub>D G.unit (F.map\<^sub>0 a))"
            using assms G.\<Phi>.naturality [of "(F.unit a, F.unit a)"]
                  C.VV.arr_char C.VV.dom_char C.VV.cod_char G.FF_def D.comp_assoc
            by simp
          also have "... = (G (F \<i>\<^sub>B[a] \<cdot>\<^sub>C \<Phi>\<^sub>F (a, a) \<cdot>\<^sub>C (F.unit a \<star>\<^sub>C F.unit a))) \<cdot>\<^sub>D
                             \<Phi>\<^sub>G (F.map\<^sub>0 a, F.map\<^sub>0 a) \<cdot>\<^sub>D
                             (G.unit (F.map\<^sub>0 a) \<star>\<^sub>D G.unit (F.map\<^sub>0 a))"
          proof -
            have "C.arr (F \<i>\<^sub>B[a] \<cdot>\<^sub>C \<Phi>\<^sub>F (a, a) \<cdot>\<^sub>C (F.unit a \<star>\<^sub>C F.unit a))"
              using assms B.VV.ide_char B.VV.arr_char F.cmp_in_hom(2)
              by (intro C.seqI' C.comp_in_homI) auto
            hence "map \<i>\<^sub>B[a] \<cdot>\<^sub>D G (\<Phi>\<^sub>F (a, a)) \<cdot>\<^sub>D G (F.unit a \<star>\<^sub>C F.unit a) =
                  G (F \<i>\<^sub>B[a] \<cdot>\<^sub>C \<Phi>\<^sub>F (a, a) \<cdot>\<^sub>C (F.unit a \<star>\<^sub>C F.unit a))"
              by auto
            thus ?thesis by argo
          qed
          also have "... = G (F.unit a \<cdot>\<^sub>C \<i>\<^sub>C[F.map\<^sub>0 a]) \<cdot>\<^sub>D
                             \<Phi>\<^sub>G (F.map\<^sub>0 a, F.map\<^sub>0 a) \<cdot>\<^sub>D
                             (G.unit (F.map\<^sub>0 a) \<star>\<^sub>D G.unit (F.map\<^sub>0 a))"
            using assms F.unit_char C.comp_assoc by simp
          also have "... = G (F.unit a) \<cdot>\<^sub>D (G \<i>\<^sub>C[F.map\<^sub>0 a] \<cdot>\<^sub>D
                             \<Phi>\<^sub>G (F.map\<^sub>0 a, F.map\<^sub>0 a)) \<cdot>\<^sub>D
                             (G.unit (F.map\<^sub>0 a) \<star>\<^sub>D G.unit (F.map\<^sub>0 a))"
            using assms D.comp_assoc by simp
          also have "... = (G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a)) \<cdot>\<^sub>D \<i>\<^sub>D[G.map\<^sub>0 (F.map\<^sub>0 a)]"
            using assms G.unit_char D.comp_assoc by simp
          also have "... = (G (F.unit a) \<cdot>\<^sub>D G.unit (F.map\<^sub>0 a)) \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a]"
            using assms map\<^sub>0_def by auto
          finally show ?thesis by simp
        qed
      qed
      thus ?thesis by simp
    qed

  end

  subsection "Restriction of Pseudofunctors"

  text \<open>
    In this section, we construct the restriction and corestriction of a pseudofunctor to
    a subbicategory of its domain and codomain, respectively.
  \<close>

  locale restricted_pseudofunctor =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi> +
    C': subbicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C Arr
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
  and \<Phi> :: "'c * 'c \<Rightarrow> 'd"
  and Arr :: "'c \<Rightarrow> bool"
  begin

    abbreviation map
    where "map \<equiv> \<lambda>\<mu>. if C'.arr \<mu> then F \<mu> else D.null"

    abbreviation cmp
    where "cmp \<equiv> \<lambda>\<mu>\<nu>. if C'.VV.arr \<mu>\<nu> then \<Phi> \<mu>\<nu> else D.null"

    interpretation "functor" C'.comp V\<^sub>D map
      using C'.inclusion C'.arr_char C'.dom_char C'.cod_char C'.seq_char C'.comp_char
            C'.arr_dom C'.arr_cod
      apply (unfold_locales)
          apply auto
      by presburger

    interpretation weak_arrow_of_homs C'.comp C'.src C'.trg V\<^sub>D src\<^sub>D trg\<^sub>D map
      using C'.arrE C'.ide_src C'.ide_trg C'.inclusion C'.src_def C'.trg_def
            F.weakly_preserves_src F.weakly_preserves_trg
      by unfold_locales auto

    interpretation H\<^sub>D\<^sub>'oFF: composite_functor C'.VV.comp D.VV.comp V\<^sub>D FF
                             \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>D snd \<mu>\<nu>\<close>
      ..
    interpretation FoH\<^sub>C\<^sub>': composite_functor C'.VV.comp C'.comp V\<^sub>D
                             \<open>\<lambda>\<mu>\<nu>. C'.hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close> map
      ..

    interpretation \<Phi>: natural_transformation C'.VV.comp V\<^sub>D H\<^sub>D\<^sub>'oFF.map FoH\<^sub>C\<^sub>'.map cmp
      using C'.arr_char C'.dom_char C'.cod_char C'.VV.arr_char C'.VV.dom_char C'.VV.cod_char
            FF_def C'.inclusion C'.dom_closed C'.cod_closed C'.src_def C'.trg_def
            F.cmp_simps'(4) C'.hcomp_def C'.hcomp_closed F.\<Phi>.is_natural_1 F.\<Phi>.is_natural_2
            C.VV.arr_char C.VV.dom_char C.VV.cod_char F.FF_def F.cmp_simps'(5)
      by unfold_locales auto

    interpretation \<Phi>: natural_isomorphism C'.VV.comp V\<^sub>D H\<^sub>D\<^sub>'oFF.map FoH\<^sub>C\<^sub>'.map cmp
      using C.VV.ide_char C.VV.arr_char C'.VV.ide_char C'.VV.arr_char C'.arr_char
            C'.src_def C'.trg_def C'.ide_char F.\<Phi>.components_are_iso
      by unfold_locales auto

    sublocale pseudofunctor C'.comp C'.hcomp C'.\<a> \<i>\<^sub>C C'.src C'.trg V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                map cmp
      using F.assoc_coherence C'.VVV.arr_char C'.VV.arr_char C'.arr_char C'.hcomp_def
            C'.src_def C'.trg_def C'.assoc_closed C'.hcomp_closed C'.ide_char
      by unfold_locales (simp add: C'.ide_char C'.src_def C'.trg_def)

    lemma is_pseudofunctor:
    shows "pseudofunctor C'.comp C'.hcomp C'.\<a> \<i>\<^sub>C C'.src C'.trg V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D map cmp"
      ..

    lemma map\<^sub>0_simp [simp]:
    assumes "C'.obj a"
    shows "map\<^sub>0 a = F.map\<^sub>0 a"
      using assms map\<^sub>0_def C'.obj_char by auto

    lemma unit_char':
    assumes "C'.obj a"
    shows "F.unit a = unit a"
    proof (intro unit_eqI)
      show "C'.obj a" by fact
      show "\<guillemotleft>F.unit a : map\<^sub>0 a \<Rightarrow>\<^sub>D map a\<guillemotright>"
        using assms map\<^sub>0_def F.unit_in_hom(2) [of a] C'.obj_char by auto
      show "D.iso (F.unit a)"
        using assms by (simp add: C'.obj_char F.unit_char(2))
      show "F.unit a \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = (map \<i>\<^sub>C[a] \<cdot>\<^sub>D cmp (a, a)) \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D F.unit a)"
      proof -
        have "F.unit a \<cdot>\<^sub>D \<i>\<^sub>D[map\<^sub>0 a] = F.unit a \<cdot>\<^sub>D \<i>\<^sub>D[F.map\<^sub>0 a]"
          using assms map\<^sub>0_def F.map\<^sub>0_def by auto
        also have "... = (F \<i>\<^sub>C[a] \<cdot>\<^sub>D \<Phi> (a, a)) \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D F.unit a)"
          using assms C'.obj_char F.unit_char(3) [of a] by simp
        also have "... = (map \<i>\<^sub>C[a] \<cdot>\<^sub>D cmp (a, a)) \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D F.unit a)"
          using assms C.VV.arr_char D.iso_is_arr iso_\<i> by auto
        finally show ?thesis by simp
      qed
    qed

  end

  text \<open>
    We define the corestriction construction only for the case of sub-bicategories
    determined by a set of objects of the ambient bicategory.
    There are undoubtedly more general constructions, but this one is adequate for our
    present needs.
  \<close>

  locale corestricted_pseudofunctor =
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    F: pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi> +
    D': subbicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<lambda>\<mu>. D.arr \<mu> \<and> Obj (src\<^sub>D \<mu>) \<and> Obj (trg\<^sub>D \<mu>)\<close>
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
  and \<Phi> :: "'c * 'c \<Rightarrow> 'd"
  and Obj :: "'d \<Rightarrow> bool" +
  assumes preserves_arr: "\<And>\<mu>. C.arr \<mu> \<Longrightarrow> D'.arr (F \<mu>)"
  begin

    abbreviation map
    where "map \<equiv> F"

    abbreviation cmp
    where "cmp \<equiv> \<Phi>"

    interpretation "functor" V\<^sub>C D'.comp F
      using preserves_arr F.is_extensional D'.arr_char D'.dom_char D'.cod_char D'.comp_char
      by (unfold_locales) auto

    interpretation weak_arrow_of_homs V\<^sub>C src\<^sub>C trg\<^sub>C D'.comp D'.src D'.trg F
    proof
      fix \<mu>
      assume \<mu>: "C.arr \<mu>"
      obtain \<phi> where \<phi>: "\<guillemotleft>\<phi> : F (src\<^sub>C \<mu>) \<Rightarrow>\<^sub>D src\<^sub>D (F \<mu>)\<guillemotright> \<and> D.iso \<phi>"
        using \<mu> F.weakly_preserves_src by auto
      have 2: "D'.in_hom \<phi> (F (src\<^sub>C \<mu>)) (D'.src (F \<mu>))"
        using \<mu> \<phi> D'.arr_char D'.dom_char D'.cod_char D'.src_def D.vconn_implies_hpar(1-2)
              preserves_arr
        by (intro D'.in_homI) auto
      moreover have "D'.iso \<phi>"
        using 2 \<phi> D'.iso_char D'.arr_char by fastforce
      ultimately show "D'.isomorphic (F (src\<^sub>C \<mu>)) (D'.src (F \<mu>))"
        using D'.isomorphic_def by auto
      obtain \<psi> where \<psi>: "\<guillemotleft>\<psi> : F (trg\<^sub>C \<mu>) \<Rightarrow>\<^sub>D trg\<^sub>D (F \<mu>)\<guillemotright> \<and> D.iso \<psi>"
        using \<mu> F.weakly_preserves_trg by auto
      have 2: "D'.in_hom \<psi> (F (trg\<^sub>C \<mu>)) (D'.trg (F \<mu>))"
        using \<mu> \<psi> D'.arr_char D'.dom_char D'.cod_char D'.trg_def D.vconn_implies_hpar(1-2)
              preserves_arr
        by (intro D'.in_homI) auto
      moreover have "D'.iso \<psi>"
        using 2 \<psi> D'.iso_char D'.arr_char by fastforce
      ultimately show "D'.isomorphic (F (trg\<^sub>C \<mu>)) (D'.trg (F \<mu>))"
        using D'.isomorphic_def by auto
    qed

    interpretation H\<^sub>D\<^sub>'oFF: composite_functor C.VV.comp D'.VV.comp D'.comp FF
                             \<open>\<lambda>\<mu>\<nu>. D'.hcomp (fst \<mu>\<nu>) (snd \<mu>\<nu>)\<close>
      ..
    interpretation FoH\<^sub>C: composite_functor C.VV.comp V\<^sub>C D'.comp \<open>\<lambda>\<mu>\<nu>. fst \<mu>\<nu> \<star>\<^sub>C snd \<mu>\<nu>\<close>
                             F
      ..

    interpretation natural_transformation C.VV.comp D'.comp H\<^sub>D\<^sub>'oFF.map FoH\<^sub>C.map \<Phi>
    proof
      show "\<And>\<mu>\<nu>. \<not> C.VV.arr \<mu>\<nu> \<Longrightarrow> \<Phi> \<mu>\<nu> = D'.null"
        by (simp add: F.\<Phi>.is_extensional)
      fix \<mu>\<nu>
      assume \<mu>\<nu>: "C.VV.arr \<mu>\<nu>"
      have 1: "D'.arr (\<Phi> \<mu>\<nu>)"
        using \<mu>\<nu> D'.arr_char F.\<Phi>.is_natural_1 F.\<Phi>.components_are_iso
        by (metis (no_types, lifting) D.src_vcomp D.trg_vcomp FoH\<^sub>C.preserves_arr
            F.\<Phi>.preserves_reflects_arr)
      show "D'.dom (\<Phi> \<mu>\<nu>) = H\<^sub>D\<^sub>'oFF.map (C.VV.dom \<mu>\<nu>)"
        using 1 \<mu>\<nu> D'.dom_char C.VV.arr_char C.VV.dom_char F.FF_def FF_def D'.hcomp_def
        by simp
      show "D'.cod (\<Phi> \<mu>\<nu>) = FoH\<^sub>C.map (C.VV.cod \<mu>\<nu>)"
        using 1 \<mu>\<nu> D'.cod_char C.VV.arr_char F.FF_def FF_def D'.hcomp_def by simp
      show "D'.comp (FoH\<^sub>C.map \<mu>\<nu>) (\<Phi> (C.VV.dom \<mu>\<nu>)) = \<Phi> \<mu>\<nu>"
        using 1 \<mu>\<nu> D'.arr_char D'.comp_char C.VV.dom_char F.\<Phi>.is_natural_1
              C.VV.arr_dom D.src_vcomp D.trg_vcomp FoH\<^sub>C.preserves_arr F.\<Phi>.preserves_reflects_arr
        by (metis (mono_tags, lifting))
      show "D'.comp (\<Phi> (C.VV.cod \<mu>\<nu>)) (H\<^sub>D\<^sub>'oFF.map \<mu>\<nu>) = \<Phi> \<mu>\<nu>"
      proof -
        have "Obj (F.map\<^sub>0 (trg\<^sub>C (fst \<mu>\<nu>))) \<and> Obj (F.map\<^sub>0 (trg\<^sub>C (snd \<mu>\<nu>)))"
          using \<mu>\<nu> C.VV.arr_char
          by (metis (no_types, lifting) C.src_trg C.trg.preserves_reflects_arr D'.arr_char
              F.map\<^sub>0_def preserves_hseq)
        moreover have "Obj (F.map\<^sub>0 (src\<^sub>C (snd \<mu>\<nu>)))"
          using \<mu>\<nu> C.VV.arr_char
          by (metis (no_types, lifting) C.src.preserves_reflects_arr C.trg_src D'.arr_char
              F.map\<^sub>0_def preserves_hseq)
        ultimately show ?thesis
          using \<mu>\<nu> 1 D'.arr_char D'.comp_char D'.hseq_char C.VV.arr_char C.VV.cod_char
                C.VxV.cod_char FF_def F.FF_def D'.hcomp_char preserves_hseq
          apply simp
          using F.\<Phi>.is_natural_2 by force
      qed
    qed

    interpretation natural_isomorphism C.VV.comp D'.comp H\<^sub>D\<^sub>'oFF.map FoH\<^sub>C.map \<Phi>
      apply unfold_locales
      using D'.iso_char D'.arr_char by fastforce

    sublocale pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C D'.comp D'.hcomp D'.\<a> \<i>\<^sub>D D'.src D'.trg
                F \<Phi>
    proof
      fix f g h
      assume f: "C.ide f" and g: "C.ide g" and h: "C.ide h"
      and fg: "src\<^sub>C f = trg\<^sub>C g" and gh: "src\<^sub>C g = trg\<^sub>C h"
      have "D'.comp (F \<a>\<^sub>C[f, g, h]) (D'.comp (\<Phi> (f \<star>\<^sub>C g, h)) (D'.hcomp (\<Phi> (f, g)) (F h))) =
            F \<a>\<^sub>C[f, g, h] \<cdot>\<^sub>D \<Phi> (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (\<Phi> (f, g) \<star>\<^sub>D F h)"
      proof -
        have 1: "D'.arr (cmp (f, g) \<star>\<^sub>D map h)"
          using f g h fg gh D'.arr_char C.VV.arr_char
          by (metis (no_types, lifting) C.ideD(1) D'.hcomp_closed F.\<Phi>.preserves_reflects_arr
              F.cmp_simps(1) F.cmp_simps(2) F.preserves_hseq preserves_reflects_arr)
        moreover have 2: "D.seq (cmp (f \<star>\<^sub>C g, h)) (cmp (f, g) \<star>\<^sub>D map h)"
          using 1 f g h fg gh D'.arr_char C.VV.arr_char C.VV.dom_char C.VV.cod_char F.FF_def
          by (intro D.seqI) auto
        moreover have "D'.arr (cmp (f \<star>\<^sub>C g, h) \<cdot>\<^sub>D (cmp (f, g) \<star>\<^sub>D map h))"
          using 1 2 D'.arr_char
          by (metis (no_types, lifting) D'.comp_char D'.seq_char D.seqE F.\<Phi>.preserves_reflects_arr
              preserves_reflects_arr)
        ultimately show ?thesis
          using f g h fg gh D'.dom_char D'.cod_char D'.comp_char D'.hcomp_def C.VV.arr_char
          apply simp
          by force
      qed
      also have "... = \<Phi> (f, g \<star>\<^sub>C h) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<Phi> (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[F f, F g, F h]"
        using f g h fg gh F.assoc_coherence [of f g h] by blast
      also have "... = D'.comp (\<Phi> (f, g \<star>\<^sub>C h))
                               (D'.comp (D'.hcomp (F f) (\<Phi> (g, h))) (D'.\<a> (F f) (F g) (F h)))"
      proof -
        have "D.seq (map f \<star>\<^sub>D cmp (g, h)) \<a>\<^sub>D[map f, map g, map h]"
          using f g h fg gh C.VV.arr_char C.VV.dom_char C.VV.cod_char F.FF_def
          by (intro D.seqI) auto
        moreover have "D'.arr \<a>\<^sub>D[map f, map g, map h]"
          using f g h fg gh D'.arr_char preserves_arr by auto
        moreover have "D'.arr (map f \<star>\<^sub>D cmp (g, h))"
          using f g h fg gh
          by (metis (no_types, lifting) D'.arr_char D.seqE D.vseq_implies_hpar(1)
              D.vseq_implies_hpar(2) calculation(1-2))
        moreover have "D'.arr ((map f \<star>\<^sub>D cmp (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[map f, map g, map h])"
          using f g h fg gh
          by (metis (no_types, lifting) D'.arr_char D'.comp_closed D.seqE
              calculation(1-3))
        moreover have "D.seq (cmp (f, g \<star>\<^sub>C h))
                             ((map f \<star>\<^sub>D cmp (g, h)) \<cdot>\<^sub>D \<a>\<^sub>D[map f, map g, map h])"
          using f g h fg gh F.cmp_simps'(1) F.cmp_simps(4) F.cmp_simps(5) by auto
        ultimately show ?thesis
          using f g h fg gh C.VV.arr_char D'.VVV.arr_char D'.VV.arr_char D'.comp_char
                D'.hcomp_def
        by simp
      qed
      finally show "D'.comp (F \<a>\<^sub>C[f, g, h])
                            (D'.comp (\<Phi> (f \<star>\<^sub>C g, h)) (D'.hcomp (\<Phi> (f, g)) (F h))) =
                    D'.comp (\<Phi> (f, g \<star>\<^sub>C h))
                            (D'.comp (D'.hcomp (F f) (\<Phi> (g, h))) (D'.\<a> (F f) (F g) (F h)))"
        by blast
    qed

    lemma is_pseudofunctor:
    shows "pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C D'.comp D'.hcomp D'.\<a> \<i>\<^sub>D D'.src D'.trg F \<Phi>"
      ..

    lemma map\<^sub>0_simp [simp]:
    assumes "C.obj a"
    shows "map\<^sub>0 a = F.map\<^sub>0 a"
      using assms map\<^sub>0_def D'.src_def by auto

    lemma unit_char':
    assumes "C.obj a"
    shows "F.unit a = unit a"
    proof (intro unit_eqI)
      show "C.obj a" by fact
      show 1: "D'.in_hom (F.unit a) (map\<^sub>0 a) (map a)"
      proof -
        have "D.in_hom (F.unit a) (F.map\<^sub>0 a) (map a)"
          using assms by auto
        moreover have "map\<^sub>0 a = map\<^sub>0 a"
          using assms map\<^sub>0_def D'.src_def by auto
        ultimately show ?thesis
          using assms D'.in_hom_char preserves_arr D'.arr_char
          by (metis (no_types, lifting) C.obj_def' D'.obj_def D'.src_def D.arrI
              D.vconn_implies_hpar(1,3) F.unit_simps(2-3) map\<^sub>0_def map\<^sub>0_simps(1))
      qed
      show "D'.iso (F.unit a)"
        using assms D'.iso_char D'.arr_char F.unit_char(2)
              \<open>D'.in_hom (F.unit a) (map\<^sub>0 a) (map a)\<close>
        by auto
      show "D'.comp (F.unit a) \<i>\<^sub>D[map\<^sub>0 a] =
            D'.comp (D'.comp (map \<i>\<^sub>C[a]) (cmp (a, a)))
                    (D'.hcomp (F.unit a) (F.unit a))"
      proof -
        have "D'.comp (F.unit a) \<i>\<^sub>D[map\<^sub>0 a] = F.unit a \<cdot>\<^sub>D \<i>\<^sub>D[src\<^sub>D (map a)]"
          using assms D'.comp_char D'.arr_char
          apply simp
          by (metis (no_types, lifting) C.obj_simps(1-2) F.preserves_src preserves_arr)
        also have "... = (map \<i>\<^sub>C[a] \<cdot>\<^sub>D cmp (a, a)) \<cdot>\<^sub>D (F.unit a \<star>\<^sub>D F.unit a)"
          using assms F.unit_char(3) [of a] by auto
        also have "... = D'.comp (D'.comp (map \<i>\<^sub>C[a]) (cmp (a, a)))
                                 (D'.hcomp (F.unit a) (F.unit a))"
        proof -
          have "D'.arr (map \<i>\<^sub>C[a] \<cdot>\<^sub>D cmp (a, a))"
            using assms D'.comp_simp by auto
          moreover have "D.seq (map \<i>\<^sub>C[a] \<cdot>\<^sub>D cmp (a, a)) (F.unit a \<star>\<^sub>D F.unit a)"
            using assms C.VV.arr_char F.cmp_simps(4-5)
            by (intro D.seqI) auto
          ultimately show ?thesis
            using assms 1 D'.comp_char D'.hcomp_def C.VV.arr_char D'.hseq_char
                  D'.arr_char F.\<i>_simps(2)
            by auto
        qed
        finally show ?thesis by blast
      qed
    qed

  end


  subsection "Equivalence Pseudofunctors"

  text \<open>
    In this section, we define ``equivalence pseudofunctors'', which are pseudofunctors
    that are locally fully faithful, locally essentially surjective, and biessentially
    surjective on objects.  In a later section, we will show that a pseudofunctor is
    an equivalence pseudofunctor if and only if it can be extended to an equivalence
    of bicategories.

    The definition below requires that an equivalence pseudofunctor be (globally) faithful
    with respect to vertical composition.  Traditional formulations do not consider a
    pseudofunctor as a single global functor, so we have to consider whether this condition
    is too strong.  In fact, a pseudofunctor (as defined here) is locally faithful if and
    only if it is globally faithful.
  \<close>

  context pseudofunctor
  begin

    definition locally_faithful
    where "locally_faithful \<equiv>
           \<forall>f g \<mu> \<mu>'. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C g\<guillemotright> \<and> \<guillemotleft>\<mu>' : f \<Rightarrow>\<^sub>C g\<guillemotright> \<and> F \<mu> = F \<mu>' \<longrightarrow> \<mu> = \<mu>'"

    lemma locally_faithful_iff_faithful:
    shows "locally_faithful \<longleftrightarrow> faithful_functor V\<^sub>C V\<^sub>D F"
    proof
      show "faithful_functor V\<^sub>C V\<^sub>D F \<Longrightarrow> locally_faithful"
      proof -
        assume 1: "faithful_functor V\<^sub>C V\<^sub>D F"
        interpret faithful_functor V\<^sub>C V\<^sub>D F
          using 1 by blast
        show "locally_faithful"
          unfolding locally_faithful_def using is_faithful by blast
      qed
      show "locally_faithful \<Longrightarrow> faithful_functor V\<^sub>C V\<^sub>D F"
      proof -
        assume 1: "locally_faithful"
        show "faithful_functor V\<^sub>C V\<^sub>D F"
        proof
          fix \<mu> \<mu>'
          assume par: "C.par \<mu> \<mu>'" and eq: "F \<mu> = F \<mu>'"
          obtain f g where fg: "\<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C g\<guillemotright> \<and> \<guillemotleft>\<mu>' : f \<Rightarrow>\<^sub>C g\<guillemotright>"
            using par by auto
          show "\<mu> = \<mu>'"
            using 1 fg locally_faithful_def eq by simp
        qed
      qed
    qed

  end

  text \<open>
    In contrast, it is not true that a pseudofunctor that is locally full is also
    globally full, because we can have \<open>\<guillemotleft>\<nu> : F h \<Rightarrow>\<^sub>D F k\<guillemotright>\<close> even if \<open>h\<close> and \<open>k\<close>
    are not in the same hom-category.  So it would be a mistake to require that an
    equivalence functor be globally full.
  \<close>

  locale equivalence_pseudofunctor =
    pseudofunctor +
    faithful_functor V\<^sub>C V\<^sub>D F +
  assumes biessentially_surjective_on_objects:
            "D.obj a' \<Longrightarrow> \<exists>a. C.obj a \<and> D.equivalent_objects (map\<^sub>0 a) a'"
  and locally_essentially_surjective:
            "\<lbrakk> C.obj a; C.obj b; \<guillemotleft>g : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright>; D.ide g \<rbrakk> \<Longrightarrow>
                \<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) g"
  and locally_full:
            "\<lbrakk> C.ide f; C.ide f'; src\<^sub>C f = src\<^sub>C f'; trg\<^sub>C f = trg\<^sub>C f'; \<guillemotleft>\<nu> : F f \<Rightarrow>\<^sub>D F f'\<guillemotright> \<rbrakk> \<Longrightarrow>
                \<exists>\<mu>. \<guillemotleft>\<mu> : f \<Rightarrow>\<^sub>C f'\<guillemotright> \<and> F \<mu> = \<nu>"
  begin

    lemma reflects_ide:
    assumes "C.endo \<mu>" and "D.ide (F \<mu>)"
    shows "C.ide \<mu>"
      using assms is_faithful [of "C.dom \<mu>" \<mu>] C.ide_char'
      by (metis C.arr_dom C.cod_dom C.dom_dom C.seqE D.ide_char preserves_dom)

    lemma reflects_iso:
    assumes "C.arr \<mu>" and "D.iso (F \<mu>)"
    shows "C.iso \<mu>"
    proof -
      obtain \<mu>' where \<mu>': "\<guillemotleft>\<mu>' : C.cod \<mu> \<Rightarrow>\<^sub>C C.dom \<mu>\<guillemotright> \<and> F \<mu>' = D.inv (F \<mu>)"
        using assms locally_full [of "C.cod \<mu>" "C.dom \<mu>" "D.inv (F \<mu>)"]
              D.inv_in_hom C.in_homE preserves_hom C.in_homI
        by auto
      have "C.inverse_arrows \<mu> \<mu>'"
        using assms \<mu>' reflects_ide
        apply (intro C.inverse_arrowsI)
         apply (metis C.cod_comp C.dom_comp C.ide_dom C.in_homE C.seqI D.comp_inv_arr'
                faithful_functor_axioms faithful_functor_def functor.preserves_ide
                preserves_comp_2 preserves_dom)
        by (metis C.cod_comp C.dom_comp C.ide_cod C.in_homE C.seqI D.comp_arr_inv'
            faithful_functor_axioms faithful_functor_def functor.preserves_ide
            preserves_cod preserves_comp_2)
      thus ?thesis by auto
    qed

    lemma reflects_isomorphic:
    assumes "C.ide f" and "C.ide f'" and "src\<^sub>C f = src\<^sub>C f'" and "trg\<^sub>C f = trg\<^sub>C f'"
    and "D.isomorphic (F f) (F f')"
    shows "C.isomorphic f f'"
      using assms C.isomorphic_def D.isomorphic_def locally_full reflects_iso C.arrI
      by metis

    lemma reflects_equivalence:
    assumes "C.ide f" and "C.ide g"
    and "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>" and "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>"
    and "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
           (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f))
           (D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g))"
    shows "equivalence_in_bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
    proof -
      interpret E': equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> \<open>F g\<close>
                      \<open>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f)\<close>
                      \<open>D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)\<close>
        using assms by auto
      show ?thesis
      proof
        show "C.ide f"
          using assms(1) by simp
        show "C.ide g"
          using assms(2) by simp
        show "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>"
          using assms(3) by simp
        show "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>"
          using assms(4) by simp
        have 0: "src\<^sub>C f = trg\<^sub>C g \<and> src\<^sub>C g = trg\<^sub>C f"
          using \<open>\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>\<close>
          by (metis C.hseqE C.ideD(1) C.ide_cod C.ide_dom C.in_homE assms(4))
        show "C.iso \<eta>"
        proof -
          have "D.iso (F \<eta>)"
          proof -
            have 1:  "\<guillemotleft>D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f) : map\<^sub>0 (src\<^sub>C f) \<Rightarrow>\<^sub>D F g \<star>\<^sub>D F f\<guillemotright>"
              using \<open>C.ide f\<close> \<open>C.ide g\<close> \<open>\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>\<close>
                    unit_char cmp_in_hom cmp_components_are_iso
              by (metis (mono_tags, lifting) C.ideD(1) E'.unit_in_vhom preserves_src)
            have 2: "D.iso (\<Phi> (g, f)) \<and> \<guillemotleft>\<Phi> (g, f) : F g \<star>\<^sub>D F f \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C f)\<guillemotright>"
              using 0 \<open>C.ide f\<close> \<open>C.ide g\<close> cmp_in_hom by simp
            have 3: "D.iso (D.inv (unit (src\<^sub>C f))) \<and>
                     \<guillemotleft>D.inv (unit (src\<^sub>C f)) : F (src\<^sub>C f) \<Rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C f)\<guillemotright>"
               using \<open>C.ide f\<close> unit_char by simp
            have "D.iso (\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f)) \<cdot>\<^sub>D
                    D.inv (unit (src\<^sub>C f)))"
              using 1 2 3 E'.unit_is_iso D.isos_compose by blast
            moreover have "\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f)) \<cdot>\<^sub>D
                             D.inv (unit (src\<^sub>C f)) =
                           F \<eta>"
            proof -
              have "\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f)) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D unit (src\<^sub>C f)) \<cdot>\<^sub>D
                    D.inv (unit (src\<^sub>C f))
                      = (\<Phi> (g, f) \<cdot>\<^sub>D (D.inv (\<Phi> (g, f))) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D (unit (src\<^sub>C f)) \<cdot>\<^sub>D
                        D.inv (unit (src\<^sub>C f)))"
                using D.comp_assoc by simp
              also have "... = F (g \<star>\<^sub>C f) \<cdot>\<^sub>D F \<eta> \<cdot>\<^sub>D F (src\<^sub>C f)"
                using 2 3 D.comp_arr_inv D.comp_inv_arr D.inv_is_inverse
                by (metis C.ideD(1) C.obj_src D.comp_assoc D.dom_inv D.in_homE unit_char(2)
                          assms(1))
              also have "... = F \<eta>"
                using \<open>\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright>\<close> D.comp_arr_dom D.comp_cod_arr by auto
              finally show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          qed
          thus ?thesis
            using assms reflects_iso by auto
        qed
        show "C.iso \<epsilon>"
        proof -
          have "D.iso (F \<epsilon>)"
          proof -
            have 1:  "\<guillemotleft>D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g) : F f \<star>\<^sub>D F g \<Rightarrow>\<^sub>D map\<^sub>0 (src\<^sub>C g)\<guillemotright>"
              using \<open>C.ide f\<close> \<open>C.ide g\<close> \<open>\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>\<close>
                    unit_char cmp_in_hom cmp_components_are_iso
              by (metis (mono_tags, lifting) C.ideD(1) E'.counit_in_vhom preserves_src)
            have 2: "D.iso (D.inv (\<Phi> (f, g))) \<and>
                     \<guillemotleft>D.inv (\<Phi> (f, g)) : F (f \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F g\<guillemotright>"
              using 0 \<open>C.ide f\<close> \<open>C.ide g\<close> \<open>\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>\<close> cmp_in_hom(2) D.inv_in_hom
              by simp
            have 3: "D.iso (unit (trg\<^sub>C f)) \<and> \<guillemotleft>unit (trg\<^sub>C f) : map\<^sub>0 (trg\<^sub>C f) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
               using \<open>C.ide f\<close> unit_char by simp
            have "D.iso (unit (trg\<^sub>C f) \<cdot>\<^sub>D (D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                  D.inv (\<Phi> (f, g)))"
              using 0 1 2 3 E'.counit_is_iso D.isos_compose
              by (metis D.arrI D.cod_comp D.cod_inv D.seqI D.seqI')
            moreover have "unit (trg\<^sub>C f) \<cdot>\<^sub>D (D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                             D.inv (\<Phi> (f, g)) =
                           F \<epsilon>"
            proof -
              have "unit (trg\<^sub>C f) \<cdot>\<^sub>D (D.inv (unit (trg\<^sub>C f)) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D \<Phi> (f, g)) \<cdot>\<^sub>D
                      D.inv (\<Phi> (f, g)) =
                    (unit (trg\<^sub>C f) \<cdot>\<^sub>D D.inv (unit (trg\<^sub>C f))) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D (\<Phi> (f, g) \<cdot>\<^sub>D D.inv (\<Phi> (f, g)))"
                using D.comp_assoc by simp
              also have "... = F (trg\<^sub>C f) \<cdot>\<^sub>D F \<epsilon> \<cdot>\<^sub>D F (f \<star>\<^sub>C g)"
                using 0 3 D.comp_arr_inv' D.comp_inv_arr'
                by (simp add: C.VV.arr_char C.VV.ide_char assms(1-2))
              also have "... = F \<epsilon>"
                using 0 \<open>\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright>\<close> D.comp_arr_dom D.comp_cod_arr by auto
              finally show ?thesis by simp
            qed
            ultimately show ?thesis by simp
          qed
          thus ?thesis
            using assms reflects_iso by auto
        qed
      qed
    qed

    lemma reflects_equivalence_map:
    assumes "C.ide f" and "D.equivalence_map (F f)"
    shows "C.equivalence_map f"
    proof -
      obtain g' \<phi> \<psi> where E': "equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) g' \<phi> \<psi>"
        using assms D.equivalence_map_def by auto
      interpret E': equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> g' \<phi> \<psi>
        using E' by auto
      obtain g where g: "\<guillemotleft>g : trg\<^sub>C f \<rightarrow>\<^sub>C src\<^sub>C f\<guillemotright> \<and> C.ide g \<and> D.isomorphic (F g) g'"
        using assms E'.antipar locally_essentially_surjective [of "trg\<^sub>C f" "src\<^sub>C f" g']
        by auto
      obtain \<mu> where \<mu>: "\<guillemotleft>\<mu> : g' \<Rightarrow>\<^sub>D F g\<guillemotright> \<and> D.iso \<mu>"
        using g D.isomorphic_def D.isomorphic_symmetric by blast
      have E'': "equivalence_in_bicategory (\<cdot>\<^sub>D) (\<star>\<^sub>D) \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D (F f) (F g)
                   ((F g \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D F f) \<cdot>\<^sub>D \<phi>)
                   (\<psi> \<cdot>\<^sub>D (D.inv (F f) \<star>\<^sub>D g') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<mu>))"
        using assms \<mu> E'.equivalence_in_bicategory_axioms D.ide_is_iso
              D.equivalence_respects_iso [of "F f" g' \<phi> \<psi> "F f" "F f" \<mu> "F g"]
        by auto
      interpret E'': equivalence_in_bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>F f\<close> \<open>F g\<close>
                       \<open>(F g \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D F f) \<cdot>\<^sub>D \<phi>\<close>
                       \<open>\<psi> \<cdot>\<^sub>D (D.inv (F f) \<star>\<^sub>D g') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<mu>)\<close>
        using E'' by auto
      let ?\<eta>' = "\<Phi> (g, f) \<cdot>\<^sub>D (F g \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<mu> \<star>\<^sub>D F f) \<cdot>\<^sub>D \<phi> \<cdot>\<^sub>D D.inv (unit (src\<^sub>C f))"
      have \<eta>': "\<guillemotleft>?\<eta>' : F (src\<^sub>C f) \<Rightarrow>\<^sub>D F (g \<star>\<^sub>C f)\<guillemotright>"
        using assms \<mu> g unit_char  E'.unit_in_hom(2) E'.antipar E''.antipar cmp_in_hom
        apply (intro D.comp_in_homI)
            apply auto
        using E'.antipar(2) by blast
      have iso_\<eta>': "D.iso ?\<eta>'"
        using assms g \<mu> \<eta>' E'.antipar E''.antipar cmp_in_hom unit_char
              E'.unit_in_hom E'.unit_is_iso
        by (intro D.isos_compose) auto
      let ?\<epsilon>' = "unit (src\<^sub>C g) \<cdot>\<^sub>D \<psi> \<cdot>\<^sub>D (D.inv (F f) \<star>\<^sub>D g') \<cdot>\<^sub>D (F f \<star>\<^sub>D D.inv \<mu>) \<cdot>\<^sub>D
                 D.inv (\<Phi> (f, g))"
      have \<epsilon>': "\<guillemotleft>?\<epsilon>' : F (f \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
      proof (intro D.comp_in_homI)
        show "\<guillemotleft>D.inv (\<Phi> (f, g)) : F (f \<star>\<^sub>C g) \<Rightarrow>\<^sub>D F f \<star>\<^sub>D F g\<guillemotright>"
          using assms g cmp_in_hom C.VV.ide_char C.VV.arr_char by auto
        show "\<guillemotleft>F f \<star>\<^sub>D D.inv \<mu> : F f \<star>\<^sub>D F g \<Rightarrow>\<^sub>D F f \<star>\<^sub>D g'\<guillemotright>"
          using assms g \<mu> E'.antipar E''.antipar D.ide_in_hom(2) by auto
        show "\<guillemotleft>D.inv (F f) \<star>\<^sub>D g' : F f \<star>\<^sub>D g' \<Rightarrow>\<^sub>D F f \<star>\<^sub>D g'\<guillemotright>"
          using assms E'.antipar E''.antipar D.ide_is_iso
          by (simp add: D.ide_in_hom(2))
        show "\<guillemotleft>\<psi> :  F f \<star>\<^sub>D g' \<Rightarrow>\<^sub>D trg\<^sub>D (F f)\<guillemotright>"
          using E'.counit_in_hom by simp
        show "\<guillemotleft>unit (src\<^sub>C g) : trg\<^sub>D (F f) \<Rightarrow>\<^sub>D F (trg\<^sub>C f)\<guillemotright>"
          using assms g unit_char E'.antipar by auto
      qed
      have iso_\<epsilon>': "D.iso ?\<epsilon>'"
      proof -
        have "D.iso (\<Phi> (f, g))"
          using assms g C.VV.ide_char C.VV.arr_char by auto
        thus ?thesis
          using assms g \<mu> E'.antipar E''.antipar cmp_in_hom unit_char
                E'.counit_in_hom D.iso_inv_iso E'.counit_is_iso \<epsilon>'
          by (metis C.ideD(1) C.obj_src D.arrI D.iso_hcomp D.hseq_char D.ide_is_iso
              D.isos_compose D.seqE E'.ide_right components_are_iso)
      qed
      obtain \<eta> where \<eta>: "\<guillemotleft>\<eta> : src\<^sub>C f \<Rightarrow>\<^sub>C g \<star>\<^sub>C f\<guillemotright> \<and> F \<eta> = ?\<eta>'"
        using assms g E'.antipar \<eta>' locally_full [of "src\<^sub>C f" "g \<star>\<^sub>C f" ?\<eta>']
        by (metis C.ide_hcomp C.ideD(1) C.in_hhomE C.src.preserves_ide C.hcomp_simps(1-2)
            C.src_trg C.trg_trg)
      have iso_\<eta>: "C.iso \<eta>"
        using \<eta> \<eta>' iso_\<eta>' reflects_iso by auto
      have 1: "\<exists>\<epsilon>. \<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright> \<and> F \<epsilon> = ?\<epsilon>'"
        using assms g \<epsilon>' locally_full [of "f \<star>\<^sub>C g" "src\<^sub>C g" ?\<epsilon>'] by force
      obtain \<epsilon> where \<epsilon>: "\<guillemotleft>\<epsilon> : f \<star>\<^sub>C g \<Rightarrow>\<^sub>C src\<^sub>C g\<guillemotright> \<and> F \<epsilon> = ?\<epsilon>'"
        using 1 by blast
      have iso_\<epsilon>: "C.iso \<epsilon>"
        using \<epsilon> \<epsilon>' iso_\<epsilon>' reflects_iso by auto
      have "equivalence_in_bicategory (\<cdot>\<^sub>C) (\<star>\<^sub>C) \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C f g \<eta> \<epsilon>"
        using assms g \<eta> \<epsilon> iso_\<eta> iso_\<epsilon> by (unfold_locales, auto)
      thus ?thesis
        using C.equivalence_map_def by auto
    qed

    lemma reflects_equivalent_objects:
    assumes "C.obj a" and "C.obj b" and "D.equivalent_objects (map\<^sub>0 a) (map\<^sub>0 b)"
    shows "C.equivalent_objects a b"
    proof -
      obtain f' where f': "\<guillemotleft>f' : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 b\<guillemotright> \<and> D.equivalence_map f'"
        using assms D.equivalent_objects_def D.equivalence_map_def by auto
      obtain f where f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright> \<and> C.ide f \<and> D.isomorphic (F f) f'"
        using assms f' locally_essentially_surjective [of a b f'] D.equivalence_map_is_ide
        by auto
      have "D.equivalence_map (F f)"
        using f f' D.equivalence_map_preserved_by_iso [of f' "F f"] D.isomorphic_symmetric
        by simp
      hence "C.equivalence_map f"
        using f f' reflects_equivalence_map [of f] by simp
      thus ?thesis
        using f C.equivalent_objects_def by auto
    qed

  end

  text\<open>
    For each pair of objects \<open>a\<close>, \<open>b\<close> of \<open>C\<close>, an equivalence pseudofunctor restricts
    to an equivalence of categories between \<open>C.hhom a b\<close> and \<open>D.hhom (map\<^sub>0 a) (map\<^sub>0 b)\<close>.
  \<close>

  (* TODO: Change the "perspective" of this locale to be the defined functor. *)
  locale equivalence_pseudofunctor_at_hom =
    equivalence_pseudofunctor +
  fixes a :: 'a and a' :: 'a
  assumes obj_a: "C.obj a"
  and obj_a': "C.obj a'"
  begin

    sublocale hhom\<^sub>C: subcategory V\<^sub>C \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : a \<rightarrow>\<^sub>C a'\<guillemotright>\<close>
      using C.hhom_is_subcategory by simp
    sublocale hhom\<^sub>D: subcategory V\<^sub>D \<open>\<lambda>\<mu>. \<guillemotleft>\<mu> : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>\<close>
      using D.hhom_is_subcategory by simp

    definition F\<^sub>1
    where "F\<^sub>1 = (\<lambda>\<mu>. if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null)"

    interpretation F\<^sub>1: "functor" hhom\<^sub>C.comp hhom\<^sub>D.comp F\<^sub>1
      unfolding F\<^sub>1_def
      using hhom\<^sub>C.arr_char hhom\<^sub>D.arr_char hhom\<^sub>C.dom_char hhom\<^sub>D.dom_char
            hhom\<^sub>C.cod_char hhom\<^sub>D.cod_char hhom\<^sub>C.seq_char hhom\<^sub>C.comp_char hhom\<^sub>D.comp_char
      by unfold_locales auto

    interpretation F\<^sub>1: fully_faithful_and_essentially_surjective_functor
                         hhom\<^sub>C.comp hhom\<^sub>D.comp F\<^sub>1
    proof
      show "\<And>\<mu> \<mu>'. \<lbrakk>hhom\<^sub>C.par \<mu> \<mu>'; F\<^sub>1 \<mu> = F\<^sub>1 \<mu>'\<rbrakk> \<Longrightarrow> \<mu> = \<mu>'"
        unfolding F\<^sub>1_def
        using is_faithful hhom\<^sub>C.dom_char hhom\<^sub>D.dom_char hhom\<^sub>C.cod_char hhom\<^sub>D.cod_char
        by (metis C.in_hhom_def hhom\<^sub>C.arrE)
      show "\<And>f f' \<nu>. \<lbrakk>hhom\<^sub>C.ide f; hhom\<^sub>C.ide f'; hhom\<^sub>D.in_hom \<nu> (F\<^sub>1 f') (F\<^sub>1 f)\<rbrakk>
               \<Longrightarrow> \<exists>\<mu>. hhom\<^sub>C.in_hom \<mu> f' f \<and> F\<^sub>1 \<mu> = \<nu>"
      proof (unfold F\<^sub>1_def)
        fix f f' \<nu>
        assume f: "hhom\<^sub>C.ide f" and f': "hhom\<^sub>C.ide f'"
        assume "hhom\<^sub>D.in_hom \<nu> (if hhom\<^sub>C.arr f' then F f' else D.null)
                              (if hhom\<^sub>C.arr f then F f else D.null)"
        hence \<nu>: "hhom\<^sub>D.in_hom \<nu> (F f') (F f)"
          using f f' by simp
        have "\<exists>\<mu>. hhom\<^sub>C.in_hom \<mu> f' f \<and> F \<mu> = \<nu>"
        proof -
          have 1: "src\<^sub>C f' = src\<^sub>C f \<and> trg\<^sub>C f' = trg\<^sub>C f"
            using f f' hhom\<^sub>C.ide_char by (metis C.in_hhomE hhom\<^sub>C.arrE)
          hence ex: "\<exists>\<mu>. C.in_hom \<mu> f' f \<and> F \<mu> = \<nu>"
            using f f' \<nu> hhom\<^sub>C.in_hom_char hhom\<^sub>D.in_hom_char hhom\<^sub>C.ide_char locally_full
            by simp
          obtain \<mu> where \<mu>: "C.in_hom \<mu> f' f \<and> F \<mu> = \<nu>"
            using ex by blast
          have "hhom\<^sub>C.in_hom \<mu> f' f"
          proof -
            have 2: "hhom\<^sub>C.arr f' \<and> hhom\<^sub>C.arr f"
              using f f' hhom\<^sub>C.arr_char hhom\<^sub>C.ide_char by simp
            moreover have "hhom\<^sub>C.arr \<mu>"
              using \<mu> 1 2 hhom\<^sub>C.arr_char C.arrI C.vconn_implies_hpar(1-2) by auto
            ultimately show ?thesis
              using f f' \<mu> hhom\<^sub>C.arr_char hhom\<^sub>C.ide_char hhom\<^sub>C.in_hom_char by simp
          qed
          thus ?thesis
            using \<mu> by auto
        qed
        thus "\<exists>\<mu>. hhom\<^sub>C.in_hom \<mu> f' f \<and> (if hhom\<^sub>C.arr \<mu> then F \<mu> else D.null) = \<nu>"
          by auto
      qed
      show "\<And>g. hhom\<^sub>D.ide g \<Longrightarrow> \<exists>f. hhom\<^sub>C.ide f \<and> hhom\<^sub>D.isomorphic (F\<^sub>1 f) g"
      proof (unfold F\<^sub>1_def)
        fix g
        assume g: "hhom\<^sub>D.ide g"
        show "\<exists>f. hhom\<^sub>C.ide f \<and> hhom\<^sub>D.isomorphic (if hhom\<^sub>C.arr f then F f else D.null) g"
        proof -
          have "C.obj a \<and> C.obj a'"
            using obj_a obj_a' by simp
          moreover have 1: "D.ide g \<and> \<guillemotleft>g : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>"
            using g obj_a obj_a' hhom\<^sub>D.ide_char by auto
          ultimately have 2: "\<exists>f. C.in_hhom f a a' \<and> C.ide f \<and> D.isomorphic (F f) g"
            using locally_essentially_surjective [of a a' g] by simp
          obtain f \<phi> where f: "C.in_hhom f a a' \<and> C.ide f \<and> D.in_hom \<phi> (F f) g \<and> D.iso \<phi>"
            using 2 by auto
          have "hhom\<^sub>C.ide f"
            using f hhom\<^sub>C.ide_char hhom\<^sub>C.arr_char by simp
          moreover have "hhom\<^sub>D.isomorphic (F f) g"
          proof -
            have "hhom\<^sub>D.arr \<phi> \<and> hhom\<^sub>D.arr (D.inv \<phi>)"
              using f 1 hhom\<^sub>D.arr_char D.in_hhom_def by auto
            hence "hhom\<^sub>D.in_hom \<phi> (F f) g \<and> hhom\<^sub>D.iso \<phi>"
              using f g hhom\<^sub>D.in_hom_char hhom\<^sub>D.iso_char hhom\<^sub>C.arr_char hhom\<^sub>D.arr_char
                    hhom\<^sub>D.ideD(1) preserves_arr
              by (simp add: C.in_hhom_def)
            thus ?thesis
              unfolding hhom\<^sub>D.isomorphic_def by blast
          qed
          ultimately show "\<exists>f. hhom\<^sub>C.ide f \<and>
                               hhom\<^sub>D.isomorphic (if hhom\<^sub>C.arr f then F f else D.null) g"
            by force
        qed
      qed
    qed

    lemma equivalence_functor_F\<^sub>1:
    shows "fully_faithful_and_essentially_surjective_functor hhom\<^sub>C.comp hhom\<^sub>D.comp F\<^sub>1"
    and "equivalence_functor hhom\<^sub>C.comp hhom\<^sub>D.comp F\<^sub>1"
      ..

    definition G\<^sub>1
    where "G\<^sub>1 = (SOME G. \<exists>\<eta>\<epsilon>.
                 adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G F\<^sub>1 (fst \<eta>\<epsilon>) (snd \<eta>\<epsilon>))"

    lemma G\<^sub>1_props:
    assumes "C.obj a" and "C.obj a'"
    shows "\<exists>\<eta> \<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta> \<epsilon>"
    proof -
      have "\<exists>G. \<exists>\<eta>\<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G F\<^sub>1 (fst \<eta>\<epsilon>) (snd \<eta>\<epsilon>)"
        using F\<^sub>1.extends_to_adjoint_equivalence by simp
      hence "\<exists>\<eta>\<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 (fst \<eta>\<epsilon>) (snd \<eta>\<epsilon>)"
        unfolding G\<^sub>1_def
        using someI_ex
                [of "\<lambda>G. \<exists>\<eta>\<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G F\<^sub>1 (fst \<eta>\<epsilon>) (snd \<eta>\<epsilon>)"]
        by blast
      thus ?thesis by simp
    qed

    definition \<eta>
    where "\<eta> = (SOME \<eta>. \<exists>\<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta> \<epsilon>)"

    definition \<epsilon>
    where "\<epsilon> = (SOME \<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta> \<epsilon>)"

    lemma \<eta>\<epsilon>_props:
    shows "adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta> \<epsilon>"
      using obj_a obj_a' \<eta>_def \<epsilon>_def G\<^sub>1_props
            someI_ex [of "\<lambda>\<eta>. \<exists>\<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta> \<epsilon>"]
            someI_ex [of "\<lambda>\<epsilon>. adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta> \<epsilon>"]
      by simp

    sublocale \<eta>\<epsilon>: adjoint_equivalence hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta> \<epsilon>
      using \<eta>\<epsilon>_props by simp

    sublocale \<eta>\<epsilon>: meta_adjunction hhom\<^sub>C.comp hhom\<^sub>D.comp G\<^sub>1 F\<^sub>1 \<eta>\<epsilon>.\<phi> \<eta>\<epsilon>.\<psi>
      using \<eta>\<epsilon>.induces_meta_adjunction by simp

  end

  context identity_pseudofunctor
  begin

    sublocale equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
                map cmp
    proof
      show "\<And>f f'. \<lbrakk>B.par f f'; map f = map f'\<rbrakk> \<Longrightarrow> f = f'"
        by simp
      show "\<And>a'. B.obj a' \<Longrightarrow> \<exists>a. B.obj a \<and> B.equivalent_objects (map\<^sub>0 a) a'"
        by (auto simp add: B.equivalent_objects_reflexive map\<^sub>0_def B.obj_simps)
      show "\<And>a b g. \<lbrakk>B.obj a; B.obj b; B.in_hhom g (map\<^sub>0 a) (map\<^sub>0 b); B.ide g\<rbrakk>
                       \<Longrightarrow> \<exists>f. B.in_hhom f a b \<and> B.ide f \<and> B.isomorphic (map f) g"
        using B.isomorphic_reflexive map\<^sub>0_def B.obj_simps by auto
      show "\<And>f f' \<nu>. \<lbrakk>B.ide f; B.ide f'; src\<^sub>B f = src\<^sub>B f'; trg\<^sub>B f = trg\<^sub>B f';
                      \<guillemotleft>\<nu> : map f \<rightarrow>\<^sub>B map f'\<guillemotright>\<rbrakk>
                       \<Longrightarrow> \<exists>\<mu>. \<guillemotleft>\<mu> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> map \<mu> = \<nu>"
        using B.arrI by auto
     qed

     lemma is_equivalence_pseudofunctor:
     shows "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B
              map cmp"
       ..

  end

  locale composite_equivalence_pseudofunctor =
    composite_pseudofunctor +
    F: equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C F \<Phi>\<^sub>F +
    G: equivalence_pseudofunctor V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
  begin

    interpretation faithful_functor V\<^sub>B V\<^sub>D \<open>G o F\<close>
      using F.faithful_functor_axioms G.faithful_functor_axioms faithful_functors_compose
      by blast

    interpretation equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                     \<open>G o F\<close> cmp
    proof
      show "\<And>c. D.obj c \<Longrightarrow> \<exists>a. B.obj a \<and> D.equivalent_objects (map\<^sub>0 a) c"
      proof -
        fix c
        assume c: "D.obj c"
        obtain b where b: "C.obj b \<and> D.equivalent_objects (G.map\<^sub>0 b) c"
          using c G.biessentially_surjective_on_objects by auto
        obtain a where a: "B.obj a \<and> C.equivalent_objects (F.map\<^sub>0 a) b"
          using b F.biessentially_surjective_on_objects by auto
        have "D.equivalent_objects (map\<^sub>0 a) c"
          using a b map\<^sub>0_def G.preserves_equivalent_objects D.equivalent_objects_transitive
          by fastforce
        thus "\<exists>a. B.obj a \<and> D.equivalent_objects (map\<^sub>0 a) c"
          using a by auto
      qed
      show "\<And>a a' h. \<lbrakk>B.obj a; B.obj a'; \<guillemotleft>h : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>; D.ide h\<rbrakk>
                 \<Longrightarrow> \<exists>f. B.in_hhom f a a' \<and> B.ide f \<and> D.isomorphic ((G \<circ> F) f) h"
      proof -
        fix a a' h
        assume a: "B.obj a" and a': "B.obj a'"
        and h_in_hom: "\<guillemotleft>h : map\<^sub>0 a \<rightarrow>\<^sub>D map\<^sub>0 a'\<guillemotright>" and ide_h: "D.ide h"
        obtain g
          where g: "C.in_hhom g (F.map\<^sub>0 a) (F.map\<^sub>0 a') \<and> C.ide g \<and> D.isomorphic (G g) h"
          using a a' h_in_hom ide_h map\<^sub>0_def B.obj_simps
                G.locally_essentially_surjective [of "F.map\<^sub>0 a" "F.map\<^sub>0 a'" h]
          by auto
        obtain f where f: "B.in_hhom f a a' \<and> B.ide f \<and> C.isomorphic (F f) g"
          using a a' g F.locally_essentially_surjective by blast
        have "D.isomorphic ((G o F) f) h"
        proof -
          have "(G o F) f = G (F f)"
            by simp
          also have "D.isomorphic ... (G g)"
            using f G.preserves_iso D.isomorphic_def by blast
          also have "D.isomorphic ... h"
            using g by simp
          finally show "D.isomorphic ((G \<circ> F) f) h" by simp
        qed
        thus "\<exists>f. B.in_hhom f a a' \<and> B.ide f \<and> D.isomorphic ((G \<circ> F) f) h"
          using f by auto
      qed
      show "\<And>f f' \<nu>. \<lbrakk>B.ide f; B.ide f'; src\<^sub>B f = src\<^sub>B f'; trg\<^sub>B f = trg\<^sub>B f';
                       \<guillemotleft>\<nu> : (G \<circ> F) f \<Rightarrow>\<^sub>D (G \<circ> F) f'\<guillemotright>\<rbrakk>
                 \<Longrightarrow> \<exists>\<tau>. \<guillemotleft>\<tau> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> (G \<circ> F) \<tau> = \<nu>"
      proof -
        fix f f' \<nu>
        assume f: "B.ide f" and f': "B.ide f'"
        and src: "src\<^sub>B f = src\<^sub>B f'" and trg: "trg\<^sub>B f = trg\<^sub>B f'"
        and \<nu>: "\<guillemotleft>\<nu> : (G \<circ> F) f \<Rightarrow>\<^sub>D (G \<circ> F) f'\<guillemotright>"
        have \<nu>: "\<guillemotleft>\<nu> : G (F f) \<Rightarrow>\<^sub>D G (F f')\<guillemotright>"
          using \<nu> by simp
        have 1: "src\<^sub>C (F f) = src\<^sub>C (F f') \<and> trg\<^sub>C (F f) = trg\<^sub>C (F f')"
          using f f' src trg by simp
        have 2: "\<exists>\<mu>. \<guillemotleft>\<mu> : F f \<Rightarrow>\<^sub>C F f'\<guillemotright> \<and> G \<mu> = \<nu>"
          using f f' 1 \<nu> G.locally_full F.preserves_ide by simp
        obtain \<mu> where \<mu>: "\<guillemotleft>\<mu> : F f \<Rightarrow>\<^sub>C F f'\<guillemotright> \<and> G \<mu> = \<nu>"
          using 2 by auto
        obtain \<tau> where \<tau>: "\<guillemotleft>\<tau> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> F \<tau> = \<mu>"
          using f f' src trg 2 \<mu> F.locally_full by blast
        show "\<exists>\<tau>. \<guillemotleft>\<tau> : f \<rightarrow>\<^sub>B f'\<guillemotright> \<and> (G \<circ> F) \<tau> = \<nu>"
          using \<mu> \<tau> by auto
      qed
    qed

    sublocale equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                \<open>G o F\<close> cmp ..

    lemma is_equivalence_pseudofunctor:
    shows "equivalence_pseudofunctor V\<^sub>B H\<^sub>B \<a>\<^sub>B \<i>\<^sub>B src\<^sub>B trg\<^sub>B V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D
                (G o F) cmp"
      ..

  end

end
