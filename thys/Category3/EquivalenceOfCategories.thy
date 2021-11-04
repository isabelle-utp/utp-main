(*  Title:       EquivalenceOfCategories
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2017
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Equivalence of Categories"

text \<open>
  In this chapter we define the notions of equivalence and adjoint equivalence of categories
  and establish some properties of functors that are part of an equivalence.
\<close>

theory EquivalenceOfCategories
imports Adjunction
begin

  locale equivalence_of_categories =
    C: category C +
    D: category D +
    F: "functor" D C F +
    G: "functor" C D G +
    \<eta>: natural_isomorphism D D D.map "G o F" \<eta> +
    \<epsilon>: natural_isomorphism C C "F o G" C.map \<epsilon>
  for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
  and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
  and F :: "'d \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<eta> :: "'d \<Rightarrow> 'd"
  and \<epsilon> :: "'c \<Rightarrow> 'c"
  begin

    notation C.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")

    lemma C_arr_expansion:
    assumes "C.arr f"
    shows "\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f)) = f"
    and "C.inv (\<epsilon> (C.cod f)) \<cdot>\<^sub>C f \<cdot>\<^sub>C \<epsilon> (C.dom f) = F (G f)"
    proof -
      have \<epsilon>_dom: "C.inverse_arrows (\<epsilon> (C.dom f)) (C.inv (\<epsilon> (C.dom f)))"
        using assms C.inv_is_inverse by auto
      have \<epsilon>_cod: "C.inverse_arrows (\<epsilon> (C.cod f)) (C.inv (\<epsilon> (C.cod f)))"
        using assms C.inv_is_inverse by auto
      have "\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f)) =
            (\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f)) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f))"
        using C.comp_assoc by force
      also have 1: "... = (f \<cdot>\<^sub>C \<epsilon> (C.dom f)) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f))"
        using assms \<epsilon>.naturality by simp
      also have 2: "... = f"
        using assms \<epsilon>_dom C.comp_arr_inv C.comp_arr_dom C.comp_assoc by force
      finally show "\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f) \<cdot>\<^sub>C C.inv (\<epsilon> (C.dom f)) = f" by blast
      show "C.inv (\<epsilon> (C.cod f)) \<cdot>\<^sub>C f \<cdot>\<^sub>C \<epsilon> (C.dom f) = F (G f)"
        using assms 1 2 \<epsilon>_dom \<epsilon>_cod C.invert_side_of_triangle C.isoI C.iso_inv_iso
        by metis
    qed

    lemma G_is_faithful:
    shows "faithful_functor C D G"
    proof
      fix f f'
      assume par: "C.par f f'" and eq: "G f = G f'"
      show "f = f'"
      proof -
        have "C.inv (\<epsilon> (C.cod f)) \<in> C.hom (C.cod f) (F (G (C.cod f))) \<and>
              C.iso (C.inv (\<epsilon> (C.cod f)))"
          using par by auto
        moreover have 1: "\<epsilon> (C.dom f) \<in> C.hom (F (G (C.dom f))) (C.dom f) \<and>
                          C.iso (\<epsilon> (C.dom f))"
          using par by auto
        ultimately have 2: "f \<cdot>\<^sub>C \<epsilon> (C.dom f) = f' \<cdot>\<^sub>C \<epsilon> (C.dom f)"
          using par C_arr_expansion eq C.iso_is_section C.section_is_mono
          by (metis C_arr_expansion(1) eq)
        show ?thesis
        proof -
          have "C.epi (\<epsilon> (C.dom f))"
            using 1 par C.iso_is_retraction C.retraction_is_epi by blast
          thus ?thesis using 2 par by auto
        qed
      qed
    qed

    lemma G_is_essentially_surjective:
    shows "essentially_surjective_functor C D G"
    proof
      fix b
      assume b: "D.ide b"
      have "C.ide (F b) \<and> D.isomorphic (G (F b)) b"
      proof
        show "C.ide (F b)" using b by simp
        show "D.isomorphic (G (F b)) b"
        proof (unfold D.isomorphic_def)
          have "\<guillemotleft>D.inv (\<eta> b) : G (F b) \<rightarrow>\<^sub>D b\<guillemotright> \<and> D.iso (D.inv (\<eta> b))"
            using b by auto
          thus "\<exists>f. \<guillemotleft>f : G (F b) \<rightarrow>\<^sub>D b\<guillemotright> \<and> D.iso f" by blast
        qed
      qed
      thus "\<exists>a. C.ide a \<and> D.isomorphic (G a) b"
        by blast
    qed

    interpretation \<epsilon>_inv: inverse_transformation C C \<open>F o G\<close> C.map \<epsilon> ..
    interpretation \<eta>_inv: inverse_transformation D D D.map \<open>G o F\<close> \<eta> ..
    interpretation GF: equivalence_of_categories D C G F \<epsilon>_inv.map \<eta>_inv.map ..

    lemma F_is_faithful:
    shows "faithful_functor D C F"
      using GF.G_is_faithful by simp

    lemma F_is_essentially_surjective:
    shows "essentially_surjective_functor D C F"
      using GF.G_is_essentially_surjective by simp

    lemma G_is_full:
    shows "full_functor C D G"
    proof
      fix a a' g
      assume a: "C.ide a" and a': "C.ide a'"
      assume g: "\<guillemotleft>g : G a \<rightarrow>\<^sub>D G a'\<guillemotright>"
      show "\<exists>f. \<guillemotleft>f : a \<rightarrow>\<^sub>C a'\<guillemotright> \<and> G f = g"
      proof
        have \<epsilon>a: "C.inverse_arrows (\<epsilon> a) (C.inv (\<epsilon> a))"
          using a C.inv_is_inverse by auto
        have \<epsilon>a': "C.inverse_arrows (\<epsilon> a') (C.inv (\<epsilon> a'))"
          using a' C.inv_is_inverse by auto
        let ?f = "\<epsilon> a' \<cdot>\<^sub>C F g \<cdot>\<^sub>C C.inv (\<epsilon> a)"
        have f: "\<guillemotleft>?f : a \<rightarrow>\<^sub>C a'\<guillemotright>"
          using a a' g \<epsilon>a \<epsilon>a' \<epsilon>.preserves_hom [of a' a' a'] \<epsilon>_inv.preserves_hom [of a a a]
          by fastforce
        moreover have "G ?f = g"
        proof -
          interpret F: faithful_functor D C F
            using F_is_faithful by auto
          have "F (G ?f) = F g"
          proof -
            have "F (G ?f) = C.inv (\<epsilon> a') \<cdot>\<^sub>C ?f \<cdot>\<^sub>C \<epsilon> a"
              using f C_arr_expansion(2) [of "?f"] by auto
            also have "... = (C.inv (\<epsilon> a') \<cdot>\<^sub>C \<epsilon> a') \<cdot>\<^sub>C F g \<cdot>\<^sub>C C.inv (\<epsilon> a) \<cdot>\<^sub>C \<epsilon> a"
              using a a' f g C.comp_assoc by fastforce
            also have "... = F g"
              using a a' g \<epsilon>a \<epsilon>a' C.comp_inv_arr C.comp_arr_dom C.comp_cod_arr by auto
            finally show ?thesis by blast
          qed
          moreover have "D.par (G (\<epsilon> a' \<cdot>\<^sub>C F g \<cdot>\<^sub>C C.inv (\<epsilon> a))) g"
            using f g by fastforce
          ultimately show ?thesis using f g F.is_faithful by blast
        qed
        ultimately show "\<guillemotleft>?f : a \<rightarrow>\<^sub>C a'\<guillemotright> \<and> G ?f = g" by blast
      qed
    qed

  end

  (* I'm not sure why I had to close and re-open the context here in order to
   * get the G_is_full fact in the interpretation GF. *)

  context equivalence_of_categories
  begin

    interpretation \<epsilon>_inv: inverse_transformation C C \<open>F o G\<close> C.map \<epsilon> ..
    interpretation \<eta>_inv: inverse_transformation D D D.map \<open>G o F\<close> \<eta> ..
    interpretation GF: equivalence_of_categories D C G F \<epsilon>_inv.map \<eta>_inv.map ..

    lemma F_is_full:
    shows "full_functor D C F"
      using GF.G_is_full by simp

  end

  text \<open>
    Traditionally the term "equivalence of categories" is also used for a functor
    that is part of an equivalence of categories.  However, it seems best to use
    that term for a situation in which all of the structure of an equivalence is
    explicitly given, and to have a different term for one of the functors involved.
\<close>

  locale equivalence_functor =
    C: category C +
    D: category D +
    "functor" C D G
  for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
  and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
  and G :: "'c \<Rightarrow> 'd" +
  assumes induces_equivalence: "\<exists>F \<eta> \<epsilon>. equivalence_of_categories C D F G \<eta> \<epsilon>"
  begin

    notation C.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hom    ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")

  end

  sublocale equivalence_of_categories \<subseteq> equivalence_functor C D G
    using equivalence_of_categories_axioms by (unfold_locales, blast)

  text \<open>
    An equivalence functor is fully faithful and essentially surjective.
\<close>

  sublocale equivalence_functor \<subseteq> fully_faithful_functor C D G
  proof -
    obtain F \<eta> \<epsilon> where 1: "equivalence_of_categories C D F G \<eta> \<epsilon>"
      using induces_equivalence by blast
    interpret equivalence_of_categories C D F G \<eta> \<epsilon>
      using 1 by auto
    show "fully_faithful_functor C D G"
      using G_is_full G_is_faithful fully_faithful_functor.intro by auto
  qed

  sublocale equivalence_functor \<subseteq> essentially_surjective_functor C D G
  proof -
    obtain F \<eta> \<epsilon> where 1: "equivalence_of_categories C D F G \<eta> \<epsilon>"
      using induces_equivalence by blast
    interpret equivalence_of_categories C D F G \<eta> \<epsilon>
      using 1 by auto
    show "essentially_surjective_functor C D G"
      using G_is_essentially_surjective by auto
  qed

  text \<open>
    A special case of an equivalence functor is an endofunctor \<open>F\<close> equipped with
    a natural isomorphism from \<open>F\<close> to the identity functor.
\<close>

  context endofunctor
  begin

    lemma isomorphic_to_identity_is_equivalence:
    assumes "natural_isomorphism A A F A.map \<phi>"
    shows "equivalence_functor A A F"
    proof -
      interpret \<phi>: natural_isomorphism A A F A.map \<phi>
         using assms by auto
      interpret \<phi>': inverse_transformation A A F A.map \<phi> ..
      interpret F\<phi>': natural_isomorphism A A F \<open>F o F\<close> \<open>F o \<phi>'.map\<close>
      proof -
        interpret F\<phi>': natural_transformation A A F \<open>F o F\<close> \<open>F o \<phi>'.map\<close>
          using \<phi>'.natural_transformation_axioms functor_axioms
                horizontal_composite [of A A A.map F \<phi>'.map A F F F]
          by simp
        show "natural_isomorphism A A F (F o F) (F o \<phi>'.map)"
          apply unfold_locales
          using \<phi>'.components_are_iso by fastforce
      qed
      interpret F\<phi>'o\<phi>': vertical_composite A A A.map F \<open>F o F\<close> \<phi>'.map \<open>F o \<phi>'.map\<close> ..
      interpret F\<phi>'o\<phi>': natural_isomorphism A A A.map \<open>F o F\<close> F\<phi>'o\<phi>'.map
        using \<phi>'.natural_isomorphism_axioms F\<phi>'.natural_isomorphism_axioms
              natural_isomorphisms_compose
        by fast
      interpret inv_F\<phi>'o\<phi>': inverse_transformation A A A.map \<open>F o F\<close> F\<phi>'o\<phi>'.map ..
      interpret F: equivalence_of_categories A A F F F\<phi>'o\<phi>'.map inv_F\<phi>'o\<phi>'.map ..
      show ?thesis ..
    qed

  end

  text \<open>
    An adjoint equivalence is an equivalence of categories that is also an adjunction.
\<close>

  locale adjoint_equivalence =
    unit_counit_adjunction C D F G \<eta> \<epsilon> +
    \<eta>: natural_isomorphism D D D.map "G o F" \<eta> +
    \<epsilon>: natural_isomorphism C C "F o G" C.map \<epsilon>
  for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
  and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
  and F :: "'d \<Rightarrow> 'c"
  and G :: "'c \<Rightarrow> 'd"
  and \<eta> :: "'d \<Rightarrow> 'd"
  and \<epsilon> :: "'c \<Rightarrow> 'c"

  text \<open>
    An adjoint equivalence is clearly an equivalence of categories.
\<close>

  sublocale adjoint_equivalence \<subseteq> equivalence_of_categories ..

  context adjoint_equivalence
  begin

    text \<open>
      The triangle identities for an adjunction reduce to inverse relations when
      \<open>\<eta>\<close> and \<open>\<epsilon>\<close> are natural isomorphisms.
\<close>

    lemma triangle_G':
    assumes "C.ide a"
    shows "D.inverse_arrows (\<eta> (G a)) (G (\<epsilon> a))"
    proof
      show "D.ide (G (\<epsilon> a) \<cdot>\<^sub>D \<eta> (G a))"
        using assms triangle_G G\<epsilon>o\<eta>G.map_simp_ide by fastforce
      thus "D.ide (\<eta> (G a) \<cdot>\<^sub>D G (\<epsilon> a))"
        using assms D.section_retraction_of_iso [of "G (\<epsilon> a)" "\<eta> (G a)"] by auto
    qed

    lemma triangle_F':
    assumes "D.ide b"
    shows "C.inverse_arrows (F (\<eta> b)) (\<epsilon> (F b))"
    proof
     show "C.ide (\<epsilon> (F b) \<cdot>\<^sub>C F (\<eta> b))"
        using assms triangle_F \<epsilon>FoF\<eta>.map_simp_ide by auto
      thus "C.ide (F (\<eta> b) \<cdot>\<^sub>C \<epsilon> (F b))"
        using assms C.section_retraction_of_iso [of "\<epsilon> (F b)" "F (\<eta> b)"] by auto
    qed

    text \<open>
      An adjoint equivalence can be dualized by interchanging the two functors and inverting
      the natural isomorphisms.  This is somewhat awkward to prove, but probably useful to have
      done it once and for all.
\<close>

    lemma dual_equivalence:
    assumes "adjoint_equivalence C D F G \<eta> \<epsilon>"
    shows "adjoint_equivalence D C G F (inverse_transformation.map C C (C.map) \<epsilon>)
                                       (inverse_transformation.map D D (G o F) \<eta>)"
    proof -
      interpret adjoint_equivalence C D F G \<eta> \<epsilon> using assms by auto
      interpret \<epsilon>': inverse_transformation C C \<open>F o G\<close> C.map \<epsilon> ..
      interpret \<eta>': inverse_transformation D D D.map \<open>G o F\<close> \<eta> ..
      interpret G\<epsilon>': natural_transformation C D G \<open>G o F o G\<close> \<open>G o \<epsilon>'.map\<close>
      proof -
        have "natural_transformation C D G (G o (F o G)) (G o \<epsilon>'.map)"
          using G.natural_transformation_axioms \<epsilon>'.natural_transformation_axioms
                horizontal_composite
          by fastforce
        thus "natural_transformation C D G (G o F o G) (G o \<epsilon>'.map)"
          using o_assoc by metis
      qed
      interpret \<eta>'G: natural_transformation C D \<open>G o F o G\<close> G \<open>\<eta>'.map o G\<close>
        using \<eta>'.natural_transformation_axioms G.natural_transformation_axioms
              horizontal_composite
        by fastforce
      interpret \<epsilon>'F: natural_transformation D C F \<open>F o G o F\<close> \<open>\<epsilon>'.map o F\<close>
        using \<epsilon>'.natural_transformation_axioms F.natural_transformation_axioms
              horizontal_composite
        by fastforce
      interpret F\<eta>': natural_transformation D C \<open>F o G o F\<close> F \<open>F o \<eta>'.map\<close>
      proof -
        have "natural_transformation D C (F o (G o F)) F (F o \<eta>'.map)"
          using \<eta>'.natural_transformation_axioms F.natural_transformation_axioms
                horizontal_composite
          by fastforce
        thus "natural_transformation D C (F o G o F) F (F o \<eta>'.map)"
          using o_assoc by metis
      qed
      interpret F\<eta>'o\<epsilon>'F: vertical_composite D C F \<open>(F o G) o F\<close> F \<open>\<epsilon>'.map o F\<close> \<open>F o \<eta>'.map\<close> ..
      interpret \<eta>'GoG\<epsilon>': vertical_composite C D G \<open>G o F o G\<close> G \<open>G o \<epsilon>'.map\<close> \<open>\<eta>'.map o G\<close> ..
      show ?thesis
      proof
        show "\<eta>'GoG\<epsilon>'.map = G"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation C D G G G"
            using G.natural_transformation_axioms by auto
          show "natural_transformation C D G G \<eta>'GoG\<epsilon>'.map"
            using \<eta>'GoG\<epsilon>'.natural_transformation_axioms by auto
          show "\<And>a. C.ide a \<Longrightarrow> \<eta>'GoG\<epsilon>'.map a = G a"
          proof -
            fix a
            assume a: "C.ide a"
            show "\<eta>'GoG\<epsilon>'.map a = G a"
              using a \<eta>'GoG\<epsilon>'.map_simp_ide triangle_G'
                    \<eta>.components_are_iso \<epsilon>.components_are_iso G.preserves_ide
                    \<eta>'.inverts_components \<epsilon>'.inverts_components
                    D.inverse_unique G.preserves_inverse_arrows G\<epsilon>o\<eta>G.map_simp_ide
                    D.inverse_arrows_sym triangle_G
              by (metis o_apply)
          qed
        qed
        show "F\<eta>'o\<epsilon>'F.map = F"
        proof (intro NaturalTransformation.eqI)
          show "natural_transformation D C F F F"
            using F.natural_transformation_axioms by auto
          show "natural_transformation D C F F F\<eta>'o\<epsilon>'F.map"
            using F\<eta>'o\<epsilon>'F.natural_transformation_axioms by auto
          show "\<And>b. D.ide b \<Longrightarrow> F\<eta>'o\<epsilon>'F.map b = F b"
          proof -
            fix b
            assume b: "D.ide b"
            show "F\<eta>'o\<epsilon>'F.map b = F b"
              using b F\<eta>'o\<epsilon>'F.map_simp_ide \<epsilon>FoF\<eta>.map_simp_ide triangle_F triangle_F'
                    \<eta>.components_are_iso \<epsilon>.components_are_iso G.preserves_ide
                    \<eta>'.inverts_components \<epsilon>'.inverts_components F.preserves_ide
                    C.inverse_unique F.preserves_inverse_arrows C.inverse_arrows_sym
              by (metis o_apply)
          qed
        qed
      qed
    qed

  end

  text \<open>
    Every fully faithful and essentially surjective functor underlies an adjoint equivalence.
    To prove this without repeating things that were already proved in @{theory Category3.Adjunction},
    we first show that a fully faithful and essentially surjective functor is a left adjoint
    functor, and then we show that if the left adjoint in a unit-counit adjunction is
    fully faithful and essentially surjective, then the unit and counit are natural isomorphisms;
    hence the adjunction is in fact an adjoint equivalence.
\<close>

  locale fully_faithful_and_essentially_surjective_functor =
    C: category C +
    D: category D +
    fully_faithful_functor C D F +
    essentially_surjective_functor C D F
    for C :: "'c comp"     (infixr "\<cdot>\<^sub>C" 55)
    and D :: "'d comp"     (infixr "\<cdot>\<^sub>D" 55)
    and F :: "'c \<Rightarrow> 'd"
  begin

    notation C.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>C _\<guillemotright>")
    notation D.in_hom      ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>D _\<guillemotright>")

    lemma is_left_adjoint_functor:
    shows "left_adjoint_functor C D F"
    proof
      fix y
      assume y: "D.ide y"
      let ?x = "SOME x. C.ide x \<and> (\<exists>e. D.iso e \<and> \<guillemotleft>e : F x \<rightarrow>\<^sub>D y\<guillemotright>)"
      let ?e = "SOME e. D.iso e \<and> \<guillemotleft>e : F ?x \<rightarrow>\<^sub>D y\<guillemotright>"
      have "\<exists>x e. D.iso e \<and> terminal_arrow_from_functor C D F x y e"
      proof -
        have "\<exists>x. D.iso ?e \<and> terminal_arrow_from_functor C D F x y ?e"
        proof -
          have x: "C.ide ?x \<and> (\<exists>e. D.iso e \<and> \<guillemotleft>e : F ?x \<rightarrow>\<^sub>D y\<guillemotright>)"
            using y essentially_surjective
                  someI_ex [of "\<lambda>x. C.ide x \<and> (\<exists>e. D.iso e \<and> \<guillemotleft>e : F x \<rightarrow>\<^sub>D y\<guillemotright>)"]
            by blast
          hence e: "D.iso ?e \<and> \<guillemotleft>?e : F ?x \<rightarrow>\<^sub>D y\<guillemotright>"
            using someI_ex [of "\<lambda>e. D.iso e \<and> \<guillemotleft>e : F ?x \<rightarrow>\<^sub>D y\<guillemotright>"] by blast
          interpret arrow_from_functor C D F ?x y ?e
            using x e by (unfold_locales, simp)
          interpret terminal_arrow_from_functor C D F ?x y ?e
          proof
            fix x' f
            assume 1: "arrow_from_functor C D F x' y f"
            interpret f: arrow_from_functor C D F x' y f
              using 1 by simp
            have f: "\<guillemotleft>f: F x' \<rightarrow>\<^sub>D y\<guillemotright>"
              by (meson f.arrow)
            show "\<exists>!g. is_coext x' f g"
            proof
              let ?g = "SOME g. \<guillemotleft>g : x' \<rightarrow>\<^sub>C ?x\<guillemotright> \<and> F g = D.inv ?e \<cdot>\<^sub>D f"
              have g: "\<guillemotleft>?g : x' \<rightarrow>\<^sub>C ?x\<guillemotright> \<and> F ?g = D.inv ?e \<cdot>\<^sub>D f"
                using f e x f.arrow is_full D.comp_in_homI D.inv_in_hom
                      someI_ex [of "\<lambda>g. \<guillemotleft>g : x' \<rightarrow>\<^sub>C ?x\<guillemotright> \<and> F g = D.inv ?e \<cdot>\<^sub>D f"]
                by auto
              show 1: "is_coext x' f ?g"
              proof -
                have "\<guillemotleft>?g : x' \<rightarrow>\<^sub>C ?x\<guillemotright>"
                  using g by simp
                moreover have "?e \<cdot>\<^sub>D F ?g = f"
                proof -
                  have "?e \<cdot>\<^sub>D F ?g = ?e \<cdot>\<^sub>D D.inv ?e \<cdot>\<^sub>D f"
                    using g by simp
                  also have "... = (?e \<cdot>\<^sub>D D.inv ?e) \<cdot>\<^sub>D f"
                    using e f D.inv_in_hom by (metis D.comp_assoc)
                  also have "... = f"
                  proof -
                    have "?e \<cdot>\<^sub>D D.inv ?e = y"
                      using e D.comp_arr_inv D.inv_is_inverse by auto
                    thus ?thesis
                      using f D.comp_cod_arr by auto
                  qed
                  finally show ?thesis by blast
                qed
                ultimately show ?thesis
                  unfolding is_coext_def by simp
              qed
              show "\<And>g'. is_coext x' f g' \<Longrightarrow> g' = ?g"
              proof -
                fix g'
                assume g': "is_coext x' f g'"
                have 2: "\<guillemotleft>g' : x' \<rightarrow>\<^sub>C ?x\<guillemotright> \<and> ?e \<cdot>\<^sub>D F g' = f" using g' is_coext_def by simp
                have 3: "\<guillemotleft>?g : x' \<rightarrow>\<^sub>C ?x\<guillemotright> \<and> ?e \<cdot>\<^sub>D F ?g = f" using 1 is_coext_def by simp
                have "F g' = F ?g"
                  using e 2 3 D.iso_is_section D.section_is_mono D.monoE by blast
                moreover have "C.par g' ?g"
                  using 2 3 by fastforce
                ultimately show "g' = ?g"
                  using is_faithful [of g' ?g] by simp
              qed
            qed
          qed
          show ?thesis
            using e terminal_arrow_from_functor_axioms by auto
        qed
        thus ?thesis by auto
      qed
      thus "\<exists>x e. terminal_arrow_from_functor C D F x y e" by blast
    qed

    lemma extends_to_adjoint_equivalence:
    shows "\<exists>G \<eta> \<epsilon>. adjoint_equivalence C D G F \<eta> \<epsilon>"
    proof -
      interpret left_adjoint_functor C D F
        using is_left_adjoint_functor by blast
      interpret Adj: meta_adjunction D C F G \<phi> \<psi>
        using induces_meta_adjunction by simp
      interpret Adj: adjunction D C replete_setcat.comp
                       Adj.\<phi>C Adj.\<phi>D F G \<phi> \<psi> Adj.\<eta> Adj.\<epsilon> Adj.\<Phi> Adj.\<Psi>
        using induces_adjunction by simp
      interpret equivalence_of_categories D C F G Adj.\<eta> Adj.\<epsilon>
      proof
        show 1: "\<And>a. D.ide a \<Longrightarrow> D.iso (Adj.\<epsilon> a)"
        proof -
          fix a
          assume a: "D.ide a"
          interpret \<epsilon>a: terminal_arrow_from_functor C D F \<open>G a\<close> a \<open>Adj.\<epsilon> a\<close>
            using a Adj.has_terminal_arrows_from_functor [of a] by blast
          have "D.retraction (Adj.\<epsilon> a)"
          proof -
            obtain b \<phi> where \<phi>: "C.ide b \<and> D.iso \<phi> \<and> \<guillemotleft>\<phi>: F b \<rightarrow>\<^sub>D a\<guillemotright>"
              using a essentially_surjective by blast
            interpret \<phi>: arrow_from_functor C D F b a \<phi>
              using \<phi> by (unfold_locales, simp)
            let ?g = "\<epsilon>a.the_coext b \<phi>"
            have 1: "\<guillemotleft>?g : b \<rightarrow>\<^sub>C G a\<guillemotright> \<and> Adj.\<epsilon> a \<cdot>\<^sub>D F ?g = \<phi>"
              using \<phi>.arrow_from_functor_axioms \<epsilon>a.the_coext_prop [of b \<phi>] by simp
            have "a = (Adj.\<epsilon> a \<cdot>\<^sub>D F ?g) \<cdot>\<^sub>D D.inv \<phi>"
              using a 1 \<phi> D.comp_cod_arr Adj.\<epsilon>.preserves_hom D.invert_side_of_triangle(2)
               by auto
            also have "... = Adj.\<epsilon> a \<cdot>\<^sub>D F ?g \<cdot>\<^sub>D D.inv \<phi>"
              using a 1 \<phi> D.inv_in_hom Adj.\<epsilon>.preserves_hom [of a a a] D.comp_assoc
              by blast
            finally have "\<exists>f. D.ide (Adj.\<epsilon> a \<cdot>\<^sub>D f)"
              using a by metis
            thus ?thesis
              unfolding D.retraction_def by blast
          qed
          moreover have "D.mono (Adj.\<epsilon> a)"
          proof
            show "D.arr (Adj.\<epsilon> a)"
              using a by simp
            show "\<And>f f'. D.seq (Adj.\<epsilon> a) f \<and> D.seq (Adj.\<epsilon> a) f' \<and> Adj.\<epsilon> a \<cdot>\<^sub>D f = Adj.\<epsilon> a \<cdot>\<^sub>D f'
                            \<Longrightarrow> f = f'"
            proof -
              fix f f'
              assume ff': "D.seq (Adj.\<epsilon> a) f \<and> D.seq (Adj.\<epsilon> a) f' \<and> Adj.\<epsilon> a \<cdot>\<^sub>D f = Adj.\<epsilon> a \<cdot>\<^sub>D f'"
              have f: "\<guillemotleft>f : D.dom f \<rightarrow>\<^sub>D F (G a)\<guillemotright>"
                using a ff' Adj.\<epsilon>.preserves_hom [of a a a] by fastforce
              have f': "\<guillemotleft>f' : D.dom f' \<rightarrow>\<^sub>D F (G a)\<guillemotright>"
                using a ff' Adj.\<epsilon>.preserves_hom [of a a a] by fastforce
              have par: "D.par f f'"
                using f f' ff' D.dom_comp [of "Adj.\<epsilon> a" f] by force
              obtain b' \<phi> where \<phi>: "C.ide b' \<and> D.iso \<phi> \<and> \<guillemotleft>\<phi>: F b' \<rightarrow>\<^sub>D D.dom f\<guillemotright>"
                using par essentially_surjective D.ide_dom [of f] by blast
              have 1: "Adj.\<epsilon> a \<cdot>\<^sub>D f \<cdot>\<^sub>D \<phi> = Adj.\<epsilon> a \<cdot>\<^sub>D f' \<cdot>\<^sub>D \<phi>"
                using ff' \<phi> par D.comp_assoc by metis
              obtain g where g: "\<guillemotleft>g : b' \<rightarrow>\<^sub>C G a\<guillemotright> \<and> F g = f \<cdot>\<^sub>D \<phi>"
                using a f \<phi> is_full [of "G a" b' "f \<cdot>\<^sub>D \<phi>"] by auto
              obtain g' where g': "\<guillemotleft>g' : b' \<rightarrow>\<^sub>C G a\<guillemotright> \<and> F g' = f' \<cdot>\<^sub>D \<phi>"
                using a f' par \<phi> is_full [of "G a" b' "f' \<cdot>\<^sub>D \<phi>"] by auto
              interpret f\<phi>: arrow_from_functor C D F b' a \<open>Adj.\<epsilon> a \<cdot>\<^sub>D f \<cdot>\<^sub>D \<phi>\<close>
                using a \<phi> f Adj.\<epsilon>.preserves_hom
                by (unfold_locales, fastforce)
              interpret f'\<phi>: arrow_from_functor C D F b' a \<open>Adj.\<epsilon> a \<cdot>\<^sub>D f' \<cdot>\<^sub>D \<phi>\<close>
                using a \<phi> f' par Adj.\<epsilon>.preserves_hom
                by (unfold_locales, fastforce)
              have "\<epsilon>a.is_coext b' (Adj.\<epsilon> a \<cdot>\<^sub>D f \<cdot>\<^sub>D \<phi>) g"
                unfolding \<epsilon>a.is_coext_def using g 1 by auto
              moreover have "\<epsilon>a.is_coext b' (Adj.\<epsilon> a \<cdot>\<^sub>D f' \<cdot>\<^sub>D \<phi>) g'"
                unfolding \<epsilon>a.is_coext_def using g' 1 by auto
              ultimately have "g = g'"
                using 1 f\<phi>.arrow_from_functor_axioms f'\<phi>.arrow_from_functor_axioms
                      \<epsilon>a.the_coext_unique \<epsilon>a.the_coext_unique [of b' "Adj.\<epsilon> a \<cdot>\<^sub>D f' \<cdot>\<^sub>D \<phi>" g']
                by auto
              hence "f \<cdot>\<^sub>D \<phi> = f' \<cdot>\<^sub>D \<phi>"
                using g g' is_faithful by argo
              thus "f = f'"
                using \<phi> f f' par D.iso_is_retraction D.retraction_is_epi D.epiE [of \<phi> f f']
                by auto
            qed
          qed
          ultimately show "D.iso (Adj.\<epsilon> a)"
            using D.iso_iff_mono_and_retraction by simp
        qed
        interpret \<epsilon>: natural_isomorphism D D \<open>F o G\<close> D.map Adj.\<epsilon>
          using 1 by (unfold_locales, auto)
        interpret \<epsilon>F: natural_isomorphism C D \<open>F o G o F\<close> F \<open>Adj.\<epsilon> o F\<close>
          using \<epsilon>.components_are_iso by (unfold_locales, simp)
        show "\<And>a. C.ide a \<Longrightarrow> C.iso (Adj.\<eta> a)"
        proof -
          fix a
          assume a: "C.ide a"
          have "D.inverse_arrows ((Adj.\<epsilon> o F) a) ((F o Adj.\<eta>) a)"
            using a \<epsilon>.components_are_iso Adj.\<eta>\<epsilon>.triangle_F Adj.\<epsilon>FoF\<eta>.map_simp_ide
                  D.section_retraction_of_iso
            by simp
          hence "D.iso ((F o Adj.\<eta>) a)"
            by blast
          thus "C.iso (Adj.\<eta> a)"
            using a reflects_iso [of "Adj.\<eta> a"] by fastforce
        qed
      qed
      (*
       * Uggh, I should have started with "right_adjoint_functor D C G" so that the
       * following would come out right.  Instead, another step is needed to dualize.
       * TODO: Maybe re-work this later.
       *)
      interpret adjoint_equivalence D C F G Adj.\<eta> Adj.\<epsilon> ..
      interpret \<epsilon>': inverse_transformation D D \<open>F o G\<close> D.map Adj.\<epsilon> ..
      interpret \<eta>': inverse_transformation C C C.map \<open>G o F\<close> Adj.\<eta> ..
      interpret E: adjoint_equivalence C D G F \<epsilon>'.map \<eta>'.map
        using adjoint_equivalence_axioms dual_equivalence by blast
      show ?thesis
        using E.adjoint_equivalence_axioms by auto
    qed

    lemma is_right_adjoint_functor:
    shows "right_adjoint_functor C D F"
    proof -
      obtain G \<eta> \<epsilon> where E: "adjoint_equivalence C D G F \<eta> \<epsilon>"
        using extends_to_adjoint_equivalence by auto
      interpret E: adjoint_equivalence C D G F \<eta> \<epsilon>
        using E by simp
      interpret Adj: meta_adjunction C D G F E.\<phi> E.\<psi>
        using E.induces_meta_adjunction by simp
      show ?thesis
        using Adj.has_right_adjoint_functor by simp
    qed

    lemma is_equivalence_functor:
    shows "equivalence_functor C D F"
    proof
      obtain G \<eta> \<epsilon> where E: "adjoint_equivalence C D G F \<eta> \<epsilon>"
        using extends_to_adjoint_equivalence by auto
      interpret E: adjoint_equivalence C D G F \<eta> \<epsilon>
        using E by simp
      have "equivalence_of_categories C D G F \<eta> \<epsilon>" ..
      thus "\<exists>G \<eta> \<epsilon>. equivalence_of_categories C D G F \<eta> \<epsilon>" by blast
    qed

    sublocale equivalence_functor C D F
      using is_equivalence_functor by blast

  end

  context equivalence_of_categories
  begin

    text \<open>
      The following development shows that an equivalence of categories can
      be refined to an adjoint equivalence by replacing just the counit.
    \<close>

    abbreviation \<epsilon>'
    where "\<epsilon>' a \<equiv> \<epsilon> a \<cdot>\<^sub>C F (D.inv (\<eta> (G a))) \<cdot>\<^sub>C C.inv (\<epsilon> (F (G a)))"

    interpretation \<epsilon>': transformation_by_components C C \<open>F \<circ> G\<close> C.map \<epsilon>'
    proof
      show "\<And>a. C.ide a \<Longrightarrow> \<guillemotleft>\<epsilon>' a : (F \<circ> G) a \<rightarrow>\<^sub>C C.map a\<guillemotright>"
        using \<eta>.components_are_iso \<epsilon>.components_are_iso by simp
      fix f
      assume f: "C.arr f"
      show "\<epsilon>' (C.cod f) \<cdot>\<^sub>C (F \<circ> G) f = C.map f \<cdot>\<^sub>C \<epsilon>' (C.dom f)"
      proof -
        have "\<epsilon>' (C.cod f) \<cdot>\<^sub>C (F \<circ> G) f =
              \<epsilon> (C.cod f) \<cdot>\<^sub>C F (D.inv (\<eta> (G (C.cod f)))) \<cdot>\<^sub>C C.inv (\<epsilon> (F (G (C.cod f)))) \<cdot>\<^sub>C F (G f)"
          using f C.comp_assoc by simp
        also have "... = \<epsilon> (C.cod f) \<cdot>\<^sub>C (F (D.inv (\<eta> (G (C.cod f)))) \<cdot>\<^sub>C
                           F (G (F (G f)))) \<cdot>\<^sub>C C.inv (\<epsilon> (F (G (C.dom f))))"
          using f \<epsilon>.inv_naturality [of "F (G f)"] C.comp_assoc by simp
        also have "... = (\<epsilon> (C.cod f) \<cdot>\<^sub>C F (G f)) \<cdot>\<^sub>C F (D.inv (\<eta> (G (C.dom f)))) \<cdot>\<^sub>C
                           C.inv (\<epsilon> (F (G (C.dom f))))"
        proof -
          have "F (D.inv (\<eta> (G (C.cod f)))) \<cdot>\<^sub>C F (G (F (G f))) =
                F (G f) \<cdot>\<^sub>C F (D.inv (\<eta> (G (C.dom f))))"
          proof -
            have "F (D.inv (\<eta> (G (C.cod f)))) \<cdot>\<^sub>C F (G (F (G f))) =
                  F (D.inv (\<eta> (G (C.cod f))) \<cdot>\<^sub>D G (F (G f)))"
              using f by simp
            also have "... = F (G f \<cdot>\<^sub>D D.inv (\<eta> (G (C.dom f))))"
              using f \<eta>.inv_naturality [of "G f"] by simp
            also have "... = F (G f) \<cdot>\<^sub>C F (D.inv (\<eta> (G (C.dom f))))"
              using f by simp
            finally show ?thesis by blast
          qed
          thus ?thesis
            using C.comp_assoc by simp
        qed
        also have "... = C.map f \<cdot>\<^sub>C \<epsilon> (C.dom f) \<cdot>\<^sub>C F (D.inv (\<eta> (G (C.dom f)))) \<cdot>\<^sub>C
                           C.inv (\<epsilon> (F (G (C.dom f))))"
          using f \<epsilon>.naturality C.comp_assoc by simp
        finally show ?thesis by blast
      qed
    qed

    interpretation \<epsilon>': natural_isomorphism C C \<open>F \<circ> G\<close> C.map \<epsilon>'.map
    proof
      show "\<And>a. C.ide a \<Longrightarrow> C.iso (\<epsilon>'.map a)"
        unfolding \<epsilon>'.map_def
        using \<eta>.components_are_iso \<epsilon>.components_are_iso
        apply simp
        by (intro C.isos_compose) auto
    qed

    lemma F\<eta>_inverse:
    assumes "D.ide b"
    shows "F (\<eta> (G (F b))) = F (G (F (\<eta> b)))"
    and "F (\<eta> b) \<cdot>\<^sub>C \<epsilon> (F b) = \<epsilon> (F (G (F b))) \<cdot>\<^sub>C F (\<eta> (G (F b)))"
    and "C.inverse_arrows (F (\<eta> b)) (\<epsilon>' (F b))"
    and "F (\<eta> b) = C.inv (\<epsilon>' (F b))"
    and "C.inv (F (\<eta> b)) = \<epsilon>' (F b)"
    proof -
      let ?\<epsilon>' = "\<lambda>a. \<epsilon> a \<cdot>\<^sub>C F (D.inv (\<eta> (G a))) \<cdot>\<^sub>C C.inv (\<epsilon> (F (G a)))"
      show 1: "F (\<eta> (G (F b))) = F (G (F (\<eta> b)))"
      proof -
        have "F (\<eta> (G (F b))) \<cdot>\<^sub>C F (\<eta> b) = F (G (F (\<eta> b))) \<cdot>\<^sub>C F (\<eta> b)"
        proof -
          have "F (\<eta> (G (F b))) \<cdot>\<^sub>C F (\<eta> b) = F (\<eta> (G (F b)) \<cdot>\<^sub>D \<eta> b)"
            using assms by simp
          also have "... = F (G (F (\<eta> b)) \<cdot>\<^sub>D \<eta> b)"
            using assms \<eta>.naturality [of "\<eta> b"] by simp
          also have "... = F (G (F (\<eta> b))) \<cdot>\<^sub>C F (\<eta> b)"
            using assms by simp
          finally show ?thesis by blast
        qed
        thus ?thesis
          using assms \<eta>.components_are_iso C.iso_cancel_right by simp
      qed
      show "F (\<eta> b) \<cdot>\<^sub>C \<epsilon> (F b) = \<epsilon> (F (G (F b))) \<cdot>\<^sub>C F (\<eta> (G (F b)))"
        using assms 1 \<epsilon>.naturality [of "F (\<eta> b)"] by simp
      show 2: "C.inverse_arrows (F (\<eta> b)) (?\<epsilon>' (F b))"
      proof
        show 3: "C.ide (?\<epsilon>' (F b) \<cdot>\<^sub>C F (\<eta> b))"
        proof -
          have "?\<epsilon>' (F b) \<cdot>\<^sub>C F (\<eta> b) =
                \<epsilon> (F b) \<cdot>\<^sub>C (F (D.inv (\<eta> (G (F b)))) \<cdot>\<^sub>C C.inv (\<epsilon> (F (G (F b))))) \<cdot>\<^sub>C F (\<eta> b)"
            using C.comp_assoc by simp
          also have "... = \<epsilon> (F b) \<cdot>\<^sub>C (F (D.inv (\<eta> (G (F b)))) \<cdot>\<^sub>C F (G (F (\<eta> b)))) \<cdot>\<^sub>C C.inv (\<epsilon> (F b))"
            using assms \<epsilon>.naturality [of "F (\<eta> b)"] \<epsilon>.components_are_iso C.comp_assoc
                  C.invert_opposite_sides_of_square
                    [of "\<epsilon> (F (G (F b)))" "F (G (F (\<eta> b)))" "F (\<eta> b)" "\<epsilon> (F b)"]
            by simp
          also have "... = \<epsilon> (F b) \<cdot>\<^sub>C C.inv (\<epsilon> (F b))"
          proof -
            have "F (D.inv (\<eta> (G (F b)))) \<cdot>\<^sub>C F (G (F (\<eta> b))) = F (G (F b))"
              using assms 1 D.comp_inv_arr' \<eta>.components_are_iso
              by (metis D.ideD(1) D.ideD(2) F.preserves_comp
                  F.preserves_ide G.preserves_ide \<eta>.preserves_dom D.map_simp)
            moreover have "F (G (F b)) \<cdot>\<^sub>C C.inv (\<epsilon> (F b)) = C.inv (\<epsilon> (F b))"
              using assms D.comp_cod_arr \<epsilon>.components_are_iso C.inv_in_hom [of "\<epsilon> (F b)"]
              by (metis C.comp_ide_arr C_arr_expansion(1) D.ide_char F.preserves_arr
                  F.preserves_dom F.preserves_ide G.preserves_ide C.seqE)
            ultimately show ?thesis by simp
          qed
          also have "... = F b"
            using assms \<epsilon>.components_are_iso C.comp_arr_inv' by simp
          finally have "(\<epsilon> (F b) \<cdot>\<^sub>C F (D.inv (\<eta> (G (F b)))) \<cdot>\<^sub>C C.inv (\<epsilon> (F (G (F b))))) \<cdot>\<^sub>C F (\<eta> b) = F b"
            by blast
          thus ?thesis
            using assms by simp
        qed
        show "C.ide (F (\<eta> b) \<cdot>\<^sub>C ?\<epsilon>' (F b))"
        proof -
          have "(F (\<eta> b) \<cdot>\<^sub>C ?\<epsilon>' (F b)) \<cdot>\<^sub>C F (\<eta> b) = F (G (F b)) \<cdot>\<^sub>C F (\<eta> b)"
          proof -
            have "(F (\<eta> b) \<cdot>\<^sub>C ?\<epsilon>' (F b)) \<cdot>\<^sub>C F (\<eta> b) =
                  F (\<eta> b) \<cdot>\<^sub>C (\<epsilon> (F b) \<cdot>\<^sub>C F (D.inv (\<eta> (G (F b)))) \<cdot>\<^sub>C C.inv (\<epsilon> (F (G (F b))))) \<cdot>\<^sub>C F (\<eta> b)"
              using C.comp_assoc by simp
            also have "... = F (\<eta> b)"
              using assms 3
                    C.comp_arr_dom
                      [of "F (\<eta> b)" "(\<epsilon> (F b) \<cdot>\<^sub>C F (D.inv (\<eta> (G (F b)))) \<cdot>\<^sub>C
                                       C.inv (\<epsilon> (F (G (F b))))) \<cdot>\<^sub>C F (\<eta> b)"]
              by auto
            also have "... = F (G (F b)) \<cdot>\<^sub>C F (\<eta> b)"
              using assms C.comp_cod_arr by simp
            finally show ?thesis by blast
          qed
          hence "F (\<eta> b) \<cdot>\<^sub>C ?\<epsilon>' (F b) = F (G (F b))"
            using assms C.iso_cancel_right by simp
          thus ?thesis
            using assms by simp
        qed
      qed
      show "C.inv (F (\<eta> b)) = ?\<epsilon>' (F b)"
        using assms 2 C.inverse_unique by simp
      show "F (\<eta> b) = C.inv (?\<epsilon>' (F b))"
      proof -
        have "C.inverse_arrows (?\<epsilon>' (F b)) (F (\<eta> b))"
          using assms 2 by auto
        thus ?thesis
          using assms C.inverse_unique by simp
      qed
    qed

    interpretation FoGoF: composite_functor D C C F \<open>F o G\<close> ..
    interpretation GoFoG: composite_functor C D D G \<open>G o F\<close> ..

    interpretation natural_transformation D C F FoGoF.map \<open>F \<circ> \<eta>\<close>
    proof -
      have "F \<circ> D.map = F"
        using hcomp_ide_dom F.natural_transformation_axioms by blast
      moreover have "F o (G o F) = FoGoF.map"
        by auto
      ultimately show "natural_transformation D C F FoGoF.map (F \<circ> \<eta>)"
        using \<eta>.natural_transformation_axioms F.natural_transformation_axioms
              horizontal_composite [of D D D.map "G o F" \<eta> C F F F]
        by simp
    qed

    interpretation natural_transformation C D G GoFoG.map \<open>\<eta> \<circ> G\<close>
      using \<eta>.natural_transformation_axioms G.natural_transformation_axioms
            horizontal_composite [of C D G G G ]
      by fastforce

    interpretation natural_transformation D C FoGoF.map F \<open>\<epsilon>'.map \<circ> F\<close>
      using \<epsilon>'.natural_transformation_axioms F.natural_transformation_axioms
            horizontal_composite [of D C F F F]
      by fastforce

    interpretation natural_transformation C D GoFoG.map G \<open>G \<circ> \<epsilon>'.map\<close>
    proof -
      have "G o C.map = G"
        using hcomp_ide_dom G.natural_transformation_axioms by blast
      moreover have "G o (F o G) = GoFoG.map"
        by auto
      ultimately show "natural_transformation C D GoFoG.map G (G \<circ> \<epsilon>'.map)"
        using G.natural_transformation_axioms \<epsilon>'.natural_transformation_axioms
              horizontal_composite [of C C "F o G" C.map \<epsilon>'.map D G G G]
        by simp
    qed

    interpretation \<epsilon>'F_F\<eta>: vertical_composite D C F FoGoF.map F \<open>F \<circ> \<eta>\<close> \<open>\<epsilon>'.map \<circ> F\<close> ..
    interpretation G\<epsilon>'_\<eta>G: vertical_composite C D G GoFoG.map G \<open>\<eta> o G\<close> \<open>G o \<epsilon>'.map\<close> ..

    interpretation \<eta>\<epsilon>': unit_counit_adjunction C D F G \<eta> \<epsilon>'.map
    proof
      show 1: "\<epsilon>'F_F\<eta>.map = F"
      proof
        fix g
        show "\<epsilon>'F_F\<eta>.map g = F g"
        proof (cases "D.arr g")
          show "\<not> D.arr g \<Longrightarrow> \<epsilon>'F_F\<eta>.map g = F g"
            using \<epsilon>'F_F\<eta>.is_extensional F.is_extensional by simp
          assume g: "D.arr g"
          have "\<epsilon>'F_F\<eta>.map g = \<epsilon>' (F (D.cod g)) \<cdot>\<^sub>C F (\<eta> g)"
            using g \<epsilon>'F_F\<eta>.map_def by simp
          also have "... = \<epsilon>' (F (D.cod g)) \<cdot>\<^sub>C F (\<eta> (D.cod g) \<cdot>\<^sub>D g)"
            using g \<eta>.is_natural_2 by simp
          also have "... = (\<epsilon>' (F (D.cod g)) \<cdot>\<^sub>C F (\<eta> (D.cod g))) \<cdot>\<^sub>C F g"
            using g C.comp_assoc by simp
          also have "... = F (D.cod g) \<cdot>\<^sub>C F g"
            using g F\<eta>_inverse(3) [of "D.cod g"] by fastforce
          also have "... = F g"
            using g C.comp_cod_arr by simp
          finally show "\<epsilon>'F_F\<eta>.map g = F g" by blast
        qed
      qed
      show "G\<epsilon>'_\<eta>G.map = G"
      proof
        fix f
        show "G\<epsilon>'_\<eta>G.map f = G f"
        proof (cases "C.arr f")
          show "\<not> C.arr f \<Longrightarrow> G\<epsilon>'_\<eta>G.map f = G f"
            using G\<epsilon>'_\<eta>G.is_extensional G.is_extensional by simp
          assume f: "C.arr f"
          have "F (G\<epsilon>'_\<eta>G.map f) = F (G (\<epsilon>' (C.cod f)) \<cdot>\<^sub>D \<eta> (G f))"
            using f G\<epsilon>'_\<eta>G.map_def D.comp_assoc by simp
          also have "... = F (G (\<epsilon>' (C.cod f)) \<cdot>\<^sub>D \<eta> (G (C.cod f)) \<cdot>\<^sub>D G f)"
            using f \<eta>.is_natural_2 [of "G f"] by simp
          also have "... = F (G (\<epsilon>' (C.cod f))) \<cdot>\<^sub>C F (\<eta> (G (C.cod f))) \<cdot>\<^sub>C F (G f)"
            using f by simp
          also have "... = (F (G (\<epsilon>' (C.cod f))) \<cdot>\<^sub>C C.inv (\<epsilon>' (F (G (C.cod f))))) \<cdot>\<^sub>C F (G f)"
            using f F\<eta>_inverse(4) C.comp_assoc by simp
          also have "... = (C.inv (\<epsilon>' (C.cod f)) \<cdot>\<^sub>C \<epsilon>' (C.cod f)) \<cdot>\<^sub>C F (G f)"
            using f \<epsilon>'.inv_naturality [of "\<epsilon>' (C.cod f)"] by simp
          also have "... = F (G (C.cod f)) \<cdot>\<^sub>C F (G f)"
            using f C.comp_inv_arr' [of "\<epsilon>' (C.cod f)"] \<epsilon>'.components_are_iso by simp
          also have "... = F (G f)"
            using f C.comp_cod_arr by simp
          finally have "F (G\<epsilon>'_\<eta>G.map f) = F (G f)" by blast
          moreover have "D.par (G\<epsilon>'_\<eta>G.map f) (G f)"
            using f by simp
          ultimately show "G\<epsilon>'_\<eta>G.map f = G f"
            using f F_is_faithful
            by (simp add: faithful_functor_axioms_def faithful_functor_def)
        qed
      qed
    qed

    interpretation \<eta>\<epsilon>': adjoint_equivalence C D F G \<eta> \<epsilon>'.map ..

    lemma refines_to_adjoint_equivalence:
    shows "adjoint_equivalence C D F G \<eta> \<epsilon>'.map"
      ..

  end

end
