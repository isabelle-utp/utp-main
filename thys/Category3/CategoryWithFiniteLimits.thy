(*  Title:       CategoryWithFiniteLimits
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Category with Finite Limits"

theory CategoryWithFiniteLimits
imports CartesianCategory CategoryWithPullbacks
begin

  text\<open>
    In this chapter we define ``category with finite limits'' and show that such
    categories coincide with those having pullbacks and a terminal object.

    Since we can't quantify over types in HOL, the best we can do at defining the notion
    ``category with finite limits'' is to state it for a fixed choice of type (e.g.~@{typ nat})
    for the arrows of the ``diagram shape''.  However, we then have to go to some
    trouble to show the existence of finite limits for diagram shapes at other types.
  \<close>

  locale category_with_finite_limits =
    category +
  assumes has_finite_limits:
            "\<lbrakk> category (J :: nat comp); finite (Collect (partial_magma.arr J)) \<rbrakk>
                 \<Longrightarrow> has_limits_of_shape J"
  begin

    text\<open>
      We show that a category with finite limits has pullbacks and a terminal object
      and is therefore also a cartesian category.
    \<close>

    interpretation category_with_pullbacks C
    proof -
      interpret J: cospan_shape
        by unfold_locales
      have 1: "finite (Collect J.arr)"
      proof -
        have "Collect J.arr = {J.AA, J.BB, J.TT, J.AT, J.BT}"
          using J.arr_char cospan_shape.Dom.cases by auto
        thus ?thesis by simp
      qed
      obtain J' :: "nat comp" where J': "isomorphic_categories J' J.comp"
        using 1 J.finite_imp_ex_iso_nat_comp by blast
      interpret J'J: isomorphic_categories J' J.comp
        using J' by simp
      obtain \<phi> \<psi> where \<phi>\<psi>: "inverse_functors J.comp J' \<phi> \<psi>"
        using J'J.iso inverse_functors_sym by blast
      interpret \<phi>\<psi>: inverse_functors J.comp J' \<phi> \<psi>
        using \<phi>\<psi> by simp
      interpret \<psi>: invertible_functor J.comp J' \<psi>
        using \<phi>\<psi>.inverse_functors_axioms
        by unfold_locales auto
      show "category_with_pullbacks C"
      proof
        show "has_pullbacks"
        proof (unfold has_pullbacks_def has_as_pullback_def, intro allI impI)
          fix f0 f1
          assume cospan: "cospan f0 f1"
          interpret D: cospan_diagram C f0 f1
            using cospan
            by (simp add: category_axioms cospan_diagram_axioms_def cospan_diagram_def)
          have 2: "has_limits_of_shape J.comp"
            using 1 bij_betw_finite J'J.A.category_axioms has_finite_limits \<psi>.bij_betw_arr_sets
                  has_limits_preserved_by_isomorphism J'J.isomorphic_categories_axioms
            by blast
          obtain a \<chi> where \<chi>: "limit_cone J.comp C D.map a \<chi>"
            using 2 D.diagram_axioms has_limits_of_shape_def by blast
          interpret \<chi>: limit_cone J.comp C D.map a \<chi>
            using \<chi> by simp
          have "D.map = cospan_diagram.map C f0 f1" by simp
          moreover have "a = dom (\<chi> J.AA)"
            using J.arr_char \<chi>.component_in_hom by force
          moreover have "\<chi> = cospan_diagram.mkCone (\<cdot>) f0 f1 (\<chi> J.AA) (\<chi> J.BB)"
            using D.mkCone_cone \<chi>.cone_axioms by auto
          ultimately have "limit_cone (\<cdot>\<^sub>J) (\<cdot>)
                             (cospan_diagram.map (\<cdot>) f0 f1) (dom (\<chi> J.AA))
                             (cospan_diagram.mkCone (\<cdot>) f0 f1 (\<chi> J.AA) (\<chi> J.BB))"
            using \<chi>.limit_cone_axioms by simp
          thus "\<exists>p0 p1. cospan f0 f1 \<and>
                        limit_cone (\<cdot>\<^sub>J) (\<cdot>)
                          (cospan_diagram.map (\<cdot>) f0 f1) (dom p0)
                          (cospan_diagram.mkCone (\<cdot>) f0 f1 p0 p1)"
            using cospan by auto
        qed
      qed
    qed

    lemma is_category_with_pullbacks:
    shows "category_with_pullbacks C"
      ..

    sublocale category_with_pullbacks C ..

    interpretation category_with_terminal_object C
    proof
      show "\<exists>a. terminal a"
      proof -
        interpret J: discrete_category \<open>{} :: nat set\<close> 0
          by unfold_locales simp
        have 1: "has_limits_of_shape J.comp"
          using has_finite_limits
          by (metis Collect_empty_eq J.arr_char J.is_category empty_iff finite.emptyI)
        interpret D: diagram J.comp C \<open>\<lambda>_. null\<close>
          by unfold_locales auto
        obtain t \<tau> where \<tau>: "D.limit_cone t \<tau>"
          using 1 D.diagram_axioms has_limits_of_shape_def by blast
        interpret \<tau>: limit_cone J.comp C \<open>\<lambda>_. null\<close> t \<tau>
          using \<tau> by simp
        have "terminal t"
        proof
          show "ide t"
            using \<tau>.ide_apex by simp
          fix a
          assume a: "ide a"
          show "\<exists>!f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright>"
          proof -
            interpret a: constant_functor J.comp C a
              using a by unfold_locales
            interpret \<chi>: cone J.comp C \<open>\<lambda>_.null\<close> a \<open>\<lambda>_.null\<close>
              apply unfold_locales
                  apply simp
              using dom_null cod_null comp_null
              by blast+
            have "\<exists>!f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright> \<and> D.cones_map f \<tau> = (\<lambda>_. null)"
              using \<tau>.induced_arrowI [of "\<lambda>_.null" a] \<chi>.cone_axioms
                    \<tau>.is_universal [of a "\<lambda>_. null"]
              by simp
            moreover have "\<And>f. \<guillemotleft>f : a \<rightarrow> t\<guillemotright> \<Longrightarrow> D.cones_map f \<tau> = (\<lambda>_. null)"
              using \<tau>.cone_axioms by auto
            ultimately show ?thesis by auto
          qed
        qed
        thus ?thesis by blast
      qed
    qed

    lemma is_category_with_terminal_object:
    shows "category_with_terminal_object C"
      ..

    sublocale category_with_terminal_object C ..

    sublocale category_with_finite_products
      using has_finite_limits has_finite_products_if_has_finite_limits
            has_limits_of_shape_def diagram_def
      by unfold_locales blast

    sublocale cartesian_category ..

  end

  locale category_with_pullbacks_and_terminal =
    category_with_pullbacks +
    category_with_terminal_object

  sublocale category_with_finite_limits \<subseteq> category_with_pullbacks_and_terminal ..

  text\<open>
    Conversely, we show that a category with pullbacks and a terminal object also
    has finite products and equalizers, and therefore has finite limits.
  \<close>

  context category_with_pullbacks_and_terminal
  begin

    interpretation ECP: elementary_category_with_pullbacks C prj0 prj1
      using extends_to_elementary_category_with_pullbacks by simp

    abbreviation prj0'
    where "prj0' a b \<equiv> (if ide a \<and> ide b then prj0 (trm a) (trm b) else null)"

    abbreviation prj1'
    where "prj1' a b \<equiv> (if ide a \<and> ide b then prj1 (trm a) (trm b) else null)"

    interpretation ECC: elementary_cartesian_category C prj0' prj1' \<one> trm
      using trm_naturality ECP.universal
      by unfold_locales auto

    interpretation category_with_equalizers C
    proof (unfold_locales, unfold has_equalizers_def, intro allI impI)
      fix f0 f1
      assume par: "par f0 f1"
      interpret J: parallel_pair
        by unfold_locales
      interpret D: parallel_pair_diagram C f0 f1
        using par by unfold_locales auto
      have 1: "cospan (ECC.prod f1 (dom f0)) (ECC.prod f0 (dom f0))"
        using par by simp
      let ?g0 = "ECC.prod f0 (dom f0) \<cdot> ECC.dup (dom f0)"
      let ?g1 = "ECC.prod f1 (dom f1) \<cdot> ECC.dup (dom f1)"
      have g0: "\<guillemotleft>?g0 : dom f0 \<rightarrow> ECC.prod (cod f0) (dom f0)\<guillemotright>"
        using par by simp
      have g1: "\<guillemotleft>?g1 : dom f1 \<rightarrow> ECC.prod (cod f1) (dom f1)\<guillemotright>"
        using par by simp
      define e0 where "e0 = prj0 ?g1 ?g0"
      define e1 where "e1 = prj1 ?g1 ?g0"
      have e0: "\<guillemotleft>e0 : dom e0 \<rightarrow> dom f0\<guillemotright>"
        using par 1 e0_def by auto
      have e1: "\<guillemotleft>e1 : dom e0 \<rightarrow> dom f1\<guillemotright>"
        using par 1 e1_def e0_def by auto
      have eq: "e0 = e1"
      proof -
        have "e1 = prj0' (cod f1) (dom f1) \<cdot> ?g1 \<cdot> e1"
        proof -
          have "((prj0' (cod f1) (dom f1) \<cdot> (ECC.prod f1 (dom f1))) \<cdot> ECC.dup (dom f1)) \<cdot> e1 =
                dom f1 \<cdot> e1"
            using par ECC.pr_naturality(1) [of "dom f1" "dom f1" "dom f1" f1 "dom f1" "cod f1"]
                  comp_cod_arr ECC.pr_dup(1)
            by auto
          also have "... = e1"
            using par e1 comp_cod_arr by blast
          finally show ?thesis
            using comp_assoc by simp
        qed
        also have "... = prj0' (cod f1) (dom f1) \<cdot> ?g0 \<cdot> e0"
          using par ECP.pullback_commutes
          unfolding commutative_square_def e0_def e1_def by simp
        also have "... = e0"
        proof -
          have "((prj0' (cod f1) (dom f1) \<cdot> (ECC.prod f0 (dom f0))) \<cdot> ECC.dup (dom f0)) \<cdot> e0 =
                dom f0 \<cdot> e0"
            using par ECC.pr_naturality(1) [of "dom f0" "dom f0" "dom f1" f0 "dom f0" "cod f0"]
                  comp_cod_arr ECC.pr_dup(1) ide_dom
            by auto
          also have "... = e0"
            using e0 comp_cod_arr by blast
          finally show ?thesis
            using comp_assoc by simp
        qed
        finally show ?thesis by auto
      qed
      have equalizes: "D.is_equalized_by e0"
      proof
        show "seq f0 e0"
          using par e0 by auto
        show "f0 \<cdot> e0 = f1 \<cdot> e0"
        proof -
          have "f0 \<cdot> e0 = (f0 \<cdot> dom f0) \<cdot> e0"
            using par comp_arr_dom by simp
          also have "... = (f0 \<cdot> (prj1' (dom f0) (dom f0) \<cdot> ECC.dup (dom f0))) \<cdot> e0"
            using par ECC.pr_dup(2) by auto
          also have "... = ((f0 \<cdot> prj1' (dom f0) (dom f0)) \<cdot> ECC.dup (dom f0)) \<cdot> e0"
            using comp_assoc by auto
          also have "... = prj1' (cod f1) (dom f1) \<cdot> ?g0 \<cdot> e0"
            using par ECC.pr_naturality(2) [of "dom f0" "dom f0" "dom f1" f0 "dom f0" "cod f0"]
            by (metis (no_types, lifting) arr_dom cod_dom dom_dom comp_assoc)
          also have "... = prj1' (cod f1) (dom f1) \<cdot> ?g1 \<cdot> e1"
            using par ECP.pullback_commutes [of ?g1 ?g0]
            unfolding commutative_square_def e0_def e1_def by simp
          also have "... = (prj1' (cod f1) (dom f1) \<cdot> ?g1) \<cdot> e1"
            using comp_assoc by simp
          also have "... = (f1 \<cdot> (prj1' (dom f1) (dom f1) \<cdot> ECC.dup (dom f1))) \<cdot> e1"
            using par ECC.pr_naturality(2) [of "dom f1" "dom f1" "dom f1" f1 "dom f1" "cod f1"]
            by (metis (no_types, lifting) arr_dom cod_dom dom_dom comp_assoc)
          also have "... = (f1 \<cdot> dom f1) \<cdot> e1"
            using par ECC.pr_dup(2) by auto
          also have "... = f1 \<cdot> e1"
            using par comp_arr_dom by simp
          also have "... = f1 \<cdot> e0"
            using eq by simp
          finally show ?thesis by simp
        qed
      qed
      show "\<exists>e. has_as_equalizer f0 f1 e"
      proof
        interpret E: constant_functor J.comp C \<open>dom e0\<close>
          using par e0 by unfold_locales auto
        interpret \<chi>: cone J.comp C D.map \<open>dom e0\<close> \<open>D.mkCone e0\<close>
          using equalizes D.cone_mkCone e0_def by auto
        interpret \<chi>: limit_cone J.comp C D.map \<open>dom e0\<close> \<open>D.mkCone e0\<close>
        proof
          show "\<And>a' \<chi>'. D.cone a' \<chi>' \<Longrightarrow>
                         \<exists>!f. \<guillemotleft>f : a' \<rightarrow> dom e0\<guillemotright> \<and> D.cones_map f (D.mkCone e0) = \<chi>'"
          proof -
            fix a' \<chi>'
            assume \<chi>': "D.cone a' \<chi>'"
            interpret \<chi>': cone J.comp C D.map a' \<chi>'
              using \<chi>' by simp
            have 3: "commutative_square ?g1 ?g0 (\<chi>' J.Zero) (\<chi>' J.Zero)"
            proof
              show "cospan ?g1 ?g0"
                using par g0 g1 by simp
              show 4: "span (\<chi>' J.Zero) (\<chi>' J.Zero)"
                using J.arr_char by simp
              show 5: "dom ?g1 = cod (\<chi>' J.Zero)"
                using par g1 J.arr_char D.map_def by simp
              show "?g1 \<cdot> \<chi>' J.Zero = ?g0 \<cdot> \<chi>' J.Zero"
              proof -
                have "?g1 \<cdot> \<chi>' J.Zero = ECC.prod f1 (dom f1) \<cdot> ECC.dup (dom f1) \<cdot> \<chi>' J.Zero"
                  using comp_assoc by simp
                also have "... = ECC.prod f1 (dom f1) \<cdot> ECC.tuple (\<chi>' J.Zero) (\<chi>' J.Zero)"
                  using par D.map_def J.arr_char comp_cod_arr by auto
                also have "... = ECC.tuple (f1 \<cdot> \<chi>' J.Zero) (\<chi>' J.Zero)"
                  using par ECC.prod_tuple [of "\<chi>' J.Zero" "\<chi>' J.Zero" f1 "dom f1"]
                        comp_cod_arr
                  by (metis (no_types, lifting) 4 5 g1 in_homE seqI)
                also have "... = ECC.tuple (f0 \<cdot> \<chi>' J.Zero) (\<chi>' J.Zero)"
                  using par D.is_equalized_by_cone \<chi>'.cone_axioms by auto
                also have "... = ECC.prod f0 (dom f0) \<cdot> ECC.tuple (\<chi>' J.Zero) (\<chi>' J.Zero)"
                  using par ECC.prod_tuple [of "\<chi>' J.Zero" "\<chi>' J.Zero" f0 "dom f0"]
                        comp_cod_arr
                  by (metis (no_types, lifting) 4 5 g1 in_homE seqI)
                also have "... = ECC.prod f0 (dom f0) \<cdot> ECC.dup (dom f0) \<cdot> \<chi>' J.Zero"
                  using par D.map_def J.arr_char comp_cod_arr by auto
                also have "... = ?g0 \<cdot> \<chi>' J.Zero"
                  using comp_assoc by simp
                finally show ?thesis by blast
              qed
            qed
            show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> dom e0\<guillemotright> \<and> D.cones_map f (D.mkCone e0) = \<chi>'"
            proof
              define f where "f = ECP.tuple (\<chi>' J.Zero) ?g1 ?g0 (\<chi>' J.Zero)"
              have 4: "e0 \<cdot> f = \<chi>' J.Zero"
                using ECP.universal by (simp add: "3" e1_def eq f_def)
              have f: "\<guillemotleft>f : a' \<rightarrow> dom e0\<guillemotright>"
              proof -
                have "a' = dom (\<chi>' J.Zero)"
                  by (simp add: J.arr_char)
                thus ?thesis
                  using 3 f_def e0_def g0 g1 ECP.tuple_in_hom ECP.pbdom_def by simp
              qed
              moreover have 5: "D.cones_map f (D.mkCone e0) = \<chi>'"
              proof -
                have "\<And>j. J.arr j \<Longrightarrow> D.mkCone e0 j \<cdot> f = \<chi>' j"
                proof -
                  fix j
                  assume j: "J.arr j"
                  show "D.mkCone e0 j \<cdot> f = \<chi>' j"
                  proof (cases "j = J.Zero")
                    case True
                    moreover have "e0 \<cdot> f = \<chi>' J.Zero"
                      using 4 by simp
                    ultimately show ?thesis
                      unfolding f_def D.mkCone_def comp_assoc
                      using J.arr_char by simp
                    next
                    case F: False
                    hence 1: "(f0 \<cdot> e0) \<cdot> f = f0 \<cdot> \<chi>' J.Zero"
                      using 4 comp_assoc by simp
                    also have "... = \<chi>' j"
                      by (metis (no_types, lifting) F D.mkCone_cone D.mkCone_def
                          \<chi>'.cone_axioms j)
                    finally show ?thesis
                      by (simp add: F D.mkCone_def j)
                  qed
                qed
                thus ?thesis
                  using f e0 \<chi>.cone_axioms \<chi>'.is_extensional by auto
              qed
              ultimately show "\<guillemotleft>f : a' \<rightarrow> dom e0\<guillemotright> \<and> D.cones_map f (D.mkCone e0) = \<chi>'"
                by simp
              fix f'
              assume f': "\<guillemotleft>f' : a' \<rightarrow> dom e0\<guillemotright> \<and> D.cones_map f' (D.mkCone e0) = \<chi>'"
              show "f' = f"
              proof -
                have "e0 \<cdot> f' = \<chi>' J.Zero"
                  using f' D.mkCone_cone D.mkCone_def \<chi>'.cone_axioms
                        comp_assoc J.arr_char \<chi>.cone_axioms
                  by auto
                thus ?thesis
                  using f' 3 4 eq ECP.universal [of ?g1 ?g0 "e1 \<cdot> f'" "e0 \<cdot> f'"] e0_def e1_def
                  by (metis (no_types, lifting))
              qed
            qed
          qed
        qed
        show "has_as_equalizer f0 f1 e0"
        proof -
          have "par f0 f1"
            by fact
          moreover have "D.has_as_equalizer e0"
            ..
          ultimately show ?thesis
            using has_as_equalizer_def by blast
        qed
      qed
    qed

    interpretation category_with_finite_products C
      by (simp add: ECC.is_cartesian_category cartesian_category.is_category_with_finite_products)

    lemma has_finite_products:
    shows "category_with_finite_products C"
      ..

    lemma has_finite_limits:
    shows "category_with_finite_limits C"
    proof
      fix J :: "nat comp"
      assume J: "category J"
      interpret J: category J
        using J by simp
      assume finite: "finite (Collect J.arr)"
      show "has_limits_of_shape J"
      proof -
        have "Collect (partial_magma.ide J) \<subseteq> Collect J.arr"
          by auto
        hence 1: "finite (Collect J.ide)"
          using finite finite_subset by blast
        have "has_products (Collect (partial_magma.ide J))"
          using 1 J.ideD(1) J.not_arr_null category_with_finite_products.has_finite_products
                is_category_with_finite_products
          by simp
        moreover have "Collect (partial_magma.ide J) \<noteq> UNIV"
          using J.not_arr_null by blast
        moreover have "Collect (partial_magma.arr J) \<noteq> UNIV"
          using J.not_arr_null by blast
        ultimately show ?thesis
          using finite 1 J.category_axioms has_limits_if_has_products
                has_finite_products' [of "Collect J.ide"]
                has_finite_products' [of "Collect J.arr"]
          by simp
      qed
    qed

    sublocale category_with_finite_limits C
      using has_finite_limits by simp

  end

end

