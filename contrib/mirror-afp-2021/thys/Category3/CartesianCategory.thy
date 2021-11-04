(*  Title:       CartesianCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Cartesian Category"

text\<open>
  In this chapter, we explore the notion of a ``cartesian category'', which we define
  to be a category having binary products and a terminal object.
  We show that every cartesian category extends to an ``elementary cartesian category'',
  whose definition assumes that specific choices have been made for projections and
  terminal object.
  Conversely, the underlying category of an elementary cartesian category is a
  cartesian category.
  We also show that cartesian categories are the same thing as categories with
  finite products.
\<close>

theory CartesianCategory
imports Limit SetCat
begin

  section "Category with Binary Products"

  subsection "Binary Product Diagrams"

  text \<open>
    The ``shape'' of a binary product diagram is a category having two distinct identity arrows
    and no non-identity arrows.
  \<close>

  locale binary_product_shape
  begin

    sublocale concrete_category \<open>UNIV :: bool set\<close> \<open>\<lambda>a b. if a = b then {()} else {}\<close>
                                \<open>\<lambda>_. ()\<close> \<open>\<lambda>_ _ _ _ _. ()\<close>
      apply (unfold_locales, auto)
       apply (meson empty_iff)
      by (meson empty_iff)

    abbreviation comp
    where "comp \<equiv> COMP"

    abbreviation FF
    where "FF \<equiv> MkIde False"

    abbreviation TT
    where "TT \<equiv> MkIde True"

    lemma arr_char:
    shows "arr f \<longleftrightarrow> f = FF \<or> f = TT"
      using arr_char by (cases f, simp_all)

    lemma ide_char:
    shows "ide f \<longleftrightarrow> f = FF \<or> f = TT"
      using ide_char ide_MkIde by (cases f, auto)

    lemma is_discrete:
    shows "ide f \<longleftrightarrow> arr f"
      using arr_char ide_char by simp

    lemma dom_simp [simp]:
    assumes "arr f"
    shows "dom f = f"
      using assms is_discrete by simp

    lemma cod_simp [simp]:
    assumes "arr f"
    shows "cod f = f"
      using assms is_discrete by simp

    lemma seq_char:
    shows "seq f g \<longleftrightarrow> arr f \<and> f = g"
      by auto

    lemma comp_simp [simp]:
    assumes "seq f g"
    shows "comp f g = f"
      using assms seq_char by fastforce

  end

  locale binary_product_diagram =
    J: binary_product_shape +
    C: category C
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and a0 :: 'c
  and a1 :: 'c +
  assumes is_discrete: "C.ide a0 \<and> C.ide a1"
  begin

    notation J.comp      (infixr "\<cdot>\<^sub>J" 55)

    fun map
    where "map J.FF = a0"
        | "map J.TT = a1"
        | "map _ = C.null"

    sublocale diagram J.comp C map
    proof
      show "\<And>f. \<not> J.arr f \<Longrightarrow> map f = C.null"
        using J.arr_char map.elims by auto
      fix f
      assume f: "J.arr f"
      show "C.arr (map f)"
        using f J.arr_char is_discrete C.ideD(1) map.simps(1-2) by metis
      show "C.dom (map f) = map (J.dom f)"
        using f J.arr_char J.dom_char is_discrete by force
      show "C.cod (map f) = map (J.cod f)"
        using f J.arr_char J.cod_char is_discrete by force
      next
      fix f g
      assume fg: "J.seq g f"
      show "map (g \<cdot>\<^sub>J f) = map g \<cdot> map f"
        using fg J.arr_char J.seq_char J.null_char J.not_arr_null is_discrete
        by (metis (no_types, lifting) C.comp_ide_self J.comp_simp map.simps(1-2))
    qed

  end

  subsection "Category with Binary Products"

  text \<open>
    A \emph{binary product} in a category @{term C} is a limit of a binary product diagram
    in @{term C}.
  \<close>

  context binary_product_diagram
  begin

    definition mkCone
    where "mkCone p0 p1 \<equiv> \<lambda>j. if j = J.FF then p0 else if j = J.TT then p1 else C.null"

    abbreviation is_rendered_commutative_by
    where "is_rendered_commutative_by p0 p1 \<equiv>
           C.seq a0 p0 \<and> C.seq a1 p1 \<and> C.dom p0 = C.dom p1"

    abbreviation has_as_binary_product
    where "has_as_binary_product p0 p1 \<equiv> limit_cone (C.dom p0) (mkCone p0 p1)"

    lemma cone_mkCone:
    assumes "is_rendered_commutative_by p0 p1"
    shows "cone (C.dom p0) (mkCone p0 p1)"
    proof -
      interpret E: constant_functor J.comp C \<open>C.dom p0\<close>
        using assms by unfold_locales auto
      show "cone (C.dom p0) (mkCone p0 p1)"
        using assms mkCone_def J.arr_char E.map_simp is_discrete C.comp_ide_arr C.comp_arr_dom
        by unfold_locales auto
    qed

    lemma is_rendered_commutative_by_cone:
    assumes "cone a \<chi>"
    shows "is_rendered_commutative_by (\<chi> J.FF) (\<chi> J.TT)"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      show ?thesis
        using is_discrete by simp
    qed

    lemma mkCone_cone:
    assumes "cone a \<chi>"
    shows "mkCone (\<chi> J.FF) (\<chi> J.TT) = \<chi>"
    proof -
      interpret \<chi>: cone J.comp C map a \<chi>
        using assms by auto
      interpret mkCone_\<chi>: cone J.comp C map \<open>C.dom (\<chi> J.FF)\<close> \<open>mkCone (\<chi> J.FF) (\<chi> J.TT)\<close>
        using assms is_rendered_commutative_by_cone cone_mkCone by blast
      show ?thesis
        using mkCone_def \<chi>.is_extensional J.ide_char mkCone_def
              NaturalTransformation.eqI [of J.comp C]
              \<chi>.natural_transformation_axioms mkCone_\<chi>.natural_transformation_axioms
        by fastforce
    qed

  end

  locale binary_product_cone =
    J: binary_product_shape +
    C: category C +
    D: binary_product_diagram C f0 f1 +
    limit_cone J.comp C D.map \<open>C.dom p0\<close> \<open>D.mkCone p0 p1\<close>
  for C :: "'c comp"      (infixr "\<cdot>" 55)
  and f0 :: 'c
  and f1 :: 'c
  and p0 :: 'c
  and p1 :: 'c
  begin

    lemma renders_commutative:
    shows "D.is_rendered_commutative_by p0 p1"
      using cone_axioms D.is_rendered_commutative_by_cone D.mkCone_def \<Phi>.Ya.Cop_S.arr.simps(1)
      by (metis (no_types, lifting))  (* TODO: pretty opaque *)

    lemma is_universal':
    assumes "D.is_rendered_commutative_by p0' p1'"
    shows "\<exists>!h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<and> p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
    proof -
      have "D.cone (C.dom p0') (D.mkCone p0' p1')"
        using assms D.cone_mkCone by blast
      hence "\<exists>!h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<and>
                  D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1'"
        using is_universal by simp
      moreover have "\<And>h. \<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright> \<Longrightarrow>
                           D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1' \<longleftrightarrow>
                           p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
      proof -
        fix h
        assume h: "\<guillemotleft>h : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
        show "D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1' \<longleftrightarrow>
              p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
        proof
          assume 1: "D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1'"
          show "p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
          proof
            show "p0 \<cdot> h = p0'"
            proof -
              have "p0' = D.mkCone p0' p1' J.FF"
                using D.mkCone_def J.arr_char by simp
              also have "... = D.cones_map h (D.mkCone p0 p1) J.FF"
                using 1 by simp
              also have "... = p0 \<cdot> h"
                using h D.mkCone_def J.arr_char cone_\<chi> by auto
              finally show ?thesis by auto
            qed
            show "p1 \<cdot> h = p1'"
            proof -
              have "p1' = D.mkCone p0' p1' J.TT"
                using D.mkCone_def J.arr_char by simp
              also have "... = D.cones_map h (D.mkCone p0 p1) J.TT"
                using 1 by simp
              also have "... = p1 \<cdot> h"
                using h D.mkCone_def J.arr_char cone_\<chi> by auto
              finally show ?thesis by auto
            qed
          qed
          next
          assume 1: "p0 \<cdot> h = p0' \<and> p1 \<cdot> h = p1'"
          show "D.cones_map h (D.mkCone p0 p1) = D.mkCone p0' p1'"
            using h 1 cone_\<chi> D.mkCone_def by auto
        qed
      qed
      ultimately show ?thesis by blast
    qed

    lemma induced_arrowI':
    assumes "D.is_rendered_commutative_by p0' p1'"
    shows "\<guillemotleft>induced_arrow (C.dom p0') (D.mkCone p0' p1') : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
    and "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') = p0'"
    and "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') = p1'"
    proof -
      interpret A': constant_functor J.comp C \<open>C.dom p0'\<close>
        using assms by (unfold_locales, auto)
      have cone: "D.cone (C.dom p0') (D.mkCone p0' p1')"
        using assms D.cone_mkCone [of p0' p1'] by blast
      show 0: "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') = p0'"
      proof -
        have "p0 \<cdot> induced_arrow (C.dom p0') (D.mkCone p0' p1') =
                D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) J.FF"
          using cone induced_arrowI(1) D.mkCone_def J.arr_char cone_\<chi> by force
        also have "... = p0'"
        proof -
          have "D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) =
                D.mkCone p0' p1'"
            using cone induced_arrowI by blast
          thus ?thesis
            using J.arr_char D.mkCone_def by simp
        qed
        finally show ?thesis by auto
      qed
      show "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') = p1'"
      proof -
        have "p1 \<cdot> induced_arrow (C.dom p1') (D.mkCone p0' p1') =
                D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) J.TT"
          using assms cone induced_arrowI(1) D.mkCone_def J.arr_char cone_\<chi> by fastforce
        also have "... = p1'"
        proof -
          have "D.cones_map (induced_arrow (C.dom p0') (D.mkCone p0' p1'))
                            (D.mkCone p0 p1) =
                D.mkCone p0' p1'"
            using cone induced_arrowI by blast
          thus ?thesis
            using J.arr_char D.mkCone_def by simp
        qed
        finally show ?thesis by auto
      qed
      show "\<guillemotleft>induced_arrow (C.dom p0') (D.mkCone p0' p1') : C.dom p0' \<rightarrow> C.dom p0\<guillemotright>"
        using 0 cone induced_arrowI by simp
    qed

  end

  context category
  begin

    definition has_as_binary_product
    where "has_as_binary_product a0 a1 p0 p1 \<equiv>
           ide a0 \<and> ide a1 \<and> binary_product_diagram.has_as_binary_product C a0 a1 p0 p1"

    definition has_binary_products
    where "has_binary_products =
           (\<forall>a0 a1. ide a0 \<and> ide a1 \<longrightarrow> (\<exists>p0 p1. has_as_binary_product a0 a1 p0 p1))"

  end

  locale category_with_binary_products =
    category +
  assumes has_binary_products: has_binary_products

  subsection "Elementary Category with Binary Products"

  text \<open>
    An \emph{elementary category with binary products} is a category equipped with a specific
    way of mapping each pair of objects \<open>a\<close> and \<open>b\<close> to a pair of arrows \<open>\<pp>\<^sub>1[a, b]\<close> and \<open>\<pp>\<^sub>0[a, b]\<close>
    that comprise a universal span.  It is useful to assume that the mappings that produce
    \<open>\<pp>\<^sub>1[a, b]\<close> and \<open>\<pp>\<^sub>0[a, b]\<close> from \<open>a\<close> and \<open>b\<close> are extensional; that is, if either \<open>a\<close> or \<open>b\<close>
    is not an identity, then \<open>\<pp>\<^sub>1[a, b]\<close> and \<open>\<pp>\<^sub>0[a, b]\<close> are \<open>null\<close>.
  \<close>

  locale elementary_category_with_binary_products =
    category C
  for C :: "'a comp"                             (infixr "\<cdot>" 55)
  and pr0 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                    ("\<pp>\<^sub>0[_, _]")
  and pr1 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"                    ("\<pp>\<^sub>1[_, _]") +
  assumes pr0_ext: "\<not> (ide a \<and> ide b) \<Longrightarrow> \<pp>\<^sub>0[a, b] = null"
  and pr1_ext: "\<not> (ide a \<and> ide b) \<Longrightarrow> \<pp>\<^sub>1[a, b] = null"
  and span_pr: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> span \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]"
  and cod_pr0: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> cod \<pp>\<^sub>0[a, b] = b"
  and cod_pr1: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> cod \<pp>\<^sub>1[a, b] = a"
  and universal: "span f g \<Longrightarrow> \<exists>!l. \<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g"
  begin

    lemma pr0_in_hom':
    assumes "ide a" and "ide b"
    shows "\<guillemotleft>\<pp>\<^sub>0[a, b] : dom \<pp>\<^sub>0[a, b] \<rightarrow> b\<guillemotright>"
      using assms span_pr cod_pr0 by auto

    lemma pr1_in_hom':
    assumes "ide a" and "ide b"
    shows "\<guillemotleft>\<pp>\<^sub>1[a, b] : dom \<pp>\<^sub>0[a, b] \<rightarrow> a\<guillemotright>"
      using assms span_pr cod_pr1 by auto

    text \<open>
      We introduce a notation for tupling, which denotes the arrow into a product that
      is induced by a span.
    \<close>

    definition tuple         ("\<langle>_, _\<rangle>")
    where "\<langle>f, g\<rangle> \<equiv> if span f g then
                      THE l. \<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g
                    else null"

    text \<open>
      The following defines product of arrows (not just of objects).  It will take a little
      while before we can prove that it is functorial, but for right now it is nice to have
      it as a notation for the apex of a product cone.  We have to go through some slightly
      unnatural contortions in the development here, though, to avoid having to introduce a
      separate preliminary notation just for the product of objects.
    \<close>
    (* TODO: I want to use \<times> but it has already been commandeered for product types. *)
    definition prod         (infixr "\<otimes>" 51)
    where "f \<otimes> g \<equiv> \<langle>f \<cdot> \<pp>\<^sub>1[dom f, dom g], g \<cdot> \<pp>\<^sub>0[dom f, dom g]\<rangle>"

    lemma seq_pr_tuple:
    assumes "span f g"
    shows "seq \<pp>\<^sub>0[cod f, cod g] \<langle>f, g\<rangle>"
    proof -
      have "\<pp>\<^sub>0[cod f, cod g] \<cdot> \<langle>f, g\<rangle> = g"
        unfolding tuple_def
        using assms universal theI [of "\<lambda>l. \<pp>\<^sub>1[cod f, cod g] \<cdot> l = f \<and> \<pp>\<^sub>0[cod f, cod g] \<cdot> l = g"]
        by simp meson
      thus ?thesis
        using assms by simp
    qed

    lemma tuple_pr_arr:
    assumes "ide a" and "ide b" and "seq \<pp>\<^sub>0[a, b] h"
    shows "\<langle>\<pp>\<^sub>1[a, b] \<cdot> h, \<pp>\<^sub>0[a, b] \<cdot> h\<rangle> = h"
      unfolding tuple_def
      using assms span_pr cod_pr0 cod_pr1 universal [of "\<pp>\<^sub>1[a, b] \<cdot> h" "\<pp>\<^sub>0[a, b] \<cdot> h"]
            theI_unique [of "\<lambda>l. \<pp>\<^sub>1[a, b] \<cdot> l = \<pp>\<^sub>1[a, b] \<cdot> h \<and> \<pp>\<^sub>0[a, b] \<cdot> l = \<pp>\<^sub>0[a, b] \<cdot> h" h]
      by auto

    lemma pr_tuple [simp]:
    assumes "span f g" and "cod f = a" and "cod g = b"
    shows "\<pp>\<^sub>1[a, b] \<cdot> \<langle>f, g\<rangle> = f" and "\<pp>\<^sub>0[a, b] \<cdot> \<langle>f, g\<rangle> = g"
    proof -
      have 1: "\<pp>\<^sub>1[a, b] \<cdot> \<langle>f, g\<rangle> = f \<and> \<pp>\<^sub>0[a, b] \<cdot> \<langle>f, g\<rangle> = g"
        unfolding tuple_def
        using assms universal theI [of "\<lambda>l. \<pp>\<^sub>1[a, b] \<cdot> l = f \<and> \<pp>\<^sub>0[a, b] \<cdot> l = g"]
        by simp meson
      show "\<pp>\<^sub>1[a, b] \<cdot> \<langle>f, g\<rangle> = f" using 1 by simp
      show "\<pp>\<^sub>0[a, b] \<cdot> \<langle>f, g\<rangle> = g" using 1 by simp
    qed

    lemma cod_tuple:
    assumes "span f g"
    shows "cod \<langle>f, g\<rangle> = cod f \<otimes> cod g"
    proof -
      have "cod f \<otimes> cod g = \<langle>\<pp>\<^sub>1[cod f, cod g], \<pp>\<^sub>0[cod f, cod g]\<rangle>"
        unfolding prod_def
        using assms comp_cod_arr span_pr cod_pr0 cod_pr1 by simp
      also have "... = \<langle>\<pp>\<^sub>1[cod f, cod g] \<cdot> dom \<pp>\<^sub>0[cod f, cod g],
                        \<pp>\<^sub>0[cod f, cod g] \<cdot> dom \<pp>\<^sub>0[cod f, cod g]\<rangle>"
        using assms span_pr comp_arr_dom by simp
      also have "... = dom \<pp>\<^sub>0[cod f, cod g]"
        using assms tuple_pr_arr span_pr by simp
      also have "... = cod \<langle>f, g\<rangle>"
        using assms seq_pr_tuple by blast
      finally show ?thesis by simp
    qed

    lemma tuple_in_hom [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>" and "\<guillemotleft>g : a \<rightarrow> c\<guillemotright>"
    shows "\<guillemotleft>\<langle>f, g\<rangle> : a \<rightarrow> b \<otimes> c\<guillemotright>"
      using assms pr_tuple dom_comp cod_tuple
      apply (elim in_homE, intro in_homI)
        apply (metis seqE)
      by metis+

    lemma tuple_in_hom' [simp]:
    assumes "arr f" and "dom f = a" and "cod f = b"
    and "arr g" and "dom g = a" and "cod g = c"
    shows "\<guillemotleft>\<langle>f, g\<rangle> : a \<rightarrow> b \<otimes> c\<guillemotright>"
      using assms by auto

    lemma tuple_ext:
    assumes "\<not> span f g"
    shows "\<langle>f, g\<rangle> = null"
      unfolding tuple_def
      by (simp add: assms)

    lemma tuple_simps [simp]:
    assumes "span f g"
    shows "arr \<langle>f, g\<rangle>" and "dom \<langle>f, g\<rangle> = dom f" and "cod \<langle>f, g\<rangle> = cod f \<otimes> cod g"
    proof -
      show "arr \<langle>f, g\<rangle>"
        using assms tuple_in_hom by blast
      show "dom \<langle>f, g\<rangle> = dom f"
        using assms tuple_in_hom
        by (metis dom_comp pr_tuple(1))
      show "cod \<langle>f, g\<rangle> = cod f \<otimes> cod g"
        using assms cod_tuple by auto
    qed

    lemma tuple_pr [simp]:
    assumes "ide a" and "ide b"
    shows "\<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle> = a \<otimes> b"
    proof -
      have 1: "dom \<pp>\<^sub>0[a, b] = a \<otimes> b"
        using assms seq_pr_tuple cod_tuple [of "\<pp>\<^sub>1[a, b]" "\<pp>\<^sub>0[a, b]"] span_pr
              pr0_in_hom' pr1_in_hom'
        by (metis cod_pr0 cod_pr1 seqE)
      hence "\<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle> = \<langle>\<pp>\<^sub>1[a, b] \<cdot> (a \<otimes> b), \<pp>\<^sub>0[a, b] \<cdot> (a \<otimes> b)\<rangle>"
        using assms pr0_in_hom' pr1_in_hom' comp_arr_dom span_pr by simp
      thus ?thesis
        using assms 1 tuple_pr_arr span_pr
        by (metis comp_arr_dom)
    qed

    lemma pr_in_hom [intro, simp]:
    assumes "ide a" and "ide b"
    shows "\<guillemotleft>\<pp>\<^sub>0[a, b] : a \<otimes> b \<rightarrow> b\<guillemotright>" and "\<guillemotleft>\<pp>\<^sub>1[a, b] : a \<otimes> b \<rightarrow> a\<guillemotright>"
    proof -
      show 0: "\<guillemotleft>\<pp>\<^sub>0[a, b] : a \<otimes> b \<rightarrow> b\<guillemotright>"
        using assms pr0_in_hom' seq_pr_tuple [of "\<pp>\<^sub>1[a, b]" "\<pp>\<^sub>0[a, b]"]
              cod_tuple [of "\<pp>\<^sub>1[a, b]" "\<pp>\<^sub>0[a, b]"] span_pr cod_pr0 cod_pr1
        by (intro in_homI, auto)
      show "\<guillemotleft>\<pp>\<^sub>1[a, b] : a \<otimes> b \<rightarrow> a\<guillemotright>"
        using assms 0 span_pr pr1_in_hom' by fastforce
    qed

    lemma pr_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr \<pp>\<^sub>0[a, b]" and "dom \<pp>\<^sub>0[a, b] = a \<otimes> b" and "cod \<pp>\<^sub>0[a, b] = b"
    and "arr \<pp>\<^sub>1[a, b]" and "dom \<pp>\<^sub>1[a, b] = a \<otimes> b" and "cod \<pp>\<^sub>1[a, b] = a"
      using assms pr_in_hom by blast+

    lemma arr_pr0_iff [iff]:
    shows "arr \<pp>\<^sub>0[a, b] \<longleftrightarrow> ide a \<and> ide b"
    proof
      show "ide a \<and> ide b \<Longrightarrow> arr \<pp>\<^sub>0[a, b]"
        using pr_in_hom by auto
      show "arr \<pp>\<^sub>0[a, b] \<Longrightarrow> ide a \<and> ide b"
        using pr0_ext not_arr_null by metis
    qed

    lemma arr_pr1_iff [iff]:
    shows "arr \<pp>\<^sub>1[a, b] \<longleftrightarrow> ide a \<and> ide b"
    proof
      show "ide a \<and> ide b \<Longrightarrow> arr \<pp>\<^sub>1[a, b]"
        using pr_in_hom by auto
      show "arr \<pp>\<^sub>1[a, b] \<Longrightarrow> ide a \<and> ide b"
        using pr1_ext not_arr_null by metis
    qed

    lemma pr_joint_monic:
    assumes "seq \<pp>\<^sub>0[a, b] h"
    and "\<pp>\<^sub>0[a, b] \<cdot> h = \<pp>\<^sub>0[a, b] \<cdot> h'" and "\<pp>\<^sub>1[a, b] \<cdot> h = \<pp>\<^sub>1[a, b] \<cdot> h'"
    shows "h = h'"
      using assms
      by (metis arr_pr0_iff seqE tuple_pr_arr)

    lemma comp_tuple_arr [simp]:
    assumes "span f g" and "arr h" and "dom f = cod h"
    shows "\<langle>f, g\<rangle> \<cdot> h = \<langle>f \<cdot> h, g \<cdot> h\<rangle>"
    proof (intro pr_joint_monic [where h = "\<langle>f, g\<rangle> \<cdot> h"])
      show "seq \<pp>\<^sub>0[cod f, cod g] (\<langle>f, g\<rangle> \<cdot> h)"
        using assms by fastforce
      show "\<pp>\<^sub>0[cod f, cod g] \<cdot> \<langle>f, g\<rangle> \<cdot> h = \<pp>\<^sub>0[cod f, cod g] \<cdot> \<langle>f \<cdot> h, g \<cdot> h\<rangle>"
      proof -
        have "\<pp>\<^sub>0[cod f, cod g] \<cdot> \<langle>f, g\<rangle> \<cdot> h = (\<pp>\<^sub>0[cod f, cod g] \<cdot> \<langle>f, g\<rangle>) \<cdot> h"
          using comp_assoc by simp
        thus ?thesis
          using assms by simp
      qed
      show "\<pp>\<^sub>1[cod f, cod g] \<cdot> \<langle>f, g\<rangle> \<cdot> h = \<pp>\<^sub>1[cod f, cod g] \<cdot> \<langle>f \<cdot> h, g \<cdot> h\<rangle>"
      proof -
        have "\<pp>\<^sub>1[cod f, cod g] \<cdot> \<langle>f, g\<rangle> \<cdot> h = (\<pp>\<^sub>1[cod f, cod g] \<cdot> \<langle>f, g\<rangle>) \<cdot> h"
          using comp_assoc by simp
        thus ?thesis
          using assms by simp
      qed
    qed

    lemma ide_prod [intro, simp]:
    assumes "ide a" and "ide b"
    shows "ide (a \<otimes> b)"
      using assms pr_simps ide_dom [of "\<pp>\<^sub>0[a, b]"] by simp

    lemma prod_in_hom [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow> c\<guillemotright>" and "\<guillemotleft>g : b \<rightarrow> d\<guillemotright>"
    shows "\<guillemotleft>f \<otimes> g : a \<otimes> b \<rightarrow> c \<otimes> d\<guillemotright>"
      using assms prod_def by fastforce

    lemma prod_in_hom' [simp]:
    assumes "arr f" and "dom f = a" and "cod f = c"
    and "arr g" and "dom g = b" and "cod g = d"
    shows "\<guillemotleft>f \<otimes> g : a \<otimes> b \<rightarrow> c \<otimes> d\<guillemotright>"
      using assms by blast

    lemma prod_simps [simp]:
    assumes "arr f0" and "arr f1"
    shows "arr (f0 \<otimes> f1)"
    and "dom (f0 \<otimes> f1) = dom f0 \<otimes> dom f1"
    and "cod (f0 \<otimes> f1) = cod f0 \<otimes> cod f1"
      using assms prod_in_hom by blast+

  end

  subsection "Agreement between the Definitions"

  text \<open>
    We now show that a category with binary products extends (by making a choice)
    to an elementary category with binary products, and that the underlying category
    of an elementary category with binary products is a category with binary products.
  \<close>

  context category_with_binary_products
  begin

    definition pr1
    where "pr1 a b \<equiv> if ide a \<and> ide b then
                        fst (SOME x. has_as_binary_product a b (fst x) (snd x))
                      else null"

    definition pr0
    where "pr0 a b \<equiv> if ide a \<and> ide b then
                        snd (SOME x. has_as_binary_product a b (fst x) (snd x))
                      else null"

    lemma pr_yields_binary_product:
    assumes "ide a" and "ide b"
    shows "has_as_binary_product a b (pr1 a b) (pr0 a b)"
    proof -
      have "\<exists>x. has_as_binary_product a b (fst x) (snd x)"
        using assms has_binary_products has_binary_products_def has_as_binary_product_def
        by simp
      thus ?thesis
        using assms has_binary_products has_binary_products_def pr0_def pr1_def
              someI_ex [of "\<lambda>x. has_as_binary_product a b (fst x) (snd x)"]
        by simp
    qed

    interpretation elementary_category_with_binary_products C pr0 pr1
    proof
      show "\<And>a b. \<not> (ide a \<and> ide b) \<Longrightarrow> pr0 a b = null"
        using pr0_def by auto
      show "\<And>a b. \<not> (ide a \<and> ide b) \<Longrightarrow> pr1 a b = null"
        using pr1_def by auto
      fix a b
      assume a: "ide a" and b: "ide b"
      interpret J: binary_product_shape .
      interpret D: binary_product_diagram C a b
        using a b by unfold_locales auto
      let ?\<chi> = "D.mkCone (pr1 a b) (pr0 a b)"
      interpret \<chi>: limit_cone J.comp C D.map \<open>dom (pr1 a b)\<close> ?\<chi>
        using a b pr_yields_binary_product
        by (simp add: has_as_binary_product_def)
      have 1: "pr1 a b = ?\<chi> J.FF \<and> pr0 a b = ?\<chi> J.TT"
        using D.mkCone_def by simp
      show "span (pr1 a b) (pr0 a b)"
        using 1 \<chi>.preserves_reflects_arr J.seqE J.arr_char J.seq_char J.is_category
              D.is_rendered_commutative_by_cone \<chi>.cone_axioms
        by metis
      show "cod (pr1 a b) = a"
        using 1 \<chi>.preserves_cod [of J.FF] J.cod_char J.arr_char by auto
      show "cod (pr0 a b) = b"
        using 1 \<chi>.preserves_cod [of J.TT] J.cod_char J.arr_char by auto
      next
      fix f g
      assume fg: "span f g"
      show "\<exists>!l. pr1 (cod f) (cod g) \<cdot> l = f \<and> pr0 (cod f) (cod g) \<cdot> l = g"
      proof -
        interpret J: binary_product_shape .
        interpret D: binary_product_diagram C \<open>cod f\<close> \<open>cod g\<close>
          using fg by unfold_locales auto
        let ?\<chi> = "D.mkCone (pr1 (cod f) (cod g)) (pr0 (cod f) (cod g))"
        interpret \<chi>: limit_cone J.comp C D.map \<open>dom (pr1 (cod f) (cod g))\<close> ?\<chi>
          using fg pr_yields_binary_product [of "cod f" "cod g"] has_as_binary_product_def
          by simp
        interpret \<chi>: binary_product_cone C \<open>cod f\<close> \<open>cod g\<close>
                       \<open>pr1 (cod f) (cod g)\<close> \<open>pr0 (cod f) (cod g)\<close> ..
        have 1: "pr1 (cod f) (cod g) = ?\<chi> J.FF \<and> pr0 (cod f) (cod g) = ?\<chi> J.TT"
          using D.mkCone_def by simp
        show "\<exists>!l. pr1 (cod f) (cod g) \<cdot> l = f \<and> pr0 (cod f) (cod g) \<cdot> l = g"
        proof -
          have "\<exists>!l. \<guillemotleft>l : dom f \<rightarrow> dom (pr1 (cod f) (cod g))\<guillemotright> \<and>
                     pr1 (cod f) (cod g) \<cdot> l = f \<and> pr0 (cod f) (cod g) \<cdot> l = g"
            using fg \<chi>.is_universal' by simp
          moreover have "\<And>l. pr1 (cod f) (cod g) \<cdot> l = f
                                \<Longrightarrow> \<guillemotleft>l : dom f \<rightarrow> dom (pr1 (cod f) (cod g))\<guillemotright>"
            using fg dom_comp in_homI seqE seqI by metis
          ultimately show ?thesis by auto
        qed
      qed
    qed

    proposition extends_to_elementary_category_with_binary_products:
    shows "elementary_category_with_binary_products C pr0 pr1"
      ..

  end

  context elementary_category_with_binary_products
  begin

    interpretation category_with_binary_products C
    proof
      show "has_binary_products"
      proof (unfold has_binary_products_def)
        have "\<And>a b. ide a \<and> ide b \<Longrightarrow> \<exists>p0 p1. has_as_binary_product a b p0 p1"
        proof -
          fix a b
          assume ab: "ide a \<and> ide b"
          interpret J: binary_product_shape .
          interpret D: binary_product_diagram C a b
            using ab by unfold_locales auto
          have 2: "D.is_rendered_commutative_by \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]"
            using ab by simp
          let ?\<chi> = "D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]"
          interpret \<chi>: cone J.comp C D.map \<open>dom \<pp>\<^sub>1[a, b]\<close> ?\<chi>
            using D.cone_mkCone 2 by auto
          interpret \<chi>: limit_cone J.comp C D.map \<open>dom \<pp>\<^sub>1[a, b]\<close> ?\<chi>
          proof
            fix a' \<chi>'
            assume \<chi>': "D.cone a' \<chi>'"
            interpret \<chi>': cone J.comp C D.map a' \<chi>'
              using \<chi>' by simp
            show "\<exists>!h. \<guillemotleft>h : a' \<rightarrow> dom \<pp>\<^sub>1[a, b]\<guillemotright> \<and>
                       D.cones_map h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]) = \<chi>'"
            proof
              let ?h = "\<langle>\<chi>' J.FF, \<chi>' J.TT\<rangle>"
              show h': "\<guillemotleft>?h : a' \<rightarrow> dom \<pp>\<^sub>1[a, b]\<guillemotright> \<and>
                        D.cones_map ?h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]) = \<chi>'"
              proof
                show h: "\<guillemotleft>?h : a' \<rightarrow> dom \<pp>\<^sub>1[a, b]\<guillemotright>"
                  using ab tuple_in_hom J.ide_char by fastforce
                show "D.cones_map ?h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]) = \<chi>'"
                proof -
                  interpret \<chi>'h: cone J.comp C D.map a'
                                   \<open>D.cones_map ?h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b])\<close>
                  proof -
                    have "D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b] \<in> D.cones (cod \<langle>\<chi>' J.FF, \<chi>' J.TT\<rangle>)"
                      using ab h D.cone_mkCone D.is_rendered_commutative_by_cone
                            \<chi>.cone_axioms
                      by auto
                    hence "D.cones_map ?h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]) \<in> D.cones a'"
                      using ab h D.cones_map_mapsto by blast
                    thus "D.cone a' (D.cones_map ?h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]))"
                      by simp
                  qed
                  show ?thesis
                  proof -
                    have "\<And>j. J.ide j \<Longrightarrow> D.cones_map ?h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]) j = \<chi>' j"
                      using ab h J.ide_char D.mkCone_def \<chi>.cone_axioms by auto
                    thus ?thesis
                      using NaturalTransformation.eqI
                            \<chi>'.natural_transformation_axioms \<chi>'h.natural_transformation_axioms
                      by blast
                  qed
                qed
              qed
              show "\<And>h. \<guillemotleft>h : a' \<rightarrow> dom \<pp>\<^sub>1[a, b]\<guillemotright> \<and>
                        D.cones_map h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]) = \<chi>' \<Longrightarrow> h = ?h"
              proof -
                fix h
                assume 1: "\<guillemotleft>h : a' \<rightarrow> dom \<pp>\<^sub>1[a, b]\<guillemotright> \<and>
                           D.cones_map h (D.mkCone \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]) = \<chi>'"
                hence "cod h = dom \<pp>\<^sub>1[a, b]" by auto
                show "h = ?h"
                  using 1 ab \<chi>.cone_axioms D.mkCone_def h' pr_joint_monic [of a b h ?h]
                  by auto
              qed
            qed
          qed
          have "has_as_binary_product a b \<pp>\<^sub>1[a, b] \<pp>\<^sub>0[a, b]"
            using ab has_as_binary_product_def \<chi>.limit_cone_axioms by blast
          thus "\<exists>p0 p1. has_as_binary_product a b p0 p1"
            by blast
        qed
        thus "\<forall>a b. ide a \<and> ide b \<longrightarrow> (\<exists>p0 p1. has_as_binary_product a b p0 p1)"
          by simp
      qed
    qed

    proposition is_category_with_binary_products:
    shows "category_with_binary_products C"
      ..

  end

  subsection "Further Properties"

  context elementary_category_with_binary_products
  begin

    lemma interchange:
    assumes "seq h f" and "seq k g"
    shows "(h \<otimes> k) \<cdot> (f \<otimes> g) = h \<cdot> f \<otimes> k \<cdot> g"
      using assms prod_def comp_tuple_arr comp_assoc by fastforce

    lemma pr_naturality [simp]:
    assumes "arr g" and "dom g = b" and "cod g = d"
        and "arr f" and "dom f = a" and "cod f = c"
    shows "\<pp>\<^sub>0[c, d] \<cdot> (f \<otimes> g) = g \<cdot> \<pp>\<^sub>0[a, b]"
    and "\<pp>\<^sub>1[c, d] \<cdot> (f \<otimes> g) = f \<cdot> \<pp>\<^sub>1[a, b]"
      using assms prod_def by fastforce+

    abbreviation dup ("\<d>[_]")
    where "\<d>[f] \<equiv> \<langle>f, f\<rangle>"

    lemma dup_in_hom [intro, simp]:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "\<guillemotleft>\<d>[f] : a \<rightarrow> b \<otimes> b\<guillemotright>"
      using assms by fastforce

    lemma dup_simps [simp]:
    assumes "arr f"
    shows "arr \<d>[f]" and "dom \<d>[f] = dom f" and "cod \<d>[f] = cod f \<otimes> cod f"
      using assms dup_in_hom by auto

    lemma dup_naturality:
    assumes "\<guillemotleft>f : a \<rightarrow> b\<guillemotright>"
    shows "\<d>[b] \<cdot> f = (f \<otimes> f) \<cdot> \<d>[a]"
      using assms prod_def comp_arr_dom comp_cod_arr comp_tuple_arr comp_assoc
      by fastforce

    lemma pr_dup [simp]:
    assumes "ide a"
    shows "\<pp>\<^sub>0[a, a] \<cdot> \<d>[a] = a" and "\<pp>\<^sub>1[a, a] \<cdot> \<d>[a] = a"
      using assms by simp_all

    lemma prod_tuple:
    assumes "span f g" and "seq h f" and "seq k g"
    shows "(h \<otimes> k) \<cdot> \<langle>f, g\<rangle> = \<langle>h \<cdot> f, k \<cdot> g\<rangle>"
      using assms prod_def comp_assoc comp_tuple_arr by fastforce

    lemma tuple_eqI:
    assumes "seq \<pp>\<^sub>0[b, c] f" and "seq \<pp>\<^sub>1[b, c] f"
    and "\<pp>\<^sub>0[b, c] \<cdot> f = f0" and "\<pp>\<^sub>1[b, c] \<cdot> f = f1"
    shows "f = \<langle>f1, f0\<rangle>"
      using assms pr_joint_monic [of b c "\<langle>f1, f0\<rangle>" f] pr_tuple by auto

    definition assoc ("\<a>[_, _, _]")
    where "\<a>[a, b, c] \<equiv> \<langle>\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>\<rangle>"

    definition assoc' ("\<a>\<^sup>-\<^sup>1[_, _, _]")
    where "\<a>\<^sup>-\<^sup>1[a, b, c] \<equiv> \<langle>\<langle>\<pp>\<^sub>1[a, b \<otimes> c], \<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c]\<rangle>, \<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>0[a, b \<otimes> c]\<rangle>"

    lemma assoc_in_hom [intro]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<guillemotleft>\<a>[a, b, c] : (a \<otimes> b) \<otimes> c \<rightarrow> a \<otimes> (b \<otimes> c)\<guillemotright>"
      using assms assoc_def by auto

    lemma assoc_simps [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "arr \<a>[a, b, c]"
    and "dom \<a>[a, b, c] = (a \<otimes> b) \<otimes> c"
    and "cod \<a>[a, b, c] = a \<otimes> (b \<otimes> c)"
      using assms assoc_in_hom by auto

    lemma assoc'_in_hom [intro]:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<guillemotleft>\<a>\<^sup>-\<^sup>1[a, b, c] : a \<otimes> (b \<otimes> c) \<rightarrow> (a \<otimes> b) \<otimes> c\<guillemotright>"
      using assms assoc'_def by auto

    lemma assoc'_simps [simp]:
    assumes "ide a" and "ide b" and "ide c"
    shows "arr \<a>\<^sup>-\<^sup>1[a, b, c]"
    and "dom \<a>\<^sup>-\<^sup>1[a, b, c] = a \<otimes> (b \<otimes> c)"
    and "cod \<a>\<^sup>-\<^sup>1[a, b, c] = (a \<otimes> b) \<otimes> c"
      using assms assoc'_in_hom by auto

    lemma assoc_naturality:
    assumes "\<guillemotleft>f0 : a0 \<rightarrow> b0\<guillemotright>" and "\<guillemotleft>f1 : a1 \<rightarrow> b1\<guillemotright>" and "\<guillemotleft>f2 : a2 \<rightarrow> b2\<guillemotright>"
    shows "\<a>[b0, b1, b2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2) = (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[a0, a1, a2]"
    proof -
      have "\<pp>\<^sub>0[b0, b1 \<otimes> b2] \<cdot> \<a>[b0, b1, b2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2) =
            \<pp>\<^sub>0[b0, b1 \<otimes> b2] \<cdot> (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[a0, a1, a2]"
      proof -
        have "\<pp>\<^sub>0[b0, b1 \<otimes> b2] \<cdot> \<a>[b0, b1, b2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2) =
              (\<pp>\<^sub>0[b0, b1 \<otimes> b2] \<cdot> \<a>[b0, b1, b2]) \<cdot> ((f0 \<otimes> f1) \<otimes> f2)"
          using comp_assoc by simp
        also have "... = \<langle>\<pp>\<^sub>0[b0, b1] \<cdot> \<pp>\<^sub>1[b0 \<otimes> b1, b2], \<pp>\<^sub>0[b0 \<otimes> b1, b2]\<rangle> \<cdot> ((f0 \<otimes> f1) \<otimes> f2)"
          using assms assoc_def by fastforce
        also have "... = \<langle>(\<pp>\<^sub>0[b0, b1] \<cdot> \<pp>\<^sub>1[b0 \<otimes> b1, b2]) \<cdot> ((f0 \<otimes> f1) \<otimes> f2),
                          \<pp>\<^sub>0[b0 \<otimes> b1, b2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2)\<rangle>"
          using assms comp_tuple_arr by fastforce
        also have "... = \<langle>(\<pp>\<^sub>0[b0, b1] \<cdot> (f0 \<otimes> f1)) \<cdot> \<pp>\<^sub>1[a0 \<otimes> a1, a2], f2 \<cdot> \<pp>\<^sub>0[a0 \<otimes> a1, a2]\<rangle>"
          using assms comp_assoc by fastforce
        also have "... = \<langle>f1 \<cdot> \<pp>\<^sub>0[a0, a1] \<cdot> \<pp>\<^sub>1[a0 \<otimes> a1, a2], f2 \<cdot> \<pp>\<^sub>0[a0 \<otimes> a1, a2]\<rangle>"
          using assms comp_assoc
          by (metis in_homE pr_naturality(1))
        also have "... = \<pp>\<^sub>0[b0, b1 \<otimes> b2] \<cdot> (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[a0, a1, a2]"
          using assms comp_assoc assoc_def prod_tuple by fastforce
        finally show ?thesis by blast
      qed
      moreover have "\<pp>\<^sub>1[b0, b1 \<otimes> b2] \<cdot> \<a>[b0, b1, b2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2) =
                     \<pp>\<^sub>1[b0, b1 \<otimes> b2] \<cdot> (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[a0, a1, a2]"
      proof -
        have "\<pp>\<^sub>1[b0, b1 \<otimes> b2] \<cdot> \<a>[b0, b1, b2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2) =
              (\<pp>\<^sub>1[b0, b1 \<otimes> b2] \<cdot> \<a>[b0, b1, b2]) \<cdot> ((f0 \<otimes> f1) \<otimes> f2)"
          using comp_assoc by simp
        also have "... = (\<pp>\<^sub>1[b0, b1] \<cdot> \<pp>\<^sub>1[b0 \<otimes> b1, b2]) \<cdot> ((f0 \<otimes> f1) \<otimes> f2)"
          using assms assoc_def by fastforce
        also have "... = (\<pp>\<^sub>1[b0, b1] \<cdot> (f0 \<otimes> f1)) \<cdot> \<pp>\<^sub>1[a0 \<otimes> a1, a2]"
          using assms comp_assoc by fastforce
        also have "... = f0 \<cdot> \<pp>\<^sub>1[a0, a1] \<cdot> \<pp>\<^sub>1[a0 \<otimes> a1, a2]"
          using assms comp_assoc
          by (metis in_homE pr_naturality(2))
        also have "... = \<pp>\<^sub>1[b0, b1 \<otimes> b2] \<cdot> (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[a0, a1, a2]"
        proof -
          have "\<pp>\<^sub>1[b0, b1 \<otimes> b2] \<cdot> (f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[a0, a1, a2] =
                (\<pp>\<^sub>1[b0, b1 \<otimes> b2] \<cdot> (f0 \<otimes> (f1 \<otimes> f2))) \<cdot> \<a>[a0, a1, a2]"
            using comp_assoc by simp
          also have "... = f0 \<cdot> \<pp>\<^sub>1[a0, a1 \<otimes> a2] \<cdot> \<a>[a0, a1, a2]"
            using assms comp_assoc by fastforce
          also have "... = f0 \<cdot> \<pp>\<^sub>1[a0, a1] \<cdot> \<pp>\<^sub>1[a0 \<otimes> a1, a2]"
            using assms assoc_def by fastforce
          finally show ?thesis by simp
        qed
        finally show ?thesis by blast
      qed
      ultimately show ?thesis
        using assms pr_joint_monic [of b0 "b1 \<otimes> b2" "\<a>[b0, b1, b2] \<cdot> ((f0 \<otimes> f1) \<otimes> f2)"
                                       "(f0 \<otimes> (f1 \<otimes> f2)) \<cdot> \<a>[a0, a1, a2]"]
        by fastforce
    qed

    lemma pentagon:
    assumes "ide a" and "ide b" and "ide c" and "ide d"
    shows "((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d) = \<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"
    proof (intro pr_joint_monic
                   [where h = "((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d)"
                      and h' = "\<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"])
      show "seq \<pp>\<^sub>0[a, b \<otimes> (c \<otimes> d)] (((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d))"
        using assms by simp
      show "\<pp>\<^sub>1[a, b \<otimes> c \<otimes> d] \<cdot> ((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d) =
            \<pp>\<^sub>1[a, b \<otimes> c \<otimes> d] \<cdot> \<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"
      proof -
        have "\<pp>\<^sub>1[a, b \<otimes> c \<otimes> d] \<cdot> ((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d) =
              ((\<pp>\<^sub>1[a, b \<otimes> c \<otimes> d] \<cdot> (a \<otimes> \<a>[b, c, d])) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d)"
          using comp_assoc by simp
        also have "... = (\<pp>\<^sub>1[a, (b \<otimes> c) \<otimes> d] \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d)"
          using assms pr_naturality(2) comp_cod_arr by force
        also have "... = \<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<pp>\<^sub>1[a \<otimes> b \<otimes> c, d] \<cdot> (\<a>[a, b, c] \<otimes> d)"
          using assms assoc_def comp_assoc by simp
        also have "... = (\<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<a>[a, b, c]) \<cdot> \<pp>\<^sub>1[(a \<otimes> b) \<otimes> c, d]"
          using assms pr_naturality(2) comp_assoc by fastforce
        also have "... = \<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c] \<cdot> \<pp>\<^sub>1[(a \<otimes> b) \<otimes> c, d]"
          using assms assoc_def comp_assoc by simp
        finally have "\<pp>\<^sub>1[a, b \<otimes> c \<otimes> d] \<cdot> ((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d) =
                      \<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c] \<cdot> \<pp>\<^sub>1[(a \<otimes> b) \<otimes> c, d]"
          by blast
        also have "... = \<pp>\<^sub>1[a, b \<otimes> c \<otimes> d] \<cdot> \<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"
          using assms assoc_def comp_assoc by auto
        finally show ?thesis by blast
      qed
      show "\<pp>\<^sub>0[a, b \<otimes> (c \<otimes> d)] \<cdot> ((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d) =
            \<pp>\<^sub>0[a, b \<otimes> (c \<otimes> d)] \<cdot> \<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"
      proof -
        have "\<pp>\<^sub>0[a, b \<otimes> (c \<otimes> d)] \<cdot> ((a \<otimes> \<a>[b, c, d]) \<cdot> \<a>[a, b \<otimes> c, d]) \<cdot> (\<a>[a, b, c] \<otimes> d) =
              \<pp>\<^sub>0[a, b \<otimes> c \<otimes> d] \<cdot>
                ((a \<otimes> \<langle>\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d], \<langle>\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d], \<pp>\<^sub>0[b \<otimes> c, d]\<rangle>\<rangle>) \<cdot>
                 \<langle>\<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<pp>\<^sub>1[a \<otimes> b \<otimes> c, d],
                  \<langle>\<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<pp>\<^sub>1[a \<otimes> b \<otimes> c, d], \<pp>\<^sub>0[a \<otimes> b \<otimes> c, d]\<rangle>\<rangle>) \<cdot>
                (\<langle>\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>\<rangle> \<otimes> d)"
          using assms assoc_def by simp
        also have "... = \<langle>\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d],
                          \<langle>\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d], \<pp>\<^sub>0[b \<otimes> c, d]\<rangle>\<rangle> \<cdot> (\<pp>\<^sub>0[a, (b \<otimes> c) \<otimes> d] \<cdot>
                            \<langle>\<pp>\<^sub>1[a, b \<otimes> c] \<cdot> \<pp>\<^sub>1[a \<otimes> b \<otimes> c, d],
                             \<langle>\<pp>\<^sub>0[a, b \<otimes> c] \<cdot> \<pp>\<^sub>1[a \<otimes> b \<otimes> c, d], \<pp>\<^sub>0[a \<otimes> b \<otimes> c, d]\<rangle>\<rangle>) \<cdot>
                            (\<langle>\<pp>\<^sub>1[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c],
                              \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c], \<pp>\<^sub>0[a \<otimes> b, c]\<rangle>\<rangle> \<otimes> d)"
        proof -
          have "\<pp>\<^sub>0[a, b \<otimes> c \<otimes> d] \<cdot>
                  (a \<otimes> \<langle>\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d], \<langle>\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d], \<pp>\<^sub>0[b \<otimes> c, d]\<rangle>\<rangle>) =
                \<langle>\<pp>\<^sub>1[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d], \<langle>\<pp>\<^sub>0[b, c] \<cdot> \<pp>\<^sub>1[b \<otimes> c, d], \<pp>\<^sub>0[b \<otimes> c, d]\<rangle>\<rangle> \<cdot>
                  \<pp>\<^sub>0[a, (b \<otimes> c) \<otimes> d]"
            using assms assoc_def ide_in_hom pr_naturality(1) by auto
          thus ?thesis using comp_assoc by metis
        qed
        also have "... = \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c] \<cdot> \<pp>\<^sub>1[(a \<otimes> b) \<otimes> c, d],
                          \<langle>\<pp>\<^sub>0[a \<otimes> b, c] \<cdot> \<pp>\<^sub>1[(a \<otimes> b) \<otimes> c, d], d \<cdot> \<pp>\<^sub>0[(a \<otimes> b) \<otimes> c, d]\<rangle>\<rangle>"
          using assms comp_assoc by simp
        also have "... = \<langle>\<pp>\<^sub>0[a, b] \<cdot> \<pp>\<^sub>1[a \<otimes> b, c] \<cdot> \<pp>\<^sub>1[(a \<otimes> b) \<otimes> c, d],
                          \<langle>\<pp>\<^sub>0[a \<otimes> b, c] \<cdot> \<pp>\<^sub>1[(a \<otimes> b) \<otimes> c, d], \<pp>\<^sub>0[(a \<otimes> b) \<otimes> c, d]\<rangle>\<rangle>"
          using assms comp_cod_arr by simp
        also have "... = \<pp>\<^sub>0[a, b \<otimes> (c \<otimes> d)] \<cdot> \<a>[a, b, c \<otimes> d] \<cdot> \<a>[a \<otimes> b, c, d]"
          using assms assoc_def comp_assoc by simp
        finally show ?thesis by simp
      qed
    qed

    lemma inverse_arrows_assoc:
    assumes "ide a" and "ide b" and "ide c"
    shows "inverse_arrows \<a>[a, b, c] \<a>\<^sup>-\<^sup>1[a, b, c]"
      using assms assoc_def assoc'_def comp_assoc
      by (auto simp add: tuple_pr_arr)

    interpretation CC: product_category C C ..

    abbreviation Prod
    where "Prod fg \<equiv> fst fg \<otimes> snd fg"
    abbreviation Prod'
    where "Prod' fg \<equiv> snd fg \<otimes> fst fg"

    interpretation \<Pi>: binary_functor C C C Prod
      using tuple_ext CC.comp_char interchange
      apply unfold_locales
          apply auto
      by (metis prod_def seqE)+

    interpretation Prod': binary_functor C C C Prod'
      using tuple_ext CC.comp_char interchange
      apply unfold_locales
          apply auto
      by (metis prod_def seqE)+

    lemma binary_functor_Prod:
    shows "binary_functor C C C Prod" and "binary_functor C C C Prod'"
      ..

    definition sym ("\<s>[_, _]")
    where "\<s>[a1, a0] \<equiv> if ide a0 \<and> ide a1 then \<langle>\<pp>\<^sub>0[a1, a0], \<pp>\<^sub>1[a1, a0]\<rangle> else null"

    lemma sym_in_hom [intro]:
    assumes "ide a" and "ide b"
    shows "\<guillemotleft>\<s>[a, b] : a \<otimes> b \<rightarrow> b \<otimes> a\<guillemotright>"
      using assms sym_def by auto

    lemma sym_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr \<s>[a, b]" and "dom \<s>[a, b] = a \<otimes> b" and "cod \<s>[a, b] = b \<otimes> a"
      using assms sym_in_hom by auto

    lemma comp_sym_tuple [simp]:
    assumes "\<guillemotleft>f0 : a \<rightarrow> b0\<guillemotright>" and "\<guillemotleft>f1 : a \<rightarrow> b1\<guillemotright>"
    shows "\<s>[b0, b1] \<cdot> \<langle>f0, f1\<rangle> = \<langle>f1, f0\<rangle>"
      using assms sym_def comp_tuple_arr by fastforce

    lemma prj_sym [simp]:
    assumes "ide a0" and "ide a1"
    shows "\<pp>\<^sub>0[a1, a0] \<cdot> \<s>[a0, a1] = \<pp>\<^sub>1[a0, a1]"
    and "\<pp>\<^sub>1[a1, a0] \<cdot> \<s>[a0, a1] = \<pp>\<^sub>0[a0, a1]"
      using assms sym_def by auto

    lemma comp_sym_sym [simp]:
    assumes "ide a0" and "ide a1"
    shows "\<s>[a1, a0] \<cdot> \<s>[a0, a1] = (a0 \<otimes> a1)"
      using assms sym_def comp_tuple_arr by auto

    lemma sym_inverse_arrows:
    assumes "ide a0" and "ide a1"
    shows "inverse_arrows \<s>[a0, a1] \<s>[a1, a0]"
      using assms sym_in_hom comp_sym_sym by auto

    lemma sym_assoc_coherence:
    assumes "ide a" and "ide b" and "ide c"
    shows "\<a>[b, c, a] \<cdot> \<s>[a, b \<otimes> c] \<cdot> \<a>[a, b, c] = (b \<otimes> \<s>[a, c]) \<cdot> \<a>[b, a, c] \<cdot> (\<s>[a, b] \<otimes> c)"
      using assms sym_def assoc_def comp_assoc prod_tuple comp_cod_arr by simp

    lemma sym_naturality:
    assumes "\<guillemotleft>f0 : a0 \<rightarrow> b0\<guillemotright>" and "\<guillemotleft>f1 : a1 \<rightarrow> b1\<guillemotright>"
    shows "\<s>[b0, b1] \<cdot> (f0 \<otimes> f1) = (f1 \<otimes> f0) \<cdot> \<s>[a0, a1]"
      using assms sym_def comp_assoc prod_tuple by fastforce

    abbreviation \<sigma>
    where "\<sigma> fg \<equiv> \<s>[cod (fst fg), cod (snd fg)] \<cdot> (fst fg \<otimes> snd fg)"

    interpretation \<sigma>: natural_transformation CC.comp C Prod Prod' \<sigma>
      using sym_def CC.arr_char CC.null_char comp_arr_dom comp_cod_arr
      apply unfold_locales
          apply auto
      using arr_cod_iff_arr ideD(1)
        apply metis
      using arr_cod_iff_arr ideD(1)
       apply metis
      using prod_tuple by simp

    lemma \<sigma>_is_natural_transformation:
    shows "natural_transformation CC.comp C Prod Prod' \<sigma>"
      ..

    abbreviation Diag
    where "Diag f \<equiv> if arr f then (f, f) else CC.null"

    interpretation \<Delta>: "functor" C CC.comp Diag
      by (unfold_locales, auto)

    lemma functor_Diag:
    shows "functor C CC.comp Diag"
      ..

    interpretation \<Delta>o\<Pi>: composite_functor CC.comp C CC.comp Prod Diag ..
    interpretation \<Pi>o\<Delta>: composite_functor C CC.comp C Diag Prod ..

    abbreviation \<pi>
    where "\<pi> \<equiv> \<lambda>(f, g). (\<pp>\<^sub>1[cod f, cod g] \<cdot> (f \<otimes> g), \<pp>\<^sub>0[cod f, cod g] \<cdot> (f \<otimes> g))"

    interpretation \<pi>: transformation_by_components CC.comp CC.comp \<Delta>o\<Pi>.map CC.map \<pi>
      using pr_naturality comp_arr_dom comp_cod_arr
      by unfold_locales auto

    lemma \<pi>_is_natural_transformation:
    shows "natural_transformation CC.comp CC.comp \<Delta>o\<Pi>.map CC.map \<pi>"
    proof -
      have "\<pi>.map = \<pi>"
        using \<pi>.map_def ext \<Pi>.is_extensional comp_arr_dom comp_cod_arr by auto
      thus "natural_transformation CC.comp CC.comp \<Delta>o\<Pi>.map CC.map \<pi>"
        using \<pi>.natural_transformation_axioms by simp
    qed

    interpretation \<delta>: natural_transformation C C map \<Pi>o\<Delta>.map dup
      using dup_naturality comp_arr_dom comp_cod_arr prod_tuple tuple_ext
      by unfold_locales auto

    lemma dup_is_natural_transformation:
    shows "natural_transformation C C map \<Pi>o\<Delta>.map dup"
      ..

    interpretation \<Delta>o\<Pi>o\<Delta>: composite_functor C CC.comp CC.comp Diag \<Delta>o\<Pi>.map ..
    interpretation \<Pi>o\<Delta>o\<Pi>: composite_functor CC.comp C C Prod \<Pi>o\<Delta>.map ..

    interpretation \<Delta>o\<delta>: natural_transformation C CC.comp Diag \<Delta>o\<Pi>o\<Delta>.map \<open>Diag \<circ> dup\<close>
    proof -
      have "Diag \<circ> map = Diag"
        by auto
      thus "natural_transformation C CC.comp Diag \<Delta>o\<Pi>o\<Delta>.map (Diag \<circ> dup)"
        using \<Delta>.natural_transformation_axioms \<delta>.natural_transformation_axioms o_assoc
              horizontal_composite [of C C map \<Pi>o\<Delta>.map dup CC.comp Diag Diag Diag]
        by metis
    qed

    interpretation \<delta>o\<Pi>: natural_transformation CC.comp C Prod \<Pi>o\<Delta>o\<Pi>.map \<open>dup \<circ> Prod\<close>
      using \<delta>.natural_transformation_axioms \<Pi>.natural_transformation_axioms o_assoc
            horizontal_composite [of CC.comp C Prod Prod Prod C map \<Pi>o\<Delta>.map dup]
      by simp

    interpretation \<pi>o\<Delta>: natural_transformation C CC.comp \<Delta>o\<Pi>o\<Delta>.map Diag \<open>\<pi>.map \<circ> Diag\<close>
      using \<pi>.natural_transformation_axioms \<Delta>.natural_transformation_axioms
            horizontal_composite
              [of C CC.comp Diag Diag Diag CC.comp \<Delta>o\<Pi>.map CC.map \<pi>.map]
      by simp

    interpretation \<Pi>o\<pi>: natural_transformation CC.comp C \<Pi>o\<Delta>o\<Pi>.map Prod \<open>Prod \<circ> \<pi>.map\<close>
    proof -
      have "Prod \<circ> \<Delta>o\<Pi>.map = \<Pi>o\<Delta>o\<Pi>.map"
        by auto
      thus "natural_transformation CC.comp C \<Pi>o\<Delta>o\<Pi>.map Prod (Prod \<circ> \<pi>.map)"
        using \<pi>.natural_transformation_axioms \<Pi>.natural_transformation_axioms o_assoc
              horizontal_composite
                [of CC.comp CC.comp \<Delta>o\<Pi>.map CC.map \<pi>.map C Prod Prod Prod]
        by simp
    qed

    interpretation \<Delta>o\<delta>_\<pi>o\<Delta>: vertical_composite C CC.comp Diag \<Delta>o\<Pi>o\<Delta>.map Diag
                               \<open>Diag \<circ> dup\<close> \<open>\<pi>.map \<circ> Diag\<close>
      ..
    interpretation \<Pi>o\<pi>_\<delta>o\<Pi>: vertical_composite CC.comp C Prod \<Pi>o\<Delta>o\<Pi>.map Prod
                               \<open>dup \<circ> Prod\<close> \<open>Prod \<circ> \<pi>.map\<close>
      ..

    interpretation \<Delta>\<Pi>: unit_counit_adjunction CC.comp C Diag Prod dup \<pi>.map
    proof
      show "\<Delta>o\<delta>_\<pi>o\<Delta>.map = Diag"
      proof
        fix f
        have "\<not> arr f \<Longrightarrow> \<Delta>o\<delta>_\<pi>o\<Delta>.map f = Diag f"
          by (simp add: \<Delta>o\<delta>_\<pi>o\<Delta>.is_extensional)
        moreover have "arr f \<Longrightarrow> \<Delta>o\<delta>_\<pi>o\<Delta>.map f = Diag f"
          using comp_cod_arr comp_assoc \<Delta>o\<delta>_\<pi>o\<Delta>.map_def by auto
        ultimately show "\<Delta>o\<delta>_\<pi>o\<Delta>.map f = Diag f" by blast
      qed
      show "\<Pi>o\<pi>_\<delta>o\<Pi>.map = Prod"
      proof
        fix fg
        show "\<Pi>o\<pi>_\<delta>o\<Pi>.map fg = Prod fg"
        proof -
          have "\<not> CC.arr fg \<Longrightarrow> ?thesis"
            by (simp add: \<Pi>.is_extensional \<Pi>o\<pi>_\<delta>o\<Pi>.is_extensional)
          moreover have "CC.arr fg \<Longrightarrow> ?thesis"
          proof -
            assume fg: "CC.arr fg"
            have 1: "dup (Prod fg) = \<langle>cod (fst fg) \<otimes> cod (snd fg), cod (fst fg) \<otimes> cod (snd fg)\<rangle> \<cdot>
                                        (fst fg \<otimes> snd fg)"
              using fg \<delta>.is_natural_2
              apply simp
              by (metis (no_types, lifting) prod_simps(1) prod_simps(3))
            have "\<Pi>o\<pi>_\<delta>o\<Pi>.map fg =
                  (\<pp>\<^sub>1[cod (fst fg), cod (snd fg)] \<otimes> \<pp>\<^sub>0[cod (fst fg), cod (snd fg)]) \<cdot>
                    \<langle>cod (fst fg) \<otimes> cod (snd fg), cod (fst fg) \<otimes> cod (snd fg)\<rangle> \<cdot>
                    (fst fg \<otimes> snd fg)"
              using fg 1 \<Pi>o\<pi>_\<delta>o\<Pi>.map_def comp_cod_arr by simp
            also have "... = ((\<pp>\<^sub>1[cod (fst fg), cod (snd fg)] \<otimes> \<pp>\<^sub>0[cod (fst fg), cod (snd fg)]) \<cdot>
                              \<langle>cod (fst fg) \<otimes> cod (snd fg), cod (fst fg) \<otimes> cod (snd fg)\<rangle>) \<cdot>
                             (fst fg \<otimes> snd fg)"
              using comp_assoc by simp
            also have "... = \<langle>\<pp>\<^sub>1[cod (fst fg), cod (snd fg)] \<cdot> (cod (fst fg) \<otimes> cod (snd fg)),
                              \<pp>\<^sub>0[cod (fst fg), cod (snd fg)] \<cdot> (cod (fst fg) \<otimes> cod (snd fg))\<rangle> \<cdot>
                             (fst fg \<otimes> snd fg)"
              using fg prod_tuple by simp
            also have "... = Prod fg"
              using fg comp_arr_dom \<Pi>.is_natural_2 by auto
            finally show ?thesis by simp
          qed
          ultimately show ?thesis by blast
        qed
      qed
    qed

    proposition induces_unit_counit_adjunction:
    shows "unit_counit_adjunction CC.comp C Diag Prod dup \<pi>.map"
      using \<Delta>\<Pi>.unit_counit_adjunction_axioms by simp

  end

  section "Category with Terminal Object"

  locale category_with_terminal_object =
    category +
  assumes has_terminal: "\<exists>t. terminal t"

  locale elementary_category_with_terminal_object =
    category C
  for C :: "'a comp"                              (infixr "\<cdot>" 55)
  and one :: "'a"                                 ("\<one>")
  and trm :: "'a \<Rightarrow> 'a"                           ("\<t>[_]") +
  assumes ide_one: "ide \<one>"
  and trm_in_hom: "ide a \<Longrightarrow> \<guillemotleft>\<t>[a] : a \<rightarrow> \<one>\<guillemotright>"
  and trm_eqI: "\<lbrakk> ide a; \<guillemotleft>f : a \<rightarrow> \<one>\<guillemotright> \<rbrakk> \<Longrightarrow> f = \<t>[a]"
  begin

    lemma trm_simps:
    assumes "ide a"
    shows "arr \<t>[a]" and "dom \<t>[a] = a" and "cod \<t>[a] = \<one>"
      using assms trm_in_hom by auto

    lemma trm_one:
    shows "\<t>[\<one>] = \<one>"
    using ide_one trm_in_hom trm_eqI ide_in_hom by auto

    lemma terminal_one:
    shows "terminal \<one>"
      using ide_one trm_in_hom trm_eqI terminal_def by metis

    lemma trm_naturality:
    assumes "arr f"
    shows "\<t>[cod f] \<cdot> f = \<t>[dom f]"
      using assms trm_eqI
      by (metis comp_in_homI' ide_cod ide_dom in_homE trm_in_hom)

    proposition is_category_with_terminal_object:
    shows "category_with_terminal_object C"
      apply unfold_locales
      using terminal_one by auto

  end

  context category_with_terminal_object
  begin

    definition some_terminal ("\<one>")
    where "some_terminal \<equiv> SOME t. terminal t"

    definition "trm" ("\<t>[_]")
    where "\<t>[f] \<equiv> if arr f then THE t. \<guillemotleft>t : dom f \<rightarrow> \<one>\<guillemotright> else null"

    lemma terminal_some_terminal [intro]:
    shows "terminal \<one>"
      using some_terminal_def has_terminal someI_ex [of "\<lambda>t. terminal t"] by presburger

    lemma ide_some_terminal:
    shows "ide \<one>"
      using terminal_def by blast

    lemma trm_in_hom [intro]:
    assumes "arr f"
    shows "\<guillemotleft>\<t>[f] : dom f \<rightarrow> \<one>\<guillemotright>"
    proof -
      have "ide (dom f)" using assms by fastforce
      hence "\<exists>!t. \<guillemotleft>t : dom f \<rightarrow> \<one>\<guillemotright>"
        using assms trm_def terminal_def terminal_some_terminal by simp
      thus ?thesis
        using assms trm_def [of f] theI' [of "\<lambda>t. \<guillemotleft>t : dom f \<rightarrow> \<one>\<guillemotright>"] by auto
    qed

    lemma trm_simps [simp]:
    assumes "arr f"
    shows "arr \<t>[f]" and "dom \<t>[f] = dom f" and "cod \<t>[f] = \<one>"
      using assms trm_in_hom by auto

    lemma trm_eqI:
    assumes "\<guillemotleft>t : dom f \<rightarrow> \<one>\<guillemotright>"
    shows "t = \<t>[f]"
    proof -
      have "ide (dom f)" using assms
        by (metis ide_dom in_homE)
      hence "\<exists>!t. \<guillemotleft>t : dom f \<rightarrow> \<one>\<guillemotright>"
        using terminal_def [of \<one>] terminal_some_terminal by auto
      moreover have "\<guillemotleft>t : dom f \<rightarrow> \<one>\<guillemotright>"
        using assms by simp
      ultimately show ?thesis
        using assms trm_def the1_equality [of "\<lambda>t. \<guillemotleft>t : dom f \<rightarrow> \<one>\<guillemotright>" t]
              \<open>ide (dom f)\<close> arr_dom_iff_arr
        by fastforce
    qed

    sublocale elementary_category_with_terminal_object C \<one> trm
      using ide_some_terminal trm_eqI
      by unfold_locales auto

    proposition extends_to_elementary_category_with_terminal_object:
      shows "elementary_category_with_terminal_object C \<one> trm"
      ..

  end

  section "Cartesian Category"

  locale cartesian_category =
    category_with_binary_products +
    category_with_terminal_object

  locale elementary_cartesian_category =
    elementary_category_with_binary_products +
    elementary_category_with_terminal_object
  begin

    proposition is_cartesian_category:
    shows "cartesian_category C"
      using cartesian_category.intro is_category_with_binary_products
            is_category_with_terminal_object
      by auto

  end

  context cartesian_category
  begin

    proposition extends_to_elementary_cartesian_category:
    shows "elementary_cartesian_category C pr0 pr1 \<one> trm"
      by (simp add: elementary_cartesian_category_def
          elementary_category_with_terminal_object_axioms
          extends_to_elementary_category_with_binary_products)

    sublocale elementary_cartesian_category C pr0 pr1 \<one> trm
      using extends_to_elementary_cartesian_category by simp

  end

  text \<open>
    Here we prove some facts that will later allow us to show that an elementary cartesian
    category is a monoidal category.
  \<close>

  context elementary_cartesian_category
  begin

    abbreviation \<iota>
    where "\<iota> \<equiv> \<pp>\<^sub>0[\<one>, \<one>]"

    lemma pr_coincidence:
    shows "\<iota> = \<pp>\<^sub>1[\<one>, \<one>]"
      using ide_one
      by (simp add: terminal_arr_unique terminal_one)

    lemma \<iota>_is_terminal_arr:
    shows "terminal_arr \<iota>"
      using ide_one
      by (simp add: terminal_one)

    lemma inverse_arrows_\<iota>:
    shows "inverse_arrows \<iota> \<langle>\<one>, \<one>\<rangle>"
      using ide_one
      by (metis (no_types, lifting) dup_is_natural_transformation \<iota>_is_terminal_arr cod_pr0
          comp_cod_arr pr_dup(1) ide_dom inverse_arrows_def map_simp
          natural_transformation.is_natural_2 pr_simps(2) pr1_in_hom' trm_eqI trm_naturality
          trm_one tuple_pr)

    lemma \<iota>_is_iso:
    shows "iso \<iota>"
      using inverse_arrows_\<iota> by auto

    lemma trm_tensor:
    assumes "ide a" and "ide b"
    shows "\<t>[a \<otimes> b] = \<iota> \<cdot> (\<t>[a] \<otimes> \<t>[b])"
    proof -
      have "\<t>[a \<otimes> b] = \<t>[a] \<cdot> \<pp>\<^sub>1[a, b]"
        by (metis assms(1-2) cod_pr1 pr_simps(4-6) trm_naturality)
      moreover have "\<guillemotleft>\<t>[b] : b \<rightarrow> \<one>\<guillemotright>"
        using assms(2) trm_in_hom by blast
      ultimately show ?thesis
        using assms(1) pr_coincidence trm_in_hom by fastforce
    qed

    abbreviation runit ("\<r>[_]")
    where "\<r>[a] \<equiv> \<pp>\<^sub>1[a, \<one>]"

    abbreviation runit' ("\<r>\<^sup>-\<^sup>1[_]")
    where "\<r>\<^sup>-\<^sup>1[a] \<equiv> \<langle>a, \<t>[a]\<rangle>"

    abbreviation lunit ("\<l>[_]")
    where "\<l>[a] \<equiv> \<pp>\<^sub>0[\<one>, a]"

    abbreviation lunit' ("\<l>\<^sup>-\<^sup>1[_]")
    where "\<l>\<^sup>-\<^sup>1[a] \<equiv> \<langle>\<t>[a], a\<rangle>"

    lemma runit_in_hom:
    assumes "ide a"
    shows "\<guillemotleft>\<r>[a] : a \<otimes> \<one> \<rightarrow> a\<guillemotright>"
     using assms ide_one by simp

    lemma runit'_in_hom:
    assumes "ide a"
    shows "\<guillemotleft>\<r>\<^sup>-\<^sup>1[a] : a \<rightarrow> a \<otimes> \<one>\<guillemotright>"
      using assms ide_in_hom trm_in_hom by blast

    lemma lunit_in_hom:
    assumes "ide a"
    shows "\<guillemotleft>\<l>[a] : \<one> \<otimes> a \<rightarrow> a\<guillemotright>"
     using assms ide_one by simp

    lemma lunit'_in_hom:
    assumes "ide a"
    shows "\<guillemotleft>\<l>\<^sup>-\<^sup>1[a] : a \<rightarrow> \<one> \<otimes> a\<guillemotright>"
      using assms ide_in_hom trm_in_hom by blast

    lemma runit_naturality:
    assumes "ide a"
    shows "\<r>[cod a] \<cdot> (a \<otimes> \<one>) = a \<cdot> \<r>[dom a]"
      using assms pr_naturality(2) ide_char ide_one by blast

    lemma inverse_arrows_runit:
    assumes "ide a"
    shows "inverse_arrows \<r>[a] \<r>\<^sup>-\<^sup>1[a]"
    proof
      show "ide (\<r>[a] \<cdot> \<r>\<^sup>-\<^sup>1[a])"
      proof -
        have "\<r>[a] \<cdot> \<r>\<^sup>-\<^sup>1[a] = a"
          using assms
          by (metis in_homE ide_char pr_tuple(1) trm_in_hom)
        thus ?thesis
          using assms by presburger
      qed
      show "ide (\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a])"
      proof -
        have "ide (a \<otimes> \<one>)"
          using assms ide_one by blast
        moreover have "\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = a \<otimes> \<one>"
        proof (intro pr_joint_monic [of a \<one> "\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a]" "a \<otimes> \<one>"])
          show "seq \<pp>\<^sub>0[a, \<one>] (\<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a])"
            using assms ide_one runit'_in_hom [of a]
            by (intro seqI) auto
          show "\<pp>\<^sub>0[a, \<one>] \<cdot> \<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = \<pp>\<^sub>0[a, \<one>] \<cdot> (a \<otimes> \<one>)"
          proof -
            have "\<pp>\<^sub>0[a, \<one>] \<cdot> \<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = (\<pp>\<^sub>0[a, \<one>] \<cdot> \<r>\<^sup>-\<^sup>1[a]) \<cdot> \<r>[a]"
              using comp_assoc by simp
            also have "... = \<t>[a] \<cdot> \<r>[a]"
              using assms ide_one
              by (metis in_homE pr_tuple(2) ide_char trm_in_hom)
            also have "... = \<t>[a \<otimes> \<one>]"
              using assms ide_one trm_naturality [of "\<r>[a]"] by simp
            also have "... = \<pp>\<^sub>0[a, \<one>] \<cdot> (a \<otimes> \<one>)"
              using assms comp_arr_dom ide_one trm_naturality trm_one by fastforce
            finally show ?thesis by blast
          qed
          show "\<pp>\<^sub>1[a, \<one>] \<cdot> \<r>\<^sup>-\<^sup>1[a] \<cdot> \<r>[a] = \<pp>\<^sub>1[a, \<one>] \<cdot> (a \<otimes> \<one>)"
            using assms
            by (metis \<open>ide (\<r>[a] \<cdot> \<r>\<^sup>-\<^sup>1[a])\<close> cod_comp cod_pr1 dom_comp ide_compE ide_one
                comp_assoc runit_naturality)
        qed
        ultimately show ?thesis by simp
      qed
    qed

    lemma lunit_naturality:
    assumes "arr f"
    shows "C \<l>[cod f] (\<one> \<otimes> f) = C f \<l>[dom f]"
      using assms pr_naturality(1) ide_char ide_one by blast

    lemma inverse_arrows_lunit:
    assumes "ide a"
    shows "inverse_arrows \<l>[a] \<l>\<^sup>-\<^sup>1[a]"
    proof
      show "ide (C \<l>[a] \<l>\<^sup>-\<^sup>1[a])"
      proof -
        have "C \<l>[a] \<l>\<^sup>-\<^sup>1[a] = a"
          using assms
          by (metis ide_char in_homE pr_tuple(2) trm_in_hom)
        thus ?thesis
          using assms by simp
      qed
      show "ide (\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a])"
      proof -
        have "\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = \<one> \<otimes> a"
        proof (intro pr_joint_monic [of \<one> a "\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a]" "\<one> \<otimes> a"])
          show "seq \<l>[a] (\<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a])"
            using assms \<open>ide (\<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a])\<close> by blast
          show "\<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = \<l>[a] \<cdot> (\<one> \<otimes> a)"
            using assms
            by (metis \<open>ide (\<l>[a] \<cdot> \<l>\<^sup>-\<^sup>1[a])\<close> cod_comp cod_pr0 dom_cod ide_compE ide_one
                comp_assoc lunit_naturality)
          show "\<pp>\<^sub>1[\<one>, a] \<cdot> \<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = \<pp>\<^sub>1[\<one>, a] \<cdot> (\<one> \<otimes> a)"
          proof -
            have "\<pp>\<^sub>1[\<one>, a] \<cdot> \<l>\<^sup>-\<^sup>1[a] \<cdot> \<l>[a] = (\<pp>\<^sub>1[\<one>, a] \<cdot> \<l>\<^sup>-\<^sup>1[a]) \<cdot> \<l>[a]"
              using comp_assoc by simp
            also have "... = \<t>[a] \<cdot> \<l>[a]"
              using assms ide_one
              by (metis pr_tuple(1) ide_char in_homE trm_in_hom)
            also have "... = \<t>[\<one> \<otimes> a]"
              using assms ide_one trm_naturality [of "\<l>[a]"] by simp
            also have "... = \<pp>\<^sub>1[\<one>, a] \<cdot> (\<one> \<otimes> a)"
              using assms comp_arr_dom ide_one trm_naturality trm_one by fastforce
            finally show ?thesis by simp
          qed
        qed
        moreover have "ide (\<one> \<otimes> a)"
          using assms ide_one by simp
        finally show ?thesis by blast
      qed
    qed

    lemma comp_lunit_term_dup:
    assumes "ide a"
    shows "\<l>[a] \<cdot> (\<t>[a] \<otimes> a) \<cdot> \<d>[a] = a"
    proof -
      have "\<guillemotleft>\<t>[a] : a \<rightarrow> \<one>\<guillemotright>"
        using assms trm_in_hom by blast
      hence "\<l>[a] \<cdot> (\<t>[a] \<otimes> a) = a \<cdot> \<pp>\<^sub>0[a, a]"
        by (metis assms pr_naturality(1) ide_char in_homE)
      thus ?thesis
        by (metis (no_types) assms comp_assoc comp_ide_self pr_dup(1))
    qed

    lemma comp_runit_term_dup:
    assumes "ide a"
    shows "\<r>[a] \<cdot> (a \<otimes> \<t>[a]) \<cdot> \<d>[a] = a"
    proof -
      have "\<guillemotleft>\<t>[a] : a \<rightarrow> \<one>\<guillemotright>"
        using assms trm_in_hom by blast
      hence "\<r>[a] \<cdot> (a \<otimes> \<t>[a]) = a \<cdot> \<pp>\<^sub>1[a, a]"
        using assms by auto
      thus ?thesis
        using assms
        by (metis comp_ide_arr pr_dup(2) ide_char comp_assoc seqI)
    qed

    lemma comp_proj_assoc:
    assumes "ide a0" and "ide a1" and "ide a2"
    shows "\<pp>\<^sub>1[a0, a1 \<otimes> a2] \<cdot> \<a>[a0, a1, a2] = \<pp>\<^sub>1[a0, a1] \<cdot> \<pp>\<^sub>1[a0 \<otimes> a1, a2]"
    and "\<pp>\<^sub>0[a0, a1 \<otimes> a2] \<cdot> \<a>[a0, a1, a2] = \<langle>\<pp>\<^sub>0[a0, a1] \<cdot> \<pp>\<^sub>1[a0 \<otimes> a1, a2], \<pp>\<^sub>0[a0 \<otimes> a1, a2]\<rangle>"
      using assms assoc_def by auto

    lemma dup_coassoc:
    assumes "ide a"
    shows "\<a>[a, a, a] \<cdot> (\<d>[a] \<otimes> a) \<cdot> \<d>[a] = (a \<otimes> \<d>[a]) \<cdot> \<d>[a]"
    proof (intro pr_joint_monic
                   [of a "a \<otimes> a" "\<a>[a, a, a] \<cdot> (\<d>[a] \<otimes> a) \<cdot> \<d>[a]" "(a \<otimes> \<d>[a]) \<cdot> \<d>[a]"])
      show "seq \<pp>\<^sub>0[a, a \<otimes> a] (\<a>[a, a, a] \<cdot> (\<d>[a] \<otimes> a) \<cdot> \<d>[a])"
        using assms by simp
      show "\<pp>\<^sub>0[a, a \<otimes> a] \<cdot> \<a>[a, a, a] \<cdot> (\<d>[a] \<otimes> a) \<cdot> \<d>[a] = \<pp>\<^sub>0[a, a \<otimes> a] \<cdot> (a \<otimes> \<d>[a]) \<cdot> \<d>[a]"
      proof -
        have "\<pp>\<^sub>0[a, a \<otimes> a] \<cdot> \<a>[a, a, a] \<cdot> (\<d>[a] \<otimes> a) \<cdot> \<d>[a] =
              ((\<pp>\<^sub>0[a, a \<otimes> a] \<cdot> \<a>[a, a, a]) \<cdot> (\<d>[a] \<otimes> a)) \<cdot> \<d>[a]"
          using comp_assoc by simp
        also have "... = \<langle>((\<pp>\<^sub>0[a, a] \<cdot> \<pp>\<^sub>1[a \<otimes> a, a]) \<cdot> (\<d>[a] \<otimes> a)) \<cdot> \<d>[a], (a \<cdot> \<pp>\<^sub>0[a, a]) \<cdot> \<d>[a]\<rangle>"
          using assms assoc_def by simp
        also have "... = \<d>[a]"
          using assms comp_assoc by simp
        also have "... = (\<pp>\<^sub>0[a, a \<otimes> a] \<cdot> (a \<otimes> \<d>[a])) \<cdot> \<d>[a]"
          using assms assoc_def comp_assoc by simp
        also have "... = \<pp>\<^sub>0[a, a \<otimes> a] \<cdot> (a \<otimes> \<d>[a]) \<cdot> \<d>[a]"
          using comp_assoc by simp
        finally show ?thesis by blast
      qed
      show "\<pp>\<^sub>1[a, a \<otimes> a] \<cdot> \<a>[a, a, a] \<cdot> (\<d>[a] \<otimes> a) \<cdot> \<d>[a] = \<pp>\<^sub>1[a, a \<otimes> a] \<cdot> (a \<otimes> \<d>[a]) \<cdot> \<d>[a]"
      proof -
        have "\<pp>\<^sub>1[a, a \<otimes> a] \<cdot> \<a>[a, a, a] \<cdot> (\<d>[a] \<otimes> a) \<cdot> \<d>[a] =
              ((\<pp>\<^sub>1[a, a \<otimes> a] \<cdot> \<a>[a, a, a]) \<cdot> (\<d>[a] \<otimes> a)) \<cdot> \<d>[a]"
          using comp_assoc by simp
        also have "... = ((\<pp>\<^sub>1[a, a] \<cdot> \<pp>\<^sub>1[a \<otimes> a, a]) \<cdot> (\<d>[a] \<otimes> a)) \<cdot> \<d>[a]"
          using assms assoc_def by simp
        also have "... = a"
          using assms comp_assoc by simp
        also have "... = (a \<cdot> \<pp>\<^sub>1[a, a]) \<cdot> \<d>[a]"
          using assms comp_assoc by simp
        also have "... = (\<pp>\<^sub>1[a, a \<otimes> a] \<cdot> (a \<otimes> \<d>[a])) \<cdot> \<d>[a]"
          using assms by simp
        also have "... = \<pp>\<^sub>1[a, a \<otimes> a] \<cdot> (a \<otimes> \<d>[a]) \<cdot> \<d>[a]"
          using comp_assoc by simp
        finally show ?thesis by blast
      qed
    qed

    lemma comp_assoc_tuple:
    assumes "\<guillemotleft>f0 : a \<rightarrow> b0\<guillemotright>" and "\<guillemotleft>f1 : a \<rightarrow> b1\<guillemotright>" and "\<guillemotleft>f2 : a \<rightarrow> b2\<guillemotright>"
    shows "\<a>[b0, b1, b2] \<cdot> \<langle>\<langle>f0, f1\<rangle>, f2\<rangle> = \<langle>f0, \<langle>f1, f2\<rangle>\<rangle>"
    and "\<a>\<^sup>-\<^sup>1[b0, b1, b2] \<cdot> \<langle>f0, \<langle>f1, f2\<rangle>\<rangle> = \<langle>\<langle>f0, f1\<rangle>, f2\<rangle>"
      using assms assoc_def assoc'_def comp_assoc by fastforce+

    lemma dup_tensor:
    assumes "ide a" and "ide b"
    shows "\<d>[a \<otimes> b] = \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> (a \<otimes> \<a>[b, a, b]) \<cdot> (a \<otimes> \<sigma> (a, b) \<otimes> b) \<cdot>
                        (a \<otimes> \<a>\<^sup>-\<^sup>1[a, b, b]) \<cdot> \<a>[a, a, b \<otimes> b] \<cdot> (\<d>[a] \<otimes> \<d>[b])"
    proof (intro pr_joint_monic [of "a \<otimes> b" "a \<otimes> b" "\<d>[a \<otimes> b]"])
      show "seq \<pp>\<^sub>0[a \<otimes> b, a \<otimes> b] (\<d>[a \<otimes> b])"
        using assms by simp
      have 1: "\<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> (a \<otimes> \<a>[b, a, b]) \<cdot> (a \<otimes> \<sigma> (a, b) \<otimes> b) \<cdot>
                 (a \<otimes> \<a>\<^sup>-\<^sup>1[a, b, b]) \<cdot> \<a>[a, a, b \<otimes> b] \<cdot> (\<d>[a] \<otimes> \<d>[b]) =
               \<langle>a \<otimes> b, a \<otimes> b\<rangle>"
      proof -
        have "\<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> (a \<otimes> \<a>[b, a, b]) \<cdot> (a \<otimes> \<sigma> (a, b) \<otimes> b) \<cdot>
              (a \<otimes> \<a>\<^sup>-\<^sup>1[a, b, b]) \<cdot> \<a>[a, a, b \<otimes> b] \<cdot> (\<d>[a] \<otimes> \<d>[b])
                = \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> (a \<otimes> \<a>[b, a, b]) \<cdot> (a \<otimes> \<sigma> (a, b) \<otimes> b) \<cdot>
                  (a \<otimes> \<a>\<^sup>-\<^sup>1[a, b, b]) \<cdot> \<langle>\<pp>\<^sub>1[a, b], \<langle>\<pp>\<^sub>1[a, b], \<d>[b] \<cdot> \<pp>\<^sub>0[a, b]\<rangle>\<rangle>"
        proof -
          have "\<a>[a, a, b \<otimes> b] \<cdot> (\<d>[a] \<otimes> \<d>[b]) = \<langle>\<pp>\<^sub>1[a, b], \<langle>\<pp>\<^sub>1[a, b], \<d>[b] \<cdot> \<pp>\<^sub>0[a, b]\<rangle>\<rangle>"
            using assms assoc_def comp_assoc pr_naturality comp_cod_arr by simp
          thus ?thesis by presburger
        qed
        also have "... = \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot>
        \<langle>a \<cdot> a \<cdot> a \<cdot> \<pp>\<^sub>1[a, b], \<a>[b, a, b] \<cdot> (\<s>[a, b] \<cdot> (a \<otimes> b) \<otimes> b) \<cdot>
                               \<a>\<^sup>-\<^sup>1[a, b, b] \<cdot> \<langle>\<pp>\<^sub>1[a, b], \<d>[b \<cdot> \<pp>\<^sub>0[a, b]]\<rangle>\<rangle>"
          using assms prod_tuple by simp
        also have "... = \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot>
        \<langle>\<pp>\<^sub>1[a, b], \<a>[b, a, b] \<cdot> (\<s>[a, b] \<otimes> b) \<cdot> \<a>\<^sup>-\<^sup>1[a, b, b] \<cdot> \<langle>\<pp>\<^sub>1[a, b], \<d>[\<pp>\<^sub>0[a, b]]\<rangle>\<rangle>"
        proof -
          have "a \<cdot> a \<cdot> a \<cdot> \<pp>\<^sub>1[a, b] = \<pp>\<^sub>1[a, b]"
            using assms comp_cod_arr by simp
          moreover have "b \<cdot> \<pp>\<^sub>0[a, b] = \<pp>\<^sub>0[a, b]"
            using assms comp_cod_arr by simp
          moreover have "\<s>[a, b] \<cdot> (a \<otimes> b) \<otimes> b = \<s>[a, b] \<otimes> b"
            using assms comp_arr_dom by simp
          ultimately show ?thesis by simp
        qed
        also have "... = \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> \<langle>\<pp>\<^sub>1[a, b], \<a>[b, a, b] \<cdot> (\<s>[a, b] \<otimes> b) \<cdot>
                           \<langle>\<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>, \<pp>\<^sub>0[a, b]\<rangle>\<rangle>"
        proof -
          have "\<a>\<^sup>-\<^sup>1[a, b, b] \<cdot> \<langle>\<pp>\<^sub>1[a, b], \<d>[\<pp>\<^sub>0[a, b]]\<rangle> = \<langle>\<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>, \<pp>\<^sub>0[a, b]\<rangle>"
            using assms comp_assoc_tuple(2) by blast
          thus ?thesis by simp
        qed
        also have "... = \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> \<langle>\<pp>\<^sub>1[a, b], \<a>[b, a, b] \<cdot> \<langle>\<s>[a, b], \<pp>\<^sub>0[a, b]\<rangle>\<rangle>"
          using assms prod_tuple comp_arr_dom comp_cod_arr by simp
        also have "... = \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> \<langle>\<pp>\<^sub>1[a, b], \<langle>\<pp>\<^sub>0[a, b], \<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>\<rangle>\<rangle>"
          using assms comp_assoc_tuple(1)
          by (metis sym_def pr_in_hom)
        also have "... = \<langle>\<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>, \<langle>\<pp>\<^sub>1[a, b], \<pp>\<^sub>0[a, b]\<rangle>\<rangle>"
          using assms comp_assoc_tuple(2) by force
        also have "... = \<d>[a \<otimes> b]"
          using assms by simp
        finally show ?thesis by simp
      qed
      show "\<pp>\<^sub>0[a \<otimes> b, a \<otimes> b] \<cdot> \<d>[a \<otimes> b]
              = \<pp>\<^sub>0[a \<otimes> b, a \<otimes> b] \<cdot>
                \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> (a \<otimes> \<a>[b, a, b]) \<cdot> (a \<otimes> \<sigma> (a, b) \<otimes> b) \<cdot>
                (a \<otimes> \<a>\<^sup>-\<^sup>1[a, b, b]) \<cdot> \<a>[a, a, b \<otimes> b] \<cdot> (\<d>[a] \<otimes> \<d>[b])"
        using assms 1 by force
      show "\<pp>\<^sub>1[a \<otimes> b, a \<otimes> b] \<cdot> \<d>[a \<otimes> b]
              = \<pp>\<^sub>1[a \<otimes> b, a \<otimes> b] \<cdot>
                \<a>\<^sup>-\<^sup>1[a, b, a \<otimes> b] \<cdot> (a \<otimes> \<a>[b, a, b]) \<cdot> (a \<otimes> \<sigma> (a, b) \<otimes> b) \<cdot>
                (a \<otimes> \<a>\<^sup>-\<^sup>1[a, b, b]) \<cdot> \<a>[a, a, b \<otimes> b] \<cdot> (\<d>[a] \<otimes> \<d>[b])"
        using assms 1 by force
    qed

    (* TODO: Not sure if the remaining facts are useful. *)

    lemma \<iota>_eq_trm:
    shows "\<iota> = \<t>[\<one> \<otimes> \<one>]"
    proof (intro terminal_arr_unique)
      show "par \<iota> \<t>[\<one> \<otimes> \<one>]"
        by (simp add: ide_one trm_one trm_tensor)
      show "terminal_arr \<t>[\<one> \<otimes> \<one>]"
        using ide_one \<iota>_is_terminal_arr \<open>par \<iota> \<t>[\<one> \<otimes> \<one>]\<close> by auto
      show "terminal_arr \<iota>"
        using \<iota>_is_terminal_arr by blast
    qed

    lemma terminal_tensor_one_one:
    shows "terminal (\<one> \<otimes> \<one>)"
    proof
      show "ide (\<one> \<otimes> \<one>)"
        using ide_one by simp
      show "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> \<one> \<otimes> \<one>\<guillemotright>"
      proof -
        fix a
        assume a: "ide a"
        show "\<exists>!f. \<guillemotleft>f : a \<rightarrow> \<one> \<otimes> \<one>\<guillemotright>"
        proof
          show "\<guillemotleft>inv \<iota> \<cdot> \<t>[a] : a \<rightarrow> \<one> \<otimes> \<one>\<guillemotright>"
            using a ide_one inverse_arrows_\<iota> inverse_unique trm_in_hom by fastforce
          show "\<And>f. \<guillemotleft>f : a \<rightarrow> \<one> \<otimes> \<one>\<guillemotright> \<Longrightarrow> f = inv \<iota> \<cdot> \<t>[a]"
          proof -
            fix f
            assume f: "\<guillemotleft>f : a \<rightarrow> \<one> \<otimes> \<one>\<guillemotright>"
            have "\<iota> \<cdot> f = \<t>[a]"
            proof (intro terminal_arr_unique)
              show "par (\<iota> \<cdot> f) \<t>[a]"
                using a f
                by (metis \<iota>_is_iso \<iota>_is_terminal_arr \<open>\<guillemotleft>inv \<iota> \<cdot> \<t>[a] : a \<rightarrow> \<one> \<otimes> \<one>\<guillemotright>\<close>
                    cod_comp dom_comp dom_inv ide_one in_homE pr_simps(2-3) seqE seqI)
              show "terminal_arr (\<iota> \<cdot> f)"
                using a f \<iota>_is_terminal_arr cod_comp by force
              show "terminal_arr \<t>[a]"
                using a \<open>par (\<iota> \<cdot> f) \<t>[a]\<close> \<open>terminal_arr (\<iota> \<cdot> f)\<close> by auto
            qed
            thus "f = inv \<iota> \<cdot> \<t>[a]"
              using a f \<iota>_is_iso invert_side_of_triangle(1)
                    \<open>\<guillemotleft>inv \<iota> \<cdot> \<t>[a] : a \<rightarrow> \<one> \<otimes> \<one>\<guillemotright>\<close>
              by blast
          qed
        qed
      qed
    qed

  end

  section "Category with Finite Products"

  text \<open>
    In this last section, we show that the notion ``cartesian category'', which we defined
    to be a category with binary products and terminal object, coincides with the notion
    ``category with finite products''.  Due to the inability to quantify over types in HOL,
    we content ourselves with defining the latter notion as "has \<open>I\<close>-indexed products
    for every finite set \<open>I\<close> of natural numbers."  We can transfer this property to finite
    sets at other types using the fact that products are preserved under bijections of
    the index sets.
  \<close>

  locale category_with_finite_products =
    category C
  for C :: "'c comp" +
  assumes has_finite_products: "finite (I :: nat set) \<Longrightarrow> has_products I"
  begin

    lemma has_finite_products':
    assumes "I \<noteq> UNIV"
    shows "finite I \<Longrightarrow> has_products I"
    proof -
      assume I: "finite I"
      obtain n \<phi> where \<phi>: "bij_betw \<phi> {k. k < (n :: nat)} I"
        using I finite_imp_nat_seg_image_inj_on inj_on_imp_bij_betw by fastforce
      show "has_products I"
        using assms(1) \<phi> has_finite_products has_products_preserved_by_bijection
              category_with_finite_products.has_finite_products
        by blast
    qed

  end

  lemma (in category) has_binary_products_if:
  assumes "has_products ({0, 1} :: nat set)"
  shows "has_binary_products"
  proof (unfold has_binary_products_def)
    show "\<forall>a0 a1. ide a0 \<and> ide a1 \<longrightarrow> (\<exists>p0 p1. has_as_binary_product a0 a1 p0 p1)"
    proof (intro allI impI)
      fix a0 a1
      assume 1: "ide a0 \<and> ide a1"
      show "\<exists>p0 p1. has_as_binary_product a0 a1 p0 p1"
      proof -
        interpret J: binary_product_shape
          by unfold_locales
        interpret D: binary_product_diagram C a0 a1
          using 1 by unfold_locales auto
        interpret discrete_diagram J.comp C D.map
          using J.is_discrete
          by unfold_locales auto
        show "\<exists>p0 p1. has_as_binary_product a0 a1 p0 p1"
        proof (unfold has_as_binary_product_def)
          text \<open>
            Here we have to work around the fact that \<open>has_finite_products\<close> is defined
            in terms of @{typ "nat set"}, whereas \<open>has_as_binary_product\<close> is defined
            in terms of \<open>J.arr set\<close>.
          \<close>
          let ?\<phi> = "(\<lambda>x :: nat. if x = 0 then J.FF else J.TT)"
          let ?\<psi> = "\<lambda>j. if j = J.FF then 0 else 1"
          have "bij_betw ?\<phi> ({0, 1} :: nat set) {J.FF, J.TT}"
            using bij_betwI [of ?\<phi> "{0, 1} :: nat set" "{J.FF, J.TT}" ?\<psi>] by fastforce
          hence "has_products {J.FF, J.TT}"
            using assms has_products_def [of "{J.FF, J.TT}"]
                  has_products_preserved_by_bijection
                    [of "{0, 1} :: nat set" ?\<phi> "{J.FF, J.TT}"]
            by blast
          hence "\<exists>a. has_as_product J.comp D.map a"
            using has_products_def [of "{J.FF, J.TT}"]
                  discrete_diagram_axioms J.arr_char
            by blast
          hence "\<exists>a \<pi>. product_cone J.comp C D.map a \<pi>"
            using has_as_product_def by blast
          hence 2: "\<exists>a \<pi>. D.limit_cone a \<pi>"
            unfolding product_cone_def by simp
          obtain a \<pi> where \<pi>: "D.limit_cone a \<pi>"
            using 2 by auto
          interpret \<pi>: limit_cone J.comp C D.map a \<pi>
            using \<pi> by auto
          have "\<pi> = D.mkCone (\<pi> J.FF) (\<pi> J.TT)"
          proof -
            have "\<And>a. J.ide a \<Longrightarrow> \<pi> a = D.mkCone (\<pi> J.FF) (\<pi> J.TT) a"
              using D.mkCone_def J.ide_char by auto
            moreover have "a = dom (\<pi> J.FF)"
              by simp
            moreover have "D.cone a (D.mkCone (\<pi> (J.MkIde False)) (\<pi> (J.MkIde True)))"
              using 1 D.cone_mkCone [of "\<pi> J.FF" "\<pi> J.TT"] by auto
            ultimately show ?thesis
              using D.mkCone_def \<pi>.natural_transformation_axioms
                    D.cone_mkCone [of "\<pi> J.FF" "\<pi> J.TT"]
                    NaturalTransformation.eqI
                      [of "J.comp" C \<pi>.A.map "D.map" \<pi> "D.mkCone (\<pi> J.FF) (\<pi> J.TT)"]
                    cone_def [of J.comp C D.map a "D.mkCone (\<pi> J.FF) (\<pi> J.TT)"] J.ide_char
              by blast
          qed
          hence "D.limit_cone (dom (\<pi> J.FF)) (D.mkCone (\<pi> J.FF) (\<pi> J.TT))"
            using \<pi>.limit_cone_axioms by simp
          thus "\<exists>p0 p1. ide a0 \<and> ide a1 \<and> D.has_as_binary_product p0 p1"
            using 1 by blast
        qed
      qed
    qed
  qed

  sublocale category_with_finite_products \<subseteq> category_with_binary_products C
    using has_binary_products_if has_finite_products
    by (unfold_locales, unfold has_binary_products_def) simp

  proposition (in category_with_finite_products) is_category_with_binary_products:
  shows "category_with_binary_products C"
    ..

  sublocale category_with_finite_products \<subseteq> category_with_terminal_object C
  proof
    interpret J: discrete_category "{} :: nat set"
      by unfold_locales auto
    interpret D: empty_diagram J.comp C "\<lambda>j. null"
      by unfold_locales auto
    interpret D: discrete_diagram J.comp C "\<lambda>j. null"
      using J.is_discrete by unfold_locales auto
    have "\<And>a. D.has_as_limit a \<longleftrightarrow> has_as_product J.comp (\<lambda>j. null) a"
      using product_cone_def J.category_axioms category_axioms D.discrete_diagram_axioms
            has_as_product_def product_cone_def
      by metis
    moreover have "\<exists>a. has_as_product J.comp (\<lambda>j. null) a"
      using has_finite_products [of "{} :: nat set"] has_products_def [of "{} :: nat set"]
            D.discrete_diagram_axioms
      by blast
    ultimately have "\<exists>a. D.has_as_limit a" by blast
    thus "\<exists>a. terminal a" using D.has_as_limit_iff_terminal by blast
  qed

  proposition (in category_with_finite_products) is_category_with_terminal_object:
  shows "category_with_terminal_object C"
    ..

  sublocale category_with_finite_products \<subseteq> cartesian_category ..

  proposition (in category_with_finite_products) is_cartesian_category:
  shows "cartesian_category C"
    ..

  context category
  begin

    lemma binary_product_of_products_is_product:
    assumes "has_as_product J0 D0 a0" and "has_as_product J1 D1 a1"
    and "has_as_binary_product a0 a1 p0 p1"
    and "Collect (partial_magma.arr J0) \<inter> Collect (partial_magma.arr J1) = {}"
    and "partial_magma.null J0 = partial_magma.null J1"
    shows "has_as_product
             (discrete_category.comp
                (Collect (partial_magma.arr J0) \<union> Collect (partial_magma.arr J1))
                (partial_magma.null J0))
             (\<lambda>i. if i \<in> Collect (partial_magma.arr J0) then D0 i
                  else if i \<in> Collect (partial_magma.arr J1) then D1 i
                  else null)
             (dom p0)"
    proof -
      obtain \<pi>0 where \<pi>0: "product_cone J0 (\<cdot>) D0 a0 \<pi>0"
        using assms(1) has_as_product_def by blast
      obtain \<pi>1 where \<pi>1: "product_cone J1 (\<cdot>) D1 a1 \<pi>1"
        using assms(2) has_as_product_def by blast
      interpret J0: category J0
        using \<pi>0 product_cone.axioms(1) by metis
      interpret J1: category J1
        using \<pi>1 product_cone.axioms(1) by metis
      interpret D0: discrete_diagram J0 C D0
        using \<pi>0 product_cone.axioms(3) by metis
      interpret D1: discrete_diagram J1 C D1
        using \<pi>1 product_cone.axioms(3) by metis
      interpret \<pi>0: product_cone J0 C D0 a0 \<pi>0
        using \<pi>0 by auto
      interpret \<pi>1: product_cone J1 C D1 a1 \<pi>1
        using \<pi>1 by auto
      interpret J: discrete_category \<open>Collect J0.arr \<union> Collect J1.arr\<close> J0.null
        using J0.not_arr_null assms(5) by unfold_locales auto
      interpret X: binary_product_shape .
      interpret a0xa1: binary_product_diagram C a0 a1
        using assms(3) has_as_binary_product_def
        by (simp add: binary_product_diagram.intro binary_product_diagram_axioms.intro
            category_axioms)
      have p0p1: "a0xa1.has_as_binary_product p0 p1"
        using assms(3) has_as_binary_product_def [of a0 a1 p0 p1] by simp

      let ?D = "(\<lambda>i. if i \<in> Collect J0.arr then D0 i
                     else if i \<in> Collect J1.arr then D1 i
                     else null)"
      let ?a = "dom p0"
      let ?\<pi> = "\<lambda>i. if i \<in> Collect J0.arr then \<pi>0 i \<cdot> p0
                    else if i \<in> Collect J1.arr then \<pi>1 i \<cdot> p1
                    else null"

      let ?p0p1 = "a0xa1.mkCone p0 p1"
      interpret p0p1: limit_cone X.comp C a0xa1.map ?a ?p0p1
        using p0p1 by simp
      have a: "ide ?a"
        using p0p1.ide_apex by simp
      have p0: "\<guillemotleft>p0 : ?a \<rightarrow> a0\<guillemotright>"
        using a0xa1.mkCone_def p0p1.preserves_hom [of X.FF X.FF X.FF] X.ide_char X.ide_in_hom
        by auto
      have p1: "\<guillemotleft>p1 : ?a \<rightarrow> a1\<guillemotright>"
        using a0xa1.mkCone_def p0p1.preserves_hom [of X.TT X.TT X.TT] X.ide_char X.ide_in_hom
        by auto

      interpret D: discrete_diagram J.comp C ?D
        using assms J.arr_char J.dom_char J.cod_char J.is_discrete D0.is_discrete D1.is_discrete
              J.cod_comp J.seq_char
        by unfold_locales auto
      interpret A: constant_functor J.comp C ?a
        using p0p1.ide_apex by unfold_locales simp
      interpret \<pi>: natural_transformation J.comp C A.map ?D ?\<pi>
      proof
        fix j
        show "\<not> J.arr j \<Longrightarrow> ?\<pi> j = null"
          by simp
        assume j: "J.arr j"
        have \<pi>0j: "J0.arr j \<Longrightarrow> \<guillemotleft>\<pi>0 j : a0 \<rightarrow> D0 j\<guillemotright>"
          using D0.is_discrete by auto
        have \<pi>1j: "J1.arr j \<Longrightarrow> \<guillemotleft>\<pi>1 j : a1 \<rightarrow> D1 j\<guillemotright>"
          using D1.is_discrete by auto
        show "dom (?\<pi> j) = A.map (J.dom j)"
          using j J.arr_char p0 p1 \<pi>0j \<pi>1j
          by fastforce
        show "cod (?\<pi> j) = ?D (J.cod j)"
          using j J.arr_char p0 p1 \<pi>0j \<pi>1j
          by fastforce
        show "?D j \<cdot> ?\<pi> (J.dom j) = ?\<pi> j"
        proof -
          have 0: "J0.arr j \<Longrightarrow> D0 j \<cdot> \<pi>0 j \<cdot> p0 = \<pi>0 j \<cdot> p0"
          proof -
            have "J0.arr j \<Longrightarrow> (D0 j \<cdot> \<pi>0 j) \<cdot> p0 = \<pi>0 j \<cdot> p0"
              using p0 \<pi>0.is_natural_1 \<pi>0.is_natural_2 D0.is_discrete by simp
            thus "J0.arr j \<Longrightarrow> D0 j \<cdot> \<pi>0 j \<cdot> p0 = \<pi>0 j \<cdot> p0"
              using comp_assoc by simp
          qed
          have 1: "J1.arr j \<Longrightarrow> D1 j \<cdot> \<pi>1 j \<cdot> p1 = \<pi>1 j \<cdot> p1"
          proof -
            have "J1.arr j \<Longrightarrow> (D1 j \<cdot> \<pi>1 j) \<cdot> p1 = \<pi>1 j \<cdot> p1"
              using p1 \<pi>1.is_natural_1 \<pi>1.is_natural_2 D1.is_discrete by simp
            thus "J1.arr j \<Longrightarrow> D1 j \<cdot> \<pi>1 j \<cdot> p1 = \<pi>1 j \<cdot> p1"
              using comp_assoc by simp
          qed
          show ?thesis
            using 0 1 by auto
        qed
        show "?\<pi> (J.cod j) \<cdot> A.map j = ?\<pi> j"
          using j comp_arr_dom p0 p1 comp_assoc by auto
      qed
      interpret \<pi>: cone J.comp C ?D ?a ?\<pi> ..
      interpret \<pi>: product_cone J.comp C ?D ?a ?\<pi>
      proof
        show "\<And>a' \<chi>'. D.cone a' \<chi>' \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a' \<rightarrow> ?a\<guillemotright> \<and> D.cones_map f ?\<pi> = \<chi>'"
        proof -
          fix a' \<chi>'
          assume \<chi>': "D.cone a' \<chi>'"
          interpret \<chi>': cone J.comp C ?D a' \<chi>'
            using \<chi>' by simp
          show "\<exists>!f. \<guillemotleft>f : a' \<rightarrow> ?a\<guillemotright> \<and> D.cones_map f ?\<pi> = \<chi>'"
          proof
            let ?\<chi>0' = "\<lambda>i. if i \<in> Collect J0.arr then \<chi>' i else null"
            let ?\<chi>1' = "\<lambda>i. if i \<in> Collect J1.arr then \<chi>' i else null"
            have 0: "\<And>i. i \<in> Collect J0.arr \<Longrightarrow> \<chi>' i \<in> hom a' (D0 i)"
              using J.arr_char by auto
            have 1: "\<And>i. i \<in> Collect J1.arr \<Longrightarrow> \<chi>' i \<in> hom a' (D1 i)"
              using J.arr_char \<open>Collect J0.arr \<inter> Collect J1.arr = {}\<close> by force
            interpret A0': constant_functor J0 C a'
              apply unfold_locales using \<chi>'.ide_apex by auto
            interpret A1': constant_functor J1 C a'
              apply unfold_locales using \<chi>'.ide_apex by auto
            interpret \<chi>0': cone J0 C D0 a' ?\<chi>0'
            proof (unfold_locales)
              fix j
              show "\<not> J0.arr j \<Longrightarrow> (if j \<in> Collect J0.arr then \<chi>' j else null) = null"
                by simp
              assume j: "J0.arr j"
              show 0: "dom (?\<chi>0' j) = A0'.map (J0.dom j)"
                using j by simp
              show 1: "cod (?\<chi>0' j) = D0 (J0.cod j)"
                using j J.arr_char J.cod_char D0.is_discrete by simp
              show "D0 j \<cdot> (?\<chi>0' (J0.dom j)) = ?\<chi>0' j"
                using 1 j J.arr_char D0.is_discrete comp_cod_arr by simp
              show "?\<chi>0' (J0.cod j) \<cdot> A0'.map j = ?\<chi>0' j"
                using 0 j J.arr_char D0.is_discrete comp_arr_dom by simp
            qed
            interpret \<chi>1': cone J1 C D1 a' ?\<chi>1'
            proof (unfold_locales)
              fix j
              show "\<not> J1.arr j \<Longrightarrow> (if j \<in> Collect J1.arr then \<chi>' j else null) = null"
                by simp
              assume j: "J1.arr j"
              show 0: "dom (?\<chi>1' j) = A1'.map (J1.dom j)"
                using j by simp
              show 1: "cod (?\<chi>1' j) = D1 (J1.cod j)"
                using assms(4) j J.arr_char J.cod_char D1.is_discrete by auto
              show "D1 j \<cdot> (?\<chi>1' (J1.dom j)) = ?\<chi>1' j"
                using 1 j J.arr_char D1.is_discrete comp_cod_arr by simp
              show "?\<chi>1' (J1.cod j) \<cdot> A1'.map j = ?\<chi>1' j"
                using 0 j J.arr_char D1.is_discrete comp_arr_dom by simp
            qed
            define f0 where "f0 = \<pi>0.induced_arrow a' ?\<chi>0'"
            define f1 where "f1 = \<pi>1.induced_arrow a' ?\<chi>1'"
            have f0: "\<guillemotleft>f0 : a' \<rightarrow> a0\<guillemotright>"
              using f0_def \<pi>0.induced_arrowI \<chi>0'.cone_axioms by simp
            have f1: "\<guillemotleft>f1 : a' \<rightarrow> a1\<guillemotright>"
              using f1_def \<pi>1.induced_arrowI \<chi>1'.cone_axioms by simp
            have 2: "a0xa1.is_rendered_commutative_by f0 f1"
              using f0 f1 by auto

            interpret p0p1: binary_product_cone C a0 a1 p0 p1 ..
            interpret f0f1: cone X.comp C a0xa1.map a' \<open>a0xa1.mkCone f0 f1\<close>
              using 2 f0 f1 a0xa1.cone_mkCone [of f0 f1] by auto
            define f where "f = p0p1.induced_arrow a' (a0xa1.mkCone f0 f1)"

            have f: "\<guillemotleft>f : a' \<rightarrow> ?a\<guillemotright>"
              using f_def 2 f0 f1 p0p1.induced_arrowI'(1) by auto
            moreover have \<chi>': "D.cones_map f ?\<pi> = \<chi>'"
            proof
              fix j
              show "D.cones_map f ?\<pi> j = \<chi>' j"
              proof (cases "J0.arr j", cases "J1.arr j")
                show "\<lbrakk>J0.arr j; J1.arr j\<rbrakk> \<Longrightarrow> D.cones_map f ?\<pi> j = \<chi>' j"
                  using assms(4) by auto
                show "\<lbrakk>J0.arr j; \<not> J1.arr j\<rbrakk> \<Longrightarrow> D.cones_map f ?\<pi> j = \<chi>' j"
                proof -
                  assume J0: "J0.arr j" and J1: "\<not> J1.arr j"
                  have "D.cones_map f ?\<pi> j = (\<pi>0 j \<cdot> p0) \<cdot> f"
                    using f J0 J1 \<pi>.cone_axioms by auto
                  also have "... = \<pi>0 j \<cdot> p0 \<cdot> f"
                    using comp_assoc by simp
                  also have "... = \<pi>0 j \<cdot> f0"
                    using 2 f0 f1 f_def p0p1.induced_arrowI' by auto
                  also have "... = \<chi>' j"
                  proof -
                    have "\<pi>0 j \<cdot> f0 = \<pi>0 j \<cdot> \<pi>0.induced_arrow' a' \<chi>'"
                      unfolding f0_def by simp
                    also have "... = (\<lambda>j. if J0.arr j then
                                            \<pi>0 j \<cdot> \<pi>0.induced_arrow a'
                                                    (\<lambda>i. if i \<in> Collect J0.arr then \<chi>' i else null)
                                          else null) j"
                      using J0 by simp
                    also have "... = D0.mkCone \<chi>' j"
                    proof -
                      have "(\<lambda>j. if J0.arr j then
                                    \<pi>0 j \<cdot> \<pi>0.induced_arrow a'
                                             (\<lambda>i. if i \<in> Collect J0.arr then \<chi>' i else null)
                                 else null) =
                            D0.mkCone \<chi>'"
                        using f0 f0_def \<pi>0.induced_arrowI(2) [of ?\<chi>0' a'] J0
                              D0.mkCone_cone \<chi>0'.cone_axioms \<pi>0.cone_axioms J0
                        by auto
                      thus ?thesis by meson
                    qed
                    also have "... = \<chi>' j"
                      using J0 by simp
                    finally show ?thesis by blast
                  qed
                  finally show ?thesis by simp
                qed
                show "\<not> J0.arr j \<Longrightarrow> D.cones_map f ?\<pi> j = \<chi>' j"
                proof (cases "J1.arr j")
                  show "\<lbrakk>\<not> J0.arr j; \<not> J1.arr j\<rbrakk> \<Longrightarrow> D.cones_map f ?\<pi> j = \<chi>' j"
                    using f \<pi>.cone_axioms \<chi>'.is_extensional by auto
                  show "\<lbrakk>\<not> J0.arr j; J1.arr j\<rbrakk> \<Longrightarrow> D.cones_map f ?\<pi> j = \<chi>' j"
                  proof -
                    assume J0: "\<not> J0.arr j" and J1: "J1.arr j"
                    have "D.cones_map f ?\<pi> j = (\<pi>1 j \<cdot> p1) \<cdot> f"
                      using J0 J1 f \<pi>.cone_axioms by auto
                    also have "... = \<pi>1 j \<cdot> p1 \<cdot> f"
                      using comp_assoc by simp
                    also have "... = \<pi>1 j \<cdot> f1"
                      using 2 f0 f1 f_def p0p1.induced_arrowI' by auto
                    also have "... = \<chi>' j"
                    proof -
                      have "\<pi>1 j \<cdot> f1 = \<pi>1 j \<cdot> \<pi>1.induced_arrow' a' \<chi>'"
                        unfolding f1_def by simp
                      also have "... = (\<lambda>j. if J1.arr j then
                                              \<pi>1 j \<cdot> \<pi>1.induced_arrow a'
                                                      (\<lambda>i. if i \<in> Collect J1.arr
                                                           then \<chi>' i else null)
                                            else null) j"
                        using J1 by simp
                      also have "... = D1.mkCone \<chi>' j"
                      proof -
                        have "(\<lambda>j. if J1.arr j then
                                      \<pi>1 j \<cdot> \<pi>1.induced_arrow a'
                                               (\<lambda>i. if i \<in> Collect J1.arr then \<chi>' i else null)
                                   else null) =
                              D1.mkCone \<chi>'"
                          using f1 f1_def \<pi>1.induced_arrowI(2) [of ?\<chi>1' a'] J1
                                D1.mkCone_cone [of a' \<chi>'] \<chi>1'.cone_axioms \<pi>1.cone_axioms J1
                          by auto
                        thus ?thesis by meson
                      qed
                      also have "... = \<chi>' j"
                        using J1 by simp
                      finally show ?thesis by blast
                    qed
                    finally show ?thesis by simp
                  qed
                qed
              qed
            qed
            ultimately show "\<guillemotleft>f : a' \<rightarrow> ?a\<guillemotright> \<and> D.cones_map f ?\<pi> = \<chi>'" by blast
            show "\<And>f'. \<guillemotleft>f' : a' \<rightarrow> ?a\<guillemotright> \<and> D.cones_map f' ?\<pi> = \<chi>' \<Longrightarrow> f' = f"
            proof -
              fix f'
              assume f': "\<guillemotleft>f' : a' \<rightarrow> ?a\<guillemotright> \<and> D.cones_map f' ?\<pi> = \<chi>'"
              let ?f0' = "p0 \<cdot> f'"
              let ?f1' = "p1 \<cdot> f'"
              have 1: "a0xa1.is_rendered_commutative_by ?f0' ?f1'"
                using f' p0 p1 p0p1.renders_commutative seqI' by auto
              have f0': "\<guillemotleft>?f0' : a' \<rightarrow> a0\<guillemotright>"
                using f' p0 by auto
              have f1': "\<guillemotleft>?f1' : a' \<rightarrow> a1\<guillemotright>"
                using f' p1 by auto
              have "p0 \<cdot> f = p0 \<cdot> f'"
              proof -
                have "D0.cones_map (p0 \<cdot> f) \<pi>0 = ?\<chi>0'"
                  using f p0 \<pi>0.cone_axioms \<chi>' \<pi>.cone_axioms comp_assoc assms(4) seqI'
                  by fastforce
                moreover have "D0.cones_map (p0 \<cdot> f') \<pi>0 = ?\<chi>0'"
                  using f' p0 \<pi>0.cone_axioms \<pi>.cone_axioms comp_assoc assms(4) seqI'
                  by fastforce
                moreover have "p0 \<cdot> f = f0"
                  using 2 f0 f_def p0p1.induced_arrowI'(2) by blast
                ultimately show ?thesis
                  using f0 f0' \<chi>0'.cone_axioms \<pi>0.is_universal [of a'] by auto
              qed
              moreover have "p1 \<cdot> f = p1 \<cdot> f'"
              proof -
                have "D1.cones_map (p1 \<cdot> f) \<pi>1 = ?\<chi>1'"
                proof
                  fix j
                  show "D1.cones_map (p1 \<cdot> f) \<pi>1 j = ?\<chi>1' j"
                    using f p1 \<pi>1.cone_axioms \<chi>' \<pi>.cone_axioms comp_assoc assms(4) seqI'
                    apply auto
                    by auto
                qed
                moreover have "D1.cones_map (p1 \<cdot> f') \<pi>1 = ?\<chi>1'"
                proof
                  fix j
                  show "D1.cones_map (p1 \<cdot> f') \<pi>1 j = ?\<chi>1' j"
                    using f' p1 \<pi>1.cone_axioms \<pi>.cone_axioms comp_assoc assms(4) seqI'
                    apply auto
                    by auto
                qed
                moreover have "p1 \<cdot> f = f1"
                  using 2 f1 f_def p0p1.induced_arrowI'(3) by blast
                  ultimately show ?thesis
                using f1 f1' \<chi>1'.cone_axioms \<pi>1.is_universal [of a'] by auto
              qed
              ultimately show "f' = f"
                using f f' p0p1.is_universal' [of a']
                by (metis (no_types, lifting) "1" dom_comp in_homE p0p1.is_universal' p1 seqI')
            qed
          qed
        qed
      qed
      show "has_as_product J.comp ?D ?a"
        unfolding has_as_product_def
        using \<pi>.product_cone_axioms by auto
    qed

  end

  sublocale cartesian_category \<subseteq> category_with_finite_products
  proof
    obtain t where t: "terminal t" using has_terminal by blast
    { fix n :: nat
      have "\<And>I :: nat set. finite I \<and> card I = n \<Longrightarrow> has_products I"
      proof (induct n)
        show "\<And>I :: nat set. finite I \<and> card I = 0 \<Longrightarrow> has_products I"
        proof -
          fix I :: "nat set"
          assume "finite I \<and> card I = 0"
          hence I: "I = {}" by force
          thus "has_products I"
          proof -
            interpret J: discrete_category I 0
              apply unfold_locales using I by auto
            have "\<And>D. discrete_diagram J.comp C D \<Longrightarrow> \<exists>a. has_as_product J.comp D a"
            proof -
              fix D
              assume D: "discrete_diagram J.comp C D"
              interpret D: discrete_diagram J.comp C D using D by auto
              interpret D: empty_diagram J.comp C D
                 using I J.arr_char by unfold_locales simp
              have "has_as_product J.comp D t"
                using t D.has_as_limit_iff_terminal has_as_product_def product_cone_def
                      J.category_axioms category_axioms D.discrete_diagram_axioms
                by metis
              thus "\<exists>a. has_as_product J.comp D a" by blast
            qed
            moreover have "I \<noteq> UNIV"
              using I by blast
            ultimately show ?thesis
              using I has_products_def
              by (metis category_with_terminal_object.has_terminal discrete_diagram.product_coneI
                  discrete_diagram_def empty_diagram.has_as_limit_iff_terminal empty_diagram.intro
                  empty_diagram_axioms.intro empty_iff has_as_product_def
                  is_category_with_terminal_object mem_Collect_eq)
          qed
        qed
        show "\<And>n I :: nat set.
                \<lbrakk> (\<And>I :: nat set. finite I \<and> card I = n \<Longrightarrow> has_products I);
                  finite I \<and> card I = Suc n \<rbrakk>
                    \<Longrightarrow> has_products I"
        proof -
          fix n :: nat
          fix I :: "nat set"
          assume IH: "\<And>I :: nat set. finite I \<and> card I = n \<Longrightarrow> has_products I"
          assume I: "finite I \<and> card I = Suc n"
          show "has_products I"
          proof -
            have "card I = 1 \<Longrightarrow> has_products I"
              using I has_unary_products by blast
            moreover have "card I \<noteq> 1 \<Longrightarrow> has_products I"
            proof -
              assume "card I \<noteq> 1"
              hence cardI: "card I > 1" using I by simp
              obtain i where i: "i \<in> I" using cardI by fastforce
              let ?I0 = "{i}" and ?I1 = "I - {i}"
              have 1: "I = ?I0 \<union> ?I1 \<and> ?I0 \<inter> ?I1 = {} \<and> card ?I0 = 1 \<and> card ?I1 = n"
                using i I cardI by auto
              show "has_products I"
              proof (unfold has_products_def, intro conjI allI impI)
                show "I \<noteq> UNIV"
                  using I by auto
                fix J D
                assume D: "discrete_diagram J C D \<and> Collect (partial_magma.arr J) = I"
                interpret D: discrete_diagram J C D
                  using D by simp
                have Null: "D.J.null \<notin> ?I0 \<and> D.J.null \<notin> ?I1"
                  using D D.J.not_arr_null i by blast
                interpret J0: discrete_category ?I0 D.J.null
                  using 1 Null D by unfold_locales auto
                interpret J1: discrete_category ?I1 D.J.null
                  using Null by unfold_locales auto
                interpret J0uJ1: discrete_category \<open>Collect J0.arr \<union> Collect J1.arr\<close> J0.null
                  using Null 1 J0.null_char J1.null_char by unfold_locales auto
                interpret D0: discrete_diagram_from_map ?I0 C D D.J.null
                  using 1 J0.ide_char D.preserves_ide D D.is_discrete i by unfold_locales auto
                interpret D1: discrete_diagram_from_map ?I1 C D D.J.null
                  using 1 J1.ide_char D.preserves_ide D D.is_discrete i by unfold_locales auto
                obtain a0 where a0: "has_as_product J0.comp D0.map a0"
                  using 1 has_unary_products [of ?I0] has_products_def [of ?I0]
                        D0.discrete_diagram_axioms
                  by fastforce
                obtain a1 where a1: "has_as_product J1.comp D1.map a1"
                  using 1 I IH [of ?I1] has_products_def [of ?I1] D1.discrete_diagram_axioms
                  by blast
                have 2: "\<exists>p0 p1. has_as_binary_product a0 a1 p0 p1"
                proof -
                  have "ide a0 \<and> ide a1"
                    using a0 a1 product_is_ide by auto
                  thus ?thesis
                     using a0 a1 has_binary_products has_binary_products_def by simp
                qed
                obtain p0 p1 where a: "has_as_binary_product a0 a1 p0 p1"
                  using 2 by auto
                let ?a = "dom p0"
                have "has_as_product J D ?a"
                proof -
                  have "D = (\<lambda>j. if j \<in> Collect J0.arr then D0.map j
                                 else if j \<in> Collect J1.arr then D1.map j
                                 else null)"
                  proof
                    fix j
                    show "D j = (if j \<in> Collect J0.arr then D0.map j
                                 else if j \<in> Collect J1.arr then D1.map j
                                 else null)"
                      using 1 D0.map_def D1.map_def D.is_extensional D J0.arr_char J1.arr_char
                      by auto
                  qed
                  moreover have "J = J0uJ1.comp"
                  proof -
                    have "\<And>j j'. J j j' = J0uJ1.comp j j'"
                    proof -
                      fix j j'
                      show "J j j' = J0uJ1.comp j j'"
                        using D J0uJ1.arr_char J0.arr_char J1.arr_char D.is_discrete i
                        apply (cases "j \<in> ?I0", cases "j' \<in> ?I0")
                          apply simp_all
                          apply auto[1]
                         apply (metis D.J.comp_arr_ide D.J.comp_ide_arr D.J.ext D.J.seqE
                            D.is_discrete J0.null_char J0uJ1.null_char)
                        by (metis D.J.comp_arr_ide D.J.comp_ide_arr D.J.comp_ide_self
                            D.J.ext D.J.seqE D.is_discrete J0.null_char J0uJ1.null_char
                            mem_Collect_eq)
                    qed
                    thus ?thesis by blast
                  qed
                  moreover have "Collect J0.arr \<inter> Collect J1.arr = {}"
                    by auto
                  moreover have "J0.null = J1.null"
                    using J0.null_char J1.null_char by simp
                  ultimately show "has_as_product J D ?a"
                    using binary_product_of_products_is_product
                            [of J0.comp D0.map a0 J1.comp D1.map a1 p0 p1]
                          J0.arr_char J1.arr_char
                          1 a0 a1 a
                    by simp
                qed
                thus "\<exists>a. has_as_product J D a" by blast
              qed
            qed
            ultimately show "has_products I" by blast
          qed
        qed
      qed
    }
    hence 1: "\<And>n I :: nat set. finite I \<and> card I = n \<Longrightarrow> has_products I" by simp
    thus "\<And>I :: nat set. finite I \<Longrightarrow> has_products I" by blast
  qed

  proposition (in cartesian_category) is_category_with_finite_products:
  shows "category_with_finite_products C"
    ..

end

