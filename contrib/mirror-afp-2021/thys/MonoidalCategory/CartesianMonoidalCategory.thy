(*  Title:       CartesianMonoidalCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Cartesian Monoidal Category"

theory CartesianMonoidalCategory
imports MonoidalCategory Category3.CartesianCategory
begin

  locale symmetric_monoidal_category =
    monoidal_category C T \<alpha> \<iota> +
    S: symmetry_functor C C +
    ToS: composite_functor CC.comp CC.comp C S.map T +
    \<sigma>: natural_isomorphism CC.comp C T ToS.map \<sigma>
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a
  and \<sigma> :: "'a * 'a \<Rightarrow> 'a" +
  assumes sym_inverse: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> inverse_arrows (\<sigma> (a, b)) (\<sigma> (b, a))"
  and unitor_coherence: "ide a \<Longrightarrow> \<l>[a] \<cdot> \<sigma> (a, \<I>) = \<r>[a]"
  and assoc_coherence: "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow>
                          \<alpha> (b, c, a) \<cdot> \<sigma> (a, b \<otimes> c) \<cdot> \<alpha> (a, b, c)
                             = (b \<otimes> \<sigma> (a, c)) \<cdot> \<alpha> (b, a, c) \<cdot> (\<sigma> (a, b) \<otimes> c)"
  begin

    abbreviation sym                  ("\<s>[_, _]")
    where "sym a b \<equiv> \<sigma> (a, b)"

  end

  locale elementary_symmetric_monoidal_category =
    elementary_monoidal_category C tensor unity lunit runit assoc
  for C :: "'a comp"                  (infixr "\<cdot>" 55)
  and tensor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<otimes>" 53)
  and unity :: 'a                      ("\<I>")
  and lunit :: "'a \<Rightarrow> 'a"              ("\<l>[_]")
  and runit :: "'a \<Rightarrow> 'a"              ("\<r>[_]")
  and assoc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]")
  and sym :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"          ("\<s>[_, _]") +
  assumes sym_in_hom: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> \<guillemotleft>\<s>[a, b] : a \<otimes> b \<rightarrow> b \<otimes> a\<guillemotright>"
  and sym_naturality: "\<lbrakk> arr f; arr g \<rbrakk> \<Longrightarrow> \<s>[cod f, cod g] \<cdot> (f \<otimes> g) = (g \<otimes> f) \<cdot> \<s>[dom f, dom g]"
  and sym_inverse: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> inverse_arrows \<s>[a, b] \<s>[b, a]"
  and unitor_coherence: "ide a \<Longrightarrow> \<l>[a] \<cdot> \<s>[a, \<I>] = \<r>[a]"
  and assoc_coherence: "\<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow>
                          \<a>[b, c, a] \<cdot> \<s>[a, b \<otimes> c] \<cdot> \<a>[a, b, c]
                             = (b \<otimes> \<s>[a, c]) \<cdot> \<a>[b, a, c] \<cdot> (\<s>[a, b] \<otimes> c)"
  begin

    lemma sym_simps [simp]:
    assumes "ide a" and "ide b"
    shows "arr \<s>[a, b]"
    and "dom \<s>[a, b] = a \<otimes> b"
    and "cod \<s>[a, b] = b \<otimes> a"
      using assms sym_in_hom by auto

    interpretation monoidal_category C T \<alpha> \<iota>
      using induces_monoidal_category by simp
    interpretation CC: product_category C C ..

    interpretation S: symmetry_functor C C ..
    interpretation ToS: composite_functor CC.comp CC.comp C S.map T ..

    definition \<sigma> :: "'a * 'a \<Rightarrow> 'a"
    where "\<sigma> f \<equiv> if CC.arr f then \<s>[cod (fst f), cod (snd f)] \<cdot> (fst f \<otimes> snd f) else null"

    interpretation \<sigma>: natural_isomorphism CC.comp C T ToS.map \<sigma>
    proof -
      interpret \<sigma>: transformation_by_components CC.comp C T ToS.map "\<lambda>a. \<s>[fst a, snd a]"
        apply unfold_locales
        using sym_in_hom sym_naturality by auto
      interpret \<sigma>: natural_isomorphism CC.comp C T ToS.map \<sigma>.map
        apply unfold_locales
        using sym_inverse \<sigma>.map_simp_ide by auto
      have "\<sigma> = \<sigma>.map"
        using \<sigma>_def \<sigma>.map_def sym_naturality by fastforce
      thus "natural_isomorphism CC.comp C T ToS.map \<sigma>"
        using \<sigma>.natural_isomorphism_axioms by presburger
    qed

    interpretation symmetric_monoidal_category C T \<alpha> \<iota> \<sigma>
    proof
      show "\<And>a b. \<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> inverse_arrows (\<sigma> (a, b)) (\<sigma> (b, a))"
      proof -
        fix a b
        assume a: "ide a" and b: "ide b"
        show "inverse_arrows (\<sigma> (a, b)) (\<sigma> (b, a))"
          using a b sym_inverse comp_arr_dom \<sigma>_def by auto
      qed
      (*
       * TODO: Here just using "lunit" refers to the locale parameter, rather than
       * the constant introduced by the interpretation above of monoidal_category.
       * This is slightly mysterious.
       *)
      show "\<And>a. ide a \<Longrightarrow> local.lunit a \<cdot> \<sigma> (a, local.unity) = local.runit a"
      proof -
        fix a
        assume a: "ide a"
        show "local.lunit a \<cdot> \<sigma> (a, local.unity) = local.runit a"
          using a lunit_agreement \<I>_agreement sym_in_hom comp_arr_dom [of "\<s>[a, \<I>]"]
                unitor_coherence runit_agreement \<sigma>_def
          by simp
      qed
      show "\<And>a b c. \<lbrakk> ide a; ide b; ide c \<rbrakk> \<Longrightarrow>
                      local.assoc b c a \<cdot> \<sigma> (a, local.tensor b c) \<cdot> local.assoc a b c
                        = local.tensor b (\<sigma> (a, c)) \<cdot> local.assoc b a c \<cdot> local.tensor (\<sigma> (a, b)) c"
      proof -
        fix a b c
        assume a: "ide a" and b: "ide b" and c: "ide c"
        show "local.assoc b c a \<cdot> \<sigma> (a, local.tensor b c) \<cdot> local.assoc a b c
                = local.tensor b (\<sigma> (a, c)) \<cdot> local.assoc b a c \<cdot> local.tensor (\<sigma> (a, b)) c"
          using a b c sym_in_hom tensor_preserves_ide \<sigma>_def assoc_coherence
                comp_arr_dom comp_cod_arr
          by simp
      qed
    qed

    lemma induces_symmetric_monoidal_category:
    shows "symmetric_monoidal_category C T \<alpha> \<iota> \<sigma>"
      ..

  end

  context symmetric_monoidal_category
  begin

    interpretation elementary_monoidal_category C tensor unity lunit runit assoc
      using induces_elementary_monoidal_category by auto

    lemma induces_elementary_symmetric_monoidal_category:
    shows "elementary_symmetric_monoidal_category
             C tensor unity lunit runit assoc (\<lambda>a b. \<sigma> (a, b))"
      using \<sigma>.naturality unitor_coherence assoc_coherence sym_inverse
      by unfold_locales auto

  end

  (* TODO: This definition of "diagonal_functor" conflicts with the one in Category3.Limit. *)
  locale diagonal_functor =
    C: category C +
    CC: product_category C C
  for C :: "'a comp"
  begin

    abbreviation map
    where "map f \<equiv> if C.arr f then (f, f) else CC.null"

    lemma is_functor:
    shows "functor C CC.comp map"
      using map_def by unfold_locales auto

    sublocale "functor" C CC.comp map
      using is_functor by simp

  end

  locale cartesian_monoidal_category =
    monoidal_category C T \<alpha> \<iota> +
    \<Omega>: constant_functor C C \<I> +
    \<Delta>: diagonal_functor C +
    \<tau>: natural_transformation C C map \<Omega>.map \<tau> +
    \<delta>: natural_transformation C C map \<open>T o \<Delta>.map\<close> \<delta>
  for C :: "'a comp"                            (infixr "\<cdot>" 55)
  and T :: "'a * 'a \<Rightarrow> 'a"
  and \<alpha> :: "'a * 'a * 'a \<Rightarrow> 'a"
  and \<iota> :: 'a
  and \<delta> :: "'a \<Rightarrow> 'a"                           ("\<d>[_]")
  and \<tau> :: "'a \<Rightarrow> 'a"                           ("\<t>[_]") +
  assumes trm_unity: "\<t>[\<I>] = \<I>"
  and pr0_dup: "ide a \<Longrightarrow> \<r>[a] \<cdot> (a \<otimes> \<t>[a]) \<cdot> \<delta> a = a"
  and pr1_dup: "ide a \<Longrightarrow> \<l>[a] \<cdot> (\<t>[a] \<otimes> a) \<cdot> \<delta> a = a"
  and tuple_pr: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> (\<r>[a] \<cdot> (a \<otimes> \<t>[b]) \<otimes> \<l>[b] \<cdot> (\<t>[a] \<otimes> b)) \<cdot> \<d>[a \<otimes> b] = a \<otimes> b"

  locale elementary_cartesian_monoidal_category =
    elementary_monoidal_category C tensor unity lunit runit assoc
  for C :: "'a comp"                   (infixr "\<cdot>" 55)
  and tensor :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"       (infixr "\<otimes>" 53)
  and unity :: 'a                      ("\<I>")
  and lunit :: "'a \<Rightarrow> 'a"              ("\<l>[_]")
  and runit :: "'a \<Rightarrow> 'a"              ("\<r>[_]")
  and assoc :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"  ("\<a>[_, _, _]")
  and trm :: "'a \<Rightarrow> 'a"                ("\<t>[_]")
  and dup :: "'a \<Rightarrow> 'a"                ("\<d>[_]") +
  assumes trm_in_hom [intro]: "ide a \<Longrightarrow> \<guillemotleft>\<t>[a] : a \<rightarrow> \<I>\<guillemotright>"
  and trm_unity: "\<t>[\<I>] = \<I>"
  and trm_naturality: "arr f \<Longrightarrow> \<t>[cod f] \<cdot> f = \<t>[dom f]"
  and dup_in_hom [intro]: "ide a \<Longrightarrow> \<guillemotleft>\<d>[a] : a \<rightarrow> a \<otimes> a\<guillemotright>"
  and dup_naturality: "arr f \<Longrightarrow> \<d>[cod f] \<cdot> f = (f \<otimes> f) \<cdot> \<d>[dom f]"
  and prj0_dup: "ide a \<Longrightarrow> \<r>[a] \<cdot> (a \<otimes> \<t>[a]) \<cdot> \<d>[a] = a"
  and prj1_dup: "ide a \<Longrightarrow> \<l>[a] \<cdot> (\<t>[a] \<otimes> a) \<cdot> \<d>[a] = a"
  and tuple_prj: "\<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow> (\<r>[a] \<cdot> (a \<otimes> \<t>[b]) \<otimes> \<l>[b] \<cdot> (\<t>[a] \<otimes> b)) \<cdot> \<d>[a \<otimes> b] = a \<otimes> b"

  context cartesian_monoidal_category
  begin

    lemma terminal_unity:
    shows "terminal \<I>"
    proof
      show "ide \<I>" by simp
      show "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> \<I>\<guillemotright>"
      proof
        fix a
        assume a: "ide a"
        show "\<guillemotleft>\<tau> a : a \<rightarrow> \<I>\<guillemotright>" using a by auto
        show "\<And>f. \<guillemotleft>f : a \<rightarrow> \<I>\<guillemotright> \<Longrightarrow> f = \<tau> a"
          using trm_unity \<tau>.naturality comp_cod_arr by fastforce
      qed
    qed

    lemma trm_is_terminal_arr:
    assumes "ide a"
    shows "terminal_arr \<t>[a]"
      using assms terminal_unity by simp

    interpretation elementary_monoidal_category C tensor unity lunit runit assoc
      using induces_elementary_monoidal_category by simp

    interpretation elementary_cartesian_monoidal_category C tensor unity lunit runit assoc \<tau> \<delta>
    proof
      show "\<And>a. ide a \<Longrightarrow> \<guillemotleft>\<t>[a] : a \<rightarrow> \<I>\<guillemotright>"
        using \<iota>_in_hom by force
      show "\<t>[\<I>] = \<I>"
        using \<tau>.preserves_hom \<iota>_in_hom ide_unity trm_is_terminal_arr terminal_unity
        by (intro terminal_arr_unique) auto
      show "\<And>f. arr f \<Longrightarrow> \<t>[cod f] \<cdot> f = \<t>[dom f]"
        using \<tau>.naturality comp_cod_arr by simp
      show "\<And>a. ide a \<Longrightarrow> \<guillemotleft>\<d>[a] : a \<rightarrow> a \<otimes> a\<guillemotright>"
        by auto
      show "\<And>f. arr f \<Longrightarrow> \<d>[cod f] \<cdot> f = (f \<otimes> f) \<cdot> \<d>[dom f]"
        using \<delta>.naturality by simp
      show "\<And>a. ide a \<Longrightarrow> \<l>[a] \<cdot> (\<t>[a] \<otimes> a) \<cdot> \<d>[a] = a"
        using pr1_dup lunit_in_hom by simp
      show "\<And>a. ide a \<Longrightarrow> \<r>[a] \<cdot> (a \<otimes> \<t>[a]) \<cdot> \<d>[a] = a"
        using pr0_dup runit_in_hom by simp
      show "\<And>a0 a1. \<lbrakk> ide a0; ide a1 \<rbrakk> \<Longrightarrow>
                     (\<r>[a0] \<cdot> (a0 \<otimes> \<t>[a1]) \<otimes> \<l>[a1] \<cdot> (\<t>[a0] \<otimes> a1)) \<cdot> \<d>[a0 \<otimes> a1]
                       = a0 \<otimes> a1"
        using tuple_pr by simp
    qed

    lemma induces_elementary_cartesian_monoidal_category:
    shows "elementary_cartesian_monoidal_category C tensor \<I> lunit runit assoc \<tau> \<delta>"
      ..

  end

  context elementary_cartesian_monoidal_category
  begin

    lemma trm_simps [simp]:
    assumes "ide a"
    shows "arr \<t>[a]" and "dom \<t>[a] = a" and "cod \<t>[a] = \<I>"
      using assms trm_in_hom by auto

    lemma dup_simps [simp]:
    assumes "ide a"
    shows "arr \<d>[a]" and "dom \<d>[a] = a" and "cod \<d>[a] = a \<otimes> a"
      using assms dup_in_hom by auto

    definition \<tau> :: "'a \<Rightarrow> 'a"
    where "\<tau> f \<equiv> if arr f then \<t>[dom f] else null"

    definition \<delta> :: "'a \<Rightarrow> 'a"
    where "\<delta> f \<equiv> if arr f then \<d>[cod f] \<cdot> f else null"

    interpretation CC: product_category C C ..

    interpretation MC: monoidal_category C T \<alpha> \<iota>
      using induces_monoidal_category by auto

    interpretation I: constant_functor C C MC.unity
      by unfold_locales auto
    interpretation \<Delta>: diagonal_functor C ..
    interpretation D: composite_functor C CC.comp C \<Delta>.map T ..
    interpretation \<tau>: natural_transformation C C map I.map \<tau>
      using trm_naturality I.map_def \<tau>_def \<I>_agreement comp_cod_arr
      by unfold_locales auto
    interpretation \<delta>: natural_transformation C C map D.map \<delta>
      using dup_naturality \<delta>_def comp_arr_dom
      by unfold_locales auto

    interpretation MC: cartesian_monoidal_category C T \<alpha> \<iota> \<delta> \<tau>
    proof
      show "\<tau> MC.unity = MC.unity"
        using \<I>_agreement trm_unity \<tau>_def by simp
      show "\<And>a. ide a \<Longrightarrow> MC.runit a \<cdot> MC.tensor a (\<tau> a) \<cdot> \<delta> a = a"
        using runit_agreement \<tau>_def \<delta>_def prj0_dup comp_arr_dom by auto
      show "\<And>a. ide a \<Longrightarrow> MC.lunit a \<cdot> MC.tensor (\<tau> a) a \<cdot> \<delta> a = a"
        using lunit_agreement \<tau>_def \<delta>_def prj1_dup comp_arr_dom by auto
      show "\<And>a b. \<lbrakk> ide a; ide b \<rbrakk> \<Longrightarrow>
                  MC.tensor (MC.runit a \<cdot> MC.tensor a (\<tau> b)) (MC.lunit b \<cdot> MC.tensor (\<tau> a) b) \<cdot>
                  \<delta> (MC.tensor a b) = MC.tensor a b"
      proof -
        fix a b
        assume a: "ide a" and b: "ide b"
        have "seq \<r>[a] (a \<otimes> \<t>[b])"
          by (metis a b arr_tensor cod_tensor ide_char in_homE runit_in_hom seqI trm_simps(1,3))
        moreover have "seq \<l>[b] (\<t>[a] \<otimes> b)"
          by (metis a b arr_tensor cod_tensor ide_char in_homE lunit_in_hom seqI trm_simps(1,3))
        ultimately show "MC.tensor (MC.runit a \<cdot> MC.tensor a (\<tau> b))
                                   (MC.lunit b \<cdot> MC.tensor (\<tau> a) b) \<cdot> \<delta> (MC.tensor a b) =
                         MC.tensor a b"
          using a b lunit_agreement runit_agreement unitor_coincidence \<tau>_def \<delta>_def comp_arr_dom
                tensor_preserves_ide tuple_prj T_def
          by auto
      qed
    qed

    lemma induces_cartesian_monoidal_category:
    shows "cartesian_monoidal_category C T \<alpha> \<iota> \<delta> \<tau>"
      ..

  end

  text \<open>
    A cartesian category extends to a a cartesian monoidal category by using the product
    structure to obtain the various canonical maps.
  \<close>

  context cartesian_category
  begin

    interpretation C: elementary_cartesian_category C pr0 pr1 \<one> trm
      using extends_to_elementary_cartesian_category by simp
    interpretation CC: product_category C C ..
    interpretation CCC: product_category C CC.comp ..
    interpretation T: binary_functor C C C Prod
      using binary_functor_Prod by simp
    interpretation T: binary_endofunctor C Prod ..
    interpretation ToTC: "functor" CCC.comp C T.ToTC
      using T.functor_ToTC by auto
    interpretation ToCT: "functor" CCC.comp C T.ToCT
      using T.functor_ToCT by auto

    interpretation \<alpha>: transformation_by_components CCC.comp C T.ToTC T.ToCT
                        \<open>\<lambda>abc. assoc (fst abc) (fst (snd abc)) (snd (snd abc))\<close>
    proof
      show "\<And>abc. CCC.ide abc \<Longrightarrow>
                     \<guillemotleft>assoc (fst abc) (fst (snd abc)) (snd (snd abc)) : T.ToTC abc \<rightarrow> T.ToCT abc\<guillemotright>"
        using CCC.ide_char CC.ide_char CCC.arr_char CC.arr_char T.ToTC_def T.ToCT_def
        by auto
      show "\<And>f. CCC.arr f \<Longrightarrow>
                  assoc (fst (CCC.cod f)) (fst (snd (CCC.cod f))) (snd (snd (CCC.cod f)))
                          \<cdot> T.ToTC f =
                  T.ToCT f
                    \<cdot> assoc (fst (CCC.dom f)) (fst (snd (CCC.dom f))) (snd (snd (CCC.dom f)))"
        using CCC.arr_char CC.arr_char CCC.dom_char CCC.cod_char T.ToTC_def T.ToCT_def
              assoc_naturality
        by simp blast
    qed

    interpretation \<alpha>: natural_isomorphism CCC.comp C T.ToTC T.ToCT \<alpha>.map
    proof
      show "\<And>a. CCC.ide a \<Longrightarrow> iso (\<alpha>.map a)"
        using CCC.ide_char CC.ide_char \<alpha>.map_simp_ide inverse_arrows_assoc by auto
    qed

    interpretation L: "functor" C C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close>
      using \<iota>_is_terminal_arr T.fixing_ide_gives_functor_1 by simp
    interpretation L: endofunctor C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close> ..
    interpretation \<l>: transformation_by_components C C
                        \<open>\<lambda>f. Prod (cod \<iota>, f)\<close> map \<open>\<lambda>a. pr0 (cod \<iota>) a\<close>
      using \<iota>_is_terminal_arr
      by unfold_locales auto
    interpretation \<l>: natural_isomorphism C C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close> map \<l>.map
      using \<l>.map_simp_ide inverse_arrows_lunit ide_some_terminal
      by unfold_locales auto
    interpretation L: equivalence_functor C C \<open>\<lambda>f. Prod (cod \<iota>, f)\<close>
      using \<l>.natural_isomorphism_axioms naturally_isomorphic_def
            L.isomorphic_to_identity_is_equivalence
      by blast

    interpretation R: "functor" C C \<open>\<lambda>f. Prod (f, cod \<iota>)\<close>
      using \<iota>_is_terminal_arr T.fixing_ide_gives_functor_2 by simp
    interpretation R: endofunctor C\<open>\<lambda>f. Prod (f, cod \<iota>)\<close> ..
    interpretation \<rho>: transformation_by_components C C
                        \<open>\<lambda>f. Prod (f, cod \<iota>)\<close> map \<open>\<lambda>a. pr1 a (cod \<iota>)\<close>
      using \<iota>_is_terminal_arr
      by unfold_locales auto
    interpretation \<rho>: natural_isomorphism C C \<open>\<lambda>f. Prod (f, cod \<iota>)\<close> map \<rho>.map
      using \<rho>.map_simp_ide inverse_arrows_runit ide_some_terminal
      by unfold_locales auto
    interpretation R: equivalence_functor C C \<open>\<lambda>f. Prod (f, cod \<iota>)\<close>
      using \<rho>.natural_isomorphism_axioms naturally_isomorphic_def
            R.isomorphic_to_identity_is_equivalence
      by blast

    interpretation C: monoidal_category C Prod \<alpha>.map \<iota>
      using ide_some_terminal \<iota>_is_iso pentagon comp_assoc
      by unfold_locales auto

    interpretation \<Omega>: constant_functor C C C.unity
      using C.ide_unity
      by unfold_locales auto

    interpretation \<tau>: natural_transformation C C map \<Omega>.map trm
      using C.unity_def \<Omega>.map_def ide_some_terminal trm_naturality comp_cod_arr trm_in_hom
      apply unfold_locales
      using trm_def
          apply auto[1]
         apply fastforce
        apply fastforce
       apply (metis in_homE trm_eqI trm_in_hom cod_pr0 dom_dom)
      by (metis trm_eqI trm_in_hom dom_dom map_simp)

    interpretation \<Delta>: "functor" C CC.comp Diag
      using functor_Diag by simp
    interpretation \<Pi>o\<Delta>: composite_functor C CC.comp C Diag Prod ..

    interpretation natural_transformation C C map \<open>Prod o Diag\<close> dup
      using dup_is_natural_transformation by simp

    lemma unity_agreement:
    shows "C.unity = \<one>"
      using C.unity_def ide_some_terminal by simp

    lemma assoc_agreement:
    assumes "ide a" and "ide b" and "ide c"
    shows "C.assoc a b c = assoc a b c"
      using assms assoc_def \<alpha>.map_simp_ide by simp

    lemma assoc'_agreement:
    assumes "ide a" and "ide b" and "ide c"
    shows "C.assoc' a b c = assoc' a b c"
      using assms inverse_arrows_assoc inverse_unique by auto

    lemma runit_char_eqn:
    assumes "ide a"
    shows "prod (runit a) \<one> = prod a \<iota> \<cdot> assoc a \<one> \<one>"
      using assms ide_one assoc_def comp_assoc prod_tuple comp_cod_arr
      by (intro pr_joint_monic [of a \<one> "prod (runit a) \<one>" "prod a \<iota> \<cdot> assoc a \<one> \<one>"]) auto

    lemma runit_agreement:
    assumes "ide a"
    shows "runit a = C.runit a"
      using assms unity_agreement assoc_agreement C.runit_char(2) runit_char_eqn
            ide_some_terminal
      by (intro C.runit_eqI) auto

    lemma lunit_char_eqn:
    assumes "ide a"
    shows "prod \<one> (lunit a) = prod \<iota> a \<cdot> assoc' \<one> \<one> a"
    proof (intro pr_joint_monic [of \<one> a "prod \<one> (lunit a)" "prod \<iota> a \<cdot> assoc' \<one> \<one> a"])
      show "seq (lunit a) (local.prod \<one> (lunit a))"
        using assms ide_one by simp
      show "lunit a \<cdot> prod \<one> (lunit a) = lunit a \<cdot> prod \<iota> a \<cdot> assoc' \<one> \<one> a"
        using assms ide_one assoc'_def comp_assoc prod_tuple comp_cod_arr by simp
      show "pr1 \<one> a \<cdot> prod \<one> (lunit a) = pr1 \<one> a \<cdot> prod \<iota> a \<cdot> assoc' \<one> \<one> a"
        using assms ide_one assoc'_def comp_cod_arr prod_tuple pr_naturality
        apply simp
        by (metis trm_eqI cod_pr0 cod_pr1 comp_in_homI' ide_prod pr_simps(1,3-6) pr1_in_hom')
    qed

    lemma lunit_agreement:
    assumes "ide a"
    shows "lunit a = C.lunit a"
      using assms unity_agreement assoc'_agreement C.lunit_char(2) lunit_char_eqn
            ide_some_terminal
      by (intro C.lunit_eqI) auto

    interpretation C: cartesian_monoidal_category C Prod \<alpha>.map \<iota> dup trm
    proof
      show "trm C.unity = C.unity"
        by (simp add: C.unity_def ide_some_terminal trm_one)
      show "\<And>a. ide a \<Longrightarrow> C.runit a \<cdot> C.tensor a \<t>[a] \<cdot> dup a = a"
        using comp_runit_term_dup runit_agreement by simp
      show "\<And>a. ide a \<Longrightarrow> C.lunit a \<cdot> C.tensor \<t>[a] a \<cdot> dup a = a"
        using comp_lunit_term_dup lunit_agreement by auto
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk>
                     \<Longrightarrow> C.tensor (C.runit a \<cdot> C.tensor a \<t>[b])
                                  (C.lunit b \<cdot> C.tensor \<t>[a] b) \<cdot> dup (C.tensor a b) =
                         C.tensor a b"
      proof -
        fix a b
        assume a: "ide a" and b: "ide b"
        have "C.tensor (C.runit a \<cdot> C.tensor a \<t>[b])
                       (C.lunit b \<cdot> C.tensor \<t>[a] b) \<cdot> dup (C.tensor a b) =
              prod (C.runit a \<cdot> prod a \<t>[b]) (C.lunit b \<cdot> prod \<t>[a] b) \<cdot> dup (prod a b)"
          using a b by simp
        also have "... = tuple ((C.runit a \<cdot> prod a \<t>[b]) \<cdot> prod a b)
                               ((C.lunit b \<cdot> prod \<t>[a] b) \<cdot> prod a b)"
          using a b ide_one trm_in_hom [of a] trm_in_hom [of b] unity_agreement prod_tuple
          by fastforce
        also have "... = tuple (C.runit a \<cdot> prod a \<t>[b] \<cdot> prod a b)
                               (C.lunit b \<cdot> prod \<t>[a] b \<cdot> prod a b)"
          using comp_assoc by simp
        also have "... = tuple (C.runit a \<cdot> prod a \<t>[b]) (C.lunit b \<cdot> prod \<t>[a] b)"
          using a b comp_arr_dom by simp
        also have "... = tuple (runit a \<cdot> prod a \<t>[b]) (lunit b \<cdot> prod \<t>[a] b)"
          using a b lunit_agreement runit_agreement by simp
        also have "... = tuple (pr1 a b) (pr0 a b)"
        proof -
          have "runit a \<cdot> prod a \<t>[b] = pr1 a b"
            using a b pr_naturality(2) trm_in_hom [of b]
            by (metis cod_pr1 comp_ide_arr ide_char in_homE pr_simps(4,6) seqI)
          moreover have "lunit b \<cdot> prod \<t>[a] b = pr0 a b"
            using a b pr_naturality(1) [of b b b "\<t>[a]" a \<one>] trm_in_hom [of a] comp_cod_arr
            by (metis cod_pr0 ide_char in_homE pr_simps(1))
          ultimately show ?thesis by simp
        qed
        also have "... = prod a b"
          using a b by simp
        finally show "C.tensor (C.runit a \<cdot> C.tensor a \<t>[b])
                               (C.lunit b \<cdot> C.tensor \<t>[a] b) \<cdot> dup (C.tensor a b) =
                      C.tensor a b"
          by auto
      qed
    qed

    lemma extends_to_cartesian_monoidal_category:
    shows "cartesian_monoidal_category C Prod \<alpha>.map \<iota> dup trm"
      ..

  end

  text \<open>
    In a \<open>cartesian_monoidal_category\<close>, the monoidal structure is given by a categorical product
    and terminal object, so that the underlying category is cartesian.
  \<close>

  context cartesian_monoidal_category
  begin

    definition pr0                        ("\<p>\<^sub>0[_, _]")
    where "\<p>\<^sub>0[a, b] \<equiv> if ide a \<and> ide b then \<r>[a] \<cdot> (a \<otimes> \<t>[b]) else null"

    definition pr1                        ("\<p>\<^sub>1[_, _]")
    where "\<p>\<^sub>1[a, b] \<equiv> if ide a \<and> ide b then \<l>[b] \<cdot> (\<t>[a] \<otimes> b) else null"

    lemma pr_in_hom [intro]:
    assumes "ide a0" and "ide a1"
    shows "\<guillemotleft>\<p>\<^sub>0[a0, a1] : a0 \<otimes> a1 \<rightarrow> a0\<guillemotright>"
    and "\<guillemotleft>\<p>\<^sub>1[a0, a1] : a0 \<otimes> a1 \<rightarrow> a1\<guillemotright>"
    proof -
      show "\<guillemotleft>\<p>\<^sub>0[a0, a1] : a0 \<otimes> a1 \<rightarrow> a0\<guillemotright>"
        unfolding pr0_def
        using assms runit_in_hom by fastforce
      show "\<guillemotleft>\<p>\<^sub>1[a0, a1] : a0 \<otimes> a1 \<rightarrow> a1\<guillemotright>"
        unfolding pr1_def
        using assms lunit_in_hom by fastforce
    qed

    lemma pr_simps [simp]:
    assumes "ide a0" and "ide a1"
    shows "arr \<p>\<^sub>0[a0, a1]" and "dom \<p>\<^sub>0[a0, a1] = a0 \<otimes> a1" and "cod \<p>\<^sub>0[a0, a1] = a0"
    and "arr \<p>\<^sub>1[a0, a1]" and "dom \<p>\<^sub>1[a0, a1] = a0 \<otimes> a1" and "cod \<p>\<^sub>1[a0, a1] = a1"
      using assms pr_in_hom(1-2) by blast+

    interpretation P: composite_functor CC.comp C CC.comp T \<Delta>.map ..

    interpretation ECC: elementary_cartesian_category C pr1 pr0 \<I> \<tau>
    proof
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> span \<p>\<^sub>0[a, b] \<p>\<^sub>1[a, b]"
        by simp
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> cod \<p>\<^sub>1[a, b] = b"
        by simp
      show "\<And>a b. \<lbrakk>ide a; ide b\<rbrakk> \<Longrightarrow> cod \<p>\<^sub>0[a, b] = a"
        by simp
      show "ide \<I>"
        by simp
      show "\<And>a. ide a \<Longrightarrow> \<guillemotleft>\<tau> a : a \<rightarrow> \<I>\<guillemotright>"
        by auto
      show "\<And>a f. \<lbrakk>ide a; \<guillemotleft>f : a \<rightarrow> \<I>\<guillemotright>\<rbrakk> \<Longrightarrow> f = \<t>[a]"
        using \<open>\<And>a. ide a \<Longrightarrow> \<guillemotleft>\<t>[a] : a \<rightarrow> \<I>\<guillemotright>\<close> terminalE terminal_unity by blast
      show "\<And>a b. \<not> (ide a \<and> ide b) \<Longrightarrow> \<p>\<^sub>1[a, b] = null"
        using pr1_def by auto
      show "\<And>a b. \<not> (ide a \<and> ide b) \<Longrightarrow> \<p>\<^sub>0[a, b] = null"
        using pr0_def by auto
      show "\<And>f g. span f g \<Longrightarrow> \<exists>!l. \<p>\<^sub>0[cod f, cod g] \<cdot> l = f \<and> \<p>\<^sub>1[cod f, cod g] \<cdot> l = g"
      proof -
        fix f g
        assume fg: "span f g"
        let ?l = "(f \<otimes> g) \<cdot> \<d>[dom f]"
        have "\<p>\<^sub>0[cod f, cod g] \<cdot> ?l = f"
        proof -
          have "\<p>\<^sub>0[cod f, cod g] \<cdot> ?l = (\<r>[cod f] \<cdot> (cod f \<otimes> \<t>[cod g])) \<cdot> (f \<otimes> g) \<cdot> \<d>[dom f]"
            using fg pr0_def by simp
          also have "... = \<r>[cod f] \<cdot> ((cod f \<otimes> \<t>[cod g]) \<cdot> (f \<otimes> g)) \<cdot> \<d>[dom f]"
            using comp_assoc by simp
          also have "... = \<r>[cod f] \<cdot> (f \<otimes> \<t>[dom f]) \<cdot> \<d>[dom f]"
            using fg interchange comp_cod_arr \<tau>.naturality by simp
          also have "... = \<r>[cod f] \<cdot> ((cod f \<otimes> \<t>[cod f]) \<cdot> (f \<otimes> f)) \<cdot> \<d>[dom f]"
            using fg interchange comp_cod_arr \<tau>.naturality by simp
          also have "... = \<r>[cod f] \<cdot> (cod f \<otimes> \<t>[cod f]) \<cdot> (f \<otimes> f) \<cdot> \<d>[dom f]"
            using comp_assoc by simp
          also have "... = (\<r>[cod f] \<cdot> (cod f \<otimes> \<t>[cod f]) \<cdot> \<d>[cod f]) \<cdot> f"
            using fg \<delta>.naturality comp_assoc by simp
          also have "... = f"
            using fg pr0_dup comp_cod_arr by simp
          finally show ?thesis by blast
        qed
        moreover have "\<p>\<^sub>1[cod f, cod g] \<cdot> ?l = g"
        proof -
          have "\<p>\<^sub>1[cod f, cod g] \<cdot> ?l = \<l>[cod g] \<cdot> ((\<t>[cod f] \<otimes> cod g) \<cdot> (f \<otimes> g)) \<cdot> \<d>[dom g]"
            using fg pr1_def comp_assoc by simp
          also have "... = \<l>[cod g] \<cdot> (\<t>[dom f] \<otimes> g) \<cdot> \<d>[dom g]"
            using fg interchange comp_cod_arr \<tau>.naturality
            by simp
          also have "... = \<l>[cod g] \<cdot> ((\<t>[cod g] \<otimes> cod g) \<cdot> (g \<otimes> g)) \<cdot> \<d>[dom g]"
            using fg interchange comp_cod_arr \<tau>.naturality by simp
          also have "... = \<l>[cod g] \<cdot> (\<t>[cod g] \<otimes> cod g) \<cdot> (g \<otimes> g) \<cdot> \<d>[dom g]"
            using comp_assoc by simp
          also have "... = (\<l>[cod g] \<cdot> (\<t>[cod g] \<otimes> cod g) \<cdot> \<d>[cod g]) \<cdot> g"
            using fg \<delta>.naturality comp_assoc by simp
          also have "... = g"
            using fg pr1_dup comp_cod_arr by simp
          finally show ?thesis by blast
        qed
        moreover have "\<And>l. \<lbrakk> \<p>\<^sub>0[cod f, cod g] \<cdot> l = f; \<p>\<^sub>1[cod f, cod g] \<cdot> l = g \<rbrakk> \<Longrightarrow> l = ?l"
        proof -
          fix l
          assume f: "\<p>\<^sub>0[cod f, cod g] \<cdot> l = f" and g: "\<p>\<^sub>1[cod f, cod g] \<cdot> l = g"
          have l: "\<guillemotleft>l : dom f \<rightarrow> cod f \<otimes> cod g\<guillemotright>"
            using f g fg
            by (metis arr_iff_in_hom dom_comp ide_cod pr_simps(5) seqE)
          have "?l = (\<p>\<^sub>0[cod f, cod g] \<cdot> l \<otimes> \<p>\<^sub>1[cod f, cod g] \<cdot> l) \<cdot> \<d>[dom f]"
            using f g by simp
          also have "... = ((\<p>\<^sub>0[cod f, cod g] \<otimes> \<p>\<^sub>1[cod f, cod g]) \<cdot> (l \<otimes> l)) \<cdot> \<d>[dom f]"
            using fg f g interchange by simp
          also have "... = (\<p>\<^sub>0[cod f, cod g] \<otimes> \<p>\<^sub>1[cod f, cod g]) \<cdot> (l \<otimes> l) \<cdot> \<d>[dom f]"
            using comp_assoc by simp
          also have "... = ((\<p>\<^sub>0[cod f, cod g] \<otimes> \<p>\<^sub>1[cod f, cod g]) \<cdot> \<d>[cod f \<otimes> cod g]) \<cdot> l"
            using l \<delta>.naturality [of l] comp_assoc by auto
          also have "... = (cod f \<otimes> cod g) \<cdot> l"
            using f g fg tuple_pr pr0_def pr1_def by auto
          also have "... = l"
            using l comp_cod_arr by auto
          finally show "l = ?l" by simp
        qed
        ultimately show "\<exists>!l. \<p>\<^sub>0[cod f, cod g] \<cdot> l = f \<and> \<p>\<^sub>1[cod f, cod g] \<cdot> l = g"
          by auto
      qed
    qed

    lemma extends_to_elementary_cartesian_category:
    shows "elementary_cartesian_category C pr1 pr0 \<I> \<tau>"
      ..

    lemma is_cartesian_category:
    shows "cartesian_category C"
      using ECC.is_cartesian_category by simp

  end

  (*
   * TODO: I would like to have coherence theorems for symmetric monoidal and cartesian
   * monoidal categories here, but I haven't yet figured out a suitably economical way
   * to extend the existing result.
   *)

end

