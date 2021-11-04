(*  Title:       Functor
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter Functor

theory Functor
imports Category ConcreteCategory DualCategory InitialTerminal
begin

  text\<open>
    One advantage of the ``object-free'' definition of category is that a functor
    from category \<open>A\<close> to category \<open>B\<close> is simply a function from the type
    of arrows of \<open>A\<close> to the type of arrows of \<open>B\<close> that satisfies certain
    conditions: namely, that arrows are mapped to arrows, non-arrows are mapped to
    \<open>null\<close>, and domains, codomains, and composition of arrows are preserved.
\<close>

  locale "functor" =
    A: category A +
    B: category B
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_extensional: "\<not>A.arr f \<Longrightarrow> F f = B.null"
  and preserves_arr: "A.arr f \<Longrightarrow> B.arr (F f)"
  and preserves_dom [iff]: "A.arr f \<Longrightarrow> B.dom (F f) = F (A.dom f)"
  and preserves_cod [iff]: "A.arr f \<Longrightarrow> B.cod (F f) = F (A.cod f)"
  and preserves_comp [iff]: "A.seq g f \<Longrightarrow> F (g \<cdot>\<^sub>A f) = F g \<cdot>\<^sub>B F f"
  begin

    notation A.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>A _\<guillemotright>")
    notation B.in_hom     ("\<guillemotleft>_ : _ \<rightarrow>\<^sub>B _\<guillemotright>")

    lemma preserves_hom [intro]:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>A b\<guillemotright>"
    shows "\<guillemotleft>F f : F a \<rightarrow>\<^sub>B F b\<guillemotright>"
      using assms B.in_homI
      by (metis A.in_homE preserves_arr preserves_cod preserves_dom)

    text\<open>
      The following, which is made possible through the presence of \<open>null\<close>,
      allows us to infer that the subterm @{term f} denotes an arrow if the
      term @{term "F f"} denotes an arrow.  This is very useful, because otherwise
      doing anything with @{term f} would require a separate proof that it is an arrow
      by some other means.
\<close>

    lemma preserves_reflects_arr [iff]:
    shows "B.arr (F f) \<longleftrightarrow> A.arr f"
      using preserves_arr is_extensional B.not_arr_null by metis

    lemma preserves_seq [intro]:
    assumes "A.seq g f"
    shows "B.seq (F g) (F f)"
      using assms by auto

    lemma preserves_ide [simp]:
    assumes "A.ide a"
    shows "B.ide (F a)"
      using assms A.ide_in_hom B.ide_in_hom by auto

    lemma preserves_iso [simp]:
    assumes "A.iso f"
    shows "B.iso (F f)"
      using assms A.inverse_arrowsE
      apply (elim A.isoE A.inverse_arrowsE A.seqE A.ide_compE)
      by (metis A.arr_dom_iff_arr B.ide_dom B.inverse_arrows_def B.isoI preserves_arr
                preserves_comp preserves_dom)

    lemma preserves_section_retraction:
    assumes "A.ide (A e m)"
    shows "B.ide (B (F e) (F m))"
      using assms by (metis A.ide_compE preserves_comp preserves_ide)

    lemma preserves_section:
    assumes "A.section m"
    shows "B.section (F m)"
      using assms preserves_section_retraction by blast

    lemma preserves_retraction:
    assumes "A.retraction e"
    shows "B.retraction (F e)"
      using assms preserves_section_retraction by blast

    lemma preserves_inverse_arrows:
    assumes "A.inverse_arrows f g"
    shows "B.inverse_arrows (F f) (F g)"
      using assms A.inverse_arrows_def B.inverse_arrows_def preserves_section_retraction
      by simp

    lemma preserves_inv:
    assumes "A.iso f"
    shows "F (A.inv f) = B.inv (F f)"
      using assms preserves_inverse_arrows A.inv_is_inverse B.inv_is_inverse
            B.inverse_arrow_unique
      by blast

    lemma preserves_iso_in_hom [intro]:
    assumes "A.iso_in_hom f a b"
    shows "B.iso_in_hom (F f) (F a) (F b)"
      using assms preserves_hom preserves_iso by blast

  end

  locale endofunctor =
    "functor" A A F
  for A :: "'a comp"     (infixr "\<cdot>" 55)
  and F :: "'a \<Rightarrow> 'a"

  locale faithful_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_faithful: "\<lbrakk> A.par f f'; F f = F f' \<rbrakk> \<Longrightarrow> f = f'"
  begin

    lemma locally_reflects_ide:
    assumes "\<guillemotleft>f : a \<rightarrow>\<^sub>A a\<guillemotright>" and "B.ide (F f)"
    shows "A.ide f"
      using assms is_faithful
      by (metis A.arr_dom_iff_arr A.cod_dom A.dom_dom A.in_homE B.comp_ide_self
          B.ide_self_inverse B.comp_arr_inv A.ide_cod preserves_dom)

  end

  locale full_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_full: "\<lbrakk> A.ide a; A.ide a'; \<guillemotleft>g : F a' \<rightarrow>\<^sub>B F a\<guillemotright> \<rbrakk> \<Longrightarrow> \<exists>f. \<guillemotleft>f : a' \<rightarrow>\<^sub>A a\<guillemotright> \<and> F f = g"

  locale fully_faithful_functor =
    faithful_functor A B F +
    full_functor A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"
  begin

    lemma reflects_iso:
    assumes "\<guillemotleft>f : a' \<rightarrow>\<^sub>A a\<guillemotright>" and "B.iso (F f)"
    shows "A.iso f"
    proof -
      from assms obtain g' where g': "B.inverse_arrows (F f) g'" by blast
      have 1: "\<guillemotleft>g' : F a \<rightarrow>\<^sub>B F a'\<guillemotright>"
        using assms g' by (metis B.inv_in_hom B.inverse_unique preserves_hom)
      from this obtain g where g: "\<guillemotleft>g : a \<rightarrow>\<^sub>A a'\<guillemotright> \<and> F g = g'"
        using assms(1) is_full by (metis A.arrI A.ide_cod A.ide_dom A.in_homE)
      have "A.inverse_arrows f g"
        using assms 1 g g' A.inverse_arrowsI
        by (metis A.arr_iff_in_hom A.dom_comp A.in_homE A.seqI' B.inverse_arrowsE
            A.cod_comp locally_reflects_ide preserves_comp)
      thus ?thesis by auto
    qed

    lemma reflects_isomorphic:
    assumes "A.ide f" and "A.ide f'" and "B.isomorphic (F f) (F f')"
    shows "A.isomorphic f f'"
    proof -
      obtain \<psi> where \<psi>: "B.in_hom \<psi> (F f) (F f') \<and> B.iso \<psi>"
        using assms B.isomorphic_def by auto
      obtain \<phi> where \<phi>: "A.in_hom \<phi> f f' \<and> F \<phi> = \<psi>"
        using assms \<psi> is_full by blast
      have "A.iso \<phi>"
        using \<phi> \<psi> reflects_iso by auto
      thus ?thesis
        using \<phi> A.isomorphic_def by auto
    qed

  end

  locale embedding_functor = "functor" A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b" +
  assumes is_embedding: "\<lbrakk> A.arr f; A.arr f'; F f = F f' \<rbrakk> \<Longrightarrow> f = f'"

  sublocale embedding_functor \<subseteq> faithful_functor
    using is_embedding by (unfold_locales, blast)

  context embedding_functor
  begin

    lemma reflects_ide:
    assumes "B.ide (F f)"
    shows "A.ide f"
      using assms is_embedding A.ide_in_hom B.ide_in_hom
      by (metis A.in_homE B.in_homE A.ide_cod preserves_cod preserves_reflects_arr)

  end

  locale full_embedding_functor =
    embedding_functor A B F +
    full_functor A B F
  for A :: "'a comp"
  and B :: "'b comp"
  and F :: "'a \<Rightarrow> 'b"

  locale essentially_surjective_functor = "functor" +
  assumes essentially_surjective: "\<And>b. B.ide b \<Longrightarrow> \<exists>a. A.ide a \<and> B.isomorphic (F a) b"

  locale constant_functor =
    A: category A +
    B: category B
  for A :: "'a comp"
  and B :: "'b comp"
  and b :: 'b +
  assumes value_is_ide: "B.ide b"
  begin

    definition map
    where "map f = (if A.arr f then b else B.null)"

    lemma map_simp [simp]:
    assumes "A.arr f"
    shows "map f = b"
      using assms map_def by auto

    lemma is_functor:
    shows "functor A B map"
      using map_def value_is_ide by (unfold_locales, auto)
      
  end

  sublocale constant_functor \<subseteq> "functor" A B map
    using is_functor by auto

  locale identity_functor =
    C: category C
    for C :: "'a comp"
  begin

    definition map :: "'a \<Rightarrow> 'a"
    where "map f = (if C.arr f then f else C.null)"

    lemma map_simp [simp]:
    assumes "C.arr f"
    shows "map f = f"
      using assms map_def by simp

    lemma is_functor:
    shows "functor C C map"
      using C.arr_dom_iff_arr C.arr_cod_iff_arr
      by (unfold_locales; auto simp add: map_def)

  end

  sublocale identity_functor \<subseteq> "functor" C C map
    using is_functor by auto

  text \<open>
    It is convenient to have an easy way to obtain from a category the identity functor
    on that category. The following declaration causes the definitions and facts from the
    @{locale identity_functor} locale to be inherited by the @{locale category} locale,
    including the function @{term map} on arrows that represents the identity functor.
    This makes it generally unnecessary to give explicit interpretations of
    @{locale identity_functor}.
\<close>

  sublocale category \<subseteq> identity_functor C ..

  text\<open>
    Composition of functors coincides with function composition, thanks to the
    magic of \<open>null\<close>.
\<close>

  lemma functor_comp:
  assumes "functor A B F" and "functor B C G"
  shows "functor A C (G o F)"
  proof -
    interpret F: "functor" A B F using assms(1) by auto
    interpret G: "functor" B C G using assms(2) by auto
    show "functor A C (G o F)"
      using F.preserves_arr F.is_extensional G.is_extensional by (unfold_locales, auto)
  qed

  locale composite_functor =
    F: "functor" A B F +
    G: "functor" B C G
  for A :: "'a comp"
  and B :: "'b comp"
  and C :: "'c comp"
  and F :: "'a \<Rightarrow> 'b"
  and G :: "'b \<Rightarrow> 'c"
  begin

    abbreviation map
    where "map \<equiv> G o F"

  end

  sublocale composite_functor \<subseteq> "functor" A C \<open>G o F\<close>
    using functor_comp F.functor_axioms G.functor_axioms by blast

  lemma comp_functor_identity [simp]:
  assumes "functor A B F"
  shows "F o identity_functor.map A = F"
  proof
    interpret "functor" A B F using assms by blast
    show "\<And>x. (F o A.map) x = F x"
      using A.map_def is_extensional by simp
  qed

  lemma comp_identity_functor [simp]:
  assumes "functor A B F"
  shows "identity_functor.map B o F = F"
  proof
    interpret "functor" A B F using assms by blast
    show "\<And>x. (B.map o F) x = F x"
      using B.map_def by (metis comp_apply is_extensional preserves_arr)
  qed

  lemma faithful_functors_compose:
  assumes "faithful_functor A B F" and "faithful_functor B C G"
  shows "faithful_functor A C (G o F)"
  proof -
    interpret F: faithful_functor A B F
      using assms(1) by simp
    interpret G: faithful_functor B C G
      using assms(2) by simp
    interpret composite_functor A B C F G ..
    show "faithful_functor A C (G o F)"
    proof
      show "\<And>f f'. \<lbrakk>F.A.par f f'; map f = map f'\<rbrakk> \<Longrightarrow> f = f'"
        using F.is_faithful G.is_faithful
        by (metis (mono_tags, lifting) F.preserves_arr F.preserves_cod F.preserves_dom o_apply)
    qed
  qed

  lemma full_functors_compose:
  assumes "full_functor A B F" and "full_functor B C G"
  shows "full_functor A C (G o F)"
  proof -
    interpret F: full_functor A B F
      using assms(1) by simp
    interpret G: full_functor B C G
      using assms(2) by simp
    interpret composite_functor A B C F G ..
    show "full_functor A C (G o F)"
    proof
      show "\<And>a a' g. \<lbrakk>F.A.ide a; F.A.ide a'; \<guillemotleft>g : map a' \<rightarrow> map a\<guillemotright>\<rbrakk>
                        \<Longrightarrow> \<exists>f. F.A.in_hom f a' a \<and> map f = g"
        using F.is_full G.is_full
        by (metis F.preserves_ide o_apply)
    qed
  qed

  lemma fully_faithful_functors_compose:
  assumes "fully_faithful_functor A B F" and "fully_faithful_functor B C G"
  shows "full_functor A C (G o F)"
  proof -
    interpret F: fully_faithful_functor A B F
      using assms(1) by simp
    interpret G: fully_faithful_functor B C G
      using assms(2) by simp
    interpret composite_functor A B C F G ..
    interpret faithful_functor A C \<open>G o F\<close>
      using F.faithful_functor_axioms G.faithful_functor_axioms faithful_functors_compose
      by blast
    interpret full_functor A C \<open>G o F\<close>
      using F.full_functor_axioms G.full_functor_axioms full_functors_compose
      by blast
    show "full_functor A C (G o F)" ..
  qed

  lemma embedding_functors_compose:
  assumes "embedding_functor A B F" and "embedding_functor B C G"
  shows "embedding_functor A C (G o F)"
  proof -
    interpret F: embedding_functor A B F
      using assms(1) by simp
    interpret G: embedding_functor B C G
      using assms(2) by simp
    interpret composite_functor A B C F G ..
    show "embedding_functor A C (G o F)"
    proof
      show "\<And>f f'. \<lbrakk>F.A.arr f; F.A.arr f'; map f = map f'\<rbrakk> \<Longrightarrow> f = f'"
        by (simp add: F.is_embedding G.is_embedding)
    qed
  qed

  lemma full_embedding_functors_compose:
  assumes "full_embedding_functor A B F" and "full_embedding_functor B C G"
  shows "full_embedding_functor A C (G o F)"
  proof -
    interpret F: full_embedding_functor A B F
      using assms(1) by simp
    interpret G: full_embedding_functor B C G
      using assms(2) by simp
    interpret composite_functor A B C F G ..
    interpret embedding_functor A C \<open>G o F\<close>
      using F.embedding_functor_axioms G.embedding_functor_axioms embedding_functors_compose
      by blast
    interpret full_functor A C \<open>G o F\<close>
      using F.full_functor_axioms G.full_functor_axioms full_functors_compose
      by blast
    show "full_embedding_functor A C (G o F)" ..
  qed

  lemma essentially_surjective_functors_compose:
  assumes "essentially_surjective_functor A B F" and "essentially_surjective_functor B C G"
  shows "essentially_surjective_functor A C (G o F)"
  proof -
    interpret F: essentially_surjective_functor A B F
      using assms(1) by simp
    interpret G: essentially_surjective_functor B C G
      using assms(2) by simp
    interpret composite_functor A B C F G ..
    show "essentially_surjective_functor A C (G o F)"
    proof
      show "\<And>c. G.B.ide c \<Longrightarrow> \<exists>a. F.A.ide a \<and> G.B.isomorphic (map a) c"
      proof -
        fix c
        assume c: "G.B.ide c"
        obtain b where b: "F.B.ide b \<and> G.B.isomorphic (G b) c"
          using c G.essentially_surjective by auto
        obtain a where a: "F.A.ide a \<and> F.B.isomorphic (F a) b"
          using b F.essentially_surjective by auto
        have "G.B.isomorphic (map a) c"
        proof -
          have "G.B.isomorphic (G (F a)) (G b)"
            using a G.preserves_iso G.B.isomorphic_def by blast
          thus ?thesis
            using b G.B.isomorphic_transitive by auto
        qed
        thus "\<exists>a. F.A.ide a \<and> G.B.isomorphic (map a) c"
          using a by auto
      qed
    qed
  qed

  locale inverse_functors =
    A: category A +
    B: category B +
    F: "functor" B A F +
    G: "functor" A B G
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'b \<Rightarrow> 'a"
  and G :: "'a \<Rightarrow> 'b" +
  assumes inv: "G o F = identity_functor.map B"
  and inv': "F o G = identity_functor.map A"
  begin

    lemma bij_betw_arr_sets:
    shows "bij_betw F (Collect B.arr) (Collect A.arr)"
      using inv inv'
      apply (intro bij_betwI)
         apply auto
      using comp_eq_dest_lhs by force+

  end

  locale isomorphic_categories =
    A: category A +
    B: category B
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55) +
  assumes iso: "\<exists>F G. inverse_functors A B F G"

  sublocale inverse_functors \<subseteq> isomorphic_categories A B
    using inverse_functors_axioms by (unfold_locales, auto)
  
  lemma inverse_functors_sym:
  assumes "inverse_functors A B F G"
  shows "inverse_functors B A G F"
  proof -
    interpret inverse_functors A B F G using assms by auto
    show ?thesis using inv inv' by (unfold_locales, auto)
  qed
  
  text \<open>
    Inverse functors uniquely determine each other.
\<close>

  lemma inverse_functor_unique:
  assumes "inverse_functors C D F G" and "inverse_functors C D F G'"
  shows "G = G'"
  proof -
    interpret FG: inverse_functors C D F G using assms(1) by auto
    interpret FG': inverse_functors C D F G' using assms(2) by auto
    show "G = G'"
      using FG.G.is_extensional FG'.G.is_extensional FG'.inv FG.inv'
      by (metis FG'.G.functor_axioms FG.G.functor_axioms comp_assoc comp_identity_functor
                comp_functor_identity)
  qed

  lemma inverse_functor_unique':
  assumes "inverse_functors C D F G" and "inverse_functors C D F' G"
  shows "F = F'"
    using assms inverse_functors_sym inverse_functor_unique by blast

  locale invertible_functor =
    A: category A +
    B: category B +
    G: "functor" A B G
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and G :: "'a \<Rightarrow> 'b" +
  assumes invertible: "\<exists>F. inverse_functors A B F G"
  begin

    lemma has_unique_inverse:
    shows "\<exists>!F. inverse_functors A B F G"
      using invertible inverse_functor_unique' by blast

    definition inv
    where "inv \<equiv> THE F. inverse_functors A B F G"

    interpretation inverse_functors A B inv G
      using inv_def has_unique_inverse theI' [of "\<lambda>F. inverse_functors A B F G"]
      by simp

    lemma inv_is_inverse:
    shows "inverse_functors A B inv G" ..
  
    lemma preserves_terminal:
    assumes "A.terminal a"
    shows "B.terminal (G a)"
    proof
      show 0: "B.ide (G a)" using assms G.preserves_ide A.terminal_def by blast
      fix b :: 'b
      assume b: "B.ide b"
      show "\<exists>!g. \<guillemotleft>g : b \<rightarrow>\<^sub>B G a\<guillemotright>"
      proof
        let ?F = "SOME F. inverse_functors A B F G"
        from invertible have F: "inverse_functors A B ?F G"
          using someI_ex [of "\<lambda>F. inverse_functors A B F G"] by fast
        interpret inverse_functors A B ?F G using F by auto
        let ?P = "\<lambda>f. \<guillemotleft>f : ?F b \<rightarrow>\<^sub>A a\<guillemotright>"
        have 1: "\<exists>!f. ?P f" using assms b A.terminal_def by simp
        hence 2: "?P (THE f. ?P f)" by (metis (no_types, lifting) theI')
        thus "\<guillemotleft>G (THE f. ?P f) : b \<rightarrow>\<^sub>B G a\<guillemotright>"
          using b apply (elim A.in_homE, intro B.in_homI, auto)
          using B.ideD(1) B.map_simp comp_def inv by metis
        hence 3: "\<guillemotleft>(THE f. ?P f) : ?F b \<rightarrow>\<^sub>A a\<guillemotright>"
          using assms 2 b F by simp
        fix g :: 'b
        assume g: "\<guillemotleft>g : b \<rightarrow>\<^sub>B G a\<guillemotright>"
        have "?F (G a) = a"
          using assms(1) A.terminal_def inv' A.map_simp
          by (metis 0 B.ideD(1) G.preserves_reflects_arr comp_eq_dest_lhs)
        hence "\<guillemotleft>?F g : ?F b \<rightarrow>\<^sub>A a\<guillemotright>"
          using assms(1) g A.terminal_def inv
          by (elim B.in_homE, auto)
        hence "?F g = (THE f. ?P f)" using assms 1 3 A.terminal_def by blast
        thus "g = G (THE f. ?P f)"
          using inv g by (metis B.in_homE B.map_simp comp_def)
      qed
    qed
  
  end

  sublocale invertible_functor \<subseteq> inverse_functors A B inv G
    using inv_is_inverse by simp

  text \<open>
    A bijection from a set \<open>S\<close> to the set of arrows of a category \<open>C\<close> induces an isomorphic
    copy of \<open>C\<close> having \<open>S\<close> as its set of arrows, assuming that there exists some \<open>n \<notin> S\<close>
    to serve as the null.
  \<close>

  context category
  begin

    lemma bij_induces_invertible_functor:
    assumes "bij_betw \<phi> S (Collect arr)" and "n \<notin> S"
    shows "\<exists>C'. Collect (partial_magma.arr C') = S \<and>
                invertible_functor C' C (\<lambda>i. if partial_magma.arr C' i then \<phi> i else null)"
    proof -
      define \<psi> where "\<psi> = (\<lambda>f. if arr f then inv_into S \<phi> f else n)"
      have \<psi>: "bij_betw \<psi> (Collect arr) S"
        using assms(1) \<psi>_def bij_betw_inv_into
        by (metis (no_types, lifting) bij_betw_cong mem_Collect_eq)
      have \<phi>_\<psi> [simp]: "\<And>f. arr f \<Longrightarrow> \<phi> (\<psi> f) = f"
        using assms(1) \<psi> \<psi>_def bij_betw_inv_into_right by fastforce
      have \<psi>_\<phi> [simp]: "\<And>i. i \<in> S \<Longrightarrow> \<psi> (\<phi> i) = i"
        unfolding \<psi>_def
        using assms(1) \<psi> bij_betw_inv_into_left [of \<phi> S "Collect arr"]
        by (metis bij_betw_def image_eqI mem_Collect_eq)
      define C' where "C' = (\<lambda>i j. if i \<in> S \<and> j \<in> S \<and> seq (\<phi> i) (\<phi> j) then \<psi> (\<phi> i \<cdot> \<phi> j) else n)"
      interpret C': partial_magma C'
        using assms(1-2) C'_def \<psi>_def
        by unfold_locales metis
      have null_char: "C'.null = n"
        using assms(1-2) C'_def \<psi>_def C'.null_eqI by metis
      have ide_char: "\<And>i. C'.ide i \<longleftrightarrow> i \<in> S \<and> ide (\<phi> i)"
      proof
        fix i
        assume i: "C'.ide i"
        show "i \<in> S \<and> ide (\<phi> i)"
        proof (unfold ide_def, intro conjI)
          show 1: "\<phi> i \<cdot> \<phi> i \<noteq> null"
            using i assms(1) C'.ide_def C'_def null_char by auto
          show 2: "i \<in> S"
            using 1 assms(1) by (metis C'.ide_def C'_def i)
          show "\<forall>f. (f \<cdot> \<phi> i \<noteq> null \<longrightarrow> f \<cdot> \<phi> i = f) \<and> (\<phi> i \<cdot> f \<noteq> null \<longrightarrow> \<phi> i \<cdot> f = f)"
          proof (intro allI conjI impI)
            show "\<And>f. f \<cdot> \<phi> i \<noteq> null \<Longrightarrow> f \<cdot> \<phi> i = f"
            proof -
              fix f
              assume f: "f \<cdot> \<phi> i \<noteq> null"
              hence 1: "arr f \<and> arr (\<phi> i) \<and> seq f (\<phi> i)"
                by (meson seqE ext)
              have "f \<cdot> \<phi> i = \<phi> (C' (\<psi> f) i)"
                using 1 2 C'_def null_char
                by (metis (no_types, lifting) \<phi>_\<psi> \<psi> bij_betw_def image_eqI mem_Collect_eq)
              also have "... = f"
                by (metis 1 C'.ide_def C'_def \<phi>_\<psi> \<psi> assms(2) bij_betw_def i image_eqI
                    mem_Collect_eq null_char)
              finally show "f \<cdot> \<phi> i = f" by simp
            qed
            show "\<And>f. \<phi> i \<cdot> f \<noteq> null \<Longrightarrow> \<phi> i \<cdot> f = f"
            proof -
              fix f
              assume f: "\<phi> i \<cdot> f \<noteq> null"
              hence 1: "arr f \<and> arr (\<phi> i) \<and> seq (\<phi> i) f"
                by (meson seqE ext)
              show "\<phi> i \<cdot> f = f"
                using 1 2 C'_def null_char \<psi>
                by (metis (no_types, lifting) \<open>\<And>f. f \<cdot> \<phi> i \<noteq> null \<Longrightarrow> f \<cdot> \<phi> i = f\<close>
                    ide_char' codomains_null comp_cod_arr has_codomain_iff_arr
                    comp_ide_arr)
            qed
          qed
        qed
        next
        fix i
        assume i: "i \<in> S \<and> ide (\<phi> i)"
        have "\<psi> (\<phi> i) \<in> S"
          using i assms(1)
          by (metis \<psi> bij_betw_def ideD(1) image_eqI mem_Collect_eq)
        show "C'.ide i"
          using assms(2) i C'_def null_char comp_arr_ide comp_ide_arr
          apply (unfold C'.ide_def, intro conjI allI impI)
            apply auto[1]
          by force+
      qed
      have dom: "\<And>i. i \<in> S \<Longrightarrow> \<psi> (dom (\<phi> i)) \<in> C'.domains i"
      proof -
        fix i
        assume i: "i \<in> S"
        have 1: "C'.ide (\<psi> (dom (\<phi> i)))"
        proof (unfold C'.ide_def, intro conjI allI impI)
          show "C' (\<psi> (dom (\<phi> i))) (\<psi> (dom (\<phi> i))) \<noteq> C'.null"
          proof -
            have "C' (\<psi> (dom (\<phi> i))) (\<psi> (dom (\<phi> i))) = \<psi> (dom (\<phi> i))"
              using C'_def i assms(1-2) \<psi> \<psi>_\<phi> \<psi>_def bij_betw_def
              by (metis (no_types, lifting) C'.ide_def \<phi>_\<psi> ide_char ide_dom image_eqI
                  mem_Collect_eq)
            moreover have "\<psi> (dom (\<phi> i)) \<noteq> C'.null"
              using i null_char assms(1-2) bij_betw_def
              by (metis \<psi> arr_dom_iff_arr image_iff mem_Collect_eq)
            ultimately show ?thesis
              by simp
          qed
          show "\<And>j. C' j (\<psi> (dom (\<phi> i))) \<noteq> C'.null \<Longrightarrow> C' j (\<psi> (dom (\<phi> i))) = j"
          proof -
            fix j
            assume j: "C' j (\<psi> (dom (\<phi> i))) \<noteq> C'.null"
            show "C' j (\<psi> (dom (\<phi> i))) = j"
              using j \<phi>_\<psi> \<psi>_def ide_char null_char
              by (metis C'.comp_null(2) C'.ide_def C'_def
                  \<open>C' (\<psi> (dom (\<phi> i))) (\<psi> (dom (\<phi> i))) \<noteq> C'.null\<close>
                  arr_dom_iff_arr ide_dom)
          qed
          show "\<And>j. C' (\<psi> (dom (\<phi> i))) j \<noteq> C'.null \<Longrightarrow> C' (\<psi> (dom (\<phi> i))) j = j"
          proof -
            fix j
            assume j: "C' (\<psi> (dom (\<phi> i))) j \<noteq> C'.null"
            show "C' (\<psi> (dom (\<phi> i))) j = j"
              using j
              by (metis C'.ide_def C'_def
                  \<open>C' (\<psi> (dom (\<phi> i))) (\<psi> (dom (\<phi> i))) \<noteq> C'.null\<close>
                  \<open>\<And>j. C' j (\<psi> (dom (\<phi> i))) \<noteq> C'.null \<Longrightarrow> C' j (\<psi> (dom (\<phi> i))) = j\<close>
                  \<phi>_\<psi> \<psi>_def arr_dom_iff_arr ide_char ide_dom null_char)
          qed
        qed
        moreover have "C' i (\<psi> (dom (\<phi> i))) \<noteq> C'.null"
          using i 1 assms(1-2) C'_def null_char ide_char \<phi>_\<psi> \<psi>_\<phi> \<psi>_def comp_arr_dom
          apply simp
          by (metis (no_types, lifting))
        ultimately show "\<psi> (dom (\<phi> i)) \<in> C'.domains i"
          using C'.domains_def by simp
      qed
      have cod: "\<And>i. i \<in> S \<Longrightarrow> \<psi> (cod (\<phi> i)) \<in> C'.codomains i"
      proof -
        fix i
        assume i: "i \<in> S"
        have 1: "C'.ide (\<psi> (cod (\<phi> i)))"
        proof (unfold C'.ide_def, intro conjI allI impI)
          show "C' (\<psi> (cod (\<phi> i))) (\<psi> (cod (\<phi> i))) \<noteq> C'.null"
          proof -
            have "C' (\<psi> (cod (\<phi> i))) (\<psi> (cod (\<phi> i))) = \<psi> (cod (\<phi> i))"
            proof -
              have "\<phi> (\<psi> (cod (\<phi> i))) = cod (\<phi> i)"
                using i assms(1-2) \<phi>_\<psi> \<psi>_\<phi> \<psi>_def arr_cod_iff_arr by force
              moreover have "cod (\<phi> i) \<cdot> cod (\<phi> i) = cod (\<phi> i)"
                using i assms(1-2) comp_ide_self ide_cod [of "\<phi> i"] \<psi>_\<phi> \<psi>_def by fastforce
              ultimately show ?thesis
                using C'_def i assms(1)
                apply simp
                by (metis (no_types, lifting) \<psi> \<psi>_def bij_betw_def image_eqI mem_Collect_eq)
            qed
            moreover have "\<psi> (cod (\<phi> i)) \<noteq> C'.null"
              using i null_char assms(1-2)
              by (metis \<psi> bij_betw_def category.arr_cod_iff_arr category_axioms
                  image_eqI mem_Collect_eq)
            ultimately show ?thesis
              by simp
          qed
          show "\<And>j. C' (\<psi> (cod (\<phi> i))) j \<noteq> C'.null \<Longrightarrow> C' (\<psi> (cod (\<phi> i))) j = j"
          proof -
            fix j
            assume j: "C' (\<psi> (cod (\<phi> i))) j \<noteq> C'.null"
            show "C' (\<psi> (cod (\<phi> i))) j = j"
              using j
              by (metis C'.comp_null(2) C'.ide_def C'_def
                  \<open>C' (\<psi> (cod (\<phi> i))) (\<psi> (cod (\<phi> i))) \<noteq> C'.null\<close>
                  \<phi>_\<psi> \<psi>_def arr_cod_iff_arr category.ide_cod category_axioms ide_char null_char)
          qed
          show "\<And>j. C' j (\<psi> (cod (\<phi> i))) \<noteq> C'.null \<Longrightarrow> C' j (\<psi> (cod (\<phi> i))) = j"
          proof -
            fix j
            assume j: "C' j (\<psi> (cod (\<phi> i))) \<noteq> C'.null"
            show "C' j (\<psi> (cod (\<phi> i))) = j"
              using j
              by (metis C'.ide_def C'_def \<open>C' (\<psi> (cod (\<phi> i))) (\<psi> (cod (\<phi> i))) \<noteq> C'.null\<close>
                  \<open>\<And>j. C' (\<psi> (cod (\<phi> i))) j \<noteq> C'.null \<Longrightarrow> C' (\<psi> (cod (\<phi> i))) j = j\<close>
                  \<phi>_\<psi> \<psi>_def arr_cod_iff_arr category.ide_cod category_axioms ide_char null_char)
          qed
        qed
        moreover have "C' (\<psi> (cod (\<phi> i))) i \<noteq> C'.null"
          using i assms(1-2) C'_def null_char \<phi>_\<psi> \<psi>_\<phi> \<psi>_def comp_cod_arr ide_char
          apply simp
          by (metis (no_types, lifting) \<psi>_def 1)
        ultimately show "\<psi> (cod (\<phi> i)) \<in> C'.codomains i"
          using C'.codomains_def by simp
      qed
      have arr_char: "\<And>i. C'.arr i \<longleftrightarrow> i \<in> S"
      proof
        fix i
        show "i \<in> S \<Longrightarrow> C'.arr i"
          using dom cod C'.arr_def by auto
        show "C'.arr i \<Longrightarrow> i \<in> S"
          using C'_def C'.arr_def C'.domains_def C'.codomains_def null_char
          apply simp
          by metis
      qed
      have seq_char: "\<And>i j. C'.seq i j \<longleftrightarrow> i \<in> S \<and> j \<in> S \<and> seq (\<phi> i) (\<phi> j)"
        using assms(1-2) C'_def arr_char null_char
        apply simp
        using \<psi> bij_betw_apply by fastforce
      interpret C': category C'
      proof
        show "\<And>g f. C' g f \<noteq> C'.null \<Longrightarrow> C'.seq g f"
          using C'_def null_char seq_char by fastforce
        show "\<And>f. (C'.domains f \<noteq> {}) = (C'.codomains f \<noteq> {})"
          using dom cod null_char arr_char C'.arr_def by blast
        show "\<And>h g f. \<lbrakk>C'.seq h g; C'.seq (C' h g) f\<rbrakk> \<Longrightarrow> C'.seq g f"
          using seq_char
          apply simp
          using C'_def by fastforce
        show "\<And>h g f. \<lbrakk>C'.seq h (C' g f); C'.seq g f\<rbrakk> \<Longrightarrow> C'.seq h g"
          using seq_char
          apply simp
          using C'_def by fastforce
        show "\<And>g f h. \<lbrakk>C'.seq g f; C'.seq h g\<rbrakk> \<Longrightarrow> C'.seq (C' h g) f"
          using seq_char arr_char
          apply simp
          using C'_def by auto
        show "\<And>g f h. \<lbrakk>C'.seq g f; C'.seq h g\<rbrakk> \<Longrightarrow> C' (C' h g) f = C' h (C' g f)"
          using seq_char arr_char C'_def comp_assoc assms(2)
          apply simp by presburger
      qed
      have dom_char: "C'.dom = (\<lambda>i. if i \<in> S then \<psi> (dom (\<phi> i)) else n)"
        using dom arr_char null_char C'.dom_eqI' C'.arr_def C'.dom_def by metis
      have cod_char: "C'.cod = (\<lambda>i. if i \<in> S then \<psi> (cod (\<phi> i)) else n)"
        using cod arr_char null_char C'.cod_eqI' C'.arr_def C'.cod_def by metis
      interpret \<phi>: "functor" C' C \<open>\<lambda>i. if C'.arr i then \<phi> i else null\<close>
        using arr_char null_char dom_char cod_char seq_char \<phi>_\<psi> \<psi>_\<phi> \<psi>_def C'.not_arr_null C'_def
              C'.arr_dom C'.arr_cod
        apply unfold_locales
            apply simp_all
           apply (metis (full_types))
          apply force
         apply force
        by metis
      interpret \<psi>: "functor" C C' \<psi>
        using \<psi>_def null_char arr_char
        apply unfold_locales
            apply simp
           apply (metis (no_types, lifting) \<psi> bij_betw_def image_eqI mem_Collect_eq)
          apply (metis (no_types, lifting) \<phi>_\<psi> \<psi> bij_betw_def dom_char image_eqI mem_Collect_eq)
         apply (metis (no_types, lifting) \<phi>_\<psi> \<psi> bij_betw_def cod_char image_eqI mem_Collect_eq)
        by (metis (no_types, lifting) C'_def \<phi>_\<psi> \<psi> bij_betw_def seqE image_eqI mem_Collect_eq)
      interpret \<phi>\<psi>: inverse_functors C' C \<psi> \<open>\<lambda>i. if C'.arr i then \<phi> i else null\<close>
      proof
        show "\<psi> \<circ> (\<lambda>i. if C'.arr i then \<phi> i else null) = C'.map"
          by (auto simp add: C'.is_extensional \<psi>.is_extensional arr_char)
        show "(\<lambda>i. if C'.arr i then \<phi> i else null) \<circ> \<psi> = map"
          by (auto simp add: is_extensional)
      qed
      have "invertible_functor C' C (\<lambda>i. if C'.arr i then \<phi> i else null)"
        using \<phi>\<psi>.inverse_functors_axioms by unfold_locales auto
      thus ?thesis
        using arr_char by blast
    qed

    corollary (in category) finite_imp_ex_iso_nat_comp:
    assumes "finite (Collect arr)"
    shows "\<exists>C' :: nat comp. isomorphic_categories C' C"
    proof -
      obtain n :: nat and \<phi> where \<phi>: "bij_betw \<phi> {0..<n} (Collect arr)"
        using assms ex_bij_betw_nat_finite by blast
      obtain C' where C': "Collect (partial_magma.arr C') = {0..<n} \<and>
                           invertible_functor C' (\<cdot>)
                             (\<lambda>i. if partial_magma.arr C' i then \<phi> i else null)"
        using \<phi> bij_induces_invertible_functor [of \<phi> "{0..<n}"] by auto
      interpret \<phi>: invertible_functor C' C \<open>\<lambda>i. if partial_magma.arr C' i then \<phi> i else null\<close>
        using C' by simp
      show ?thesis
        using \<phi>.isomorphic_categories_axioms by blast
    qed

  end

  text \<open>
    We now prove the result, advertised earlier in theory \<open>ConcreteCategory\<close>,
    that any category is in fact isomorphic to the concrete category formed from it in
    the obvious way.
  \<close>

  context category
  begin

    interpretation CC: concrete_category \<open>Collect ide\<close> hom id \<open>\<lambda>C B A g f. g \<cdot> f\<close>
      using comp_arr_dom comp_cod_arr comp_assoc
      by (unfold_locales, auto)

    interpretation F: "functor" C CC.COMP
                       \<open>\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null\<close>
      by (unfold_locales, auto simp add: in_homI)

    interpretation G: "functor" CC.COMP C \<open>\<lambda>F. if CC.arr F then CC.Map F else null\<close>
      using CC.Map_in_Hom CC.seq_char
      by (unfold_locales, auto)

    interpretation FG: inverse_functors C CC.COMP
                       \<open>\<lambda>F. if CC.arr F then CC.Map F else null\<close>
                       \<open>\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null\<close>
    proof
      show "(\<lambda>F. if CC.arr F then CC.Map F else null) \<circ>
              (\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null) =
            map"
        using CC.arr_char map_def by fastforce
      show "(\<lambda>f. if arr f then CC.MkArr (dom f) (cod f) f else CC.null) \<circ>
              (\<lambda>F. if CC.arr F then CC.Map F else null) =
            CC.map"
        using CC.MkArr_Map G.preserves_arr G.preserves_cod G.preserves_dom
              CC.is_extensional
        by auto
    qed

    interpretation isomorphic_categories C CC.COMP ..

    theorem is_isomorphic_to_concrete_category:
    shows "isomorphic_categories C CC.COMP"
      ..

  end

  locale dual_functor =
    F: "functor" A B F +
    Aop: dual_category A +
    Bop: dual_category B
  for A :: "'a comp"      (infixr "\<cdot>\<^sub>A" 55)
  and B :: "'b comp"      (infixr "\<cdot>\<^sub>B" 55)
  and F :: "'a \<Rightarrow> 'b"
  begin

    notation Aop.comp     (infixr "\<cdot>\<^sub>A\<^sup>o\<^sup>p" 55)
    notation Bop.comp     (infixr "\<cdot>\<^sub>B\<^sup>o\<^sup>p" 55)

    definition map
    where "map \<equiv> F"

    lemma map_simp [simp]:
    shows "map f = F f"
      by (simp add: map_def)

    lemma is_functor:
    shows "functor Aop.comp Bop.comp map"
      using F.is_extensional by (unfold_locales, auto)

  end

  sublocale invertible_functor \<subseteq> inverse_functors A B inv G
    using inv_is_inverse by simp

   sublocale dual_functor \<subseteq> "functor" Aop.comp Bop.comp map
    using is_functor by auto

end

