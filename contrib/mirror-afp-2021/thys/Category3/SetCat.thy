(*  Title:       SetCat
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter SetCat

theory SetCat
imports SetCategory ConcreteCategory
begin

  text\<open>
    This theory proves the consistency of the \<open>set_category\<close> locale by giving
    a particular concrete construction of an interpretation for it.
    Applying the general construction given by @{locale concrete_category},
    we define arrows to be terms \<open>MkArr A B F\<close>, where \<open>A\<close> and \<open>B\<close> are sets
    and \<open>F\<close> is an extensional function that maps \<open>A\<close> to \<open>B\<close>.
\<close>

  text\<open>
    This locale uses an extra dummy parameter just to fix the element type for sets.
    Without this, a type is used for each interpretation, which makes it impossible to
    construct set categories whose element types are related to the context.
  \<close>

  locale setcat =
  fixes dummy :: 'e
  and \<AA> :: "'a rel"
  assumes cardinal: "Card_order \<AA> \<and> infinite (Field \<AA>)"
  begin

    lemma finite_imp_card_less:
    assumes "finite A"
    shows "|A| <o \<AA>"
    proof -
      have "finite (Field |A| )"
        using assms by simp
      thus ?thesis
        using cardinal card_of_Well_order card_order_on_def finite_ordLess_infinite
        by blast
    qed

    type_synonym 'b arr = "('b set, 'b \<Rightarrow> 'b) concrete_category.arr"

    interpretation concrete_category \<open>{A :: 'e set. |A| <o \<AA>}\<close> \<open>\<lambda>A B. extensional A \<inter> (A \<rightarrow> B)\<close>
                     \<open>\<lambda>A. \<lambda>x \<in> A. x\<close> \<open>\<lambda>C B A g f. compose A g f\<close>
      using compose_Id Id_compose
      apply unfold_locales
          apply auto[3]
       apply blast
      by (metis IntD2 compose_assoc)

    abbreviation comp :: "'e setcat.arr comp"     (infixr "\<cdot>" 55)
    where "comp \<equiv> COMP"
    notation in_hom                               ("\<guillemotleft>_ : _ \<rightarrow> _\<guillemotright>")

    lemma MkArr_expansion:
    assumes "arr f"
    shows "f = MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x)"
    proof (intro arr_eqI)
      show "arr f" by fact
      show "arr (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        using assms arr_char
        by (metis (mono_tags, lifting) Int_iff MkArr_Map extensional_restrict)
      show "Dom f = Dom (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        by simp
      show "Cod f = Cod (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        by simp
      show "Map f = Map (MkArr (Dom f) (Cod f) (\<lambda>x \<in> Dom f. Map f x))"
        using assms arr_char
        by (metis (mono_tags, lifting) Int_iff MkArr_Map extensional_restrict)
    qed

    lemma arr_char:
    shows "arr f \<longleftrightarrow> f \<noteq> Null \<and> |Dom f| <o \<AA> \<and> |Cod f| <o \<AA> \<and>
                     Map f \<in> extensional (Dom f) \<inter> (Dom f \<rightarrow> Cod f)"
      using arr_char by auto

    lemma terminal_char:
    shows "terminal a \<longleftrightarrow> (\<exists>x. a = MkIde {x})"
    proof
      show "\<exists>x. a = MkIde {x} \<Longrightarrow> terminal a"
      proof -
        assume a: "\<exists>x. a = MkIde {x}"
        from this obtain x where x: "a = MkIde {x}" by blast
        have "terminal (MkIde {x})"
        proof
          show 1: "ide (MkIde {x})"
            using finite_imp_card_less ide_MkIde by auto
          show "\<And>a. ide a \<Longrightarrow> \<exists>!f. \<guillemotleft>f : a \<rightarrow> MkIde {x}\<guillemotright>"
          proof
            fix a :: "'e setcat.arr"
            assume a: "ide a"
            show "\<guillemotleft>MkArr (Dom a) {x} (\<lambda>_\<in>Dom a. x) : a \<rightarrow> MkIde {x}\<guillemotright>"
            proof
              show 2: "arr (MkArr (Dom a) {x} (\<lambda>_ \<in> Dom a. x))"
                using a 1 arr_MkArr [of "Dom a" "{x}"] ide_char by force
              show "dom (MkArr (Dom a) {x} (\<lambda>_ \<in> Dom a. x)) = a"
                using a 2 dom_MkArr by force
              show "cod (MkArr (Dom a) {x} (\<lambda>_\<in>Dom a. x)) = MkIde {x}"
                using 2 cod_MkArr by blast
            qed
            fix f :: "'e setcat.arr"
            assume f: "\<guillemotleft>f : a \<rightarrow> MkIde {x}\<guillemotright>"
            show "f = MkArr (Dom a) {x} (\<lambda>_ \<in> Dom a. x)"
            proof -
              have 1: "Dom f = Dom a \<and> Cod f = {x}"
                using a f by (metis (mono_tags, lifting) Dom.simps(1) in_hom_char)
              moreover have "Map f = (\<lambda>_ \<in> Dom a. x)"
              proof
                fix z
                have "z \<notin> Dom a \<Longrightarrow> Map f z = (\<lambda>_ \<in> Dom a. x) z"
                  using f 1 MkArr_expansion
                  by (metis (mono_tags, lifting) Map.simps(1) in_homE restrict_apply)
                moreover have "z \<in> Dom a \<Longrightarrow> Map f z = (\<lambda>_ \<in> Dom a. x) z"
                  using f 1 arr_char [of f] by fastforce
                ultimately show "Map f z = (\<lambda>_ \<in> Dom a. x) z" by auto
              qed
              ultimately show ?thesis
               using f MkArr_expansion [of f] by fastforce
            qed
          qed
        qed
        thus "terminal a" using x by simp
      qed
      show "terminal a \<Longrightarrow> \<exists>x. a = MkIde {x}"
      proof -
        assume a: "terminal a"
        hence ide_a: "ide a" using terminal_def by auto
        have 1: "\<exists>!x. x \<in> Dom a"
        proof -
          have "Dom a = {} \<Longrightarrow> \<not>terminal a"
          proof -
            assume "Dom a = {}"
            hence 1: "a = MkIde {}"
              using MkIde_Dom' \<open>ide a\<close> by fastforce
            have "\<And>f. f \<in> hom (MkIde {undefined}) (MkIde ({} :: 'e set))
                         \<Longrightarrow> Map f \<in> {undefined} \<rightarrow> {}"
            proof -
              fix f
              assume f: "f \<in> hom (MkIde {undefined}) (MkIde ({} :: 'e set))"
              show "Map f \<in> {undefined} \<rightarrow> {}"
                using f MkArr_expansion arr_char [of f] in_hom_char by auto
            qed
            hence "hom (MkIde {undefined}) a = {}" using 1 by auto
            moreover have "ide (MkIde {undefined})"
              using finite_imp_card_less
              by (metis (mono_tags, lifting) finite.intros(1-2) ide_MkIde mem_Collect_eq)
            ultimately show "\<not>terminal a" by blast
          qed
          moreover have "\<And>x x'. x \<in> Dom a \<and> x' \<in> Dom a \<and> x \<noteq> x' \<Longrightarrow> \<not>terminal a"
          proof -
            fix x x'
            assume 1: "x \<in> Dom a \<and> x' \<in> Dom a \<and> x \<noteq> x'"
            let ?f = "MkArr {undefined} (Dom a) (\<lambda>_ \<in> {undefined}. x)"
            let ?f' = "MkArr {undefined} (Dom a) (\<lambda>_ \<in> {undefined}. x')"
            have "\<guillemotleft>?f : MkIde {undefined} \<rightarrow> a\<guillemotright>"
            proof
              show 2: "arr ?f"
              proof (intro arr_MkArr)
                show "{undefined} \<in> {A. |A| <o \<AA>}"
                  by (simp add: finite_imp_card_less)
                show "Dom a \<in> {A. |A| <o \<AA>}"
                  using ide_a ide_char by blast
                show "(\<lambda>_ \<in> {undefined}. x) \<in> extensional {undefined} \<inter> ({undefined} \<rightarrow> Dom a)"
                  using 1 by blast
              qed
              show "dom ?f = MkIde {undefined}"
                using 2 dom_MkArr by auto
              show "cod ?f = a"
                using 2 cod_MkArr ide_a by force
            qed
            moreover have "\<guillemotleft>?f' : MkIde {undefined} \<rightarrow> a\<guillemotright>"
            proof
              show 2: "arr ?f'"
                using 1 ide_a ide_char arr_MkArr [of "{undefined}" "Dom a"]
                      finite_imp_card_less
              proof (intro arr_MkArr)
                show "{undefined} \<in> {A. |A| <o \<AA>}"
                  by (simp add: finite_imp_card_less)
                show "Dom a \<in> {A. |A| <o \<AA>}"
                  using ide_a ide_char by blast
                show "(\<lambda>_ \<in> {undefined}. x') \<in> extensional {undefined} \<inter> ({undefined} \<rightarrow> Dom a)"
                  using 1 by blast
              qed
              show "dom ?f' = MkIde {undefined}"
                using 2 dom_MkArr by auto
              show "cod ?f' = a"
                using 2 cod_MkArr ide_a by force
            qed
            moreover have "?f \<noteq> ?f'"
              using 1 by (metis arr.inject restrict_apply' singletonI)
            ultimately show "\<not>terminal a"
              using terminal_arr_unique
              by (metis (mono_tags, lifting) in_homE)
          qed
          ultimately show ?thesis
            using a by auto
        qed
        hence "Dom a = {THE x. x \<in> Dom a}"
          using theI [of "\<lambda>x. x \<in> Dom a"] by auto
        hence "a = MkIde {THE x. x \<in> Dom a}"
          using a terminal_def by (metis (mono_tags, lifting) MkIde_Dom')
        thus "\<exists>x. a = MkIde {x}"
          by auto
      qed
    qed

    definition IMG :: "'e setcat.arr \<Rightarrow> 'e setcat.arr"
    where "IMG f = MkIde (Map f ` Dom f)"
  
    interpretation set_category_data comp IMG ..

    lemma terminal_unity:
    shows "terminal unity"
      using terminal_char unity_def someI_ex [of terminal]
      by (metis (mono_tags, lifting))
  
    text\<open>
      The inverse maps @{term UP} and @{term DOWN} are used to pass back and forth between
      the inhabitants of type @{typ 'a} and the corresponding terminal objects.
      These are exported so that a client of the theory can relate the concrete
      element type @{typ 'a} to the otherwise abstract arrow type.
\<close>

    definition UP :: "'e \<Rightarrow> 'e setcat.arr"
    where "UP x \<equiv> MkIde {x}"
  
    definition DOWN :: "'e setcat.arr \<Rightarrow> 'e"
    where "DOWN t \<equiv> the_elem (Dom t)"

    abbreviation U
    where "U \<equiv> DOWN unity"
  
    lemma UP_mapsto:
    shows "UP \<in> UNIV \<rightarrow> Univ"
      using terminal_char UP_def by fast
    
    lemma DOWN_mapsto:
    shows "DOWN \<in> Univ \<rightarrow> UNIV"
      by auto
    
    lemma DOWN_UP [simp]:
    shows "DOWN (UP x) = x"
      by (simp add: DOWN_def UP_def)
    
    lemma UP_DOWN [simp]:
    assumes "t \<in> Univ"
    shows "UP (DOWN t) = t"
      using assms terminal_char UP_def DOWN_def
      by (metis (mono_tags, lifting) mem_Collect_eq DOWN_UP)
  
    lemma inj_UP:
    shows "inj UP"
      by (metis DOWN_UP injI)
  
    lemma bij_UP:
    shows "bij_betw UP UNIV Univ"
    proof (intro bij_betwI)
      interpret category comp using is_category by auto
      show DOWN_UP: "\<And>x :: 'e. DOWN (UP x) = x" by simp
      show UP_DOWN: "\<And>t. t \<in> Univ \<Longrightarrow> UP (DOWN t) = t" by simp
      show "UP \<in> UNIV \<rightarrow> Univ" using UP_mapsto by auto
      show "DOWN \<in> Collect terminal \<rightarrow> UNIV" by auto
    qed
  
    lemma Dom_terminal:
    assumes "terminal t"
    shows "Dom t = {DOWN t}"
      using assms UP_def
      by (metis (mono_tags, lifting) Dom.simps(1) DOWN_def terminal_char the_elem_eq)

    text\<open>
      The image of a point @{term "p \<in> hom unity a"} is a terminal object, which is given
      by the formula @{term "(UP o Fun p o DOWN) unity"}.
\<close>

    lemma IMG_point:
    assumes "\<guillemotleft>p : unity \<rightarrow> a\<guillemotright>"
    shows "IMG \<in> hom unity a \<rightarrow> Univ"
    and "IMG p = (UP o Map p o DOWN) unity"
    proof -
      show "IMG \<in> hom unity a \<rightarrow> Univ"
      proof
        fix f
        assume f: "f \<in> hom unity a"
        have "terminal (MkIde (Map f ` Dom unity))"
        proof -
          obtain u :: 'e where u: "unity = MkIde {u}"
            using terminal_unity terminal_char
            by (metis (mono_tags, lifting))
          have "Map f ` Dom unity = {Map f u}"
            using u by simp
          thus ?thesis
            using terminal_char by auto
        qed
        hence "MkIde (Map f ` Dom unity) \<in> Univ" by simp
        moreover have "MkIde (Map f ` Dom unity) = IMG f"
          using f IMG_def in_hom_char
          by (metis (mono_tags, lifting) mem_Collect_eq)
        ultimately show "IMG f \<in> Univ" by auto
      qed
      have "IMG p = MkIde (Map p ` Dom p)" using IMG_def by blast
      also have "... = MkIde (Map p ` {U})"
        using assms in_hom_char terminal_unity Dom_terminal
        by (metis (mono_tags, lifting))
      also have "... = (UP o Map p o DOWN) unity" by (simp add: UP_def)
      finally show "IMG p = (UP o Map p o DOWN) unity" using assms by auto
    qed
  
    text\<open>
      The function @{term IMG} is injective on @{term "hom unity a"} and its inverse takes
      a terminal object @{term t} to the arrow in @{term "hom unity a"} corresponding to the
      constant-@{term t} function.
\<close>

    abbreviation MkElem :: "'e setcat.arr => 'e setcat.arr => 'e setcat.arr"
    where "MkElem t a \<equiv> MkArr {U} (Dom a) (\<lambda>_ \<in> {U}. DOWN t)"

    lemma MkElem_in_hom:
    assumes "arr f" and "x \<in> Dom f"
    shows "\<guillemotleft>MkElem (UP x) (dom f) : unity \<rightarrow> dom f\<guillemotright>"
    proof -
      have "(\<lambda>_ \<in> {U}. DOWN (UP x)) \<in> {U} \<rightarrow> Dom (dom f)"
        using assms dom_char [of f] by simp
      moreover have "MkIde {U} = unity"
        using terminal_char terminal_unity
        by (metis (mono_tags, lifting) DOWN_UP UP_def)
      moreover have "MkIde (Dom (dom f)) = dom f"
        using assms dom_char MkIde_Dom' ide_dom by blast
      ultimately show ?thesis
        using assms MkArr_in_hom [of "{U}" "Dom (dom f)" "\<lambda>_ \<in> {U}. DOWN (UP x)"]
        by (metis (no_types, lifting) Dom.simps(1) Dom_in_Obj IntI arr_dom ideD(1)
            restrict_extensional terminal_def terminal_unity)
    qed

    lemma MkElem_IMG:
    assumes "p \<in> hom unity a"
    shows "MkElem (IMG p) a = p"
    proof -
      have 0: "IMG p = UP (Map p U)"
        using assms IMG_point(2) by auto
      have 1: "Dom p = {U}"
        using assms terminal_unity Dom_terminal
        by (metis (mono_tags, lifting) in_hom_char mem_Collect_eq)
      moreover have "Cod p = Dom a"
        using assms
        by (metis (mono_tags, lifting) in_hom_char mem_Collect_eq)
      moreover have "Map p = (\<lambda>_ \<in> {U}. DOWN (IMG p))"
      proof
        fix e
        show "Map p e = (\<lambda>_ \<in> {U}. DOWN (IMG p)) e"
        proof -
          have "Map p e = (\<lambda>x \<in> Dom p. Map p x) e"
            using assms MkArr_expansion [of p]
            by (metis (mono_tags, lifting) CollectD Map.simps(1) in_homE)
          also have "... = (\<lambda>_ \<in> {U}. DOWN (IMG p)) e"
            using assms 0 1 by simp
          finally show ?thesis by blast
        qed
      qed
      ultimately show "MkElem (IMG p) a = p"
        using assms MkArr_Map CollectD
        by (metis (mono_tags, lifting) in_homE mem_Collect_eq)
    qed

    lemma inj_IMG:
    assumes "ide a"
    shows "inj_on IMG (hom unity a)"
    proof (intro inj_onI)
      fix x y
      assume x: "x \<in> hom unity a"
      assume y: "y \<in> hom unity a"
      assume eq: "IMG x = IMG y"
      show "x = y"
      proof (intro arr_eqI)
        show "arr x" using x by blast
        show "arr y" using y by blast
        show "Dom x = Dom y"
          using x y in_hom_char by (metis (mono_tags, lifting) CollectD)
        show "Cod x = Cod y"
          using x y in_hom_char by (metis (mono_tags, lifting) CollectD)
        show "Map x = Map y"
        proof -
          have "\<And>a. y \<in> hom unity a \<Longrightarrow> MkArr {U} (Dom a) (\<lambda>e\<in>{U}. DOWN (IMG x)) = y"
            using MkElem_IMG eq by presburger
          hence "y = x"
            using MkElem_IMG x y by blast
          thus ?thesis by meson
        qed
      qed
    qed

    lemma set_char:
    assumes "ide a"
    shows "set a = UP ` Dom a"
    proof
      show "set a \<subseteq> UP ` Dom a"
      proof
        fix t
        assume "t \<in> set a"
        from this obtain p where p: "\<guillemotleft>p : unity \<rightarrow> a\<guillemotright> \<and> t = IMG p"
          using set_def by blast
        have "t = (UP o Map p o DOWN) unity"
          using p IMG_point(2) by blast
        moreover have "(Map p o DOWN) unity \<in> Dom a"
          using p arr_char in_hom_char Dom_terminal terminal_unity
          by (metis (mono_tags, lifting) IntD2 Pi_split_insert_domain o_apply)
        ultimately show "t \<in> UP ` Dom a" by simp
      qed
      show "UP ` Dom a \<subseteq> set a"
      proof
        fix t
        assume "t \<in> UP ` Dom a"
        from this obtain x where x: "x \<in> Dom a \<and> t = UP x" by blast
        let ?p = "MkElem (UP x) a"
        have p: "?p \<in> hom unity a"
          using assms x MkElem_in_hom [of "dom a"] ideD(1-2) by force
        moreover have "IMG ?p = t"
          using p x DOWN_UP IMG_def UP_def
          by (metis (no_types, lifting) Dom.simps(1) Map.simps(1) image_empty
              image_insert image_restrict_eq)
        ultimately show "t \<in> set a" using set_def by blast
      qed
    qed
  
    lemma Map_via_comp:
    assumes "arr f"
    shows "Map f = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U)"
    proof
      fix x
      have "x \<notin> Dom f \<Longrightarrow> Map f x = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U) x"
        using assms arr_char [of f] IntD1 extensional_arb restrict_apply by fastforce
      moreover have
           "x \<in> Dom f \<Longrightarrow> Map f x = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U) x"
      proof -
        assume x: "x \<in> Dom f"
        let ?X = "MkElem (UP x) (dom f)"
        have "\<guillemotleft>?X : unity \<rightarrow> dom f\<guillemotright>"
          using assms x MkElem_in_hom by auto
        moreover have "Dom ?X = {U} \<and> Map ?X = (\<lambda>_ \<in> {U}. x)"
          using x by simp
        ultimately have
          "Map (f \<cdot> MkElem (UP x) (dom f)) = compose {U} (Map f) (\<lambda>_ \<in> {U}. x)"
          using assms x Map_comp [of "MkElem (UP x) (dom f)" f]
          by (metis (mono_tags, lifting) Cod.simps(1) Dom_dom arr_iff_in_hom seqE seqI')
        thus ?thesis
          using x by (simp add: compose_eq restrict_apply' singletonI)
      qed
      ultimately show "Map f x = (\<lambda>x \<in> Dom f. Map (f \<cdot> MkElem (UP x) (dom f)) U) x"
        by auto
    qed

    lemma arr_eqI':
    assumes "par f f'" and "\<And>t. \<guillemotleft>t : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> t = f' \<cdot> t"
    shows "f = f'"
    proof (intro arr_eqI)
      show "arr f" using assms by simp
      show "arr f'" using assms by simp
      show "Dom f = Dom f'"
        using assms by (metis (mono_tags, lifting) Dom_dom)
      show "Cod f = Cod f'"
        using assms by (metis (mono_tags, lifting) Cod_cod)
      show "Map f = Map f'"
      proof
        have 1: "\<And>x. x \<in> Dom f \<Longrightarrow> \<guillemotleft>MkElem (UP x) (dom f) : unity \<rightarrow> dom f\<guillemotright>"
          using MkElem_in_hom by (metis (mono_tags, lifting) assms(1))
        fix x
        show "Map f x = Map f' x"
          using assms 1 \<open>Dom f = Dom f'\<close> by (simp add: Map_via_comp)
      qed
    qed

    text \<open>
      We need to show that the cardinality constraint on the sets that determine objects
      implies a corresponding constraint on the sets of global elements of those objects.
    \<close>
    
    lemma card_points_less:
    assumes "ide a"
    shows "|hom unity a| <o \<AA>"
    proof -
      have "bij_betw (\<lambda>f. Map f U) (hom unity a) (Dom a)"
      proof (intro bij_betwI')
        show "\<And>x. x \<in> hom unity a \<Longrightarrow> Map x (DOWN unity) \<in> Dom a"
          using arr_char Dom_terminal terminal_unity in_hom_char by auto
        show "\<And>x y. \<lbrakk>x \<in> hom unity a; y \<in> hom unity a\<rbrakk> \<Longrightarrow> Map x U = Map y U \<longleftrightarrow> x = y"
        proof -
          fix x y
          assume x: "x \<in> hom unity a" and y: "y \<in> hom unity a"
          have 1: "Map x \<in> extensional {U} \<and> Map y \<in> extensional {U}"
            using x y in_hom_char Dom_terminal terminal_unity
            by (metis (mono_tags, lifting) Map_via_comp mem_Collect_eq restrict_extensional)
          show "Map x U = Map y U \<longleftrightarrow> x = y"
          proof
            show "x = y \<Longrightarrow> Map x U = Map y U"
              by simp
            show "Map x U = Map y U \<Longrightarrow> x = y"
            proof -
              assume 2: "Map x U = Map y U"
              have "Map x = Map y"
              proof
                fix z
                show "Map x z = Map y z"
                  using 1 2 extensional_arb [of "Map x"] extensional_arb [of "Map y"]
                  by (cases "z = U") auto
              qed
              thus "x = y"
                using x y 1 in_hom_char
                by (intro arr_eqI) auto
            qed
          qed
        qed
        show "\<And>y. y \<in> Dom a \<Longrightarrow> \<exists>x \<in> hom unity a. y = Map x (DOWN unity)"
        proof -
          fix y
          assume y: "y \<in> Dom a"
          let ?x = "MkArr {DOWN unity} (Dom a) (\<lambda>_ \<in> {U}. y)"
          have "arr ?x"
          proof (intro arr_MkArr)
            show "{U} \<in> {A. |A| <o \<AA>}"
              by (metis (mono_tags, lifting) Dom_terminal ide_char terminal_def terminal_unity)
            show "Dom a \<in> {A. |A| <o \<AA>}"
              using assms ide_char by blast
            show "(\<lambda>_ \<in> {U}. y) \<in> extensional {U} \<inter> ({U} \<rightarrow> Dom a)"
              using assms y by blast
          qed
          hence "?x \<in> hom unity a"
            using UP_DOWN UP_def assms cod_MkArr dom_char in_homI terminal_unity by simp
          moreover have "y = Map ?x (DOWN unity)"
            by simp
          ultimately show "\<exists>x \<in> hom unity a. y = Map x (DOWN unity)"
            by auto
        qed
      qed
      hence "|hom unity a| =o |Dom a|"
        using card_of_ordIsoI by auto
      moreover have "|Dom a| <o \<AA>"
        using assms ide_char by auto
      ultimately show "|hom unity a| <o \<AA>"
        using ordIso_ordLess_trans by auto
    qed

    text\<open>
      The main result, which establishes the consistency of the \<open>set_category\<close> locale
      and provides us with a way of obtaining ``set categories'' at arbitrary types.
\<close>

    theorem is_set_category:
    shows "set_category comp \<AA>"
    proof
      show "\<exists>img :: 'e setcat.arr \<Rightarrow> 'e setcat.arr. set_category_given_img comp img \<AA>"
      proof
        show "set_category_given_img (comp :: 'e setcat.arr comp) IMG \<AA>"
        proof
          show "Card_order \<AA> \<and> infinite (Field \<AA> )"
            using cardinal by simp
          show "Univ \<noteq> {}" using terminal_char by blast
          fix a :: "'e setcat.arr"
          assume a: "ide a"
          show "IMG \<in> hom unity a \<rightarrow> Univ" using IMG_point terminal_unity by blast
          show "|hom unity a| <o \<AA>" using a card_points_less by simp
          show "inj_on IMG (hom unity a)" using a inj_IMG terminal_unity by blast
          next
          fix t :: "'e setcat.arr"
          assume t: "terminal t"
          show "t \<in> IMG ` hom unity t"
          proof -
            have "t \<in> set t"
              using t set_char [of t]
              by (metis (mono_tags, lifting) Dom.simps(1) image_insert insertI1 UP_def
                  terminal_char terminal_def)
            thus ?thesis
              using t set_def [of t] by simp
          qed
          next
          fix A :: "'e setcat.arr set"
          assume A: "A \<subseteq> Univ" and 0: "|A| <o \<AA>"
          show "\<exists>a. ide a \<and> set a = A"
          proof
            let ?a = "MkArr (DOWN ` A) (DOWN ` A) (\<lambda>x \<in> (DOWN ` A). x)"
            show "ide ?a \<and> set ?a = A"
            proof
              have "|DOWN ` A| <o \<AA>"
                using 0 card_of_image ordLeq_ordLess_trans by blast
              thus 1: "ide ?a"
                using ide_char [of ?a] by simp
              show "set ?a = A"
              proof -
                have 2: "\<And>x. x \<in> A \<Longrightarrow> x = UP (DOWN x)"
                  using A UP_DOWN by force
                hence "UP ` DOWN ` A = A"
                  using A UP_DOWN by auto
                thus ?thesis
                  using 1 A set_char [of ?a] by simp
              qed
            qed
          qed
          next
          fix a b :: "'e setcat.arr"
          assume a: "ide a" and b: "ide b" and ab: "set a = set b"
          show "a = b"
            using a b ab set_char inj_UP inj_image_eq_iff dom_char in_homE ide_in_hom
            by (metis (mono_tags, lifting))
          next
          fix f f' :: "'e setcat.arr"
          assume par: "par f f'" and ff': "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<Longrightarrow> f \<cdot> x = f' \<cdot> x"
          show "f = f'" using par ff' arr_eqI' by blast
          next
          fix a b :: "'e setcat.arr" and F :: "'e setcat.arr \<Rightarrow> 'e setcat.arr"
          assume a: "ide a" and b: "ide b" and F: "F \<in> hom unity a \<rightarrow> hom unity b"
          show "\<exists>f. \<guillemotleft>f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom f\<guillemotright> \<longrightarrow> f \<cdot> x = F x)"
          proof
            let ?f = "MkArr (Dom a) (Dom b) (\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U)"
            have 1: "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright>"
            proof -
              have "(\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U)
                      \<in> extensional (Dom a) \<inter> (Dom a \<rightarrow> Dom b)"
              proof
                show "(\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U) \<in> extensional (Dom a)"
                  using a F by simp
                show "(\<lambda>x \<in> Dom a. Map (F (MkElem (UP x) a)) U) \<in> Dom a \<rightarrow> Dom b"
                proof
                  fix x
                  assume x: "x \<in> Dom a"
                  have "MkElem (UP x) a \<in> hom unity a"
                    using x a MkElem_in_hom [of a x] ide_char ideD(1-2) by force
                  hence 1: "F (MkElem (UP x) a) \<in> hom unity b"
                    using F by auto
                  moreover have "Dom (F (MkElem (UP x) a)) = {U}"
                    using 1 MkElem_IMG
                    by (metis (mono_tags, lifting) Dom.simps(1))
                  moreover have "Cod (F (MkElem (UP x) a)) = Dom b"
                    using 1 by (metis (mono_tags, lifting) CollectD in_hom_char)
                  ultimately have "Map (F (MkElem (UP x) a)) \<in> {U} \<rightarrow> Dom b"
                    using arr_char [of "F (MkElem (UP x) a)"] by blast
                  thus "Map (F (MkElem (UP x) a)) U \<in> Dom b" by blast
                qed
              qed
              hence "\<guillemotleft>?f : MkIde (Dom a) \<rightarrow> MkIde (Dom b)\<guillemotright>"
                using a b MkArr_in_hom ide_char by blast
              thus ?thesis
                using a b by simp
            qed
            moreover have "\<And>x. \<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright> \<Longrightarrow> ?f \<cdot> x = F x"
            proof -
              fix x
              assume x: "\<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright>"
              have 2: "x = MkElem (IMG x) a"
                using a x 1 MkElem_IMG [of x a]
                by (metis (mono_tags, lifting) in_homE mem_Collect_eq)
              moreover have 5: "Dom x = {U} \<and> Cod x = Dom a \<and>
                                Map x = (\<lambda>_ \<in> {U}. DOWN (IMG x))"
                using x 2
                by (metis (no_types, lifting) Cod.simps(1) Dom.simps(1) Map.simps(1))
              moreover have "Cod ?f = Dom b" using 1 by simp
              ultimately have
                   3: "?f \<cdot> x =
                       MkArr {U} (Dom b) (compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)))"
                using 1 x comp_char [of ?f "MkElem (IMG x) a"]
                by (metis (mono_tags, lifting) in_homE seqI)
              have 4: "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)) = Map (F x)"
              proof
                fix y
                have "y \<notin> {U} \<Longrightarrow>
                        compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)) y = Map (F x) y"
                proof -
                  assume y: "y \<notin> {U}"
                  have "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)) y = undefined"
                    using y compose_def extensional_arb by simp
                  also have "... = Map (F x) y"
                  proof -
                    have 5: "F x \<in> hom unity b" using x F 1 by fastforce
                    hence "Dom (F x) = {U}"
                      by (metis (mono_tags, lifting) "2" CollectD Dom.simps(1) in_hom_char x)
                    thus ?thesis
                      using x y F 5 arr_char [of "F x"] extensional_arb [of "Map (F x)" "{U}" y]
                      by (metis (mono_tags, lifting) CollectD Int_iff in_hom_char)
                  qed
                  ultimately show ?thesis by auto
                qed
                moreover have
                    "y \<in> {U} \<Longrightarrow>
                       compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)) y = Map (F x) y"
                proof -
                  assume y: "y \<in> {U}"
                  have "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)) y =
                        Map ?f (DOWN (IMG x))"
                    using y by (simp add: compose_eq restrict_apply')
                  also have "... = (\<lambda>x. Map (F (MkElem (UP x) a)) U) (DOWN (IMG x))"
                  proof -
                    have "DOWN (IMG x) \<in> Dom a"
                      using x y a 5 arr_char in_homE restrict_apply by force
                    thus ?thesis
                      using restrict_apply by simp
                  qed
                  also have "... = Map (F x) y"
                    using x y 1 2 MkElem_IMG [of x a] by simp
                  finally show
                      "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)) y = Map (F x) y"
                    by auto
                qed
                ultimately show
                    "compose {U} (Map ?f) (\<lambda>_ \<in> {U}. DOWN (IMG x)) y = Map (F x) y"
                  by auto
              qed
              show "?f \<cdot> x = F x"
              proof (intro arr_eqI)
                have 5: "?f \<cdot> x \<in> hom unity b" using 1 x by blast
                have 6: "F x \<in> hom unity b"
                  using x F 1
                  by (metis (mono_tags, lifting) PiE in_homE mem_Collect_eq)
                show "arr (comp ?f x)" using 5 by blast
                show "arr (F x)" using 6 by blast
                show "Dom (comp ?f x) = Dom (F x)"
                  using 5 6 by (metis (mono_tags, lifting) CollectD in_hom_char)
                show "Cod (comp ?f x) = Cod (F x)"
                  using 5 6 by (metis (mono_tags, lifting) CollectD in_hom_char)
                show "Map (comp ?f x) = Map (F x)"
                  using 3 4 by simp
              qed
            qed
            thus "\<guillemotleft>?f : a \<rightarrow> b\<guillemotright> \<and> (\<forall>x. \<guillemotleft>x : unity \<rightarrow> dom ?f\<guillemotright> \<longrightarrow> comp ?f x = F x)"
              using 1 by blast
          qed
        qed
      qed
    qed

    text\<open>
      \<open>SetCat\<close> can be viewed as a concrete set category over its own element type
      @{typ 'a}, using @{term UP} as the required injection from @{typ 'a} to the universe
      of \<open>SetCat\<close>.
\<close>

    corollary is_concrete_set_category:
    shows "concrete_set_category comp \<AA> UNIV UP"
    proof -
      interpret S: set_category comp \<AA> using is_set_category by auto
      show ?thesis
      proof
        show 1: "UP \<in> UNIV \<rightarrow> S.Univ"
          using UP_def terminal_char by force
        show "inj_on UP UNIV"
          using inj_UP by blast
      qed
    qed

    text\<open>
      As a consequence of the categoricity of the \<open>set_category\<close> axioms,
      if @{term S} interprets \<open>set_category\<close>, and if @{term \<phi>} is a bijection between
      the universe of @{term S} and the elements of type @{typ 'a}, then @{term S} is isomorphic
      to the category \<open>setcat\<close> of @{typ 'a} sets and functions between them constructed here.
\<close>

    corollary set_category_iso_SetCat:
    fixes S :: "'s comp" and \<phi> :: "'s \<Rightarrow> 'e"
    assumes "set_category S \<AA>"
    and "bij_betw \<phi> (Collect (category.terminal S)) UNIV"
    shows "\<exists>\<Phi>. invertible_functor S (comp :: 'e setcat.arr comp) \<Phi>
                 \<and> (\<forall>m. set_category.incl S \<AA> m \<longrightarrow> set_category.incl comp \<AA> (\<Phi> m))"
    proof -
      interpret S: set_category S using assms by auto
      let ?\<psi> = "inv_into S.Univ \<phi>"
      have "bij_betw (UP o \<phi>) S.Univ (Collect terminal)"
      proof (intro bij_betwI)
        show "UP o \<phi> \<in> S.Univ \<rightarrow> Collect terminal"
          using assms(2) UP_mapsto by auto
        show "?\<psi> o DOWN \<in> Collect terminal \<rightarrow> S.Univ"
        proof
          fix x :: "'e setcat.arr"
          assume x: "x \<in> Univ"
          show "(inv_into S.Univ \<phi> \<circ> DOWN) x \<in> S.Univ"
            using x assms(2) bij_betw_def comp_apply inv_into_into
            by (metis UNIV_I)
        qed
        fix t
        assume "t \<in> S.Univ"
        thus "(?\<psi> o DOWN) ((UP o \<phi>) t) = t"
          using assms(2) bij_betw_inv_into_left
          by (metis comp_apply DOWN_UP)
        next
        fix t' :: "'e setcat.arr"
        assume "t' \<in> Collect terminal"
        thus "(UP o \<phi>) ((?\<psi> o DOWN) t') = t'"
          using assms(2) by (simp add: bij_betw_def f_inv_into_f)
      qed
      thus ?thesis
        using assms(1) set_category_is_categorical [of S \<AA> comp "UP o \<phi>"] is_set_category
        by auto
    qed

  end

  sublocale setcat \<subseteq> set_category comp \<AA>
    using is_set_category by simp
  sublocale setcat \<subseteq> concrete_set_category comp \<AA> UNIV UP
    using is_concrete_set_category by simp

  text\<open>
    By using a large enough cardinal, we can effectively eliminate the cardinality constraint
    on the sets that determine objects and thereby obtain a set category that is replete.
    This is the normal use case, which we want to streamline as much as possible,
    so it is useful to introduce a special locale for this purpose.
  \<close>

  locale replete_setcat =
  fixes dummy :: 'e
  begin

    interpretation SC: setcat dummy
                         \<open>cardSuc (cmax (card_of (UNIV :: 'e setcat.arr set)) natLeq)\<close>
    proof
      show "Card_order (cardSuc (cmax (card_of (UNIV :: 'e setcat.arr set)) natLeq)) \<and>
            infinite (Field (cardSuc (cmax (card_of (UNIV :: 'e setcat.arr set)) natLeq)))"
      by (metis Card_order_cmax Field_natLeq cardSuc_Card_order cardSuc_finite
          card_of_Card_order finite_cmax infinite_UNIV_char_0 natLeq_Card_order)
    qed

    text\<open>
      We don't want to expose the concrete details of the construction used to obtain
      the interpretation \<open>SC\<close>; instead, we want any facts proved about it to be derived
      solely from the assumptions of the @{locale set_category} locales.
      So we create another level of definitions here.
    \<close>

    definition comp
    where "comp \<equiv> SC.comp"

    definition UP
    where "UP \<equiv> SC.UP"

    definition DOWN
    where "DOWN \<equiv> SC.DOWN"

    sublocale set_category comp \<open>cardSuc (cmax (card_of (UNIV :: 'e setcat.arr set)) natLeq)\<close>
      using SC.is_set_category comp_def by simp

    sublocale concrete_set_category comp
                \<open>cardSuc (cmax (card_of (UNIV :: 'e setcat.arr set)) natLeq)\<close> UNIV UP
      using SC.is_concrete_set_category comp_def UP_def by simp

    sublocale replete_set_category comp ..

    lemma UP_mapsto:
    shows "UP \<in> UNIV \<rightarrow> Univ"
      using SC.UP_mapsto
      by (simp add: UP_def comp_def)

    lemma DOWN_mapsto:
    shows "DOWN \<in> Univ \<rightarrow> UNIV"
      by auto

    lemma DOWN_UP [simp]:
    shows "DOWN (UP x) = x"
      by (simp add: DOWN_def UP_def)

    lemma UP_DOWN [simp]:
    assumes "t \<in> Univ"
    shows "UP (DOWN t) = t"
      using assms DOWN_def UP_def
      by (simp add: DOWN_def UP_def comp_def)

    lemma inj_UP:
    shows "inj UP"
      by (metis DOWN_UP injI)

    lemma bij_UP:
    shows "bij_betw UP UNIV Univ"
      by (metis SC.bij_UP UP_def comp_def)

  end

end

