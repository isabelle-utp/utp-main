(*  Title:       Modification
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2020
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

section "Modifications"

text \<open>
  Modifications are morphisms of pseudonatural transformations.
  In this section, we give a definition of ``modification'', and we prove that
  the mappings \<open>\<eta>\<close> and \<open>\<epsilon>\<close>, which were chosen in the course of showing that a
  pseudonatural equivalence \<open>\<tau>\<close> has a converse pseudonatural equivalence \<open>\<tau>'\<close>,
  are invertible modifications that relate the composites \<open>\<tau>'\<tau>\<close> and \<open>\<tau>\<tau>'\<close>
  to the identity pseudonatural transformations on \<open>F\<close> and \<open>G\<close>.
  This means that \<open>\<tau>\<close> and \<open>\<tau>'\<close> are quasi-inverses in a suitable bicategory
  of pseudofunctors, pseudonatural transformations, and modifications, though
  we do not go so far as to give a formal construction of such a bicategory.
\<close>

theory Modification
imports PseudonaturalTransformation
begin

  locale modification =  (* 12 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    \<tau>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1 +
    \<tau>': pseudonatural_transformation
          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0' \<tau>\<^sub>1'
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
  and \<tau>\<^sub>0' :: "'c \<Rightarrow> 'd"
  and \<tau>\<^sub>1' :: "'c \<Rightarrow> 'd"
  and \<Gamma> :: "'c \<Rightarrow> 'd" +
  assumes \<Gamma>_in_hom: "C.obj a \<Longrightarrow> \<guillemotleft>\<Gamma> a : \<tau>\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>\<^sub>0' a\<guillemotright>"
  and naturality: "\<lbrakk> \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>; C.ide f \<rbrakk> \<Longrightarrow> \<tau>\<^sub>1' f \<cdot>\<^sub>D (G f \<star>\<^sub>D \<Gamma> a) = (\<Gamma> b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<tau>\<^sub>1 f"

  locale invertible_modification =  (* 13 sec *)
    modification +
    assumes components_are_iso: "C.obj a \<Longrightarrow> D.iso (\<Gamma> a)"

  locale identity_modification =  (* 12 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    \<tau>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1
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

    abbreviation map
    where "map \<equiv> \<tau>\<^sub>0"

    sublocale invertible_modification
                V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1 \<tau>\<^sub>0 \<tau>\<^sub>1 map
      using D.comp_arr_dom D.comp_cod_arr
      by unfold_locales auto

  end

  locale composite_modification =  (* 13 sec *)
    C: bicategory V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C +
    D: bicategory V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D +
    \<rho>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<rho>\<^sub>0 \<rho>\<^sub>1 +
    \<sigma>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<sigma>\<^sub>0 \<sigma>\<^sub>1 +
    \<tau>: pseudonatural_transformation
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<tau>\<^sub>0 \<tau>\<^sub>1 +
    \<Gamma>: modification
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<rho>\<^sub>0 \<rho>\<^sub>1 \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<Gamma> +
    \<Delta>: modification
         V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<sigma>\<^sub>0 \<sigma>\<^sub>1 \<tau>\<^sub>0 \<tau>\<^sub>1 \<Delta>
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
  and \<rho>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<rho>\<^sub>1 :: "'c \<Rightarrow> 'd"
  and \<sigma>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<sigma>\<^sub>1 :: "'c \<Rightarrow> 'd"
  and \<tau>\<^sub>0 :: "'c \<Rightarrow> 'd"
  and \<tau>\<^sub>1 :: "'c \<Rightarrow> 'd"
  and \<Gamma> :: "'c \<Rightarrow> 'd"
  and \<Delta> :: "'c \<Rightarrow> 'd"
  begin

    abbreviation map
    where "map a \<equiv> \<Delta> a \<cdot>\<^sub>D \<Gamma> a"

    sublocale modification
                V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G \<rho>\<^sub>0 \<rho>\<^sub>1 \<tau>\<^sub>0 \<tau>\<^sub>1 map
      using \<Delta>.\<Gamma>_in_hom \<Gamma>.\<Gamma>_in_hom \<Delta>.naturality \<Gamma>.naturality
      apply unfold_locales
       apply auto[1]
    proof -
      fix f a b
      assume f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>" and ide_f: "C.ide f"
      have "\<tau>\<^sub>1 f \<cdot>\<^sub>D (G f \<star>\<^sub>D map a) = (\<tau>\<^sub>1 f \<cdot>\<^sub>D (G f \<star>\<^sub>D \<Delta> a)) \<cdot>\<^sub>D (G f \<star>\<^sub>D \<Gamma> a)"
      proof -
        have "D.seq (\<Delta> a) (\<Gamma> a)"
          using f \<Delta>.\<Gamma>_in_hom \<Gamma>.\<Gamma>_in_hom by blast
        thus ?thesis
          using f ide_f D.whisker_left [of "G f" "\<Delta> a" "\<Gamma> a"] D.comp_assoc
          by simp
      qed
      also have "... = (\<Delta> b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<sigma>\<^sub>1 f \<cdot>\<^sub>D (G f \<star>\<^sub>D \<Gamma> a)"
        using f ide_f \<Delta>.naturality [of f a b] D.comp_assoc by simp
      also have "... = ((\<Delta> b \<star>\<^sub>D F f) \<cdot>\<^sub>D (\<Gamma> b \<star>\<^sub>D F f)) \<cdot>\<^sub>D \<rho>\<^sub>1 f"
        using f ide_f \<Gamma>.naturality [of f a b] D.comp_assoc by simp
      also have "...  = (map b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<rho>\<^sub>1 f"
      proof -
        have "D.seq (\<Delta> b) (\<Gamma> b)"
          using f \<Delta>.\<Gamma>_in_hom \<Gamma>.\<Gamma>_in_hom by blast
        thus ?thesis
          using f ide_f D.whisker_right [of "F f" "\<Delta> b" "\<Gamma> b"] by simp
      qed
      finally show "\<tau>\<^sub>1 f \<cdot>\<^sub>D (G f \<star>\<^sub>D map a) = (map b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<rho>\<^sub>1 f" by simp
    qed

  end

  context converse_pseudonatural_equivalence
  begin

    interpretation EV: self_evaluation_map V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D ..
    notation EV.eval ("\<lbrace>_\<rbrace>")

    interpretation \<iota>\<^sub>F: identity_pseudonatural_transformation
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F
      ..
    interpretation \<iota>\<^sub>G: identity_pseudonatural_transformation
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G
      ..

    interpretation \<tau>'\<tau>: composite_pseudonatural_equivalence
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F G \<Phi>\<^sub>G F \<Phi>\<^sub>F
                          \<tau>\<^sub>0 \<tau>\<^sub>1 map\<^sub>0 map\<^sub>1
      ..
    interpretation \<tau>\<tau>': composite_pseudonatural_equivalence
                          V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G F \<Phi>\<^sub>F G \<Phi>\<^sub>G
                          map\<^sub>0 map\<^sub>1 \<tau>\<^sub>0 \<tau>\<^sub>1
      ..

    interpretation \<eta>: invertible_modification
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F F \<Phi>\<^sub>F
                        \<iota>\<^sub>F.map\<^sub>0 \<iota>\<^sub>F.map\<^sub>1 \<tau>'\<tau>.map\<^sub>0 \<tau>'\<tau>.map\<^sub>1 \<eta>
    proof
      show "\<And>a. C.obj a \<Longrightarrow> \<guillemotleft>\<eta> a : F.map\<^sub>0 a \<Rightarrow>\<^sub>D \<tau>'\<tau>.map\<^sub>0 a\<guillemotright>"
        using unit_in_hom \<tau>'\<tau>.map\<^sub>0_def by simp
      show "\<And>a. C.obj a \<Longrightarrow> D.iso (\<eta> a)"
        by simp
      show "\<And>f a b. \<lbrakk> \<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>; C.ide f\<rbrakk>
                       \<Longrightarrow> \<tau>'\<tau>.map\<^sub>1 f \<cdot>\<^sub>D (F f \<star>\<^sub>D \<eta> a) = (\<eta> b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<cdot>\<^sub>D \<r>\<^sub>D[F f]"
      proof -
        fix f a b
        assume f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>" and ide_f: "C.ide f"
        have a: "C.obj a" and b: "C.obj b"
          using f by auto
        have "\<tau>'\<tau>.map\<^sub>1 f \<cdot>\<^sub>D (F f \<star>\<^sub>D \<eta> a) =
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                 (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                 (\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                 ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                 (\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                 ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                 (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a)
                    \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                (F f \<star>\<^sub>D \<eta> a)"
          unfolding \<tau>'\<tau>.map\<^sub>1_def map\<^sub>1_def
          using a b f D.comp_assoc by auto
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D \<eta> a)"
        proof -
          have "(\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                (\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a)
                   \<star>\<^sub>D \<tau>\<^sub>0 a
                  = ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    (((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    ((\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    (((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    ((\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a)"
          proof -
            have "D.arr ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a))"
              using a b f ide_f \<tau>.iso_map\<^sub>1_ide
              by (intro D.seqI) auto
            thus ?thesis
              using a b f D.whisker_right [of "\<tau>\<^sub>0 a"] by fastforce
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (F f \<star>\<^sub>D \<eta> a)"
        proof -
          have "((\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] =
                \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a)"
            using a b f ide_f D.assoc'_naturality [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F f]" "\<tau>\<^sub>0' a" "\<tau>\<^sub>0 a"] by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         ((F\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<eta> a) = \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<eta> a"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F f]" "F f" "\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a" "\<eta> a"]
            by simp
          also have "... = ((F\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "F\<^sub>0 b \<star>\<^sub>D F f" "\<l>\<^sub>D\<^sup>-\<^sup>1[F f]" "\<eta> a" "F\<^sub>0 a"]
            by auto
          finally have "(\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D (F f \<star>\<^sub>D \<eta> a) =
                        ((F\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         (((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((F\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "(((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[F\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] =
                \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a)"
            using a b f ide_f D.assoc'_naturality [of "\<eta> b \<star>\<^sub>D F f" "\<tau>\<^sub>0' a" "\<tau>\<^sub>0 a"] by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D ((F\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a)
                  = (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<eta> b \<star>\<^sub>D F f" "F\<^sub>0 b \<star>\<^sub>D F f" "\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a" "\<eta> a"]
            by auto
          also have "... = (((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a)"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f" "\<eta> b \<star>\<^sub>D F f" "\<eta> a" "F\<^sub>0 a"]
            by auto
          finally have "((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D ((F\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) =
                        (((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "(((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                  ((\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) =
                ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a"
            using a b f ide_f D.whisker_right \<tau>.iso_map\<^sub>1_ide by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 a), \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a)) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "(((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] =
                \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 a), \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a)"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide
                  D.assoc'_naturality
                    [of "(\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]" "\<tau>\<^sub>0' a" "\<tau>\<^sub>0 a"]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 a), \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                  (((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) =
                ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]) \<cdot>\<^sub>D ((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D
                  (\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<eta> a"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide
                  D.interchange [of "(\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]"
                                    "(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f" "\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a" "\<eta> a"]
            by auto
          also have "... = (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<eta> a"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr D.comp_assoc
            by auto
          also have "... = (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                           \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]
                             \<star>\<^sub>D \<eta> a \<cdot>\<^sub>D F\<^sub>0 a"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr by auto
          also have "... = ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a)"
          proof -
            have "D.seq (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a) ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f])"
              using a b f ide_f \<tau>.iso_map\<^sub>1_ide
              by (intro D.seqI D.hseqI') auto
            thus ?thesis
              using a b f ide_f \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr
                    D.interchange [of "(\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a)"
                                      "(\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]"
                                      "\<eta> a" "F\<^sub>0 a"]
              by simp
          qed
          finally have "((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                          (((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f) \<star>\<^sub>D \<eta> a) =
                        ((\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                          ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, G\<^sub>0 a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 a), \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, F\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "(\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a
                  = (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, G\<^sub>0 a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                    (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a)"
          proof -
            have "(\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a
                    = (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                      (((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> a) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                      (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a)"
              using a b f ide_f D.hcomp_reassoc D.whisker_right [of "\<tau>\<^sub>0 a"] by auto
            also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, G\<^sub>0 a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a)"
              using a b f ide_f D.hcomp_reassoc(1) [of "\<tau>\<^sub>0' b \<star>\<^sub>D G f" "\<epsilon> a" "\<tau>\<^sub>0 a"]
              by auto
            finally show ?thesis by blast
          qed
          moreover have "(\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<eta> a
                           = (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, F\<^sub>0 a]) \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a)"
          proof -
            have "(\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<eta> a =
                  \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D
                    (\<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D \<eta> a \<cdot>\<^sub>D F\<^sub>0 a"
              using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                    D.hcomp_reassoc(2) [of "\<tau>\<^sub>0' b" "G f" "\<tau>\<^sub>0 a"]
              by auto
            also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                             (((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a) \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a)"
              using a b f ide_f D.inv_inv D.iso_inv_iso D.interchange by auto
            also have "... = (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<eta> a) \<cdot>\<^sub>D
                             \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, F\<^sub>0 a]) \<cdot>\<^sub>D
                             (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a)"
              using a b f ide_f D.hcomp_reassoc(1) [of "\<tau>\<^sub>0' b \<star>\<^sub>D G f" "\<tau>\<^sub>0 a" "\<eta> a"] by auto
            finally show ?thesis by blast
          qed
          ultimately show ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, G\<^sub>0 a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         (((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<eta> a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, F\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "\<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 a), \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a] =
                (\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]"
          proof -
            have "\<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                    (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D (G f \<star>\<^sub>D \<tau>\<^sub>0 a), \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                    (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a \<star>\<^sub>D \<tau>\<^sub>0 a]
                      = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                        (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>) \<^bold>\<cdot>
                        ((\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[ \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>) \<^bold>\<cdot>
                        (\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>G f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>) \<^bold>\<cdot>
                        \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> (\<^bold>\<langle>G f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>), \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                        (\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>) \<^bold>\<cdot>
                        \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by auto
            also have "... = \<lbrace>(\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using a b f ide_f by (intro EV.eval_eqI, auto)
            also have "... = (\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by auto
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, G\<^sub>0 a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, F\<^sub>0 a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          interpret adjoint_equivalence_in_bicategory
                      V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 a\<close> \<open>\<tau>\<^sub>0' a\<close> \<open>\<eta> a\<close> \<open>\<epsilon> a\<close>
            using a chosen_adjoint_equivalence by simp
          have "((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<eta> a)
                  = (\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D (\<epsilon> a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 a \<star>\<^sub>D \<eta> a)"
            using a b f ide_f D.whisker_left by auto
          also have "... = (\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]"
            using triangle_left by simp
          finally have "((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<epsilon> a \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a, \<tau>\<^sub>0' a, \<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<eta> a)
                          = (\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         (\<r>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a)) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, G\<^sub>0 a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, F\<^sub>0 a]) \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a)
                  = \<r>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a]"
          proof -
            have "\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                  (\<a>\<^sub>D[\<tau>\<^sub>0' b, G f, G\<^sub>0 a] \<star>\<^sub>D \<tau>\<^sub>0 a) \<cdot>\<^sub>D
                  (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D G f, G\<^sub>0 a, \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' b \<star>\<^sub>D G f) \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 a] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f, \<tau>\<^sub>0 a, F\<^sub>0 a]) \<cdot>\<^sub>D
                  (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, G f, \<tau>\<^sub>0 a] \<star>\<^sub>D F\<^sub>0 a)
                    = \<lbrace>\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                      ((\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<r>\<^bold>[\<^bold>\<langle>G f\<^bold>\<rangle>\<^bold>]) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>) \<^bold>\<cdot>
                      (\<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>G\<^sub>0 a\<^bold>\<rangle>\<^sub>0\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>) \<^bold>\<cdot>
                      (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>G\<^sub>0 a\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                      ((\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> \<^bold>\<r>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                      \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 a\<^bold>\<rangle>\<^sub>0\<^bold>]) \<^bold>\<cdot>
                      (\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>G f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>F\<^sub>0 a\<^bold>\<rangle>\<^sub>0)\<rbrace>"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char D.\<ll>_ide_simp D.\<rr>_ide_simp
              by auto
            also have "... = \<lbrace>\<^bold>\<r>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>G f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using a b f ide_f by (intro EV.eval_eqI, auto)
            also have "... = \<r>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a]"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char D.\<ll>_ide_simp D.\<rr>_ide_simp
              by auto
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)))) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D \<r>\<^sub>D[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f] \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "\<r>\<^sub>D[\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a] \<cdot>\<^sub>D
                ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D F\<^sub>0 a)
                  = (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D
                    \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                    \<r>\<^sub>D[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f]"
            using a b f ide_f D.comp_assoc \<tau>.iso_map\<^sub>1_ide
                  D.runit_naturality [of "(\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]"]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D
                          \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]) \<cdot>\<^sub>D
                          \<r>\<^sub>D[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f]) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D ((\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>1 f) \<cdot>\<^sub>D (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)))
                  = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]"
            using a b f ide_f D.comp_arr_inv' D.comp_arr_dom \<tau>.iso_map\<^sub>1_ide
                  D.whisker_left [of "\<tau>\<^sub>0' b" "\<tau>\<^sub>1 f" "D.inv (\<tau>\<^sub>1 f)"]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<r>\<^sub>D[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f] \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a)) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "(\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f]) \<cdot>\<^sub>D \<r>\<^sub>D[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f]
                  = \<r>\<^sub>D[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f]"
            using a b f ide_f D.comp_inv_arr' D.comp_cod_arr by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<eta> b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<r>\<^sub>D[F\<^sub>0 b \<star>\<^sub>D F f] \<cdot>\<^sub>D (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D F\<^sub>0 a)"
        proof -
          have "\<r>\<^sub>D[(\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f] \<cdot>\<^sub>D ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D F\<^sub>0 a)
                  = (\<eta> b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<r>\<^sub>D[F\<^sub>0 b \<star>\<^sub>D F f]"
            using a b f ide_f D.runit_naturality [of "\<eta> b \<star>\<^sub>D F f"] by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<eta> b \<star>\<^sub>D F f) \<cdot>\<^sub>D  \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<cdot>\<^sub>D \<r>\<^sub>D[F f]"
          using a b f ide_f D.runit_naturality [of "\<l>\<^sub>D\<^sup>-\<^sup>1[F f]"] by auto
        finally show "\<tau>'\<tau>.map\<^sub>1 f \<cdot>\<^sub>D (F f \<star>\<^sub>D \<eta> a) = (\<eta> b \<star>\<^sub>D F f) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<cdot>\<^sub>D \<r>\<^sub>D[F f]"
          by blast
      qed
    qed

    lemma unit_is_invertible_modification:
    shows "invertible_modification
                     V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D F \<Phi>\<^sub>F F \<Phi>\<^sub>F
                     \<iota>\<^sub>F.map\<^sub>0 \<iota>\<^sub>F.map\<^sub>1 \<tau>'\<tau>.map\<^sub>0 \<tau>'\<tau>.map\<^sub>1 \<eta>"
      ..

    interpretation \<epsilon>: invertible_modification
                        V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G G \<Phi>\<^sub>G
                        \<tau>\<tau>'.map\<^sub>0 \<tau>\<tau>'.map\<^sub>1 \<iota>\<^sub>G.map\<^sub>0 \<iota>\<^sub>G.map\<^sub>1 \<epsilon>
    proof
      show "\<And>a. C.obj a \<Longrightarrow> \<guillemotleft>\<epsilon> a : \<tau>\<tau>'.map\<^sub>0 a \<Rightarrow>\<^sub>D G\<^sub>0 a\<guillemotright>"
        using counit_in_hom \<tau>\<tau>'.map\<^sub>0_def by simp
      show "\<And>a. C.obj a \<Longrightarrow> D.iso (\<epsilon> a)"
        by simp
      show "\<And>f a b. \<lbrakk>\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>; C.ide f\<rbrakk>
                       \<Longrightarrow> (\<l>\<^sub>D\<^sup>-\<^sup>1[G f] \<cdot>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> a) = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D \<tau>\<tau>'.map\<^sub>1 f"
      proof -
        fix f a b
        assume f: "\<guillemotleft>f : a \<rightarrow>\<^sub>C b\<guillemotright>" and ide_f: "C.ide f"
        have a: "C.obj a" and b: "C.obj b"
          using f by auto
        have "(\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D \<tau>\<tau>'.map\<^sub>1 f
                = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D 
                  \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f] \<cdot>\<^sub>D
                  (\<tau>\<^sub>0 b \<star>\<^sub>D
                     (\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                     (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                     (\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                     \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                     ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                     (\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                     ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                     (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                  (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
          unfolding \<tau>\<tau>'.map\<^sub>1_def map\<^sub>1_def
          using a b f D.comp_assoc by auto
        also have "... = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D 
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "\<tau>\<^sub>0 b \<star>\<^sub>D
                  (\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                  (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                  (\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  (\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 b \<star>\<^sub>D (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                    (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a)"
          proof -
            have "D.arr ((\<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a))"
              using a b f ide_f \<tau>.iso_map\<^sub>1_ide
              by (intro D.seqI) auto
            thus ?thesis
              using a b f D.whisker_left [of "\<tau>\<^sub>0 b"] by fastforce
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D 
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "(\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                (\<tau>\<^sub>0 b \<star>\<^sub>D (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                           ((\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a b f ide_f D.whisker_left [of "\<tau>\<^sub>0 b"] \<tau>.iso_map\<^sub>1_ide by auto
          also have "... = \<tau>\<^sub>0 b \<star>\<^sub>D (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                                  \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide
                  D.assoc_naturality [of "\<tau>\<^sub>0' b" "D.inv (\<tau>\<^sub>1 f)" "\<tau>\<^sub>0' a"]
            by auto
          also have "... = (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                           (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a])"
            using a b f ide_f D.whisker_left [of "\<tau>\<^sub>0 b"] \<tau>.iso_map\<^sub>1_ide by auto
          finally have "(\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                        (\<tau>\<^sub>0 b \<star>\<^sub>D (\<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f)) \<star>\<^sub>D \<tau>\<^sub>0' a)
                          = (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a])"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D 
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "(\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a b f ide_f D.whisker_left \<tau>.iso_map\<^sub>1_ide by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D 
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f \<star>\<^sub>D G\<^sub>0 a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f] \<cdot>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<r>\<^sub>D[G f])
                  = ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f \<star>\<^sub>D G\<^sub>0 a]"
            using a b f ide_f D.assoc'_naturality [of "\<tau>\<^sub>0 b" "\<tau>\<^sub>0' b" "\<r>\<^sub>D[G f]"]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D 
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a))) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f \<star>\<^sub>D G\<^sub>0 a] \<cdot>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a)
                  = ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a]"
            using a b f ide_f D.assoc'_naturality [of "\<tau>\<^sub>0 b" "\<tau>\<^sub>0' b" "G f \<star>\<^sub>D \<epsilon> a"]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D 
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<r>\<^sub>D[G f])) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a))
                  = ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a]"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide
                  D.assoc'_naturality
                    [of "\<tau>\<^sub>0 b" "\<tau>\<^sub>0' b" "\<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)"]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         ((\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a)) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "(\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<r>\<^sub>D[G f]) = \<epsilon> b \<star>\<^sub>D \<r>\<^sub>D[G f]"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<epsilon> b" "\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b" "G f" "\<r>\<^sub>D[G f]"]
            by simp
          also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D (\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 a)"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "G\<^sub>0 b" "\<epsilon> b" "\<r>\<^sub>D[G f]" "G f \<star>\<^sub>D G\<^sub>0 a"]
            by auto
          finally have "(\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<r>\<^sub>D[G f]) =
                        (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D (\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         ((\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a))) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "(\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 a) \<cdot>\<^sub>D ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a)
                  = \<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "\<epsilon> b" "\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b" "G f \<star>\<^sub>D G\<^sub>0 a" "G f \<star>\<^sub>D \<epsilon> a"]
            by auto
          also have "... = (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D (\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                  D.interchange [of "G\<^sub>0 b" "\<epsilon> b" "G f \<star>\<^sub>D \<epsilon> a" "G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a"]
            by auto
          finally have "(\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D G\<^sub>0 a) \<cdot>\<^sub>D ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) =
                        (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D (\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (\<epsilon> b \<star>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have 1: "D.seq (G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a)
                         (\<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a))"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide
            by (intro D.seqI D.hseqI') auto
          have 2: "D.seq (\<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a))
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide
            by (intro D.seqI D.hseqI') auto
          have "(\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) =
                \<epsilon> b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using 1 a b f ide_f D.comp_arr_dom D.comp_cod_arr \<tau>.iso_map\<^sub>1_ide
                  D.interchange [of "\<epsilon> b" "\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b" "G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a"
                                    "\<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)"]
            by auto
          also have "... = G\<^sub>0 b \<cdot>\<^sub>D \<epsilon> b \<star>\<^sub>D
                             (\<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                             ((\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide D.comp_arr_dom D.comp_cod_arr by auto
          also have "... = (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                           (\<epsilon> b \<star>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using 2 a b f ide_f \<tau>.iso_map\<^sub>1_ide D.comp_assoc
                  D.interchange [of "G\<^sub>0 b" "\<epsilon> b"
                                    "\<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
                                    "(\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a"]
            by simp
          finally have "(\<epsilon> b \<star>\<^sub>D G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                        ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a))
                          = (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                            (\<epsilon> b \<star>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            by blast
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[G\<^sub>0 b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "\<epsilon> b \<star>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a
                  = (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                    (\<a>\<^sub>D[G\<^sub>0 b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                    ((\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                    \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                    ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a])"
          proof -
            have "\<epsilon> b \<star>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a
                    = (G\<^sub>0 b \<cdot>\<^sub>D \<epsilon> b \<cdot>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b)) \<star>\<^sub>D
                      \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]"
              using a b f ide_f D.comp_arr_dom D.comp_cod_arr
                    D.hcomp_reassoc(1) [of "\<tau>\<^sub>0 b" "F f" "\<tau>\<^sub>0' a"]
              by auto
           also have "... = (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                            (\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a])"
             using a b f ide_f D.comp_arr_dom D.comp_cod_arr D.assoc'_is_natural_1
                   D.interchange [of "G\<^sub>0 b" "\<epsilon> b \<cdot>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b)" "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]"
                                     "(\<tau>\<^sub>0 b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]"]
                   D.interchange [of "\<epsilon> b" "\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b" "\<tau>\<^sub>0 b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a"
                                     "\<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]"]
             by fastforce
           also have "... = (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[G\<^sub>0 b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                            ((\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a])"
              using a b f ide_f D.hcomp_reassoc(2) [of "\<epsilon> b" "\<tau>\<^sub>0 b" "F f \<star>\<^sub>D \<tau>\<^sub>0' a"]
              by auto
           finally show ?thesis by blast
         qed
         moreover have "\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a
                          = (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                            (\<a>\<^sub>D[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                            ((\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                            \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                            (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a])"
         proof -
           have "\<tau>\<^sub>0 b \<star>\<^sub>D (\<eta> b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a =
                 (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                   (\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                   (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a])"
             using a b f ide_f D.hcomp_reassoc(1) [of "\<eta> b" "F f" "\<tau>\<^sub>0' a"]
                   D.whisker_left [of "\<tau>\<^sub>0 b"]
             by auto
           also have "... = (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                              (\<a>\<^sub>D[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                              ((\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                              \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                              (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a])"
             using a b f ide_f D.hcomp_reassoc(2) [of "\<tau>\<^sub>0 b" "\<eta> b" "F f \<star>\<^sub>D \<tau>\<^sub>0' a"]
             by auto
           finally show ?thesis by blast
         qed
         ultimately show ?thesis
           using D.comp_assoc by simp
       qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[G\<^sub>0 b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (((\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, \<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         ((\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
       proof -
         have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
               ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
               \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
               (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
               (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
               (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
               \<a>\<^sub>D[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]
                 = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, \<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a"
         proof -
           have "\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                 ((\<tau>\<^sub>0 b \<star>\<^sub>D \<tau>\<^sub>0' b) \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                 \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, (\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                 (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b \<star>\<^sub>D F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                 (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[\<tau>\<^sub>0' b, \<tau>\<^sub>0 b, F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                 (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                 \<a>\<^sub>D[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b \<star>\<^sub>D \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]
                   = \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                     ((\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                     \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, (\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                     (\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                     (\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>) \<^bold>\<cdot>
                     (\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                     \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by auto
            also have "... = \<lbrace>\<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' b\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<rbrace>"
              using a b f ide_f by (intro EV.eval_eqI, auto)
            also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, \<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char
              by auto
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by auto
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         ((G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<a>\<^sub>D[G\<^sub>0 b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         (\<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "((\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, \<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                ((\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a)
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a"
          proof -
            interpret adjoint_equivalence_in_bicategory
                        V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D \<open>\<tau>\<^sub>0 b\<close> \<open>\<tau>\<^sub>0' b\<close> \<open>\<eta> b\<close> \<open>\<epsilon> b\<close>
              using b chosen_adjoint_equivalence by simp
            have "((\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  (\<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, \<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  ((\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a)
                    = (\<epsilon> b \<star>\<^sub>D \<tau>\<^sub>0 b) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, \<tau>\<^sub>0' b, \<tau>\<^sub>0 b] \<cdot>\<^sub>D (\<tau>\<^sub>0 b \<star>\<^sub>D \<eta> b) \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a"
              using a b f ide_f D.whisker_right by auto
            also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a"
              using triangle_left by simp
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         ((G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "(G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                (\<a>\<^sub>D[G\<^sub>0 b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                (\<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a]"
          proof -
            have "(G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                  (\<a>\<^sub>D[G\<^sub>0 b, \<tau>\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                  (\<l>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b] \<cdot>\<^sub>D \<r>\<^sub>D[\<tau>\<^sub>0 b] \<star>\<^sub>D F f \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  \<a>\<^sub>D\<^sup>-\<^sup>1[\<tau>\<^sub>0 b, F\<^sub>0 b, F f \<star>\<^sub>D \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                  (\<tau>\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[F\<^sub>0 b, F f, \<tau>\<^sub>0' a]) \<cdot>\<^sub>D
                  (\<tau>\<^sub>0 b \<star>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[F f] \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                  \<a>\<^sub>D[\<tau>\<^sub>0 b, F f, \<tau>\<^sub>0' a]
                    = \<lbrace>(\<^bold>\<langle>G\<^sub>0 b\<^bold>\<rangle>\<^sub>0 \<^bold>\<star> \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                      (\<^bold>\<a>\<^bold>[\<^bold>\<langle>G\<^sub>0 b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot>
                      (\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>\<^bold>] \<^bold>\<cdot> \<^bold>\<r>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>) \<^bold>\<cdot>
                      \<^bold>\<a>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F\<^sub>0 b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                      (\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<a>\<^bold>[\<^bold>\<langle>F\<^sub>0 b\<^bold>\<rangle>\<^sub>0, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]) \<^bold>\<cdot>
                      (\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[\<^bold>\<langle>F f\<^bold>\<rangle>\<^bold>] \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>) \<^bold>\<cdot>
                      \<^bold>\<a>\<^bold>[\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle>, \<^bold>\<langle>F f\<^bold>\<rangle>, \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char D.\<ll>_ide_simp D.\<rr>_ide_simp
              by auto
            also have "... = \<lbrace>\<^bold>\<l>\<^sup>-\<^sup>1\<^bold>[(\<^bold>\<langle>\<tau>\<^sub>0 b\<^bold>\<rangle> \<^bold>\<star> \<^bold>\<langle>F f\<^bold>\<rangle>) \<^bold>\<star> \<^bold>\<langle>\<tau>\<^sub>0' a\<^bold>\<rangle>\<^bold>]\<rbrace>"
              using a b f ide_f by (intro EV.eval_eqI, auto)
            also have "... = \<l>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a]"
              using a b f ide_f D.\<alpha>_def D.\<alpha>'.map_ide_simp D.VVV.ide_char D.VVV.arr_char
                    D.VV.ide_char D.VV.arr_char D.\<ll>_ide_simp
              by auto
            finally show ?thesis by blast
          qed
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         ((D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D
                         (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "(G\<^sub>0 b \<star>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D
                \<l>\<^sub>D\<^sup>-\<^sup>1[(\<tau>\<^sub>0 b \<star>\<^sub>D F f) \<star>\<^sub>D \<tau>\<^sub>0' a]
                  = \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                    \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                    (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide
                  D.lunit'_naturality [of "\<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D (D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a)"]
            by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D
                         \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
        proof -
          have "((D.inv (\<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D (\<tau>\<^sub>1 f \<star>\<^sub>D \<tau>\<^sub>0' a)) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] =
                ((D.inv (\<tau>\<^sub>1 f) \<cdot>\<^sub>D \<tau>\<^sub>1 f) \<star>\<^sub>D \<tau>\<^sub>0' a) \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide D.whisker_right [of "\<tau>\<^sub>0' a"] by simp
          also have "... = \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a]"
            using a b f ide_f \<tau>.iso_map\<^sub>1_ide D.comp_inv_arr' D.comp_cod_arr by auto
          finally show ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D
                         (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D
                         \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a]"
        proof -
          have "\<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] \<cdot>\<^sub>D \<a>\<^sub>D[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] \<cdot>\<^sub>D \<a>\<^sub>D\<^sup>-\<^sup>1[G f, \<tau>\<^sub>0 a, \<tau>\<^sub>0' a] =
                \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a]"
            using a b f ide_f D.comp_arr_inv' D.comp_arr_dom by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = ((G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D G\<^sub>0 a]) \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> a)"
        proof -
          have "(G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D (G\<^sub>0 b \<star>\<^sub>D G f \<star>\<^sub>D \<epsilon> a) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D \<tau>\<^sub>0 a \<star>\<^sub>D \<tau>\<^sub>0' a] =
                (G\<^sub>0 b \<star>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D \<l>\<^sub>D\<^sup>-\<^sup>1[G f \<star>\<^sub>D G\<^sub>0 a] \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> a)"
            using a b f ide_f D.lunit'_naturality [of "G f \<star>\<^sub>D \<epsilon> a"] by auto
          thus ?thesis
            using D.comp_assoc by simp
        qed
        also have "... = (\<l>\<^sub>D\<^sup>-\<^sup>1[G f] \<cdot>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> a)"
          using a b f ide_f D.lunit'_naturality [of "\<r>\<^sub>D[G f]"] by auto
        finally show "(\<l>\<^sub>D\<^sup>-\<^sup>1[G f] \<cdot>\<^sub>D \<r>\<^sub>D[G f]) \<cdot>\<^sub>D (G f \<star>\<^sub>D \<epsilon> a) = (\<epsilon> b \<star>\<^sub>D G f) \<cdot>\<^sub>D \<tau>\<tau>'.map\<^sub>1 f"
          by simp
      qed
    qed

    lemma counit_is_invertible_modification:
    shows "invertible_modification
             V\<^sub>C H\<^sub>C \<a>\<^sub>C \<i>\<^sub>C src\<^sub>C trg\<^sub>C V\<^sub>D H\<^sub>D \<a>\<^sub>D \<i>\<^sub>D src\<^sub>D trg\<^sub>D G \<Phi>\<^sub>G G \<Phi>\<^sub>G
             \<tau>\<tau>'.map\<^sub>0 \<tau>\<tau>'.map\<^sub>1 \<iota>\<^sub>G.map\<^sub>0 \<iota>\<^sub>G.map\<^sub>1 \<epsilon>"
      ..

  end

end


