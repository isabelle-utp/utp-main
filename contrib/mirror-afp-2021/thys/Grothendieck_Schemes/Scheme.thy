
text \<open>Authors: Anthony Bordg and Lawrence Paulson,
with some contributions from Wenda Li\<close>

theory Scheme
imports "Comm_Ring"

begin

section \<open>Misc\<close> 

lemma (in Set_Theory.map) set_map_\<alpha>_cong:
  assumes \<alpha>_eq:"\<And>x. x\<in>S \<Longrightarrow> \<alpha>' x  = \<alpha> x" and \<alpha>_ext:"\<alpha>' \<in> extensional S"       
  shows "Set_Theory.map \<alpha>' S T"
using map_axioms \<alpha>_eq \<alpha>_ext
unfolding Set_Theory.map_def by (auto simp:extensional_def)

lemma (in monoid_homomorphism) monoid_homomorphism_\<eta>_cong:
  assumes \<eta>_eq:"\<And>x. x\<in>M \<Longrightarrow> \<eta>' x  = \<eta> x" and \<eta>_ext:"\<eta>' \<in> extensional M"
  shows "monoid_homomorphism \<eta>' M (\<cdot>) \<one> M' (\<cdot>') \<one>'"
proof -
  have "Set_Theory.map \<eta>' M M'"
    using set_map_\<alpha>_cong \<eta>_eq \<eta>_ext by auto
  moreover have "monoid_homomorphism_axioms \<eta>' M (\<cdot>) \<one> (\<cdot>') \<one>'" 
    unfolding monoid_homomorphism_axioms_def
    by (simp add: \<eta>_eq commutes_with_composition commutes_with_unit)
  ultimately show ?thesis
    unfolding monoid_homomorphism_def 
    using source.monoid_axioms target.monoid_axioms by blast
qed

lemma (in group_homomorphism) group_homomorphism_\<eta>_cong:
  assumes \<eta>_eq:"\<And>x. x\<in>G \<Longrightarrow> \<eta>' x  = \<eta> x" and \<eta>_ext:"\<eta>' \<in> extensional G"
  shows "group_homomorphism \<eta>' G (\<cdot>) \<one> G' (\<cdot>') \<one>'"
  by (simp add: \<eta>_eq \<eta>_ext group_homomorphism_def monoid_homomorphism_\<eta>_cong source.group_axioms 
      target.group_axioms)

lemma (in ring_homomorphism) ring_homomorphism_\<eta>_cong:
  assumes \<eta>_eq:"\<And>x. x\<in>R \<Longrightarrow> \<eta>' x  = \<eta> x" and \<eta>_ext:"\<eta>' \<in> extensional R"
  shows "ring_homomorphism \<eta>' R (+) (\<cdot>) \<zero> \<one> R' (+') (\<cdot>') \<zero>' \<one>'"
  unfolding ring_homomorphism_def
  using \<eta>_eq \<eta>_ext additive.group_homomorphism_\<eta>_cong multiplicative.monoid_homomorphism_\<eta>_cong 
    set_map_\<alpha>_cong source.ring_axioms target.ring_axioms by presburger

lemma (in morphism_presheaves_of_rings) morphism_presheaves_of_rings_fam_cong:
  assumes fam_eq:"\<And>U x. \<lbrakk> is_open U; x\<in>\<FF> U\<rbrakk> \<Longrightarrow> fam_morphisms' U x= fam_morphisms U x"
    and fam_ext:"\<And>U. is_open U \<Longrightarrow> fam_morphisms' U \<in> extensional (\<FF> U)"
  shows "morphism_presheaves_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str \<FF>' \<rho>' b' 
      add_str' mult_str'
      zero_str' one_str' fam_morphisms'"
proof -
  have " presheaf_of_rings X is_open \<FF> \<rho> b add_str mult_str zero_str one_str"
    using source.presheaf_of_rings_axioms .
  moreover have "presheaf_of_rings X is_open \<FF>' \<rho>' b' add_str' mult_str' zero_str' one_str'" 
    using target.presheaf_of_rings_axioms .
  moreover have "
    morphism_presheaves_of_rings_axioms is_open \<FF> \<rho> add_str mult_str zero_str one_str \<FF>' \<rho>' add_str' mult_str'
     zero_str' one_str' fam_morphisms'"
  proof -
    have "ring_homomorphism (fam_morphisms' U) (\<FF> U) +\<^bsub>U\<^esub> \<cdot>\<^bsub>U\<^esub> \<zero>\<^bsub>U\<^esub> \<one>\<^bsub>U\<^esub> (\<FF>' U) +'\<^bsub>U\<^esub> \<cdot>'\<^bsub>U\<^esub> \<zero>'\<^bsub>U\<^esub> \<one>'\<^bsub>U\<^esub>"
      if "is_open U" for U
      apply (rule is_ring_morphism[OF that,THEN ring_homomorphism.ring_homomorphism_\<eta>_cong])
      using fam_eq fam_ext 
      by (auto simp add: that)
    moreover have "(\<rho>' U V \<circ> fam_morphisms' U) x = (fam_morphisms' V \<circ> \<rho> U V) x" 
      if "is_open U" "is_open V" "V \<subseteq> U" "x \<in> \<FF> U" for U V x 
      by (metis calculation comm_diagrams fam_eq fam_morphisms_are_maps map_eq ring_homomorphism_def 
          that(1) that(2) that(3) that(4))
    ultimately show ?thesis
      using comm_diagrams is_ring_morphism 
      unfolding morphism_presheaves_of_rings_axioms_def by auto
  qed
  ultimately show ?thesis 
    unfolding morphism_presheaves_of_rings_def by auto
qed


section \<open>Affine Schemes\<close>

text \<open>Computational affine schemes take the isomorphism with Spec as part of their data,
while in the locale for affine schemes we merely assert the existence of such an isomorphism.\<close> 

locale affine_scheme = comm_ring +
locally_ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str +
iso_locally_ringed_spaces X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
"Spec" is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b "\<lambda>U. add_sheaf_spec U"
"\<lambda>U. mult_sheaf_spec U" "\<lambda>U. zero_sheaf_spec U" "\<lambda>U. one_sheaf_spec U" f \<phi>\<^sub>f
for X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str f \<phi>\<^sub>f

section \<open>Schemes\<close>

(* def. 0.47 *)
locale scheme = comm_ring + 
locally_ringed_space X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str 
for X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str +
  assumes are_affine_schemes: "\<And>x. x \<in> X \<Longrightarrow> (\<exists>U. x\<in>U \<and> is_open U \<and> 
(\<exists>f \<phi>\<^sub>f. affine_scheme  R (+) (\<cdot>) \<zero> \<one> U (ind_topology.ind_is_open X is_open U) (ind_sheaf.ind_sheaf \<O>\<^sub>X U) 
(ind_sheaf.ind_ring_morphisms \<rho> U) b (ind_sheaf.ind_add_str add_str U)
(ind_sheaf.ind_mult_str mult_str U) (ind_sheaf.ind_zero_str zero_str U)
(ind_sheaf.ind_one_str one_str U) f \<phi>\<^sub>f))"

locale iso_stalks = 
  stk1:stalk S is_open \<FF>1 \<rho>1 b add_str1 mult_str1 zero_str1 one_str1 I x +
  stk2:stalk S is_open \<FF>2 \<rho>2 b add_str2 mult_str2 zero_str2 one_str2 I x
  for S is_open \<FF>1 \<rho>1 b add_str1 mult_str1 zero_str1 one_str1 I x 
        \<FF>2 \<rho>2 add_str2 mult_str2 zero_str2 one_str2 +
  assumes 
    stalk_eq:"\<forall>U\<in>I. \<FF>1 U = \<FF>2 U \<and> add_str1 U = add_str2 U \<and> mult_str1 U = mult_str2 U 
            \<and> zero_str1 U = zero_str2 U \<and> one_str1 U = one_str2 U"
    and stalk\<rho>_eq:"\<forall>U V. U\<in>I \<and> V \<in>I \<longrightarrow> \<rho>1 U V = \<rho>2 U V"
begin

lemma 
  assumes "U \<in> I"
  shows has_ring_isomorphism:"ring_isomorphism (identity stk1.carrier_stalk) stk1.carrier_stalk 
          stk1.add_stalk stk1.mult_stalk (stk1.zero_stalk U) (stk1.one_stalk U)
          stk2.carrier_stalk stk2.add_stalk stk2.mult_stalk (stk2.zero_stalk U) (stk2.one_stalk U)"
   and carrier_stalk_eq:"stk1.carrier_stalk = stk2.carrier_stalk"
   and class_of_eq:"stk1.class_of = stk2.class_of"
proof -
  have "is_open U" "x \<in> U"
    using stk1.index assms by auto
  interpret ring1:ring stk1.carrier_stalk stk1.add_stalk stk1.mult_stalk "stk1.zero_stalk U" 
                  "stk1.one_stalk U"
    using stk1.stalk_is_ring[OF \<open>is_open U\<close> \<open>x \<in> U\<close>] .
  interpret ring2:ring stk2.carrier_stalk stk2.add_stalk stk2.mult_stalk "stk2.zero_stalk U"
                  "stk2.one_stalk U"
    using stk2.stalk_is_ring[OF \<open>is_open U\<close> \<open>x \<in> U\<close>] .

  interpret e1:equivalence "Sigma I \<FF>1" "{(x, y). stk1.rel x y}"
    using stk1.rel_is_equivalence .
  interpret e2:equivalence "Sigma I \<FF>2" "{(x, y). stk2.rel x y}"
    using stk2.rel_is_equivalence .

  have Sigma_eq:"Sigma I \<FF>1  =  Sigma I \<FF>2"
  proof (rule Sigma_cong[OF refl])
    fix x assume "x \<in> I" 
    from stalk_eq[rule_format,OF this]
    show "\<FF>1 x = \<FF>2 x" by simp
  qed
  moreover have "stk1.rel xx yy \<longleftrightarrow> stk2.rel xx yy" 
                  if "xx\<in>Sigma I \<FF>1" "yy\<in>Sigma I \<FF>2"
                  for xx yy 
    unfolding stk1.rel_def stk2.rel_def                
    by (metis stalk\<rho>_eq stalk_eq)          
  ultimately have Class_eq: "e1.Class = e2.Class" 
    unfolding e1.Class_def e2.Class_def
    by (auto intro!:ext)
  then show class_of_eq:"stk1.class_of = stk2.class_of"
    unfolding stk1.class_of_def stk2.class_of_def by auto

  show "stk1.carrier_stalk = stk2.carrier_stalk"
    using Class_eq Sigma_eq e1.natural.surjective e2.natural.surjective 
      stk1.carrier_direct_lim_def stk1.carrier_stalk_def stk2.carrier_direct_lim_def 
      stk2.carrier_stalk_def stk2.neighborhoods_eq by force

  let ?id = "identity stk1.carrier_stalk"
  show "ring_isomorphism (identity stk1.carrier_stalk) stk1.carrier_stalk 
          stk1.add_stalk stk1.mult_stalk (stk1.zero_stalk U) (stk1.one_stalk U)
          stk2.carrier_stalk stk2.add_stalk stk2.mult_stalk (stk2.zero_stalk U) (stk2.one_stalk U)"
  proof
    show "?id (stk1.one_stalk U) = stk2.one_stalk U" 
    proof -
      have "stk1.one_stalk U \<in> stk1.carrier_stalk" by blast
      then have "?id (stk1.one_stalk U) = stk1.one_stalk U" by auto
      also have "... = stk2.one_stalk U"
        unfolding stk1.one_stalk_def stk2.one_stalk_def class_of_eq
        by (simp add: assms stalk_eq)
      finally show ?thesis .
    qed
    show "?id (stk1.zero_stalk U) = stk2.zero_stalk U" 
    proof -
      have "stk1.zero_stalk U \<in> stk1.carrier_stalk" by blast
      then have "?id (stk1.zero_stalk U) = stk1.zero_stalk U" by auto
      also have "... = stk2.zero_stalk U"
        unfolding stk1.zero_stalk_def stk2.zero_stalk_def class_of_eq
        by (simp add: assms stalk_eq)
      finally show ?thesis .
    qed

   
    show "?id (stk1.add_stalk X' Y') = stk2.add_stalk (?id X') (?id Y')" 
      "?id (stk1.mult_stalk X' Y') = stk2.mult_stalk (?id X') (?id Y')" 
      if "X' \<in> stk1.carrier_stalk" "Y' \<in> stk1.carrier_stalk" for X' Y'
    proof -
      define x where "x=(SOME x. x \<in> X')"
      define y where "y=(SOME y. y \<in> Y')"
      have x:"x\<in>X'" "x\<in>Sigma I \<FF>1" and x_alt:"X' = stk1.class_of (fst x) (snd x)"
        using stk1.rel_carrier_Eps_in that(1) stk1.carrier_stalk_def stk2.neighborhoods_eq x_def 
        by auto
      have y:"y\<in>Y'" "y\<in>Sigma I \<FF>1" and y_alt:"Y' = stk1.class_of (fst y) (snd y)"
        using stk1.rel_carrier_Eps_in that(2) stk1.carrier_stalk_def stk2.neighborhoods_eq y_def 
        by auto
      obtain "fst x \<subseteq> S" "fst y \<subseteq> S"
        using x(2) y(2) stk1.index 
        by (metis mem_Sigma_iff prod.collapse stk1.open_imp_subset stk2.subset_of_opens)
      obtain w where w: "w\<in>I" "w \<subseteq> fst x" "w \<subseteq> fst y"
        using stk1.has_lower_bound x(2) y(2) by force
      have "w \<subseteq> S"  
        by (simp add: stk1.open_imp_subset stk1.subset_of_opens w(1))

      have "stk1.add_stalk X' Y' = stk1.class_of w (add_str1 w (\<rho>1 (fst x) w (snd x))
                                         (\<rho>1 (fst y) w (snd y)))"
        unfolding x_alt y_alt stk1.add_stalk_def
        apply (subst stk1.add_rel_class_of[where W=w])
        using x y w by auto
      also have "... = stk2.class_of w (add_str2 w (\<rho>2 (fst x) w (snd x)) (\<rho>2 (fst y) w (snd y)))"
        using class_of_eq stalk\<rho>_eq stalk_eq w(1) x(2) y(2) by force
      also have "... = stk2.add_stalk X' Y'"
        unfolding stk2.add_stalk_def x_alt y_alt class_of_eq   
        apply (subst stk2.add_rel_class_of[where W=w])
        using x y w by (auto simp add: Sigma_eq)
      finally have "stk1.add_stalk X' Y' = stk2.add_stalk X' Y'" .
      moreover have "stk1.add_stalk X' Y' \<in> stk1.carrier_stalk"
        by (simp add: that(1) that(2))
      ultimately show "?id (stk1.add_stalk X' Y') = stk2.add_stalk (?id X') (?id Y')" 
        using that by simp

      have "stk1.mult_stalk X' Y' = stk1.class_of w (mult_str1 w (\<rho>1 (fst x) w (snd x))
                                         (\<rho>1 (fst y) w (snd y)))"
        unfolding x_alt y_alt stk1.mult_stalk_def
        apply (subst stk1.mult_rel_class_of[where W=w])
        using x y w by auto
      also have "... = stk2.class_of w (mult_str2 w (\<rho>2 (fst x) w (snd x)) (\<rho>2 (fst y) w (snd y)))"
        using class_of_eq stalk\<rho>_eq stalk_eq w(1) x(2) y(2) by force
      also have "... = stk2.mult_stalk X' Y'"
        unfolding stk2.mult_stalk_def x_alt y_alt class_of_eq   
        apply (subst stk2.mult_rel_class_of[where W=w])
        using x y w by (auto simp add: Sigma_eq)
      finally have "stk1.mult_stalk X' Y' = stk2.mult_stalk X' Y'" .
      moreover have "stk1.mult_stalk X' Y' \<in> stk1.carrier_stalk"
        by (simp add: that(1) that(2))
      ultimately show "?id (stk1.mult_stalk X' Y') = stk2.mult_stalk (?id X') (?id Y')" 
        using that by simp
    qed

    from \<open>stk1.carrier_stalk = stk2.carrier_stalk\<close> 
    show "?id \<in> stk1.carrier_stalk \<rightarrow>\<^sub>E stk2.carrier_stalk"
      "bij_betw ?id stk1.carrier_stalk stk2.carrier_stalk"
      by (auto simp flip: id_def)
  qed
qed
end

lemma (in affine_scheme) affine_scheme_is_scheme:
  shows "scheme R (+) (\<cdot>) \<zero> \<one> X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str"
proof -
  interpret ind_sheaf X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str X
    by (metis ind_sheaf_axioms_def ind_sheaf_def open_space ringed_space_axioms ringed_space_def)
  have ind_is_open[simp]: "ind_topology.ind_is_open X is_open X = is_open"
    by (rule ext) (meson ind_is_open_iff_open open_imp_subset)

  interpret sheaf_of_rings X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str 
    ind_mult_str ind_zero_str ind_one_str
    using ind_sheaf_is_sheaf by force

  have eq_\<O>\<^sub>X: "local.ind_sheaf U = \<O>\<^sub>X U" if "U \<subseteq> X" for U
    using that by (simp add: Int_absorb2 Int_commute local.ind_sheaf_def)
  have eq_\<rho>: "\<And>U V. U \<subseteq> X \<and> V \<subseteq> X \<Longrightarrow> ind_ring_morphisms U V = \<rho> U V"
    by (simp add: ind_ring_morphisms_def inf.absorb_iff2)
  have eq_add_str: "\<And>U. U \<subseteq> X \<Longrightarrow> ind_add_str U = add_str U"
    by (simp add: ind_add_str_def inf.absorb_iff2)
  have eq_mult_str : "\<And>U. U \<subseteq> X \<Longrightarrow> ind_mult_str U = mult_str U"
    by (simp add: ind_mult_str_def inf.absorb_iff2)
  have eq_zero_str : "\<And>U. U \<subseteq> X \<Longrightarrow> ind_zero_str U = zero_str U"
    by (simp add: Int_absorb2 Int_commute ind_zero_str_def)
  have eq_one_str : "\<And>U. U \<subseteq> X \<Longrightarrow> ind_one_str U = one_str U"
    by (simp add: ind_one_str_def inf.absorb_iff2)

  have "affine_scheme R (+) (\<cdot>) \<zero> \<one> X is_open local.ind_sheaf ind_ring_morphisms b
          ind_add_str ind_mult_str ind_zero_str ind_one_str f \<phi>\<^sub>f"
  proof -
    have "locally_ringed_space X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str ind_mult_str ind_zero_str
     ind_one_str" 
    proof -
      have "stalk.is_local is_open local.ind_sheaf ind_ring_morphisms ind_add_str
                ind_mult_str ind_zero_str ind_one_str
                (neighborhoods u) u U"
        if "u \<in> U" and opeU: "is_open U" for u U
      proof -
        have UX: "U \<subseteq> X" by (simp add: opeU open_imp_subset)

        interpret stX: stalk X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str 
          ind_mult_str ind_zero_str ind_one_str "neighborhoods u" u
          apply (unfold_locales)
          unfolding neighborhoods_def using \<open>U \<subseteq> X\<close> \<open>u\<in>U\<close> by auto
        interpret stalk X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str "neighborhoods u" u
          by (meson direct_lim_def ind_sheaf.axioms(1) ind_sheaf_axioms stX.stalk_axioms stalk_def)
       
        have "local_ring carrier_stalk add_stalk mult_stalk (zero_stalk U) (one_stalk U)"
          using is_local_def opeU stalks_are_local that(1) by blast
        moreover have "ring_isomorphism (identity stX.carrier_stalk)
            stX.carrier_stalk stX.add_stalk stX.mult_stalk (stX.zero_stalk U) (stX.one_stalk U)
            carrier_stalk add_stalk mult_stalk (zero_stalk U) (one_stalk U)"
        proof -
          interpret iso_stalks X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str 
              ind_mult_str ind_zero_str ind_one_str "neighborhoods u" u \<O>\<^sub>X \<rho>  add_str mult_str 
              zero_str one_str 
            apply unfold_locales
            subgoal 
              by (simp add: eq_\<O>\<^sub>X eq_add_str eq_mult_str eq_one_str eq_zero_str open_imp_subset 
                  subset_of_opens)
            subgoal using eq_\<rho> open_imp_subset subset_of_opens by auto
            done
          have "U \<in> neighborhoods u" 
            by (simp add: opeU stX.index that(1))
          from has_ring_isomorphism[OF this] 
          show ?thesis .
        qed
        ultimately show ?thesis unfolding stX.is_local_def
          using isomorphic_to_local_is_local by fast
      qed
      then show ?thesis
        by (simp add: locally_ringed_space_axioms_def locally_ringed_space_def
            ringed_space_def sheaf_of_rings_axioms)
    qed
    moreover have "iso_locally_ringed_spaces X is_open local.ind_sheaf ind_ring_morphisms b 
        ind_add_str ind_mult_str ind_zero_str ind_one_str Spec is_zariski_open sheaf_spec 
        sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f" 
    proof- 
      interpret im_sheafXS: Comm_Ring.im_sheaf X is_open local.ind_sheaf
              ind_ring_morphisms b ind_add_str ind_mult_str ind_zero_str ind_one_str Spec 
              is_zariski_open f
        by intro_locales
      interpret iso_sheaves_of_rings Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b 
          add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec local.im_sheaf 
          im_sheaf_morphisms b add_im_sheaf mult_im_sheaf zero_im_sheaf one_im_sheaf \<phi>\<^sub>f
        using is_iso_of_sheaves by blast

      have ring_homoU:"ring_homomorphism (\<phi>\<^sub>f U) (\<O> U) (add_sheaf_spec U) (mult_sheaf_spec U) (zero_sheaf_spec U)
          (one_sheaf_spec U) (im_sheafXS.im_sheaf U) (im_sheafXS.add_im_sheaf U) (im_sheafXS.mult_im_sheaf U)
          (im_sheafXS.zero_im_sheaf U) (im_sheafXS.one_im_sheaf U)" 
        if "is_zariski_open U " for U 
        using mor.is_ring_morphism 
        by (metis Int_commute Int_left_absorb add_im_sheaf_def im_sheafXS.add_im_sheaf_def 
            im_sheafXS.im_sheaf_def im_sheafXS.mult_im_sheaf_def im_sheafXS.one_im_sheaf_def 
            im_sheafXS.zero_im_sheaf_def ind_add_str_def ind_mult_str_def ind_one_str_def 
            ind_zero_str_def local.im_sheaf_def local.ind_sheaf_def 
            mult_im_sheaf_def one_im_sheaf_def that zero_im_sheaf_def)

      note ring_homoU
      moreover have "(\<forall>U V. is_zariski_open U \<longrightarrow>
       is_zariski_open V \<longrightarrow>
       V \<subseteq> U \<longrightarrow>
       (\<forall>x. x \<in> \<O> U \<longrightarrow> (im_sheafXS.im_sheaf_morphisms U V \<circ> \<phi>\<^sub>f U) x = (\<phi>\<^sub>f V \<circ> sheaf_spec_morphisms U V) x))"
        using eq_\<rho> im_sheafXS.im_sheaf_morphisms_def im_sheaf_morphisms_def mor.comm_diagrams by auto
      ultimately interpret morphism_ringed_spaces X is_open local.ind_sheaf ind_ring_morphisms b 
          ind_add_str ind_mult_str ind_zero_str ind_one_str Spec is_zariski_open sheaf_spec
          sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec
          zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f 
        apply intro_locales
        unfolding morphism_ringed_spaces_axioms_def morphism_ringed_spaces_def
        apply intro_locales
        unfolding morphism_presheaves_of_rings_axioms_def
        by auto
    
      have "iso_locally_ringed_spaces X is_open local.ind_sheaf ind_ring_morphisms b 
            ind_add_str ind_mult_str ind_zero_str ind_one_str 
            Spec is_zariski_open sheaf_spec sheaf_spec_morphisms
            \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f"
        apply intro_locales
        subgoal  
        proof -
          have "ind_mor_btw_stalks.is_local X is_open local.ind_sheaf ind_ring_morphisms ind_add_str 
                ind_mult_str ind_zero_str ind_one_str is_zariski_open sheaf_spec sheaf_spec_morphisms 
                add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec f x U
               \<phi>\<^bsub>X is_open local.ind_sheaf ind_ring_morphisms is_zariski_open sheaf_spec 
                        sheaf_spec_morphisms f \<phi>\<^sub>f x\<^esub>"
            if "x \<in> X" "is_zariski_open U" "f x \<in> U" for x U
          proof -
            interpret ind_btw:ind_mor_btw_stalks X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str
                ind_mult_str ind_zero_str ind_one_str Spec is_zariski_open sheaf_spec 
                sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec
                zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f x
              apply intro_locales
              using \<open>x \<in> X\<close> by (simp add: ind_mor_btw_stalks_axioms.intro)

            interpret ind_mor_btw_stalks X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str
                Spec is_zariski_open sheaf_spec 
                sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec
                zero_sheaf_spec one_sheaf_spec f \<phi>\<^sub>f x
              apply intro_locales
              using \<open>x \<in> X\<close> by (simp add: ind_mor_btw_stalks_axioms.intro)

            interpret stk1:stalk X is_open \<O>\<^sub>X \<rho> b add_str mult_str zero_str one_str 
                              "{U. is_open U \<and> x \<in> U}" x 
              apply unfold_locales
              using \<open>x \<in> X\<close> by auto
            interpret stk2:stalk X is_open local.ind_sheaf ind_ring_morphisms b ind_add_str
                ind_mult_str ind_zero_str ind_one_str "{U. is_open U \<and> x \<in> U}" x 
              apply unfold_locales
              using \<open>x \<in> X\<close> by auto
            interpret stk3:stalk Spec is_zariski_open sheaf_spec 
                sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec
                zero_sheaf_spec one_sheaf_spec "{U. is_zariski_open U \<and> f x \<in> U}" "f x"
              apply unfold_locales
              by (auto simp add: stk2.is_elem)
            interpret ring31:ring_homomorphism induced_morphism stk3.carrier_stalk stk3.add_stalk 
              stk3.mult_stalk "stk3.zero_stalk U" "stk3.one_stalk U" stk1.carrier_stalk 
              stk1.add_stalk stk1.mult_stalk "stk1.zero_stalk (f \<^sup>\<inverse> X U)" "stk1.one_stalk (f \<^sup>\<inverse> X U)"
              using ring_homomorphism_induced_morphism[OF \<open>is_zariski_open U\<close> \<open>f x \<in> U\<close>] .
            interpret ring32:ring_homomorphism ind_btw.induced_morphism stk3.carrier_stalk 
              stk3.add_stalk 
              stk3.mult_stalk "stk3.zero_stalk U" "stk3.one_stalk U" stk2.carrier_stalk 
              stk2.add_stalk stk2.mult_stalk "stk2.zero_stalk (f \<^sup>\<inverse> X U)" "stk2.one_stalk (f \<^sup>\<inverse> X U)"
              using ind_btw.ring_homomorphism_induced_morphism[OF \<open>is_zariski_open U\<close> \<open>f x \<in> U\<close>] .

            interpret iso:iso_stalks X is_open \<O>\<^sub>X \<rho>  b add_str mult_str zero_str one_str   
                      "{U. is_open U \<and> x \<in> U}" x local.ind_sheaf ind_ring_morphisms   
                      ind_add_str 
                      ind_mult_str ind_zero_str ind_one_str
              apply unfold_locales
              subgoal 
                by (metis eq_\<O>\<^sub>X eq_add_str eq_mult_str eq_one_str eq_zero_str open_imp_subset 
                    stk2.subset_of_opens)
              subgoal 
                using eq_\<rho> open_imp_subset stk2.subset_of_opens by presburger
              done
            have fU:"f \<^sup>\<inverse> X U \<in> {U. is_open U \<and> x \<in> U}" 
              using is_continuous[OF \<open>is_zariski_open U\<close>] 
              using stk2.is_elem that(3) by blast

            have is_local:"is_local U induced_morphism"
              using are_local_morphisms[of x U] using that by auto           
            from this[unfolded is_local_def] 
            have "local_ring_morphism (identity stk2.carrier_stalk \<circ> induced_morphism \<down> stk3.carrier_stalk) 
                    stk3.carrier_stalk stk3.add_stalk stk3.mult_stalk (stk3.zero_stalk U) 
                    (stk3.one_stalk U) stk2.carrier_stalk stk2.add_stalk stk2.mult_stalk 
                     (stk2.zero_stalk (f \<^sup>\<inverse> X U)) (stk2.one_stalk (f \<^sup>\<inverse> X U))" 
            proof (elim comp_of_local_ring_morphisms)
              interpret local_ring_morphism induced_morphism stk3.carrier_stalk stk3.add_stalk 
                stk3.mult_stalk "stk3.zero_stalk U" "stk3.one_stalk U" stk1.carrier_stalk 
                stk1.add_stalk stk1.mult_stalk "stk1.zero_stalk (f \<^sup>\<inverse> X U)"
                "stk1.one_stalk (f \<^sup>\<inverse> X U)"
                using is_local[unfolded is_local_def] .

              have "local_ring stk1.carrier_stalk stk1.add_stalk stk1.mult_stalk 
                      (stk1.zero_stalk (f \<^sup>\<inverse> X U)) (stk1.one_stalk (f \<^sup>\<inverse> X U))"
                using target.local_ring_axioms .
              moreover have "ring_isomorphism (identity stk1.carrier_stalk) stk1.carrier_stalk 
                    stk1.add_stalk stk1.mult_stalk (stk1.zero_stalk (f \<^sup>\<inverse> X U)) 
                    (stk1.one_stalk (f \<^sup>\<inverse> X U)) stk2.carrier_stalk stk2.add_stalk stk2.mult_stalk
                    (stk2.zero_stalk (f \<^sup>\<inverse> X U)) (stk2.one_stalk (f \<^sup>\<inverse> X U))"
                using iso.has_ring_isomorphism[OF fU] .
              ultimately have "local_ring_morphism (identity stk1.carrier_stalk) stk1.carrier_stalk 
                    stk1.add_stalk stk1.mult_stalk (stk1.zero_stalk (f \<^sup>\<inverse> X U)) 
                    (stk1.one_stalk (f \<^sup>\<inverse> X U)) stk2.carrier_stalk stk2.add_stalk stk2.mult_stalk
                    (stk2.zero_stalk (f \<^sup>\<inverse> X U)) (stk2.one_stalk (f \<^sup>\<inverse> X U))"
                by (rule iso_is_local_ring_morphism)
              then show "local_ring_morphism (identity stk2.carrier_stalk) stk1.carrier_stalk 
                    stk1.add_stalk stk1.mult_stalk (stk1.zero_stalk (f \<^sup>\<inverse> X U)) 
                    (stk1.one_stalk (f \<^sup>\<inverse> X U)) stk2.carrier_stalk stk2.add_stalk stk2.mult_stalk
                    (stk2.zero_stalk (f \<^sup>\<inverse> X U)) (stk2.one_stalk (f \<^sup>\<inverse> X U))"
                using iso.carrier_stalk_eq[OF fU] by simp
            qed
            moreover have "identity stk2.carrier_stalk \<circ> induced_morphism \<down> stk3.carrier_stalk
                              = ind_btw.induced_morphism"
            proof -
              have "(identity stk2.carrier_stalk \<circ> induced_morphism \<down> stk3.carrier_stalk) x 
                        = ind_btw.induced_morphism x" (is "?L=?R") if "x\<in>stk3.carrier_stalk" for x 
              proof -
                have "?L = identity stk2.carrier_stalk (induced_morphism x)"
                  unfolding compose_def using that by simp
                also have "... = induced_morphism x"
                  using that iso.carrier_stalk_eq[OF fU] by auto
                also have "... = ?R"
                  unfolding induced_morphism_def ind_btw.induced_morphism_def
                  using iso.class_of_eq[OF fU] by auto
                finally show ?thesis .
              qed
              then show ?thesis unfolding ind_btw.induced_morphism_def
                by (smt (z3) compose_def restrict_apply' restrict_ext)
            qed
            ultimately show ?thesis unfolding is_local_def ind_btw.is_local_def
              by auto
          qed
          then show ?thesis 
            by (simp add: morphism_locally_ringed_spaces_axioms_def)
        qed
        subgoal 
        proof -
          obtain \<psi> where  \<psi>_morph:"morphism_presheaves_of_rings Spec is_zariski_open local.im_sheaf 
            im_sheaf_morphisms b add_im_sheaf mult_im_sheaf zero_im_sheaf one_im_sheaf sheaf_spec 
            sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec \<psi>" 
            and \<psi>_comp:"(\<forall>U. is_zariski_open U \<longrightarrow> (\<forall>x\<in>local.im_sheaf U. (\<phi>\<^sub>f U \<circ> \<psi> U) x = x) 
                      \<and> (\<forall>x\<in>\<O> U. (\<psi> U \<circ> \<phi>\<^sub>f U) x = x))"
            using is_inv by auto

          interpret \<psi>_morph:morphism_presheaves_of_rings Spec is_zariski_open local.im_sheaf 
            im_sheaf_morphisms b add_im_sheaf mult_im_sheaf zero_im_sheaf one_im_sheaf sheaf_spec 
            sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec \<psi>
            using \<psi>_morph .

          have "morphism_presheaves_of_rings Spec is_zariski_open 
                  im_sheafXS.im_sheaf im_sheafXS.im_sheaf_morphisms b im_sheafXS.add_im_sheaf
                  im_sheafXS.mult_im_sheaf im_sheafXS.zero_im_sheaf im_sheafXS.one_im_sheaf
                  im_sheaf im_sheaf_morphisms b add_im_sheaf
                  mult_im_sheaf zero_im_sheaf one_im_sheaf (\<lambda>U. identity (im_sheafXS.im_sheaf U))"
          proof -
            have "ring_homomorphism (identity (im_sheafXS.im_sheaf U)) (im_sheafXS.im_sheaf U) 
                  (im_sheafXS.add_im_sheaf U) (im_sheafXS.mult_im_sheaf U) (im_sheafXS.zero_im_sheaf U) 
                  (im_sheafXS.one_im_sheaf U) (local.im_sheaf U) (add_im_sheaf U) (mult_im_sheaf U) 
                  (zero_im_sheaf U) (one_im_sheaf U)" 
              if "is_zariski_open U" for U 
            proof -
              have "bijective_map (\<phi>\<^sub>f U \<circ> \<psi> U \<down> local.im_sheaf U) (local.im_sheaf U) 
                                    (im_sheafXS.im_sheaf U)"
                apply unfold_locales
                subgoal 
                  by (smt (verit, ccfv_threshold) Int_commute Int_left_absorb Pi_I \<psi>_comp 
                      compose_def im_sheafXS.im_sheaf_def local.im_sheaf_def local.ind_sheaf_def 
                      o_apply restrict_PiE that)
                subgoal 
                  by (smt (verit, best) \<psi>_comp bij_betw_iff_bijections comp_apply compose_eq eq_\<O>\<^sub>X 
                      im_sheafXS.im_sheaf_def is_continuous local.im_sheaf_def open_imp_subset that)
                done
              with comp_ring_morphisms[OF \<psi>_morph.is_ring_morphism[OF that] ring_homoU[OF that]] 
              interpret ring_isomorphism "\<phi>\<^sub>f U \<circ> \<psi> U \<down> local.im_sheaf U" "local.im_sheaf U" 
                "add_im_sheaf U" "mult_im_sheaf U" "zero_im_sheaf U" "one_im_sheaf U" 
                "im_sheafXS.im_sheaf U" "im_sheafXS.add_im_sheaf U" "im_sheafXS.mult_im_sheaf U"  
                "im_sheafXS.zero_im_sheaf U" "im_sheafXS.one_im_sheaf U"
                using ring_isomorphism.intro by fast

              have "ring_homomorphism (restrict (inv_into (local.im_sheaf U) 
                      (\<phi>\<^sub>f U \<circ> \<psi> U \<down> local.im_sheaf U)) (im_sheafXS.im_sheaf U))
                      (im_sheafXS.im_sheaf U) (im_sheafXS.add_im_sheaf U) 
                      (im_sheafXS.mult_im_sheaf U) (im_sheafXS.zero_im_sheaf U)
                      (im_sheafXS.one_im_sheaf U) (local.im_sheaf U) (add_im_sheaf U) 
                      (mult_im_sheaf U) (zero_im_sheaf U) (one_im_sheaf U)"
                using inverse_ring_isomorphism[unfolded ring_isomorphism_def] by auto
              moreover have "(restrict (inv_into (local.im_sheaf U) 
                      (\<phi>\<^sub>f U \<circ> \<psi> U \<down> local.im_sheaf U)) (im_sheafXS.im_sheaf U))
                       = identity (im_sheafXS.im_sheaf U)" 
                by (smt (verit, best) Int_commute Int_left_absorb \<psi>_comp compose_eq 
                    im_sheafXS.im_sheaf_def injective inv_into_f_f local.im_sheaf_def 
                    local.ind_sheaf_def o_apply restrict_ext that)
              ultimately show ?thesis by auto
            qed
            moreover have "(im_sheaf_morphisms U V \<circ> identity (im_sheafXS.im_sheaf U)) x =
                (identity (im_sheafXS.im_sheaf V) \<circ> im_sheafXS.im_sheaf_morphisms U V) x"
              (is "?L=?R")
              if "is_zariski_open U" "is_zariski_open V" "V \<subseteq> U" "x \<in> im_sheafXS.im_sheaf U"
              for U V x 
            proof -
              have "?L = im_sheaf_morphisms U V x"
                by (simp add: that(4))
              also have "... = im_sheafXS.im_sheaf_morphisms U V x"
                by (simp add: eq_\<rho> im_sheafXS.im_sheaf_morphisms_def im_sheaf_morphisms_def)
              also have "... = ?R" 
                using im_sheafXS.is_map_from_is_homomorphism[OF that(1,2,3)] map.map_closed that(4) 
                by fastforce
              finally show ?thesis .
            qed
            ultimately show ?thesis 
              apply intro_locales 
              unfolding morphism_presheaves_of_rings_axioms_def by auto
          qed
          from comp_of_presheaves[OF this \<psi>_morph]
          have "morphism_presheaves_of_rings Spec is_zariski_open im_sheafXS.im_sheaf 
                  im_sheafXS.im_sheaf_morphisms b im_sheafXS.add_im_sheaf im_sheafXS.mult_im_sheaf 
                im_sheafXS.zero_im_sheaf im_sheafXS.one_im_sheaf sheaf_spec
              sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
                (\<lambda>U. \<psi> U \<circ> identity (im_sheafXS.im_sheaf U) \<down> im_sheafXS.im_sheaf U)"
            by simp
          then have "morphism_presheaves_of_rings Spec is_zariski_open im_sheafXS.im_sheaf 
            im_sheafXS.im_sheaf_morphisms b im_sheafXS.add_im_sheaf im_sheafXS.mult_im_sheaf 
            im_sheafXS.zero_im_sheaf im_sheafXS.one_im_sheaf sheaf_spec sheaf_spec_morphisms \<O>b 
            add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec \<psi>"
          proof (elim morphism_presheaves_of_rings.morphism_presheaves_of_rings_fam_cong)
            fix U x assume "is_zariski_open U" "x \<in> im_sheafXS.im_sheaf U"
            then show " \<psi> U x = (\<psi> U \<circ> identity (im_sheafXS.im_sheaf U) \<down> im_sheafXS.im_sheaf U) x"
              by (simp add: compose_eq)
          next
            show "\<And>U. is_zariski_open U \<Longrightarrow> \<psi> U \<in> extensional (im_sheafXS.im_sheaf U)"
              by (metis PiE_iff \<psi>_morph.fam_morphisms_are_maps eq_\<O>\<^sub>X im_sheafXS.im_sheaf_def 
                  is_continuous local.im_sheaf_def map.graph open_imp_subset)
          qed
          moreover have " (\<forall>U. is_zariski_open U \<longrightarrow> (\<forall>x\<in>im_sheafXS.im_sheaf U. (\<phi>\<^sub>f U \<circ> \<psi> U) x = x) 
                        \<and> (\<forall>x\<in>\<O> U. (\<psi> U \<circ> \<phi>\<^sub>f U) x = x))"
            using \<psi>_comp
            by (metis Int_commute Int_left_absorb im_sheafXS.im_sheaf_def local.im_sheaf_def 
                local.ind_sheaf_def)
          moreover have "homeomorphism X is_open Spec is_zariski_open f" 
            using is_homeomorphism by blast
          ultimately show ?thesis 
            unfolding iso_locally_ringed_spaces_axioms_def
            apply clarify
            apply (auto intro!: iso_presheaves_of_rings.intro iso_sheaves_of_rings.intro 
                        simp:iso_presheaves_of_rings_axioms_def)
            by (meson is_morphism_of_sheaves morphism_sheaves_of_rings.axioms)
        qed
        done
      then show ?thesis by (simp add: iso_locally_ringed_spaces_def)
    qed
    ultimately show ?thesis 
      unfolding affine_scheme_def using comm_ring_axioms by auto
  qed
  moreover have "is_open X" by simp
  ultimately show ?thesis
    by unfold_locales fastforce
qed

lemma (in comm_ring) spec_is_affine_scheme:
  shows "affine_scheme R (+) (\<cdot>) \<zero> \<one> Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
(\<lambda>U. add_sheaf_spec U) (\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U)
(identity Spec) (\<lambda>U. identity (\<O> U))"
proof (intro affine_scheme.intro)
  show "comm_ring R (+) (\<cdot>) \<zero> \<one>" by (simp add: local.comm_ring_axioms)
next
  show "locally_ringed_space Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec
     zero_sheaf_spec one_sheaf_spec" using spec_is_locally_ringed_space by simp
next
  have [simp]: "\<And>x A. x \<in> A \<Longrightarrow> inv_into A (identity A) x = x"
    by (metis bij_betw_def bij_betw_restrict_eq inj_on_id2 inv_into_f_f restrict_apply')
  interpret zar: topological_space Spec is_zariski_open
    by blast
  interpret im_sheaf Spec is_zariski_open sheaf_spec
    sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec Spec
    is_zariski_open "identity Spec"
    by (metis homeomorphism_def im_sheaf_def sheaf_spec_is_sheaf zar.id_is_homeomorphism)
  have rh: "\<And>U V. \<lbrakk>is_zariski_open U; is_zariski_open V; V \<subseteq> U\<rbrakk>
             \<Longrightarrow> ring_homomorphism
                  (im_sheaf_morphisms U V)
                  (local.im_sheaf U) (add_sheaf_spec U)
                  (mult_sheaf_spec U) (zero_sheaf_spec U)
                  (one_sheaf_spec U) (local.im_sheaf V)
                  (add_sheaf_spec V) (mult_sheaf_spec V)
                  (zero_sheaf_spec V) (one_sheaf_spec V)"
    using im_sheaf_morphisms_def local.im_sheaf_def sheaf_spec_morphisms_are_ring_morphisms zar.open_preimage_identity by presburger
  interpret F: presheaf_of_rings Spec is_zariski_open 
    "im_sheaf.im_sheaf Spec sheaf_spec (identity Spec)"
    "im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec)" \<O>b 
    "\<lambda>V. add_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)" "\<lambda>V. mult_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)" 
    "\<lambda>V. zero_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)"  "\<lambda>V. one_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)"
    unfolding presheaf_of_rings_def presheaf_of_rings_axioms_def
  proof (intro conjI strip)
    show "im_sheaf_morphisms U W x = (im_sheaf_morphisms V W \<circ> im_sheaf_morphisms U V) x"
      if "is_zariski_open U" "is_zariski_open V" "is_zariski_open W" "V \<subseteq> U"
        and "W \<subseteq> V" "x \<in> local.im_sheaf U" for U V W x
      using that assoc_comp by blast
  qed (auto simp: rh ring_of_empty)

  show "iso_locally_ringed_spaces Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
     add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec Spec is_zariski_open sheaf_spec
     sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
     (identity Spec) (\<lambda>U. identity (\<O> U))"
  proof -
    have "iso_sheaves_of_rings
            Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
            (im_sheaf.im_sheaf Spec sheaf_spec (identity Spec))
            (im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec))
            \<O>b
            (\<lambda>V x y. add_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V) x y) 
            (\<lambda>V x y. mult_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V) x y) 
            (\<lambda>V. zero_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V)) 
            (\<lambda>V. one_sheaf_spec ((identity Spec)\<^sup>\<inverse> Spec V))
            (\<lambda>U. identity (\<O> U))"
    proof intro_locales
      show "morphism_presheaves_of_rings_axioms is_zariski_open sheaf_spec sheaf_spec_morphisms add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec (im_sheaf.im_sheaf Spec sheaf_spec (identity Spec)) (im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec)) (\<lambda>V. add_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. mult_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. zero_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. one_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>U. identity (\<O> U))"
        using F.id_is_mor_pr_rngs
        by (simp add: local.im_sheaf_def morphism_presheaves_of_rings_def morphism_presheaves_of_rings_axioms_def im_sheaf_morphisms_def)
      then show "iso_presheaves_of_rings_axioms Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec (im_sheaf.im_sheaf Spec sheaf_spec (identity Spec)) (im_sheaf.im_sheaf_morphisms Spec sheaf_spec_morphisms (identity Spec)) \<O>b (\<lambda>V. add_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. mult_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. zero_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>V. one_sheaf_spec (identity Spec \<^sup>\<inverse> Spec V)) (\<lambda>U. identity (\<O> U))"
        unfolding iso_presheaves_of_rings_axioms_def
        apply (rule_tac x="(\<lambda>U. identity (\<O> U))" in exI)
        using F.presheaf_of_rings_axioms
        by (simp add: im_sheaf_morphisms_def local.im_sheaf_def morphism_presheaves_of_rings.intro morphism_presheaves_of_rings_axioms_def sheaf_spec_is_presheaf)
    qed
    moreover have "morphism_locally_ringed_spaces
                    Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
                    Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b add_sheaf_spec mult_sheaf_spec zero_sheaf_spec one_sheaf_spec
                    (identity Spec)
                    (\<lambda>U. identity (\<O> U))"
      by (simp add: locally_ringed_space.id_to_mor_locally_ringed_spaces spec_is_locally_ringed_space) 
    ultimately show ?thesis 
      by (metis locally_ringed_space.id_to_iso_locally_ringed_spaces spec_is_locally_ringed_space)
  qed
qed

lemma (in comm_ring) spec_is_scheme:
  shows "scheme R (+) (\<cdot>) \<zero> \<one> Spec is_zariski_open sheaf_spec sheaf_spec_morphisms \<O>b
(\<lambda>U. add_sheaf_spec U) (\<lambda>U. mult_sheaf_spec U) (\<lambda>U. zero_sheaf_spec U) (\<lambda>U. one_sheaf_spec U)"
  by (metis spec_is_affine_scheme affine_scheme.affine_scheme_is_scheme)
 
lemma empty_scheme_is_affine_scheme:
  shows "affine_scheme {0::nat} (\<lambda>x y. 0) (\<lambda>x y. 0) 0 0 
{} (\<lambda>U. U={}) (\<lambda>U. {0::nat}) (\<lambda>U V. identity{0}) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)
(\<lambda>\<pp>\<in>Spec. undefined) (\<lambda>U. \<lambda>s \<in> cring0.sheaf_spec U. 0)"
proof -
  interpret im0: im_sheaf "{}" "\<lambda>U. U = {}" "\<lambda>U. {0}" "\<lambda>U V. identity {0}"
    "0" "\<lambda>U x y. 0" "\<lambda>U x y. 0" "\<lambda>U. 0" "\<lambda>U. 0" "{}" "\<lambda>U. U = {}" "\<lambda>\<pp>\<in>Spec. undefined"
  proof qed (use invertible_0 in auto)
  note im0.target.open_space [simp del] im0.ring_of_empty [simp del] im0.open_space [simp del] 
  have cring0_open [simp]: "\<And>N. cring0.is_zariski_open N \<longleftrightarrow> N = {}"
    by (metis comm_ring.cring0_is_zariski_open cring0.comm_ring_axioms)
  have ring_im: "ring (im0.im_sheaf V) (im0.add_im_sheaf V) (im0.mult_im_sheaf V) (im0.zero_im_sheaf V) (im0.one_im_sheaf V)"
    for V :: "nat set set"
  proof intro_locales
    show "Group_Theory.monoid (im0.im_sheaf V) (im0.add_im_sheaf V) (im0.zero_im_sheaf V)"
      unfolding im0.add_im_sheaf_def im0.im_sheaf_def im0.zero_im_sheaf_def monoid_def
      by force
    then show "Group_Theory.group_axioms (im0.im_sheaf V) (im0.add_im_sheaf V) (im0.zero_im_sheaf V)"
      unfolding Group_Theory.group_axioms_def im0.im_sheaf_def im0.zero_im_sheaf_def im0.add_im_sheaf_def
      by (simp add: invertible_0)
    show "commutative_monoid_axioms (im0.im_sheaf V) (im0.add_im_sheaf V)"
      by (metis im0.add_im_sheaf_def commutative_monoid_axioms.intro)
  qed (auto simp: im0.im_sheaf_def im0.add_im_sheaf_def im0.mult_im_sheaf_def im0.one_im_sheaf_def monoid_def ring_axioms_def)
  have rh0: "ring_homomorphism (cring0.sheaf_spec_morphisms {} {}) {\<lambda>x. undefined}
             (cring0.add_sheaf_spec {}) (cring0.mult_sheaf_spec {}) (cring0.zero_sheaf_spec {}) (cring0.one_sheaf_spec {}) {\<lambda>x. undefined}
             (cring0.add_sheaf_spec {}) (cring0.mult_sheaf_spec {}) (cring0.zero_sheaf_spec {}) (cring0.one_sheaf_spec {})"
    by (metis cring0.cring0_sheaf_spec_empty cring0.is_zariski_open_empty cring0.sheaf_spec_morphisms_are_ring_morphisms im0.target.open_imp_subset)
  show ?thesis
  proof intro_locales
    show "locally_ringed_space_axioms (\<lambda>U. U={}) (\<lambda>U. {0::nat}) (\<lambda>U V. identity{0}) (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)"
      by (metis (mono_tags, lifting) empty_iff locally_ringed_space_axioms_def)
    show "topological_space cring0.spectrum cring0.is_zariski_open"
      by blast
    show [simp]: "Set_Theory.map (\<lambda>\<pp>\<in>Spec. undefined) {} cring0.spectrum"
      by (metis cring0.cring0_spectrum_eq im0.map_axioms)
    show "continuous_map_axioms {} (\<lambda>U. U={}) cring0.is_zariski_open (\<lambda>\<pp>\<in>Spec. undefined)"
      unfolding continuous_map_axioms_def by fastforce
    show "presheaf_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec
            cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec"
      using cring0.\<O>_on_emptyset cring0.sheaf_morphisms_sheaf_spec
      by (metis cring0.sheaf_spec_is_presheaf presheaf_of_rings_def) 
    show "sheaf_of_rings_axioms cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.zero_sheaf_spec"
      using cring0.sheaf_spec_is_sheaf sheaf_of_rings_def by metis
    have im_sheaf_0[simp]: "im_sheaf.im_sheaf {} (\<lambda>U. {0}) (\<lambda>\<pp>\<in>Spec. undefined) U = {0}" for U :: "nat set set"
      using im0.im_sheaf_def by blast
    have rh: "ring_homomorphism (im0.im_sheaf_morphisms U V) (im0.im_sheaf U) (im0.add_im_sheaf U)
         (im0.mult_im_sheaf U) (im0.zero_im_sheaf U) (im0.one_im_sheaf U) (im0.im_sheaf V)
         (im0.add_im_sheaf V) (im0.mult_im_sheaf V) (im0.zero_im_sheaf V) (im0.one_im_sheaf V)"
      if "cring0.is_zariski_open U" "cring0.is_zariski_open V" "V \<subseteq> U" for U V
      using that by (metis cring0.cring0_is_zariski_open im0.is_ring_morphism) 
    show "morphism_ringed_spaces_axioms {} (\<lambda>U. {0})
         (\<lambda>U V. identity {0}) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0)
         (\<lambda>U. 0) (\<lambda>U. 0) cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec
         cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec
         cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec
         (\<lambda>\<pp>\<in>Spec. undefined) (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
      unfolding morphism_ringed_spaces_axioms_def morphism_sheaves_of_rings_def
        morphism_presheaves_of_rings_def 
    proof (intro conjI)
      show "presheaf_of_rings cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec
         cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec
         cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec"
        using cring0.sheaf_spec_is_presheaf by force
      show "presheaf_of_rings cring0.spectrum cring0.is_zariski_open im0.im_sheaf im0.im_sheaf_morphisms
 0 im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf"
        by (smt (z3) comm_ring.cring0_is_zariski_open cring0.comm_ring_axioms cring0.cring0_spectrum_eq im0.presheaf_of_rings_axioms)
      show "morphism_presheaves_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms 
               cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec 
               im0.im_sheaf im0.im_sheaf_morphisms im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
        unfolding morphism_presheaves_of_rings_axioms_def
      proof (intro conjI strip)
        fix U
        assume "cring0.is_zariski_open U"
        interpret rU: ring "cring0.sheaf_spec U" "cring0.add_sheaf_spec U" "cring0.mult_sheaf_spec U" "cring0.zero_sheaf_spec U" "cring0.one_sheaf_spec U"
          by (metis \<open>cring0.is_zariski_open U\<close> comm_ring.axioms(1) cring0.sheaf_spec_on_open_is_comm_ring)
        interpret rU': ring "im0.im_sheaf U" "im0.add_im_sheaf U" "im0.mult_im_sheaf U" "im0.zero_im_sheaf U" "im0.one_im_sheaf U"
          using ring_im by blast
        show "ring_homomorphism (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (cring0.add_sheaf_spec U) (cring0.mult_sheaf_spec U) (cring0.zero_sheaf_spec U) (cring0.one_sheaf_spec U) 
                            (im0.im_sheaf U) (im0.add_im_sheaf U) (im0.mult_im_sheaf U) (im0.zero_im_sheaf U) (im0.one_im_sheaf U)"
        proof intro_locales
          show "Set_Theory.map (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (im0.im_sheaf U)"
            unfolding  Set_Theory.map_def by (metis ext_funcset_to_sing_iff im0.im_sheaf_def singletonI)
          show "monoid_homomorphism_axioms (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (cring0.add_sheaf_spec U) (cring0.zero_sheaf_spec U) (im0.add_im_sheaf U) (im0.zero_im_sheaf U)"
            unfolding monoid_homomorphism_axioms_def im0.zero_im_sheaf_def im0.add_im_sheaf_def
            by (metis rU.additive.unit_closed rU.additive.composition_closed restrict_apply)
          show "monoid_homomorphism_axioms (\<lambda>s\<in>cring0.sheaf_spec U. 0) (cring0.sheaf_spec U) (cring0.mult_sheaf_spec U) (cring0.one_sheaf_spec U) (im0.mult_im_sheaf U) (im0.one_im_sheaf U)"
            unfolding monoid_homomorphism_axioms_def im0.mult_im_sheaf_def im0.one_im_sheaf_def
            by (metis rU.multiplicative.composition_closed rU.multiplicative.unit_closed restrict_apply)
        qed
        show "(im0.im_sheaf_morphisms U V \<circ> (\<lambda>s\<in>cring0.sheaf_spec U. 0)) x = ((\<lambda>s\<in>cring0.sheaf_spec V. 0) \<circ> cring0.sheaf_spec_morphisms U V) x"
          if "cring0.is_zariski_open U" "cring0.is_zariski_open V" "V \<subseteq> U" "x \<in> cring0.sheaf_spec U"
          for U V x
          using that cring0.sheaf_morphisms_sheaf_spec 
          unfolding im0.im_sheaf_morphisms_def o_def
          by (metis cring0.cring0_is_zariski_open insertI1 restrict_apply')
      qed
    qed
    interpret monoid0: Group_Theory.monoid "{\<lambda>x. undefined}"
      "cring0.add_sheaf_spec {}"
      "(\<lambda>\<pp>\<in>{}. quotient_ring.zero_rel ({0}\<setminus>\<pp>) {0} ring0.subtraction ring0.subtraction 0 0)"
      by (smt (verit, best) Group_Theory.monoid.intro cring0.add_sheaf_spec_extensional extensional_empty restrict_extensional singletonD)

    show "iso_locally_ringed_spaces_axioms {} (\<lambda>U. U = {})
     (\<lambda>U. {0}) (\<lambda>U V. identity {0}) 0 (\<lambda>U x y. 0)
     (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0) cring0.spectrum
     cring0.is_zariski_open cring0.sheaf_spec
     cring0.sheaf_spec_morphisms cring0.\<O>b
     cring0.add_sheaf_spec cring0.mult_sheaf_spec
     cring0.zero_sheaf_spec cring0.one_sheaf_spec
     (\<lambda>\<pp>\<in>Spec. undefined)
     (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0::nat)"
      unfolding iso_locally_ringed_spaces_axioms_def
    proof (intro conjI)
      show "homeomorphism {} (\<lambda>U. U = {}) cring0.spectrum cring0.is_zariski_open (\<lambda>\<pp>\<in>Spec. undefined)"
      proof intro_locales
        show "bijective (\<lambda>\<pp>\<in>Spec. undefined) {} cring0.spectrum"
          unfolding bijective_def bij_betw_def
          using cring0.cring0_spectrum_eq by blast
        show "Set_Theory.map (inverse_map (\<lambda>\<pp>\<in>Spec. undefined) {} cring0.spectrum) cring0.spectrum {}"
          unfolding Set_Theory.map_def inverse_map_def restrict_def
          by (smt (verit, best) PiE_I cring0.cring0_spectrum_eq empty_iff)
      qed (use im0.map_axioms continuous_map_axioms_def in \<open>force+\<close>)
      show "iso_sheaves_of_rings cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec
                 cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec 
                 im0.im_sheaf im0.im_sheaf_morphisms (0::nat) im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0::nat)"
      proof intro_locales
        show "topological_space cring0.spectrum cring0.is_zariski_open"
          by force
        show "presheaf_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec"
          using \<open>presheaf_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec\<close> by force
        show "presheaf_of_rings_axioms cring0.is_zariski_open im0.im_sheaf im0.im_sheaf_morphisms (0::nat) im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf"
          using im0.presheaf_of_rings_axioms presheaf_of_rings_def by force
        show "morphism_presheaves_of_rings_axioms cring0.is_zariski_open cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec im0.im_sheaf im0.im_sheaf_morphisms im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0::nat)"
        proof qed (auto simp: cring0.zero_sheaf_spec_def cring0.one_sheaf_spec_def cring0.add_sheaf_spec_def cring0.mult_sheaf_spec_def 
            im0.zero_im_sheaf_def im0.one_im_sheaf_def im0.add_im_sheaf_def im0.mult_im_sheaf_def
            im0.im_sheaf_morphisms_def cring0.sheaf_morphisms_sheaf_spec monoid0.invertible_def)
      have morph_empty: "morphism_presheaves_of_rings {} (\<lambda>U. U = {})
             im0.im_sheaf im0.im_sheaf_morphisms 0 (\<lambda>V. ring0.subtraction) (\<lambda>V. ring0.subtraction)
             (\<lambda>V. 0) (\<lambda>V. 0) cring0.sheaf_spec cring0.sheaf_spec_morphisms cring0.\<O>b
             cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec
             (\<lambda>S. \<lambda>n\<in>{0}. \<lambda>x. undefined)"
      proof qed (auto simp: im0.im_sheaf_morphisms_def cring0.sheaf_spec_morphisms_def 
            cring0.zero_sheaf_spec_def cring0.one_sheaf_spec_def cring0.add_sheaf_spec_def cring0.mult_sheaf_spec_def 
            cring0.\<O>b_def monoid0.invertible_def)
      then show "iso_presheaves_of_rings_axioms cring0.spectrum cring0.is_zariski_open cring0.sheaf_spec 
                   cring0.sheaf_spec_morphisms cring0.\<O>b cring0.add_sheaf_spec cring0.mult_sheaf_spec cring0.zero_sheaf_spec cring0.one_sheaf_spec 
                   im0.im_sheaf im0.im_sheaf_morphisms (0::nat) im0.add_im_sheaf im0.mult_im_sheaf im0.zero_im_sheaf im0.one_im_sheaf (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
        by unfold_locales (auto simp add: im0.zero_im_sheaf_def im0.one_im_sheaf_def im0.add_im_sheaf_def im0.mult_im_sheaf_def)
      qed
    qed
    show "morphism_locally_ringed_spaces_axioms {}
     (\<lambda>U. U = {}) (\<lambda>U. {0}) (\<lambda>U V. identity {0})
     (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)
     cring0.is_zariski_open cring0.sheaf_spec
     cring0.sheaf_spec_morphisms cring0.add_sheaf_spec
     cring0.mult_sheaf_spec cring0.zero_sheaf_spec
     cring0.one_sheaf_spec (\<lambda>\<pp>\<in>Spec. undefined)
     (\<lambda>U. \<lambda>s\<in>cring0.sheaf_spec U. 0)"
      by (meson equals0D morphism_locally_ringed_spaces_axioms.intro)
  qed 
qed

lemma empty_scheme_is_scheme:
  shows "scheme {0::nat} (\<lambda>x y. 0) (\<lambda>x y. 0) 0 0 {} (\<lambda>U. U={}) (\<lambda>U. {0}) (\<lambda>U V. identity{0::nat}) 0 (\<lambda>U x y. 0) (\<lambda>U x y. 0) (\<lambda>U. 0) (\<lambda>U. 0)"
  by (metis affine_scheme.affine_scheme_is_scheme empty_scheme_is_affine_scheme)

end