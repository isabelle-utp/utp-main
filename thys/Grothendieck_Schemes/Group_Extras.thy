
text \<open>Authors: Anthony Bordg and Lawrence Paulson\<close>

theory Group_Extras
  imports Main
          "Jacobson_Basic_Algebra.Group_Theory"
          "Set_Extras"

begin

section \<open>Fold operator with a subdomain\<close>

inductive_set
  foldSetD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a] \<Rightarrow> ('b set * 'a) set"
  for D :: "'a set" and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a" and e :: 'a
  where
    emptyI [intro]: "e \<in> D \<Longrightarrow> ({}, e) \<in> foldSetD D f e"
  | insertI [intro]: "\<lbrakk>x \<notin> A; f x y \<in> D; (A, y) \<in> foldSetD D f e\<rbrakk> \<Longrightarrow>
                      (insert x A, f x y) \<in> foldSetD D f e"

inductive_cases empty_foldSetDE [elim!]: "({}, x) \<in> foldSetD D f e"

definition
  foldD :: "['a set, 'b \<Rightarrow> 'a \<Rightarrow> 'a, 'a, 'b set] \<Rightarrow> 'a"
  where "foldD D f e A = (THE x. (A, x) \<in> foldSetD D f e)"

lemma foldSetD_closed: "(A, z) \<in> foldSetD D f e \<Longrightarrow> z \<in> D"
  by (erule foldSetD.cases) auto

lemma Diff1_foldSetD:
  "\<lbrakk>(A - {x}, y) \<in> foldSetD D f e; x \<in> A; f x y \<in> D\<rbrakk> \<Longrightarrow>
   (A, f x y) \<in> foldSetD D f e"
  by (metis Diff_insert_absorb foldSetD.insertI mk_disjoint_insert)

lemma foldSetD_imp_finite [simp]: "(A, x) \<in> foldSetD D f e \<Longrightarrow> finite A"
  by (induct set: foldSetD) auto

lemma finite_imp_foldSetD:
  "\<lbrakk>finite A; e \<in> D; \<And>x y. \<lbrakk>x \<in> A; y \<in> D\<rbrakk> \<Longrightarrow> f x y \<in> D\<rbrakk>
    \<Longrightarrow> \<exists>x. (A, x) \<in> foldSetD D f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSetD D f e" by auto
  with insert have "y \<in> D" by (auto dest: foldSetD_closed)
  with y and insert have "(insert x F, f x y) \<in> foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed

lemma foldSetD_backwards:
  assumes "A \<noteq> {}" "(A, z) \<in> foldSetD D f e"
  shows "\<exists>x y. x \<in> A \<and> (A - { x }, y) \<in> foldSetD D f e \<and> z = f x y"
  using assms(2) by (cases) (simp add: assms(1), metis Diff_insert_absorb insertI1)

subsection \<open>Left-Commutative Operations\<close>

locale LCD =
  fixes B :: "'b set"
  and D :: "'a set"
  and f :: "'b \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>" 70)
  assumes left_commute:
    "\<lbrakk>x \<in> B; y \<in> B; z \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
  and f_closed [simp, intro!]: "!!x y. \<lbrakk>x \<in> B; y \<in> D\<rbrakk> \<Longrightarrow> f x y \<in> D"

lemma (in LCD) foldSetD_closed [dest]: "(A, z) \<in> foldSetD D f e \<Longrightarrow> z \<in> D"
  by (erule foldSetD.cases) auto

lemma (in LCD) Diff1_foldSetD:
  "\<lbrakk>(A - {x}, y) \<in> foldSetD D f e; x \<in> A; A \<subseteq> B\<rbrakk> \<Longrightarrow>
  (A, f x y) \<in> foldSetD D f e"
  by (meson Diff1_foldSetD f_closed local.foldSetD_closed subsetCE)

lemma (in LCD) finite_imp_foldSetD:
  "\<lbrakk>finite A; A \<subseteq> B; e \<in> D\<rbrakk> \<Longrightarrow> \<exists>x. (A, x) \<in> foldSetD D f e"
proof (induct set: finite)
  case empty then show ?case by auto
next
  case (insert x F)
  then obtain y where y: "(F, y) \<in> foldSetD D f e" by auto
  with insert have "y \<in> D" by auto
  with y and insert have "(insert x F, f x y) \<in> foldSetD D f e"
    by (intro foldSetD.intros) auto
  then show ?case ..
qed


lemma (in LCD) foldSetD_determ_aux:
  assumes "e \<in> D" and A: "card A < n" "A \<subseteq> B" "(A, x) \<in> foldSetD D f e" "(A, y) \<in> foldSetD D f e"
  shows "y = x"
  using A
proof (induction n arbitrary: A x y)
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  then consider "card A = n" | "card A < n"
    by linarith
  then show ?case
  proof cases
    case 1
    show ?thesis
      using foldSetD.cases [OF \<open>(A,x) \<in> foldSetD D (\<cdot>) e\<close>]
    proof cases
      case 1
      then show ?thesis
        using \<open>(A,y) \<in> foldSetD D (\<cdot>) e\<close> by auto
    next
      case (2 x' A' y')
      note A' = this
      show ?thesis
        using foldSetD.cases [OF \<open>(A,y) \<in> foldSetD D (\<cdot>) e\<close>]
      proof cases
        case 1
        then show ?thesis
          using \<open>(A,x) \<in> foldSetD D (\<cdot>) e\<close> by auto
      next
        case (2 x'' A'' y'')
        note A'' = this
        show ?thesis
        proof (cases "x' = x''")
          case True
          show ?thesis
          proof (cases "y' = y''")
            case True
            then show ?thesis
              using A' A'' \<open>x' = x''\<close> by (blast elim!: equalityE)
          next
            case False
            then show ?thesis
              using A' A'' \<open>x' = x''\<close>
              by (metis \<open>card A = n\<close> Suc.IH Suc.prems(2) card_insert_disjoint foldSetD_imp_finite insert_eq_iff insert_subset lessI)
          qed
        next
          case False
          then have *: "A' - {x''} = A'' - {x'}" "x'' \<in> A'" "x' \<in> A''"
            using A' A'' by fastforce+
          then have "A' = insert x'' A'' - {x'}"
            using \<open>x' \<notin> A'\<close> by blast
          then have card: "card A' \<le> card A''"
            using A' A'' * by (metis card_Suc_Diff1 eq_refl foldSetD_imp_finite)
          obtain u where u: "(A' - {x''}, u) \<in> foldSetD D (\<cdot>) e"
            using finite_imp_foldSetD [of "A' - {x''}"] A' Diff_insert \<open>A \<subseteq> B\<close> \<open>e \<in> D\<close> by fastforce
          have "y' = f x'' u"
            using Diff1_foldSetD [OF u] \<open>x'' \<in> A'\<close> \<open>card A = n\<close> A' Suc.IH \<open>A \<subseteq> B\<close> by auto
          then have "(A'' - {x'}, u) \<in> foldSetD D f e"
            using "*"(1) u by auto
          then have "y'' = f x' u"
            using A'' by (metis * \<open>card A = n\<close> A'(1) Diff1_foldSetD Suc.IH \<open>A \<subseteq> B\<close>
                card card_Suc_Diff1 card_insert_disjoint foldSetD_imp_finite insert_subset le_imp_less_Suc)
          then show ?thesis
            using A' A''
            by (metis \<open>A \<subseteq> B\<close> \<open>y' = x'' \<cdot> u\<close> insert_subset left_commute local.foldSetD_closed u)
        qed
      qed
    qed
  next
    case 2 with Suc show ?thesis by blast
  qed
qed

lemma (in LCD) foldSetD_determ:
  "\<lbrakk>(A, x) \<in> foldSetD D f e; (A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B\<rbrakk>
  \<Longrightarrow> y = x"
  by (blast intro: foldSetD_determ_aux [rule_format])

lemma (in LCD) foldD_equality:
  "\<lbrakk>(A, y) \<in> foldSetD D f e; e \<in> D; A \<subseteq> B\<rbrakk> \<Longrightarrow> foldD D f e A = y"
  by (unfold foldD_def) (blast intro: foldSetD_determ)

lemma foldD_empty [simp]:
  "e \<in> D \<Longrightarrow> foldD D f e {} = e"
  by (unfold foldD_def) blast

lemma (in LCD) foldD_insert_aux:
  "\<lbrakk>x \<notin> A; x \<in> B; e \<in> D; A \<subseteq> B\<rbrakk>
    \<Longrightarrow> ((insert x A, v) \<in> foldSetD D f e) \<longleftrightarrow> (\<exists>y. (A, y) \<in> foldSetD D f e \<and> v = f x y)"
  apply auto
  by (metis Diff_insert_absorb f_closed finite_Diff foldSetD.insertI foldSetD_determ foldSetD_imp_finite insert_subset local.finite_imp_foldSetD local.foldSetD_closed)

lemma (in LCD) foldD_insert:
  assumes "finite A" "x \<notin> A" "x \<in> B" "e \<in> D" "A \<subseteq> B"
  shows "foldD D f e (insert x A) = f x (foldD D f e A)"
proof -
  have "(THE v. \<exists>y. (A, y) \<in> foldSetD D (\<cdot>) e \<and> v = x \<cdot> y) = x \<cdot> (THE y. (A, y) \<in> foldSetD D (\<cdot>) e)"
    by (rule the_equality) (use assms foldD_def foldD_equality foldD_def finite_imp_foldSetD in \<open>metis+\<close>)
  then show ?thesis
    unfolding foldD_def using assms by (simp add: foldD_insert_aux)
qed

lemma (in LCD) foldD_closed [simp]:
  "\<lbrakk>finite A; e \<in> D; A \<subseteq> B\<rbrakk> \<Longrightarrow> foldD D f e A \<in> D"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: foldD_insert)
qed

lemma (in LCD) foldD_commute:
  "\<lbrakk>finite A; x \<in> B; e \<in> D; A \<subseteq> B\<rbrakk> \<Longrightarrow>
   f x (foldD D f e A) = foldD D f (f x e) A"
  by (induct set: finite) (auto simp add: left_commute foldD_insert)

lemma Int_mono2:
  "\<lbrakk>A \<subseteq> C; B \<subseteq> C\<rbrakk> \<Longrightarrow> A Int B \<subseteq> C"
  by blast

lemma (in LCD) foldD_nest_Un_Int:
  "\<lbrakk>finite A; finite C; e \<in> D; A \<subseteq> B; C \<subseteq> B\<rbrakk> \<Longrightarrow>
   foldD D f (foldD D f e C) A = foldD D f (foldD D f e (A Int C)) (A Un C)"
proof (induction set: finite)
  case (insert x F)
  then show ?case
    by (simp add: foldD_insert foldD_commute Int_insert_left insert_absorb Int_mono2)
qed simp

lemma (in LCD) foldD_nest_Un_disjoint:
  "\<lbrakk>finite A; finite B; A Int B = {}; e \<in> D; A \<subseteq> B; C \<subseteq> B\<rbrakk>
    \<Longrightarrow> foldD D f e (A Un B) = foldD D f (foldD D f e B) A"
  by (simp add: foldD_nest_Un_Int)

\<comment> \<open>Delete rules to do with \<open>foldSetD\<close> relation.\<close>

declare foldSetD_imp_finite [simp del]
  empty_foldSetDE [rule del]
  foldSetD.intros [rule del]
declare (in LCD)
  foldSetD_closed [rule del]

section \<open>Monoids\<close>

lemma comp_monoid_morphisms:
  assumes "monoid_homomorphism \<eta> A multA oneA B multB oneB" and
          "monoid_homomorphism \<theta> B multB oneB C multC oneC"
shows "monoid_homomorphism (\<theta> \<circ> \<eta> \<down> A) A multA oneA C multC oneC"
proof-
  have "map (\<theta> \<circ> \<eta> \<down> A) A C" using assms comp_maps by (metis monoid_homomorphism.axioms(1))
  moreover have "(\<theta> \<circ> \<eta> \<down> A) oneA = oneC"
    using assms
    by (metis compose_eq monoid.unit_closed monoid_homomorphism.axioms(2) monoid_homomorphism.commutes_with_unit)
  moreover have "(\<theta> \<circ> \<eta> \<down> A) (multA x y) = multC ((\<theta> \<circ> \<eta> \<down> A) x) ((\<theta> \<circ> \<eta> \<down> A) y)"
      if "x \<in> A" "y \<in> A" for x y
    using that assms monoid_homomorphism.commutes_with_composition
    by (smt compose_eq map.map_closed monoid.composition_closed monoid_homomorphism.axioms)
  ultimately show ?thesis
    using monoid_homomorphism_def assms comp_maps by (smt monoid_homomorphism_axioms.intro)
qed

text \<open>Commutative Monoids\<close>

text \<open>
  We enter a more restrictive context, with \<open>f :: 'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  instead of \<open>'b \<Rightarrow> 'a \<Rightarrow> 'a\<close>.
\<close>

locale ACeD =
  fixes D :: "'a set"
    and f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"    (infixl "\<cdot>" 70)
    and e :: 'a
  assumes ident [simp]: "x \<in> D \<Longrightarrow> x \<cdot> e = x"
    and commute: "\<lbrakk>x \<in> D; y \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
    and assoc: "\<lbrakk>x \<in> D; y \<in> D; z \<in> D\<rbrakk> \<Longrightarrow> (x \<cdot> y) \<cdot> z = x \<cdot> (y \<cdot> z)"
    and e_closed [simp]: "e \<in> D"
    and f_closed [simp]: "\<lbrakk>x \<in> D; y \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> y \<in> D"

lemma (in ACeD) left_commute:
  "\<lbrakk>x \<in> D; y \<in> D; z \<in> D\<rbrakk> \<Longrightarrow> x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  assume D: "x \<in> D" "y \<in> D" "z \<in> D"
  then have "x \<cdot> (y \<cdot> z) = (y \<cdot> z) \<cdot> x" by (simp add: commute)
  also from D have "... = y \<cdot> (z \<cdot> x)" by (simp add: assoc)
  also from D have "z \<cdot> x = x \<cdot> z" by (simp add: commute)
  finally show ?thesis .
qed

lemmas (in ACeD) AC = assoc commute left_commute

lemma (in ACeD) left_ident [simp]: "x \<in> D \<Longrightarrow> e \<cdot> x = x"
proof -
  assume "x \<in> D"
  then have "x \<cdot> e = x" by (rule ident)
  with \<open>x \<in> D\<close> show ?thesis by (simp add: commute)
qed

lemma (in ACeD) foldD_Un_Int:
  "\<lbrakk>finite A; finite B; A \<subseteq> D; B \<subseteq> D\<rbrakk> \<Longrightarrow>
    foldD D f e A \<cdot> foldD D f e B =
    foldD D f e (A Un B) \<cdot> foldD D f e (A Int B)"
proof (induction set: finite)
  case empty
  then show ?case
    by(simp add: left_commute LCD.foldD_closed [OF LCD.intro [of D]])
next
  case (insert x F)
  then show ?case
    by(simp add: AC insert_absorb Int_insert_left Int_mono2
                 LCD.foldD_insert [OF LCD.intro [of D]]
                 LCD.foldD_closed [OF LCD.intro [of D]])
qed

lemma (in ACeD) foldD_Un_disjoint:
  "\<lbrakk>finite A; finite B; A Int B = {}; A \<subseteq> D; B \<subseteq> D\<rbrakk> \<Longrightarrow>
    foldD D f e (A Un B) = foldD D f e A \<cdot> foldD D f e B"
  by (simp add: foldD_Un_Int
    left_commute LCD.foldD_closed [OF LCD.intro [of D]])


subsection \<open>Finite Products\<close>

context monoid
begin

definition finprod:: "'b set => ('b => 'a) \<Rightarrow> 'a"
  where "finprod I f \<equiv> if finite I then foldD M (composition \<circ> f) \<one> I else \<one>"

end (* monoid *)


section \<open>Groups\<close>

lemma comp_group_morphisms:
  assumes "group_homomorphism \<eta> A multA oneA B multB oneB" and
"group_homomorphism \<theta> B multB oneB C multC oneC"
shows "group_homomorphism (\<theta> \<circ> \<eta> \<down> A) A multA oneA C multC oneC"
  using assms group_homomorphism_def comp_monoid_morphisms by metis

subsection \<open>Subgroup Generated by a Subset\<close>

context group
begin

inductive_set generate :: "'a set \<Rightarrow> 'a set"
  for H where
    unit:  "\<one> \<in> generate H"
  | incl: "a \<in> H \<Longrightarrow> a \<in> generate H"
  | inv:  "a \<in> H \<Longrightarrow> inverse a \<in> generate H"
  | mult:  "a \<in> generate H \<Longrightarrow> b \<in> generate H \<Longrightarrow> a \<cdot> b \<in> generate H"

lemma generate_into_G: "a \<in> generate (G \<inter> H) \<Longrightarrow> a \<in> G"
  by (induction rule: generate.induct) auto


definition subgroup_generated :: "'a set \<Rightarrow> 'a set"
  where "subgroup_generated S = generate (G \<inter> S)"

lemma inverse_in_subgroup_generated: "a \<in> subgroup_generated H \<Longrightarrow> inverse a \<in> subgroup_generated H"
  unfolding subgroup_generated_def
proof (induction rule: generate.induct)
  case (mult a b)
  then show ?case
    by (simp add: generate.mult generate_into_G inverse_composition_commute)
qed (auto simp add: generate.unit generate.incl generate.inv)

lemma subgroup_generated_is_monoid:
  fixes H
  shows "Group_Theory.monoid (subgroup_generated H) (\<cdot>) \<one>"
  unfolding subgroup_generated_def
proof qed (auto simp: generate.unit generate.mult associative generate_into_G)

lemma subgroup_generated_is_subset:
  fixes H
  shows "subgroup_generated H \<subseteq> G"
    using generate_into_G subgroup_generated_def by blast

lemma subgroup_generated_is_subgroup:
  fixes H
  shows "subgroup (subgroup_generated H) G (\<cdot>) \<one>"
proof
  show "subgroup_generated H \<subseteq> G"
    by (simp add: subgroup_generated_is_subset)
  show "a \<cdot> b \<in> subgroup_generated H"
    if "a \<in> subgroup_generated H" "b \<in> subgroup_generated H" for a b
    using that by (meson monoid.composition_closed subgroup_generated_is_monoid)
  show "a \<cdot> b \<cdot> c = a \<cdot> (b \<cdot> c)"
    if "a \<in> subgroup_generated H" "b \<in> subgroup_generated H" "c \<in> subgroup_generated H"
    for a b c
    using that by (meson monoid.associative subgroup_generated_is_monoid)
  show "monoid.invertible (subgroup_generated H) (\<cdot>) \<one> u"
    if "u \<in> subgroup_generated H" for u
  proof (rule monoid.invertibleI )
    show "Group_Theory.monoid (subgroup_generated H) (\<cdot>) \<one>"
      by (simp add: subgroup_generated_is_monoid)
    show "u \<cdot> local.inverse u = \<one>" "local.inverse u \<cdot> u = \<one>" "u \<in> subgroup_generated H"
      using \<open>subgroup_generated H \<subseteq> G\<close> that by auto
    show "local.inverse u \<in> subgroup_generated H"
      using inverse_in_subgroup_generated that by blast
  qed
qed (auto simp: generate_into_G generate.unit subgroup_generated_def)


end (* group *)


section \<open>Abelian Groups\<close>

context abelian_group
begin

definition minus:: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<hyphen>" 70)
  where "x \<hyphen> y \<equiv> x \<cdot> inverse y "

definition finsum:: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "finsum I f \<equiv> finprod I f"

(* A notation "\<Sum>i\<in>I. f i" should be introduced for a sum of a family of elements of an abelian group *)

end (* abelian_group*)

end
