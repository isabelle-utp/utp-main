(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

header {* Finite Suprema *}

theory Finite_Suprema
imports Dioid
begin

text {* This file contains an adaptation of Isabelle's library for
finite sums to the case of (join) semilattices and dioids. In this
setting, addition is idempotent; finite sums are finite suprema.

We add some basic properties of finite suprema for (join) semilattices
and dioids. *}

subsection {* Auxiliary Lemmas *}

lemma fun_im: "{f a |a. a \<in> A} = {b. b \<in> f ` A}"
  by auto

lemma fset_to_im: "{f x |x. x \<in> X} = f ` X"
  by auto

lemma cart_flip_aux: "{f (snd p) (fst p) |p. p \<in> (B \<times> A)} = {f (fst p) (snd p) |p. p \<in> (A \<times> B)}"
  by auto

lemma cart_flip: "(\<lambda>p. f (snd p) (fst p)) ` (B \<times> A) = (\<lambda>p. f (fst p) (snd p)) ` (A \<times> B)"
  by (metis cart_flip_aux fset_to_im)

lemma fprod_aux: "{x \<cdot> y |x y. x \<in> (f ` A) \<and> y \<in> (g ` B)} = {f x \<cdot> g y |x y. x \<in> A \<and> y \<in> B}"
  by auto

subsection {*Finite Suprema in Semilattices *}

text {* The first lemma shows that, in the context of semilattices,
finite sums satisfy the defining property of finite suprema. *}

lemma setsum_sup:
  assumes "finite (A :: 'a::join_semilattice_zero set)"
  shows "\<Sum>A \<le> z \<longleftrightarrow> (\<forall>a \<in> A. a \<le> z)"
proof (induct rule: finite_induct[OF assms])
  fix z ::'a
  show "(\<Sum>{} \<le> z) = (\<forall>a \<in> {}. a \<le> z)"
    by (metis setsum.empty zero_least Int_empty_right disjoint_iff_not_equal)
next
  fix x z :: 'a and F :: "'a set"
  assume finF: "finite F"
    and xnF: "x \<notin> F"
    and indhyp: "(\<Sum>F \<le> z) = (\<forall>a \<in> F. a \<le> z)"
  show "(\<Sum>(insert x F) \<le> z) = (\<forall>a \<in> insert x F. a \<le> z)"
  proof -
    have "\<Sum>(insert x F) \<le> z \<longleftrightarrow> (x + \<Sum>F) \<le> z"
      by (metis finF setsum_insert xnF)
    also have "... \<longleftrightarrow> x \<le> z \<and> \<Sum>F \<le> z"
      by (metis add_lub)
    also have "... \<longleftrightarrow> x \<le> z \<and> (\<forall>a \<in> F. a \<le> z)"
      by (metis (lifting) indhyp)
    also have "... \<longleftrightarrow> (\<forall>a \<in> insert x F. a \<le> z)"
      by (metis insert_iff)
    ultimately show "(\<Sum>(insert x F) \<le> z) = (\<forall>a \<in> insert x F. a \<le> z)"
      by blast
  qed
qed

text {* This immediately implies some variants. *}

lemma setsum_fun_image_sup:
  fixes f :: "'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite (A :: 'a set)"
  shows "\<Sum>(f ` A) \<le> z \<longleftrightarrow> (\<forall>a \<in> A. f a \<le> z)"
  by (simp add: assms setsum_sup)

lemma setsum_fun_sup:
  fixes f :: "'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite (A ::'a set)"
  shows "\<Sum>{f a | a. a \<in> A} \<le> z \<longleftrightarrow> (\<forall>a \<in> A. f a \<le> z)"
  by (simp only: fset_to_im assms setsum_fun_image_sup)

lemma setsum_intro:
  assumes "finite (A :: 'a::join_semilattice_zero set)" and "finite B"
  shows "(\<forall>a \<in> A. \<exists>b \<in> B. a \<le> b) \<longrightarrow> (\<Sum>A \<le> \<Sum>B)"
  by (metis assms order_refl order_trans setsum_sup)

text {* Next we prove an additivity property for suprema. *}

lemma setsum_union:
  assumes "finite (A :: 'a::join_semilattice_zero set)"
  and "finite (B :: 'a::join_semilattice_zero set)"
  shows "\<Sum>(A \<union> B) = \<Sum>A + \<Sum>B"
proof -
    have "\<forall>z. \<Sum>(A \<union> B) \<le> z \<longleftrightarrow> (\<Sum>A + \<Sum>B \<le> z)"
      by (auto simp add: assms setsum_sup add_lub)
  thus ?thesis
    by (simp add: eq_iff)
qed

text {* It follows that the sum (supremum) of a two-element set is the
join of its elements. *}

lemma setsum_bin[simp]: "\<Sum>{(x :: 'a::join_semilattice_zero),y} = x + y"
  by (subst insert_is_Un, subst setsum_union, auto)

text {* Next we show that finite suprema are order preserving. *}

lemma setsum_iso:
  assumes "finite (B :: 'a::join_semilattice_zero set)"
  shows "A \<subseteq> B \<longrightarrow> \<Sum> A \<le> \<Sum> B"
  by (metis assms finite_subset order_refl set_rev_mp setsum_sup)

text {* The following lemmas state unfold properties for suprema and
finite sets. They are subtly different from the non-idempotent case,
where additional side conditions are required. *}

lemma setsum_insert:
  assumes "finite (A :: 'a::join_semilattice_zero set)"
  shows "\<Sum>(insert x A) = x + \<Sum>A"
proof -
  have "\<Sum>(insert x A) = \<Sum>{x} + \<Sum>A"
    by (metis insert_is_Un assms finite.emptyI finite.insertI setsum_union)
  thus ?thesis
    by auto
qed

lemma setsum_fun_insert:
  fixes f :: "'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite (A :: 'a set)"
  shows "\<Sum>(f ` (insert x A)) = f x + \<Sum>(f ` A)"
  by (simp add: setsum_insert assms)

text {* Now we show that set comprehensions with nested suprema can
be flattened. *}

lemma flatten1_im:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite (A :: 'a set)"
  and "finite (B :: 'a set)"
  shows "\<Sum>((\<lambda>x. \<Sum>(f x ` B)) ` A) = \<Sum>((\<lambda>p. f (fst p) (snd p)) ` (A \<times> B))"
proof -
  have "\<forall>z. \<Sum>((\<lambda>x. \<Sum>(f x ` B)) ` A) \<le> z \<longleftrightarrow> \<Sum>((\<lambda>p. f (fst p) (snd p)) ` (A \<times> B)) \<le> z"
    by (simp add: assms finite_cartesian_product setsum_fun_image_sup)
  thus ?thesis
    by (simp add: eq_iff)
qed

lemma flatten2_im:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite (A ::'a set)"
  and "finite (B ::'a set)"
  shows "\<Sum>((\<lambda>y. \<Sum> ((\<lambda>x. f x y) ` A)) ` B) = \<Sum>((\<lambda>p. f (fst p) (snd p)) ` (A \<times> B))"
  by (simp only: flatten1_im assms cart_flip)

lemma setsum_flatten1:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite (A :: 'a set)"
  and "finite (B :: 'a set)"
  shows "\<Sum>{\<Sum>{f x y |y. y \<in> B} |x. x \<in> A} = \<Sum>{f x y |x y. x \<in> A \<and> y \<in> B}"
  by  (simp add: fset_to_im assms flatten1_im, simp add: fset_to_im[symmetric])


lemma setsum_flatten2:
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite A"
  and "finite B"
  shows "\<Sum>{\<Sum> {f x y |x. x \<in> A} |y. y \<in> B} = \<Sum>{f x y |x y. x \<in> A \<and> y \<in> B}"
  by  (simp add: fset_to_im assms flatten2_im, simp add: fset_to_im[symmetric])

text {* Next we show another additivity property for suprema. *}

lemma setsum_fun_sum:
  fixes f g :: "'a \<Rightarrow> 'b::join_semilattice_zero"
  assumes  "finite (A :: 'a set)"
  shows "\<Sum>((\<lambda>x. f x + g x) ` A) = \<Sum>(f ` A) + \<Sum>(g ` A)"
proof -
  {
    fix z:: 'b
    have "\<Sum>((\<lambda>x. f x + g x) ` A) \<le> z \<longleftrightarrow> \<Sum>(f ` A) + \<Sum>(g ` A) \<le> z"
      by (auto simp add: assms setsum_fun_image_sup add_lub)
  }
  thus ?thesis
    by (simp add: eq_iff)
qed

text {* The last lemma of this section prepares the distributivity
  laws that hold for dioids. It states that a strict additive function
  distributes over finite suprema, which is a continuity property in
  the finite. *}

lemma setsum_fun_add:
  fixes f :: "'a::join_semilattice_zero \<Rightarrow> 'b::join_semilattice_zero"
  assumes "finite (X :: 'a set)"
  and fstrict: "f 0 = 0"
  and fadd: "\<And>x y. f (x + y) = f x + f y"
  shows "f (\<Sum> X) = \<Sum>(f ` X)"
proof (induct rule: finite_induct[OF assms(1)])
  show "f (\<Sum>{}) = \<Sum>(f ` {})"
    by (metis fstrict image_empty setsum.empty)
  fix x :: 'a and  F ::" 'a set"
  assume finF: "finite F"
    and indhyp: "f (\<Sum>F) = \<Sum>(f ` F)"
  have "f (\<Sum>(insert x F)) = f (x + \<Sum>F)"
    by (metis setsum_insert finF)
  also have "... = f x + (f (\<Sum>F))"
    by (rule fadd)
  also have "... = f x + \<Sum>(f ` F)"
    by (metis indhyp)
  also have "... = \<Sum>(f ` (insert x F))"
    by (metis finF setsum_fun_insert)
  finally show "f (\<Sum>(insert x F)) = \<Sum>(f ` insert x F)" .
qed

subsection {* Finite Suprema in Dioids *}

text {* In this section we mainly prove variants of distributivity
laws. *}

lemma setsum_distl:
  assumes "finite Y"
  shows "(x :: 'a::dioid_one_zero) \<cdot> (\<Sum>Y) = \<Sum>{x \<cdot> y|y. y \<in> Y}"
  by (simp only: setsum_fun_add assms annir right_distrib Collect_mem_eq fun_im)

lemma setsum_distr:
  assumes "finite X"
  shows "(\<Sum>X) \<cdot> (y :: 'a::dioid_one_zero) = \<Sum>{x \<cdot> y|x. x \<in> X}"
proof -
  have "(\<Sum> X) \<cdot> y = \<Sum> ((\<lambda>x. x \<cdot> y) ` X)"
    by (rule setsum_fun_add, metis assms, rule annil, rule left_distrib)
  thus ?thesis
    by (metis Collect_mem_eq fun_im)
qed

lemma setsum_fun_distl:
  fixes f :: "'a \<Rightarrow> 'b::dioid_one_zero"
  assumes "finite (Y :: 'a set)"
  shows "x \<cdot> \<Sum>(f ` Y) = \<Sum>{x \<cdot> f y |y. y \<in> Y}"
  by (simp add: assms fun_im image_image setsum_distl)

lemma setsum_fun_distr:
  fixes f :: "'a \<Rightarrow> 'b::dioid_one_zero"
  assumes "finite (X :: 'a set)"
  shows "\<Sum>(f ` X) \<cdot> y = \<Sum>{f x \<cdot> y |x. x \<in> X}"
  by (simp add: assms fun_im image_image setsum_distr)

lemma setsum_distl_flat:
  assumes "finite (X ::'a::dioid_one_zero set)"
  and "finite Y"
  shows "\<Sum>{x \<cdot> \<Sum>Y |x. x \<in> X} = \<Sum>{x \<cdot> y|x y. x \<in> X \<and> y \<in> Y}"
  by (simp only: assms setsum_distl setsum_flatten1)

lemma setsum_distr_flat:
  assumes "finite X"
  and "finite (Y :: 'a::dioid_one_zero set)"
  shows "\<Sum>{(\<Sum>X) \<cdot> y |y. y \<in> Y} = \<Sum>{x \<cdot> y|x y. x \<in> X \<and> y \<in> Y}"
  by (simp only: assms setsum_distr setsum_flatten2)

lemma setsum_sum_distl:
  assumes "finite (X :: 'a::dioid_one_zero set)"
  and "finite Y"
  shows "\<Sum>((\<lambda>x. x \<cdot> (\<Sum>Y)) ` X) = \<Sum>{x \<cdot> y |x y. x \<in> X \<and> y \<in> Y}"
proof -
  have "\<Sum>((\<lambda>x. x \<cdot> (\<Sum>Y)) ` X) = \<Sum>{\<Sum>{x \<cdot> y |y. y \<in> Y} |x. x \<in> X}"
    by (auto simp add: setsum_distl assms fset_to_im)
  thus ?thesis
    by (simp add: assms setsum_flatten1)
qed

lemma setsum_sum_distr:
  assumes "finite X"
  and "finite Y"
  shows "\<Sum>((\<lambda>y. (\<Sum>X) \<cdot> (y :: 'a::dioid_one_zero)) ` Y) = \<Sum>{x \<cdot> y|x y. x \<in> X \<and> y \<in> Y}"
proof -
  have "\<Sum>((\<lambda>y. (\<Sum>X) \<cdot> y) ` Y) = \<Sum>{\<Sum>{x \<cdot> y |x. x \<in> X} |y. y \<in> Y}"
    by (auto simp add: setsum_distr assms fset_to_im)
  thus ?thesis
    by (simp add: assms setsum_flatten2)
qed

lemma setsum_sum_distl_fun:
  fixes f g :: "'a \<Rightarrow> 'b::dioid_one_zero"
  fixes h :: "'a \<Rightarrow> 'a set"
  assumes "\<And>x. finite (h x)"
  and "finite X"
  shows "\<Sum>((\<lambda>x. f x \<cdot> \<Sum>(g ` h x)) ` X) = \<Sum>{\<Sum> {f x \<cdot> g y |y. y \<in> h x} |x. x \<in> X}"
  by (auto simp add: setsum_fun_distl assms fset_to_im)

lemma setsum_sum_distr_fun:
  fixes f g :: "'a \<Rightarrow> 'b::dioid_one_zero"
  fixes h :: "'a \<Rightarrow> 'a set"
  assumes "finite Y"
  and "\<And>y. finite (h y)"
  shows "\<Sum>((\<lambda>y. \<Sum>(f ` h y) \<cdot> g y) ` Y) = \<Sum>{\<Sum>{f x \<cdot> g y |x. x \<in> (h y)} |y. y \<in> Y}"
  by (auto simp add: setsum_fun_distr assms fset_to_im)

lemma setsum_dist:
  assumes "finite (A :: 'a::dioid_one_zero set)"
  and "finite B"
  shows "(\<Sum>A) \<cdot> (\<Sum>B) = \<Sum>{x \<cdot> y |x y. x \<in> A \<and> y \<in> B}"
proof -
  have "(\<Sum>A) \<cdot> (\<Sum>B) = \<Sum>{x \<cdot> \<Sum>B |x. x \<in> A}"
    by (simp add: assms setsum_distr)
  also have "... = \<Sum>{\<Sum>{x \<cdot> y |y. y \<in> B} |x. x \<in> A}"
    by (simp add: assms setsum_distl)
  finally show ?thesis
    by  (simp only: setsum_flatten1 assms finite_cartesian_product)
qed

lemma dioid_setsum_prod_var:
  fixes f g :: "'a \<Rightarrow> 'b::dioid_one_zero"
  assumes "finite (A ::'a set)"
  shows "(\<Sum>(f ` A)) \<cdot> (\<Sum> (g ` A)) = \<Sum>{f x \<cdot> g y |x y. x \<in> A \<and> y \<in> A}"
  by (simp add: assms setsum_dist fprod_aux)

lemma dioid_setsum_prod:
  fixes f g :: "'a \<Rightarrow> 'b::dioid_one_zero"
  assumes "finite (A :: 'a set)"
  shows "(\<Sum>{f x |x. x \<in> A}) \<cdot> (\<Sum>{g x |x. x \<in> A}) = \<Sum>{f x \<cdot> g y |x y. x \<in> A \<and> y \<in> A}"
  by (simp add: assms dioid_setsum_prod_var fset_to_im)

text {* There are interesting theorems for finite sums in Kleene
algebras; we leave them for future consideration. *}

end
