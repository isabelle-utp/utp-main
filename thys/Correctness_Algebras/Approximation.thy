(* Title:      Approximation
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Approximation\<close>

theory Approximation

imports Stone_Kleene_Relation_Algebras.Iterings

begin

class apx =
  fixes apx :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)

class apx_order = apx +
  assumes apx_reflexive: "x \<sqsubseteq> x"
  assumes apx_antisymmetric: "x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longrightarrow> x = y"
  assumes apx_transitive: "x \<sqsubseteq> y \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z"

sublocale apx_order < apx: order where less_eq = apx and less = "\<lambda>x y . x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x"
  apply unfold_locales
  apply simp
  apply (rule apx_reflexive)
  using apx_transitive apply blast
  by (simp add: apx_antisymmetric)

context apx_order
begin

abbreviation the_apx_least_fixpoint    :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<kappa> _" [201] 200)  where "\<kappa>  f \<equiv> apx.the_least_fixpoint f"
abbreviation the_apx_least_prefixpoint :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" ("p\<kappa> _" [201] 200) where "p\<kappa> f \<equiv> apx.the_least_prefixpoint f"

definition is_apx_meet  :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"          where "is_apx_meet x y z \<equiv> z \<sqsubseteq> x \<and> z \<sqsubseteq> y \<and> (\<forall>w . w \<sqsubseteq> x \<and> w \<sqsubseteq> y \<longrightarrow> w \<sqsubseteq> z)"
definition has_apx_meet :: "'a \<Rightarrow> 'a \<Rightarrow> bool"                where "has_apx_meet x y \<equiv> \<exists>z . is_apx_meet x y z"
definition the_apx_meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<triangle>" 66) where "x \<triangle> y \<equiv> THE z . is_apx_meet x y z"

lemma apx_meet_unique:
  "has_apx_meet x y \<Longrightarrow> \<exists>!z . is_apx_meet x y z"
  by (meson apx_antisymmetric has_apx_meet_def is_apx_meet_def)

lemma apx_meet:
  assumes "has_apx_meet x y"
    shows "is_apx_meet x y (x \<triangle> y)"
proof -
  have "is_apx_meet x y (THE z . is_apx_meet x y z)"
    by (metis apx_meet_unique assms theI)
  thus ?thesis
    by (simp add: the_apx_meet_def)
qed

lemma apx_greatest_lower_bound:
  "has_apx_meet x y \<Longrightarrow> (w \<sqsubseteq> x \<and> w \<sqsubseteq> y \<longleftrightarrow> w \<sqsubseteq> x \<triangle> y)"
  by (meson apx_meet apx_transitive is_apx_meet_def)

lemma apx_meet_same:
  "is_apx_meet x y z \<Longrightarrow> z = x \<triangle> y"
  using apx_meet apx_meet_unique has_apx_meet_def by blast

lemma apx_meet_char:
  "is_apx_meet x y z \<longleftrightarrow> has_apx_meet x y \<and> z = x \<triangle> y"
  using apx_meet_same has_apx_meet_def by auto

end

class apx_biorder = apx_order + order
begin

lemma mu_below_kappa:
  "has_least_fixpoint f \<Longrightarrow> apx.has_least_fixpoint f \<Longrightarrow> \<mu> f \<le> \<kappa> f"
  using apx.mu_unfold is_least_fixpoint_def least_fixpoint by auto

lemma kappa_below_nu:
  "has_greatest_fixpoint f \<Longrightarrow> apx.has_least_fixpoint f \<Longrightarrow> \<kappa> f \<le> \<nu> f"
  by (meson apx.mu_unfold greatest_fixpoint is_greatest_fixpoint_def)

lemma kappa_apx_below_mu:
  "has_least_fixpoint f \<Longrightarrow> apx.has_least_fixpoint f \<Longrightarrow> \<kappa> f \<sqsubseteq> \<mu> f"
  using apx.is_least_fixpoint_def apx.least_fixpoint mu_unfold by auto

lemma kappa_apx_below_nu:
  "has_greatest_fixpoint f \<Longrightarrow> apx.has_least_fixpoint f \<Longrightarrow> \<kappa> f \<sqsubseteq> \<nu> f"
  by (metis apx.is_least_fixpoint_def apx.least_fixpoint nu_unfold)

end

class apx_semiring = apx_biorder + idempotent_left_semiring + L +
  assumes apx_L_least: "L \<sqsubseteq> x"
  assumes sup_apx_left_isotone: "x \<sqsubseteq> y \<longrightarrow> x \<squnion> z \<sqsubseteq> y \<squnion> z"
  assumes mult_apx_left_isotone: "x \<sqsubseteq> y \<longrightarrow> x * z \<sqsubseteq> y * z"
  assumes mult_apx_right_isotone: "x \<sqsubseteq> y \<longrightarrow> z * x \<sqsubseteq> z * y"
begin

lemma sup_apx_right_isotone:
  "x \<sqsubseteq> y \<Longrightarrow> z \<squnion> x \<sqsubseteq> z \<squnion> y"
  by (simp add: sup_apx_left_isotone sup_commute)

lemma sup_apx_isotone:
  "w \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> w \<squnion> x \<sqsubseteq> y \<squnion> z"
  by (meson apx_transitive sup_apx_left_isotone sup_apx_right_isotone)

lemma mult_apx_isotone:
  "w \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> w * x \<sqsubseteq> y * z"
  by (meson apx_transitive mult_apx_left_isotone mult_apx_right_isotone)

lemma affine_apx_isotone:
  "apx.isotone (\<lambda>x . y * x \<squnion> z)"
  by (simp add: apx.isotone_def mult_apx_right_isotone sup_apx_left_isotone)

end

end

