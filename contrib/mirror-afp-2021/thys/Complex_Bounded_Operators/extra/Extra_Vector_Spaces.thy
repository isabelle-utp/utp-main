section \<open>\<open>Extra_Vector_Spaces\<close> -- Additional facts about vector spaces\<close>

theory Extra_Vector_Spaces
  imports
    "HOL-Analysis.Inner_Product"
    "HOL-Analysis.Euclidean_Space"
    "HOL-Library.Indicator_Function"
    "HOL-Analysis.Topology_Euclidean_Space"
    "HOL-Analysis.Line_Segment"
    Extra_General
begin

subsection \<open>Euclidean spaces\<close>

typedef 'a euclidean_space = "UNIV :: ('a \<Rightarrow> real) set" ..
setup_lifting type_definition_euclidean_space

instantiation euclidean_space :: (type) real_vector begin
lift_definition plus_euclidean_space ::
  "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space"
  is "\<lambda>f g x. f x + g x" .
lift_definition zero_euclidean_space :: "'a euclidean_space" is "\<lambda>_. 0" .
lift_definition uminus_euclidean_space :: 
  "'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>f x. - f x" .
lift_definition minus_euclidean_space :: 
  "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>f g x. f x - g x".
lift_definition scaleR_euclidean_space :: 
  "real \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>c f x. c * f x" .
instance
  apply intro_classes
  by (transfer; auto intro: distrib_left distrib_right)+
end

instantiation euclidean_space :: (finite) real_inner begin
lift_definition inner_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> real"
  is "\<lambda>f g. \<Sum>x\<in>UNIV. f x * g x :: real" .
definition "norm_euclidean_space (x::'a euclidean_space) = sqrt (inner x x)"
definition "dist_euclidean_space (x::'a euclidean_space) y = norm (x-y)"
definition "sgn x = x /\<^sub>R norm x" for x::"'a euclidean_space"
definition "uniformity = (INF e\<in>{0<..}. principal {(x::'a euclidean_space, y). dist x y < e})"
definition "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x'::'a euclidean_space, y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
instance
proof intro_classes
  fix x :: "'a euclidean_space"
    and y :: "'a euclidean_space"
    and z :: "'a euclidean_space"
  show "dist (x::'a euclidean_space) y = norm (x - y)"
    and "sgn (x::'a euclidean_space) = x /\<^sub>R norm x"
    and "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a euclidean_space) y < e})"
    and "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a euclidean_space) = x \<longrightarrow> y \<in> U)"
    and "norm x = sqrt (inner x x)" for U
    unfolding dist_euclidean_space_def norm_euclidean_space_def sgn_euclidean_space_def
      uniformity_euclidean_space_def open_euclidean_space_def
    by simp_all

  show "inner x y = inner y x"
    apply transfer
    by (simp add: mult.commute)
  show "inner (x + y) z = inner x z + inner y z"
  proof transfer
    fix x y z::"'a \<Rightarrow> real"
    have "(\<Sum>i\<in>UNIV. (x i + y i) * z i) = (\<Sum>i\<in>UNIV. x i * z i + y i * z i)"
      by (simp add: distrib_left mult.commute)
    thus "(\<Sum>i\<in>UNIV. (x i + y i) * z i) = (\<Sum>j\<in>UNIV. x j * z j) + (\<Sum>k\<in>UNIV. y k * z k)"
      by (subst sum.distrib[symmetric])      
  qed

  show "inner (r *\<^sub>R x) y = r * (inner x y)" for r
  proof transfer
    fix r and x y::"'a\<Rightarrow>real"
    have "(\<Sum>i\<in>UNIV. r * x i * y i) = (\<Sum>i\<in>UNIV. r * (x i * y i))"
      by (simp add: mult.assoc)
    thus "(\<Sum>i\<in>UNIV. r * x i * y i) = r * (\<Sum>j\<in>UNIV. x j * y j)"
      by (subst sum_distrib_left)
  qed
  show "0 \<le> inner x x"
    apply transfer
    by (simp add: sum_nonneg)
  show "(inner x x = 0) = (x = 0)"
  proof (transfer, rule)
    fix f :: "'a \<Rightarrow> real"
    assume "(\<Sum>i\<in>UNIV. f i * f i) = 0"
    hence "f x * f x = 0" for x
      apply (rule_tac sum_nonneg_eq_0_iff[THEN iffD1, rule_format, where A=UNIV and x=x])
      by auto
    thus "f = (\<lambda>_. 0)"
      by auto
  qed auto
qed
end

instantiation euclidean_space :: (finite) euclidean_space begin
lift_definition euclidean_space_basis_vector :: "'a \<Rightarrow> 'a euclidean_space" is
  "\<lambda>x. indicator {x}" .
definition "Basis_euclidean_space == (euclidean_space_basis_vector ` UNIV)"
instance
proof intro_classes
  fix u :: "'a euclidean_space"
    and v :: "'a euclidean_space"
  show "(Basis::'a euclidean_space set) \<noteq> {}"
    unfolding Basis_euclidean_space_def by simp
  show "finite (Basis::'a euclidean_space set)"
    unfolding Basis_euclidean_space_def by simp
  show "inner u v = (if u = v then 1 else 0)"
    if "u \<in> Basis" and "v \<in> Basis"
    using that unfolding Basis_euclidean_space_def
    apply transfer apply auto
    by (auto simp: indicator_def)
  show "(\<forall>v\<in>Basis. inner u v = 0) = (u = 0)"
    unfolding Basis_euclidean_space_def
    apply transfer
    by auto
qed
end (* euclidean_space :: (finite) euclidean_space *)

lemma closure_bounded_linear_image_subset_eq:
  assumes f: "bounded_linear f"
  shows "closure (f ` closure S) = closure (f ` S)"
  by (meson closed_closure closure_bounded_linear_image_subset closure_minimal closure_mono closure_subset f image_mono subset_antisym)

lemma not_singleton_real_normed_is_perfect_space[simp]: \<open>class.perfect_space (open :: 'a::{not_singleton,real_normed_vector} set \<Rightarrow> bool)\<close>
  apply standard
  by (metis UNIV_not_singleton clopen closed_singleton empty_not_insert)

end
