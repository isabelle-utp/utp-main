section {* Derivatives: extra laws and tactics *}

theory Derivative_extra
  imports
  "HOL-Analysis.Analysis"
  "HOL-Eisbach.Eisbach"
begin

subsection {* Properties of filters *}

lemma filtermap_within_range_minus: "filtermap (\<lambda> x. x - n::real) (at y within {x..<y}) = (at (y - n) within ({x-n..<y-n}))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])

lemma filtermap_within_range_plus: "filtermap (\<lambda> x. x + n::real) (at y within {x..<y}) = (at (y + n) within ({x+n..<y+n}))"
  using filtermap_within_range_minus[of "-n"] by simp

lemma filter_upto_contract:
  "\<lbrakk> (x::real) \<le> y; y < z \<rbrakk> \<Longrightarrow> (at z within {x..<z}) = (at z within {y..<z})"
  by (rule at_within_nhd[of _ "{y<..<z+1}"], auto)

subsection {* Topological Spaces *}
  
instantiation unit :: t2_space
begin
  definition open_unit :: "unit set \<Rightarrow> bool" where "open_unit = (\<lambda> _. True)"
  instance by (intro_classes, simp_all add: open_unit_def)
end
 
subsection {* Extra derivative rules *}

lemma has_vector_derivative_Pair [derivative_intros]:
  "\<lbrakk> (f has_vector_derivative f') (at x within s); (g has_vector_derivative g') (at x within s) \<rbrakk> \<Longrightarrow>
      ((\<lambda> x. (f x, g x)) has_vector_derivative (f', g')) (at x within s)"
  by (auto intro: has_derivative_Pair simp add: has_vector_derivative_def)

lemma has_vector_derivative_power[simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a :: real_normed_field"
  assumes f: "(f has_vector_derivative f') (at x within s)"
  shows "((\<lambda>x. f x^n) has_vector_derivative (of_nat n * f' * f x^(n - 1))) (at x within s)"
  using assms
  apply (simp add: has_vector_derivative_def)
  apply (subst has_derivative_eq_rhs)
  apply (rule has_derivative_power)
  apply (auto)
done

lemma has_vector_derivative_divide[simp, derivative_intros]:
  fixes f :: "real \<Rightarrow> 'a :: real_normed_div_algebra"
  assumes f: "(f has_vector_derivative f') (at x within s)"
      and g: "(g has_vector_derivative g') (at x within s)"
  assumes x: "g x \<noteq> 0"
  shows "((\<lambda>x. f x / g x) has_vector_derivative
                (- f x * (inverse (g x) * g' * inverse (g x)) + f' / g x)) (at x within s)"
  using assms
  apply (simp add: has_vector_derivative_def)
  apply (subst has_derivative_eq_rhs)
  apply (rule has_derivative_divide)
  apply (auto simp add: divide_inverse real_vector.scale_right_diff_distrib)
done

lemma Pair_has_vector_derivative:
  assumes "(f has_vector_derivative f') (at x within s)"
    "(g has_vector_derivative g') (at x within s)"
  shows "((\<lambda>x. (f x, g x)) has_vector_derivative (f', g')) (at x within s)"
  using assms
  by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros)
  
lemma has_vector_derivative_fst:
  assumes "((\<lambda>x. (f x, g x)) has_vector_derivative (f', g')) (at x within s)"
  shows "(f has_vector_derivative f') (at x within s)"
  using assms
  by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros dest: has_derivative_fst)

lemma has_vector_derivative_fst' [derivative_intros]:
  assumes "(f has_vector_derivative (f', g')) (at x within s)"
  shows "(fst \<circ> f has_vector_derivative f') (at x within s)"
proof -
  have "(\<lambda> x. (fst (f x), snd (f x))) = f"
    by (simp)
  with assms have "((\<lambda> x. (fst (f x), snd (f x))) has_vector_derivative (f', g')) (at x within s)"
    by (simp)
  thus ?thesis
    by (drule_tac has_vector_derivative_fst, simp add: comp_def)
qed
    
lemma has_vector_derivative_snd:
  assumes "((\<lambda>x. (f x, g x)) has_vector_derivative (f', g')) (at x within s)"
  shows "(g has_vector_derivative g') (at x within s)"
  using assms
  by (auto simp: has_vector_derivative_def intro!: derivative_eq_intros dest: has_derivative_snd)

lemma has_vector_derivative_snd'' [derivative_intros]:
  assumes "(f has_vector_derivative (f', g')) (at x within s)"
  shows "(snd \<circ> f has_vector_derivative g') (at x within s)"
proof -
  have "(\<lambda> x. (fst (f x), snd (f x))) = f"
    by (simp)
  with assms have "((\<lambda> x. (fst (f x), snd (f x))) has_vector_derivative (f', g')) (at x within s)"
    by (simp)
  thus ?thesis
    by (drule_tac has_vector_derivative_snd, simp add: comp_def)
qed

lemma Pair_has_vector_derivative_iff:
  "((\<lambda>x. (f x, g x)) has_vector_derivative (f', g')) (at x within s) \<longleftrightarrow>
   (f has_vector_derivative f') (at x within s) \<and> (g has_vector_derivative g') (at x within s)"
  using Pair_has_vector_derivative has_vector_derivative_fst has_vector_derivative_snd by blast
  
text {* The next four rules allow us to prove derivatives when the function is equivalent to
  another a function when approach from the left or right. *}
 
lemma has_derivative_left_point:
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f has_derivative f') (at x within s)" "x \<in> s" "x < y" "\<forall>x'<y. f x' = g x'"
  shows "(g has_derivative f') (at x within s)"
  apply (rule has_derivative_transform_within[of f f' x s "y-x" g])
  apply (simp_all add: assms dist_real_def)
done
  
lemma has_derivative_right_point:
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f has_derivative f') (at x within s)" "x \<in> s" "x > y" "\<forall>x'>y. f x' = g x'"
  shows "(g has_derivative f') (at x within s)"
  apply (rule has_derivative_transform_within[of f f' x s "x-y" g])
  apply (simp_all add: assms dist_real_def)
done
  
lemma has_vector_derivative_left_point:
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f has_vector_derivative f') (at x within s)" "x \<in> s" "x < y" "\<forall>x'<y. f x' = g x'"
  shows "(g has_vector_derivative f') (at x within s)"
  using assms
  apply (simp add: has_vector_derivative_def)
  apply (rule_tac y="y" and f="f" in has_derivative_left_point)
  apply (auto simp add: assms)
done

lemma has_vector_derivative_right_point:
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f has_vector_derivative f') (at x within s)" "x \<in> s" "x > y" "\<forall>x'>y. f x' = g x'"
  shows "(g has_vector_derivative f') (at x within s)"
  using assms
  apply (simp add: has_vector_derivative_def)
  apply (rule_tac y="y" and f="f" in has_derivative_right_point)
  apply (auto simp add: assms)
done
  
lemma max_simps [simp]: 
  "(y::real) < max x y \<longleftrightarrow> y < x" 
  "x < max x y \<longleftrightarrow> x < y"
  "max x y = y \<longleftrightarrow> x \<le> y"
  by auto
    
lemma min_simps [simp]:
  "min (x::real) y < x \<longleftrightarrow> y < x"
  "min x y < y \<longleftrightarrow> x < y"
  by auto

subsection \<open> Calculating derivatives \<close>

text \<open> We set up some nice syntax for taking derivatives by calculation, and prove associated
  theorems based on the Multivariate Analysis package. \<close>

notation frechet_derivative ("\<partial>")
notation vector_derivative ("\<partial>\<^sub>v")

lemma vector_derivative_chain_frechet: 
  fixes g :: "'a::ordered_euclidean_space \<Rightarrow> 'b::ordered_euclidean_space"
  assumes "f differentiable (at x)" "g differentiable (at (f x))"
  shows "\<partial>\<^sub>v (g \<circ> f) (at x) = \<partial> g (at (f x)) (\<partial>\<^sub>v f (at x))"
proof -
  have "(g has_derivative \<partial> g (at (f x))) (at (f x))"
    using assms(2) frechet_derivative_works by blast
  hence 1:"(g has_derivative \<partial> g (at (f x))) (at (f x) within range f)"
    by (simp add: has_derivative_at_withinI)
  from 1 assms show ?thesis
    by (auto intro: vector_derivative_chain_within simp add: at_eq_bot_iff)
qed

lemma frechet_derivative_const: "\<partial> (\<lambda> x. k) (at t) = (\<lambda> x. 0)"
  by (metis frechet_derivative_at has_derivative_const)

lemma frechet_derivative_plus:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "f differentiable (at t)" "g differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x + g x) (at t) = (\<lambda> x. \<partial> f (at t) x + \<partial> g (at t) x)"
proof -
  have "((\<lambda>x. f x + g x) has_derivative (\<lambda>x. \<partial> f (at t) x + \<partial> g (at t) x)) (at t)"
    using assms(1) assms(2) frechet_derivative_works has_derivative_add by blast
  thus ?thesis
    using frechet_derivative_at by force
qed

lemma frechet_derivative_uminus:
  assumes "f differentiable (at t)"
  shows "\<partial> (\<lambda> x. - f x) (at t) = (\<lambda>x. - \<partial> f (at t) x)"
proof -
  have "((\<lambda>x. - f x) has_derivative (\<lambda>x. - \<partial> f (at t) x)) (at t)"
    using assms frechet_derivative_works has_derivative_minus by blast
  thus ?thesis
    using frechet_derivative_at by force
qed

lemma frechet_derivative_minus:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes "f differentiable (at t)" "g differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x - g x) (at t) = (\<lambda> x. \<partial> f (at t) x - \<partial> g (at t) x)"
proof -
  have "((\<lambda>x. f x - g x) has_derivative (\<lambda>x. \<partial> f (at t) x - \<partial> g (at t) x)) (at t)"
    using assms(1) assms(2) frechet_derivative_works has_derivative_diff by blast
  thus ?thesis
    using frechet_derivative_at by force
qed

lemma frechet_derivative_mult:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "f differentiable (at t)" "g differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x * g x) (at t) = 
         (\<lambda> x. f t * \<partial> g (at t) x + \<partial> f (at t) x * g t)"
proof -
  have "((\<lambda>x. f x * g x) has_derivative (\<lambda> x. f t * \<partial> g (at t) x + \<partial> f (at t) x * g t)) (at t)"
    using assms(1) assms(2) frechet_derivative_works has_derivative_mult by blast
  thus ?thesis
    using frechet_derivative_at by force
qed

lemma frechet_derivative_scaleR:
  fixes g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes "f differentiable (at t)" "g differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x *\<^sub>R g x) (at t) = 
         (\<lambda> x. f t *\<^sub>R \<partial> g (at t) x + \<partial> f (at t) x *\<^sub>R g t)"
proof -
  have "((\<lambda>x. f x *\<^sub>R g x) has_derivative (\<lambda> x. f t *\<^sub>R \<partial> g (at t) x + \<partial> f (at t) x *\<^sub>R g t)) (at t)"
  proof -
    have "(f has_derivative \<partial> f (at t)) (at t)"
      by (meson assms(1) frechet_derivative_works)
    then show ?thesis
      using assms(2) frechet_derivative_works has_derivative_scaleR by blast
  qed

  thus ?thesis
    using frechet_derivative_at by force
qed

lemma frechet_derivative_norm:
  fixes f :: "'a::{real_inner} \<Rightarrow> 'b::{real_inner}"
  assumes "f differentiable (at t)" "f t \<noteq> 0"
  shows "\<partial> (\<lambda> x. norm (f x)) (at t) = (\<lambda> x. \<partial> f (at t) x \<bullet> sgn (f t))"
proof -
  have "(norm \<circ> f has_derivative ((\<lambda> x. x \<bullet> sgn (f t)) \<circ> \<partial> f (at t))) (at t)"
    using assms(1) assms(2) diff_chain_at frechet_derivative_works has_derivative_norm by blast
  thus ?thesis
    by (metis assms differentiable_def frechet_derivative_at has_derivative_compose has_derivative_norm)
qed

lemma frechet_derivative_power:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_field"
  assumes "f differentiable (at t)"
  shows "\<partial> (\<lambda> x. f x ^ n) (at t) = (\<lambda>y. of_nat n * \<partial> f (at t) y * f t ^ (n - 1))"
  using assms has_derivative_power[of f "\<partial> f (at t)" t UNIV n] frechet_derivative_at
  by (fastforce simp add: frechet_derivative_works)

lemma frechet_derivative_powr:
  fixes f :: "'a::{banach, real_normed_algebra_1} \<Rightarrow> real"
  assumes "f differentiable (at t)" "g differentiable (at t)" "0 < f t"
  shows "\<partial> (\<lambda> x. f x powr g x) (at t) = (\<lambda>h. f t powr g t * (\<partial> g (at t) h * ln (f t) + \<partial> f (at t) h * g t / f t))"
  using assms has_derivative_powr[of f "\<partial> f (at t)" t UNIV g "\<partial> g (at t)"] frechet_derivative_at
  by (fastforce simp add: frechet_derivative_works)

lemma frechet_derivative_ln:
  fixes f :: "'a::{banach, real_normed_algebra_1} \<Rightarrow> real"
  assumes "f differentiable (at t)" "0 < f t"
  shows "\<partial> (\<lambda> x. ln (f x)) (at t) = (\<lambda> x. \<partial> f (at t) x * inverse (f t))"
  by (metis assms(1) assms(2) frechet_derivative_at frechet_derivative_works has_derivative_ln)

lemma frechet_derivative_sin:
  fixes f :: "'a::{banach, real_normed_algebra_1} \<Rightarrow> real"
  assumes "f differentiable (at t)"
  shows "\<partial> (\<lambda> x. sin (f x)) (at t) = (\<lambda> x. \<partial> f (at t) x * cos (f t))"
  by (metis assms frechet_derivative_at frechet_derivative_works has_derivative_sin)

end