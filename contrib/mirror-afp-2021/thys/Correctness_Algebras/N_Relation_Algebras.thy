(* Title:      N-Relation-Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>N-Relation-Algebras\<close>

theory N_Relation_Algebras

imports Stone_Relation_Algebras.Relation_Algebras N_Omega_Algebras

begin

context bounded_distrib_allegory
begin

subclass lattice_ordered_pre_left_semiring ..

end

text \<open>Theorem 37\<close>

sublocale relation_algebra < n_algebra where sup = sup and bot = bot and top = top and inf = inf and n = N and L = top
  apply unfold_locales
  using N_comp_top comp_inf.semiring.distrib_left inf.sup_monoid.add_commute inf_vector_comp apply simp
  apply (metis N_comp compl_sup double_compl mult_assoc mult_right_dist_sup top_mult_top N_comp_N)
  apply (metis brouwer.p_antitone inf.sup_monoid.add_commute inf.sup_right_isotone mult_left_isotone p_antitone_sup)
  apply simp
  using N_vector_top apply force
  apply simp
  apply (simp add: brouwer.p_antitone_iff top_right_mult_increasing)
  apply simp
  apply (metis N_comp_top conv_complement_sub double_compl le_supI2 le_iff_sup mult_assoc mult_left_isotone schroeder_3)
  by simp

sublocale relation_algebra < n_algebra_apx where sup = sup and bot = bot and top = top and inf = inf and n = N and L = top and apx = greater_eq
  apply unfold_locales
  using n_less_eq_char by force

no_notation
  inverse_divide (infixl "'/" 70)

notation
  divide (infixl "'/" 70)

class left_residuated_relation_algebra = relation_algebra + inverse +
  assumes lres_def: "x / y = -(-x * y\<^sup>T)"
begin

text \<open>Theorem 32.1\<close>

subclass residuated_pre_left_semiring
  apply unfold_locales
  by (metis compl_le_swap1 lres_def schroeder_4)

end

context left_residuated_relation_algebra
begin

text \<open>Theorem 32.3\<close>

lemma lres_mult_lres_lres:
  "x / (z * y) = (x / y) / z"
  by (metis conv_dist_comp double_compl lres_def mult_assoc)

text \<open>Theorem 32.5\<close>

lemma lres_dist_inf:
  "(x \<sqinter> y) / z = (x / z) \<sqinter> (y / z)"
  by (metis compl_inf compl_sup lres_def mult_right_dist_sup)

text \<open>Theorem 32.6\<close>

lemma lres_add_export_vector:
  assumes "vector x"
    shows "(x \<squnion> y) / z = x \<squnion> (y / z)"
proof -
  have "(x \<squnion> y) / z = -((-x \<sqinter> -y) * z\<^sup>T)"
    by (simp add: lres_def)
  also have "... = -(-x \<sqinter> (-y * z\<^sup>T))"
    using assms vector_complement_closed vector_inf_comp by auto
  also have "... = x \<squnion> (y / z)"
    by (simp add: lres_def)
  finally show ?thesis
    .
qed

text \<open>Theorem 32.7\<close>

lemma lres_top_vector:
  "vector (x / top)"
  using equivalence_top_closed lres_def vector_complement_closed vector_mult_closed vector_top_closed by auto

text \<open>Theorem 32.10\<close>

lemma lres_top_export_inf_mult:
  "((x / top) \<sqinter> y) * z = (x / top) \<sqinter> (y * z)"
  by (simp add: vector_inf_comp lres_top_vector)

lemma N_lres:
  "N(x) = x / top \<sqinter> 1"
  using lres_def by auto

end

class complete_relation_algebra = relation_algebra + complete_lattice
begin

definition mu :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where "mu f \<equiv> Inf { y . f y \<le> y }"
definition nu :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a" where "nu f \<equiv> Sup { y . y \<le> f y }"

lemma mu_lower_bound:
  "f x \<le> x \<Longrightarrow> mu f \<le> x"
  by (auto simp add: mu_def intro: Inf_lower)

lemma mu_greatest_lower_bound:
  "(\<forall>y . f y \<le> y \<longrightarrow> x \<le> y) \<Longrightarrow> x \<le> mu f"
  using lfp_def lfp_greatest mu_def by auto

lemma mu_unfold_1:
  "isotone f \<Longrightarrow> f (mu f) \<le> mu f"
  by (metis mu_greatest_lower_bound order_trans mu_lower_bound isotone_def)

lemma mu_unfold_2:
  "isotone f \<Longrightarrow> mu f \<le> f (mu f)"
  by (simp add: mu_lower_bound mu_unfold_1 ord.isotone_def)

lemma mu_unfold:
  "isotone f \<Longrightarrow> mu f = f (mu f)"
  by (simp add: order.antisym mu_unfold_1 mu_unfold_2)

lemma mu_const:
  "mu (\<lambda>x . y) = y"
  by (simp add: isotone_def mu_unfold)

lemma mu_lpfp:
  "isotone f \<Longrightarrow> is_least_prefixpoint f (mu f)"
  by (simp add: is_least_prefixpoint_def mu_lower_bound mu_unfold_1)
  
lemma mu_lfp:
  "isotone f \<Longrightarrow> is_least_fixpoint f (mu f)"
  by (metis is_least_fixpoint_def mu_lower_bound mu_unfold order_refl)

lemma mu_pmu:
  "isotone f \<Longrightarrow> p\<mu> f = mu f"
  using least_prefixpoint_same mu_lpfp by force
  
lemma mu_mu:
  "isotone f \<Longrightarrow> \<mu> f = mu f"
  using least_fixpoint_same mu_lfp by fastforce
  
end

class omega_relation_algebra = relation_algebra + star + omega +
  assumes ra_star_left_unfold : "1 \<squnion> y * y\<^sup>\<star> \<le> y\<^sup>\<star>"
  assumes ra_star_left_induct : "z \<squnion> y * x \<le> x \<longrightarrow> y\<^sup>\<star> * z \<le> x"
  assumes ra_star_right_induct: "z \<squnion> x * y \<le> x \<longrightarrow> z * y\<^sup>\<star> \<le> x"
  assumes ra_omega_unfold: "y\<^sup>\<omega> = y * y\<^sup>\<omega>"
  assumes ra_omega_induct: "x \<le> z \<squnion> y * x \<longrightarrow> x \<le> y\<^sup>\<omega> \<squnion> y\<^sup>\<star> * z"
begin

subclass bounded_omega_algebra
  apply unfold_locales
  using ra_star_left_unfold apply blast
  using ra_star_left_induct apply blast
  using ra_star_right_induct apply blast
  using ra_omega_unfold apply blast
  using ra_omega_induct by blast

end

text \<open>Theorem 38\<close>

sublocale omega_relation_algebra < n_omega_algebra where sup = sup and bot = bot and top = top and inf = inf and n = N and L = top and apx = greater_eq and Omega = "\<lambda>x . N(x\<^sup>\<omega>) * top \<squnion> x\<^sup>\<star>"
  apply unfold_locales
  apply simp
  using n_split_omega_mult omega_vector star_mult_omega apply force
  by simp

end

