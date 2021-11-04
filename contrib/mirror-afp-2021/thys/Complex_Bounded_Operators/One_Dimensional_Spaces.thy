section \<open>\<open>One_Dimensional_Spaces\<close> -- One dimensional complex vector spaces\<close>

theory One_Dimensional_Spaces
  imports
    Complex_Inner_Product
    "Complex_Bounded_Operators.Extra_Operator_Norm"
begin

text \<open>The class \<open>one_dim\<close> applies to one-dimensional vector spaces.
     Those are additionally interpreted as \<^class>\<open>complex_algebra_1\<close>s 
     via the canonical isomorphism between a one-dimensional vector space and 
     \<^typ>\<open>complex\<close>.\<close>
class one_dim = onb_enum + one + times + complex_inner + inverse +
  assumes one_dim_canonical_basis[simp]: "canonical_basis = [1]"
  assumes one_dim_prod_scale1: "(a *\<^sub>C 1) * (b *\<^sub>C 1) = (a*b) *\<^sub>C 1"
  assumes divide_inverse: "x / y = x * inverse y"
  assumes one_dim_inverse: "inverse (a *\<^sub>C 1) = inverse a *\<^sub>C 1"

hide_fact (open) divide_inverse (* divide_inverse from field_class, instantiated below, subsumed this one *)

instance complex :: one_dim
  apply intro_classes
  unfolding canonical_basis_complex_def is_ortho_set_def
  by (auto simp: divide_complex_def)

lemma one_cinner_one[simp]: \<open>\<langle>(1::('a::one_dim)), 1\<rangle> = 1\<close>
proof-
  include notation_norm
  have \<open>(canonical_basis::'a list) = [1::('a::one_dim)]\<close>
    by (simp add: one_dim_canonical_basis)    
  hence \<open>\<parallel>1::'a::one_dim\<parallel> = 1\<close>
    by (metis is_normal list.set_intros(1))
  hence \<open>\<parallel>1::'a::one_dim\<parallel>^2 = 1\<close>
    by simp
  moreover have  \<open>\<parallel>(1::('a::one_dim))\<parallel>^2 = \<langle>(1::('a::one_dim)), 1\<rangle>\<close>
    by (metis cnorm_eq_square)
  ultimately show ?thesis by simp
qed

lemma one_cinner_a_scaleC_one[simp]: \<open>\<langle>1::('a::one_dim), a\<rangle> *\<^sub>C 1 = a\<close>
proof-
  have \<open>(canonical_basis::'a list) = [1]\<close>
    by (simp add: one_dim_canonical_basis)
  hence r2: \<open>a \<in> complex_vector.span ({1::'a})\<close>        
    using  iso_tuple_UNIV_I empty_set is_generator_set list.simps(15)
    by metis
  have "(1::'a) \<notin> {}"
    by (metis equals0D)
  hence r1: \<open>\<exists> s. a = s *\<^sub>C 1\<close>
    by (metis Diff_insert_absorb r2 complex_vector.span_breakdown 
        complex_vector.span_empty eq_iff_diff_eq_0 singleton_iff)
  then obtain s where s_def: \<open>a = s *\<^sub>C 1\<close>
    by blast
  have  \<open>\<langle>(1::'a), a\<rangle> = \<langle>(1::'a), s *\<^sub>C 1\<rangle>\<close>
    using \<open>a = s *\<^sub>C 1\<close>
    by simp 
  also have \<open>\<dots> = s * \<langle>(1::'a), 1\<rangle>\<close>
    by simp
  also have \<open>\<dots> = s\<close>
    using one_cinner_one by auto
  finally show ?thesis
    by (simp add: s_def) 
qed

lemma one_dim_apply_is_times_def:
  "\<psi> * \<phi> = (\<langle>1, \<psi>\<rangle> * \<langle>1, \<phi>\<rangle>) *\<^sub>C 1" for \<psi> :: \<open>'a::one_dim\<close>
  by (metis one_cinner_a_scaleC_one one_dim_prod_scale1)

instance one_dim \<subseteq> complex_algebra_1
proof
  fix x y z :: \<open>'a::one_dim\<close> and c :: complex
  show "(x * y) * z = x * (y * z)"
    by (simp add: one_dim_apply_is_times_def[where ?'a='a])
  show "(x + y) * z = x * z + y * z"
    by (metis (no_types, lifting) cinner_simps(2) complex_vector.vector_space_assms(2) complex_vector.vector_space_assms(3) one_dim_apply_is_times_def)
  show "x * (y + z) = x * y + x * z"
    by (metis (mono_tags, lifting) cinner_simps(2) complex_vector.vector_space_assms(2) distrib_left one_dim_apply_is_times_def)
  show "(c *\<^sub>C x) * y = c *\<^sub>C (x * y)"
    by (simp add: one_dim_apply_is_times_def[where ?'a='a])
  show "x * (c *\<^sub>C y) = c *\<^sub>C (x * y)"
    by (simp add: one_dim_apply_is_times_def[where ?'a='a])
  show "1 * x = x"
    by (metis mult.left_neutral one_cinner_a_scaleC_one one_cinner_one one_dim_apply_is_times_def)
  show "x * 1 = x"
    by (simp add: one_dim_apply_is_times_def [where ?'a = 'a])
  show "(0::'a) \<noteq> 1"
    by (metis cinner_eq_zero_iff one_cinner_one zero_neq_one)
qed

instance one_dim \<subseteq> complex_normed_algebra
proof
  fix x y :: \<open>'a::one_dim\<close>
  show "norm (x * y) \<le> norm x * norm y"
  proof-
    have r1:  "cmod (\<langle>1::'a, x\<rangle>) \<le> norm (1::'a) * norm x"
      by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
    have r2: "cmod (\<langle>1::'a, y\<rangle>) \<le> norm (1::'a) * norm y"
      by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)

    have q1: "\<langle>(1::'a), 1\<rangle> = 1"
      by (simp add: )
    hence "(norm (1::'a))^2 = 1"
      by (simp add: cnorm_eq_1 power2_eq_1_iff)
    hence "norm (1::'a) = 1"
      by (smt abs_norm_cancel power2_eq_1_iff)
    hence "cmod (\<langle>1::'a, x\<rangle> * \<langle>1::'a, y\<rangle>) * norm (1::'a) = cmod (\<langle>1::'a, x\<rangle> * \<langle>1::'a, y\<rangle>)"
      by simp
    also have "\<dots> = cmod (\<langle>1::'a, x\<rangle>) * cmod (\<langle>1::'a, y\<rangle>)"
      by (simp add: norm_mult)
    also have "\<dots> \<le> norm (1::'a) * norm x * norm (1::'a) * norm y"
      by (smt \<open>norm 1 = 1\<close> mult.commute mult_cancel_right1 norm_scaleC one_cinner_a_scaleC_one)
    also have "\<dots> = norm x * norm y"
      by (simp add: \<open>norm 1 = 1\<close>)
    finally show ?thesis
      by (simp add: one_dim_apply_is_times_def[where ?'a='a])
  qed
qed

instance one_dim \<subseteq> complex_normed_algebra_1
proof intro_classes
  show "norm (1::'a) = 1"
    by (metis complex_inner_1_left norm_eq_sqrt_cinner norm_one one_cinner_one)
qed


text \<open>This is the canonical isomorphism between any two one dimensional spaces. Specifically,
  if 1 denotes the element of the canonical basis (which is specified by type class \<^class>\<open>basis_enum\<close>,
  then \<^term>\<open>one_dim_iso\<close> is the unique isomorphism that maps 1 to 1.\<close>
definition one_dim_iso :: "'a::one_dim \<Rightarrow> 'b::one_dim"
  where "one_dim_iso a = of_complex (\<langle>1, a\<rangle>)"

lemma one_dim_iso_idem[simp]: "one_dim_iso (one_dim_iso x) = one_dim_iso x"
  by (simp add: one_dim_iso_def)

lemma one_dim_iso_id[simp]: "one_dim_iso = id"
  unfolding one_dim_iso_def
  by (auto simp add: of_complex_def)

lemma one_dim_iso_adjoint[simp]: \<open>cadjoint one_dim_iso = one_dim_iso\<close>
  apply (rule cadjoint_eqI)
  by (simp add: one_dim_iso_def of_complex_def)

lemma one_dim_iso_is_of_complex[simp]: "one_dim_iso = of_complex"
  unfolding one_dim_iso_def by auto

lemma of_complex_one_dim_iso[simp]: "of_complex (one_dim_iso \<psi>) = one_dim_iso \<psi>"
  by (metis one_dim_iso_is_of_complex one_dim_iso_idem)

lemma one_dim_iso_of_complex[simp]: "one_dim_iso (of_complex c) = of_complex c"
  by (metis one_dim_iso_is_of_complex one_dim_iso_idem)

lemma one_dim_iso_add[simp]:
  \<open>one_dim_iso (a + b) = one_dim_iso a + one_dim_iso b\<close>
  by (simp add: cinner_simps(2) one_dim_iso_def)

lemma one_dim_iso_minus[simp]:
  \<open>one_dim_iso (a - b) = one_dim_iso a - one_dim_iso b\<close>
  by (simp add: cinner_simps(3) one_dim_iso_def)

lemma one_dim_iso_scaleC[simp]: "one_dim_iso (c *\<^sub>C \<psi>) = c *\<^sub>C one_dim_iso \<psi>"
  by (metis cinner_scaleC_right of_complex_mult one_dim_iso_def scaleC_conv_of_complex)

lemma clinear_one_dim_iso[simp]: "clinear one_dim_iso"
  by (rule clinearI, auto)

lemma bounded_clinear_one_dim_iso[simp]: "bounded_clinear one_dim_iso"
proof (rule bounded_clinear_intro [where K = 1] , auto)
  fix x :: \<open>'a::one_dim\<close>
  show "norm (one_dim_iso x) \<le> norm x"
    by (metis (full_types) norm_of_complex of_complex_def one_cinner_a_scaleC_one one_dim_iso_def 
        order_refl)
qed

lemma one_dim_iso_of_one[simp]: "one_dim_iso 1 = 1"
  by (simp add: one_dim_iso_def)

lemma onorm_one_dim_iso[simp]: "onorm one_dim_iso = 1"
proof (rule onormI [where b = 1 and x = 1])
  fix x :: \<open>'a::one_dim\<close>
  have "norm (one_dim_iso x ::'b) \<le> norm x"
    by (metis eq_iff norm_of_complex of_complex_def one_cinner_a_scaleC_one one_dim_iso_def)
  thus "norm (one_dim_iso (x::'a)::'b) \<le> 1 * norm x"
    by auto
  show "(1::'a) \<noteq> 0"
    by simp
  show "norm (one_dim_iso (1::'a)::'b) = 1 * norm (1::'a)"
    by auto
qed

lemma one_dim_iso_times[simp]: "one_dim_iso (\<psi> * \<phi>) = one_dim_iso \<psi> * one_dim_iso \<phi>"
  by (metis mult.left_neutral mult_scaleC_left of_complex_def one_cinner_a_scaleC_one one_dim_iso_def one_dim_iso_scaleC)

lemma one_dim_iso_of_zero[simp]: "one_dim_iso 0 = 0"
  by (simp add: complex_vector.linear_0)

lemma one_dim_iso_of_zero': "one_dim_iso x = 0 \<Longrightarrow> x = 0"
  by (metis of_complex_def of_complex_eq_0_iff one_cinner_a_scaleC_one one_dim_iso_def)

lemma one_dim_scaleC_1[simp]: "one_dim_iso x *\<^sub>C 1 = x"
  by (simp add: one_dim_iso_def)

lemma one_dim_clinear_eqI: 
  assumes "(x::'a::one_dim) \<noteq> 0" and "clinear f" and "clinear g" and "f x = g x"
  shows "f = g"
proof (rule ext)
  fix y :: 'a
  from \<open>f x = g x\<close>
  have \<open>one_dim_iso x *\<^sub>C f 1 = one_dim_iso x *\<^sub>C g 1\<close>
    by (metis assms(2) assms(3) complex_vector.linear_scale one_dim_scaleC_1)
  hence "f 1 = g 1"
    using assms(1) one_dim_iso_of_zero' by auto
  then show "f y = g y"
    by (metis assms(2) assms(3) complex_vector.linear_scale one_dim_scaleC_1)
qed

lemma one_dim_norm: "norm x = cmod (one_dim_iso x)"
proof (subst one_dim_scaleC_1 [symmetric])
  show "norm (one_dim_iso x *\<^sub>C (1::'a)) = cmod (one_dim_iso x)"
    by (metis norm_of_complex of_complex_def)    
qed

lemma one_dim_onorm:
  fixes f :: "'a::one_dim \<Rightarrow> 'b::complex_normed_vector"
  assumes "clinear f"
  shows "onorm f = norm (f 1)"
proof (rule onormI[where x=1])
  fix x :: 'a
  have "norm x * norm (f 1) \<le> norm (f 1) * norm x"
    by simp    
  hence "norm (f (one_dim_iso x *\<^sub>C 1)) \<le> norm (f 1) * norm x"
    by (metis (mono_tags, lifting) assms complex_vector.linear_scale norm_scaleC one_dim_norm)
  thus "norm (f x) \<le> norm (f 1) * norm x"
    by (subst one_dim_scaleC_1 [symmetric]) 
qed auto

lemma one_dim_onorm':
  fixes f :: "'a::one_dim \<Rightarrow> 'b::one_dim"
  assumes "clinear f"
  shows "onorm f = cmod (one_dim_iso (f 1))"
  using assms one_dim_norm one_dim_onorm by fastforce

instance one_dim \<subseteq> zero_neq_one ..

lemma one_dim_iso_inj: "one_dim_iso x = one_dim_iso y \<Longrightarrow> x = y"
  by (metis one_dim_iso_idem one_dim_scaleC_1)

instance one_dim \<subseteq> comm_ring
proof intro_classes
  fix x y z :: 'a
  show "x * y = y * x"
    by (metis one_dim_apply_is_times_def ordered_field_class.sign_simps(5))
  show "(x + y) * z = x * z + y * z"
    by (simp add: ring_class.ring_distribs(2))
qed

instance one_dim \<subseteq> field
proof intro_classes
  fix x y z :: \<open>'a::one_dim\<close>
  show "1 * x = x"
    by simp

  have "(inverse \<langle>1, x\<rangle> * \<langle>1, x\<rangle>) *\<^sub>C (1::'a) = 1" if "x \<noteq> 0"
    by (metis left_inverse of_complex_def one_cinner_a_scaleC_one one_dim_iso_of_zero 
        one_dim_iso_is_of_complex one_dim_iso_of_one that)
  hence "inverse (\<langle>1, x\<rangle> *\<^sub>C 1) * \<langle>1, x\<rangle> *\<^sub>C 1 = (1::'a)" if "x \<noteq> 0"
    by (metis one_dim_inverse one_dim_prod_scale1 that)    
  hence "inverse (\<langle>1, x\<rangle> *\<^sub>C 1) * x = 1" if "x \<noteq> 0"
    using one_cinner_a_scaleC_one[of x, symmetric] that by auto
  thus "inverse x * x = 1" if "x \<noteq> 0"
    by (simp add: that)    
  show "x / y = x * inverse y"
    by (simp add: one_dim_class.divide_inverse)
  show "inverse (0::'a) = 0"
    by (subst complex_vector.scale_zero_left[symmetric], subst one_dim_inverse, simp)
qed


instance one_dim \<subseteq> complex_normed_field
proof intro_classes
  fix x y :: 'a
  show "norm (x * y) = norm x * norm y"
    by (metis norm_mult one_dim_iso_times one_dim_norm)
qed

instance one_dim \<subseteq> chilbert_space..

end
