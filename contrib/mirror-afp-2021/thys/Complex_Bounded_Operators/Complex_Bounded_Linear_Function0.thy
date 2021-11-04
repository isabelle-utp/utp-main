(*  Title:      HOL/Analysis/Bounded_Linear_Function.thy
    Author:     Fabian Immler, TU München
*)

section \<open>\<open>Complex_Bounded_Linear_Function0\<close> -- Bounded Linear Function\<close>

theory Complex_Bounded_Linear_Function0
  imports
    "HOL-Analysis.Bounded_Linear_Function"
    Complex_Inner_Product
    Complex_Euclidean_Space0
begin

unbundle cinner_syntax

lemma conorm_componentwise:
  assumes "bounded_clinear f"
  shows "onorm f \<le> (\<Sum>i\<in>CBasis. norm (f i))"
proof -
  {
    fix i::'a
    assume "i \<in> CBasis"
    hence "onorm (\<lambda>x. (i \<bullet>\<^sub>C x) *\<^sub>C f i) \<le> onorm (\<lambda>x. (i \<bullet>\<^sub>C x)) * norm (f i)"
      by (auto intro!: onorm_scaleC_left_lemma bounded_clinear_cinner_right)
    also have "\<dots> \<le>  norm i * norm (f i)"
      apply (rule mult_right_mono)
       apply (simp add: complex_inner_class.Cauchy_Schwarz_ineq2 onorm_bound)
      by simp
    finally have "onorm (\<lambda>x. (i \<bullet>\<^sub>C x) *\<^sub>C f i) \<le> norm (f i)" using \<open>i \<in> CBasis\<close>
      by simp
  } hence "onorm (\<lambda>x. \<Sum>i\<in>CBasis. (i \<bullet>\<^sub>C x) *\<^sub>C f i) \<le> (\<Sum>i\<in>CBasis. norm (f i))"
    by (auto intro!: order_trans[OF onorm_sum_le] bounded_clinear_scaleC_const
        sum_mono bounded_clinear_cinner_right bounded_clinear.bounded_linear)
  also have "(\<lambda>x. \<Sum>i\<in>CBasis. (i \<bullet>\<^sub>C x) *\<^sub>C f i) = (\<lambda>x. f (\<Sum>i\<in>CBasis. (i \<bullet>\<^sub>C x) *\<^sub>C i))"
    by (simp add: clinear.scaleC linear_sum bounded_clinear.clinear clinear.linear assms)
  also have "\<dots> = f"
    by (simp add: ceuclidean_representation)
  finally show ?thesis .
qed

lemmas conorm_componentwise_le = order_trans[OF conorm_componentwise]

subsection\<^marker>\<open>tag unimportant\<close> \<open>Intro rules for \<^term>\<open>bounded_linear\<close>\<close>

(* We share the same attribute [bounded_linear_intros] with Bounded_Linear_Function *)
(* named_theorems bounded_linear_intros *)

lemma onorm_cinner_left:
  assumes "bounded_linear r"
  shows "onorm (\<lambda>x. r x \<bullet>\<^sub>C f) \<le> onorm r * norm f"
proof (rule onorm_bound)
  fix x
  have "norm (r x \<bullet>\<^sub>C f) \<le> norm (r x) * norm f"
    by (simp add: Cauchy_Schwarz_ineq2)
  also have "\<dots> \<le> onorm r * norm x * norm f"
    by (simp add: assms mult.commute mult_left_mono onorm)
  finally show "norm (r x \<bullet>\<^sub>C f) \<le> onorm r * norm f * norm x"
    by (simp add: ac_simps)
qed (intro mult_nonneg_nonneg norm_ge_zero onorm_pos_le assms)

lemma onorm_cinner_right:
  assumes "bounded_linear r"
  shows "onorm (\<lambda>x. f \<bullet>\<^sub>C r x) \<le> norm f * onorm r"
proof (rule onorm_bound)
  fix x
  have "norm (f \<bullet>\<^sub>C r x) \<le> norm f * norm (r x)"
    by (simp add: Cauchy_Schwarz_ineq2)
  also have "\<dots> \<le> onorm r * norm x * norm f"
    by (simp add: assms mult.commute mult_left_mono onorm)
  finally show "norm (f \<bullet>\<^sub>C r x) \<le> norm f * onorm r * norm x"
    by (simp add: ac_simps)
qed (intro mult_nonneg_nonneg norm_ge_zero onorm_pos_le assms)

lemmas [bounded_linear_intros] =
  bounded_clinear_zero
  bounded_clinear_add
  bounded_clinear_const_mult
  bounded_clinear_mult_const
  bounded_clinear_scaleC_const
  bounded_clinear_const_scaleC
  bounded_clinear_const_scaleR
  bounded_clinear_ident
  bounded_clinear_sum
  (* bounded_clinear_Pair *) (* The Product_Vector theory does not instantiate Pair for complex vector spaces *)
  bounded_clinear_sub
  (* bounded_clinear_fst_comp *) (* The Product_Vector theory does not instantiate Pair for complex vector spaces *)
  (* bounded_clinear_snd_comp *) (* The Product_Vector theory does not instantiate Pair for complex vector spaces *)
  bounded_antilinear_cinner_left_comp
  bounded_clinear_cinner_right_comp


subsection\<^marker>\<open>tag unimportant\<close> \<open>declaration of derivative/continuous/tendsto introduction rules for bounded linear functions\<close>

attribute_setup bounded_clinear =
  \<open>let val bounded_linear = Attrib.attribute \<^context> (the_single @{attributes [bounded_linear]}) in
   Scan.succeed (Thm.declaration_attribute (fn thm =>
    Thm.attribute_declaration bounded_linear (thm RS @{thm bounded_clinear.bounded_linear}) o
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (* Not present in Bounded_Linear_Function *)
        (@{thm bounded_clinear_compose}, \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_clinear_o_bounded_antilinear[unfolded o_def]}, \<^named_theorems>\<open>bounded_linear_intros\<close>)
      ]))
  end\<close>

(* Analogue to [bounded_clinear], not present in Bounded_Linear_Function *)
attribute_setup bounded_antilinear =
  \<open>let val bounded_linear = Attrib.attribute \<^context> (the_single @{attributes [bounded_linear]}) in
   Scan.succeed (Thm.declaration_attribute (fn thm =>
    Thm.attribute_declaration bounded_linear (thm RS @{thm bounded_antilinear.bounded_linear}) o
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (* Not present in Bounded_Linear_Function *)
        (@{thm bounded_antilinear_o_bounded_clinear[unfolded o_def]}, \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_antilinear_o_bounded_antilinear[unfolded o_def]}, \<^named_theorems>\<open>bounded_linear_intros\<close>)
      ]))
  end\<close>

attribute_setup bounded_cbilinear =
  \<open>let val bounded_bilinear = Attrib.attribute \<^context> (the_single @{attributes [bounded_bilinear]}) in
   Scan.succeed (Thm.declaration_attribute (fn thm =>
    Thm.attribute_declaration bounded_bilinear (thm RS @{thm bounded_cbilinear.bounded_bilinear}) o
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (@{thm bounded_clinear_compose[OF bounded_cbilinear.bounded_clinear_left]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_clinear_compose[OF bounded_cbilinear.bounded_clinear_right]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_clinear_o_bounded_antilinear[unfolded o_def, OF bounded_cbilinear.bounded_clinear_left]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_clinear_o_bounded_antilinear[unfolded o_def, OF bounded_cbilinear.bounded_clinear_right]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>)
      ]))
  end\<close>

(* Analogue to [bounded_sesquilinear], not present in Bounded_Linear_Function *)
attribute_setup bounded_sesquilinear =
  \<open>let val bounded_bilinear = Attrib.attribute \<^context> (the_single @{attributes [bounded_bilinear]}) in
   Scan.succeed (Thm.declaration_attribute (fn thm =>
    Thm.attribute_declaration bounded_bilinear (thm RS @{thm bounded_sesquilinear.bounded_bilinear}) o
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (@{thm bounded_antilinear_o_bounded_clinear[unfolded o_def, OF bounded_sesquilinear.bounded_antilinear_left]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_clinear_compose[OF bounded_sesquilinear.bounded_clinear_right]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_antilinear_o_bounded_antilinear[unfolded o_def, OF bounded_sesquilinear.bounded_antilinear_left]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>),
        (@{thm bounded_clinear_o_bounded_antilinear[unfolded o_def, OF bounded_sesquilinear.bounded_clinear_right]},
          \<^named_theorems>\<open>bounded_linear_intros\<close>)
      ]))
  end\<close>


subsection \<open>Type of complex bounded linear functions\<close>

typedef\<^marker>\<open>tag important\<close> (overloaded) ('a, 'b) cblinfun ("(_ \<Rightarrow>\<^sub>C\<^sub>L /_)" [22, 21] 21) =
  "{f::'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector. bounded_clinear f}"
  morphisms cblinfun_apply CBlinfun
  by (blast intro: bounded_linear_intros)

declare [[coercion
      "cblinfun_apply :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]

lemma bounded_clinear_cblinfun_apply[bounded_linear_intros]:
  "bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. cblinfun_apply f (g x))"
  by (metis cblinfun_apply mem_Collect_eq bounded_clinear_compose)

setup_lifting type_definition_cblinfun

lemma cblinfun_eqI: "(\<And>i. cblinfun_apply x i = cblinfun_apply y i) \<Longrightarrow> x = y"
  by transfer auto

lemma bounded_clinear_CBlinfun_apply: "bounded_clinear f \<Longrightarrow> cblinfun_apply (CBlinfun f) = f"
  by (auto simp: CBlinfun_inverse)


subsection \<open>Type class instantiations\<close>

instantiation cblinfun :: (complex_normed_vector, complex_normed_vector) complex_normed_vector
begin

lift_definition\<^marker>\<open>tag important\<close> norm_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> real" is onorm .

lift_definition minus_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  is "\<lambda>f g x. f x - g x"
  by (rule bounded_clinear_sub)

definition dist_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> real"
  where "dist_cblinfun a b = norm (a - b)"

definition [code del]:
  "(uniformity :: (('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b)) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_cblinfun :: "('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set \<Rightarrow> bool"
  where [code del]: "open_cblinfun S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lift_definition uminus_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is "\<lambda>f x. - f x"
  by (rule bounded_clinear_minus)

lift_definition\<^marker>\<open>tag important\<close> zero_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is "\<lambda>x. 0"
  by (rule bounded_clinear_zero)

lift_definition\<^marker>\<open>tag important\<close> plus_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  is "\<lambda>f g x. f x + g x"
  by (metis bounded_clinear_add)

lift_definition\<^marker>\<open>tag important\<close> scaleC_cblinfun::"complex \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is "\<lambda>r f x. r *\<^sub>C f x"
  by (metis bounded_clinear_compose bounded_clinear_scaleC_right)
lift_definition\<^marker>\<open>tag important\<close> scaleR_cblinfun::"real \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is "\<lambda>r f x. r *\<^sub>R f x"
  by (rule bounded_clinear_const_scaleR)

definition sgn_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  where "sgn_cblinfun x = scaleC (inverse (norm x)) x"

instance
proof
  fix a b c :: "'a \<Rightarrow>\<^sub>C\<^sub>L'b" and r q :: real and s t :: complex

  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  show \<open>0 + a = a\<close>
    apply transfer by auto
  show \<open>a + b = b + a\<close>
    apply transfer by auto
  show \<open>- a + a = 0\<close>
    apply transfer by auto
  show \<open>a - b = a + - b\<close>
    apply transfer by auto
  show scaleR_scaleC: \<open>((*\<^sub>R) r::('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> for r
    apply (rule ext, transfer fixing: r) by (simp add: scaleR_scaleC)
  show \<open>s *\<^sub>C (b + c) = s *\<^sub>C b + s *\<^sub>C c\<close>
    apply transfer by (simp add: scaleC_add_right) 
  show \<open>(s + t) *\<^sub>C a = s *\<^sub>C a + t *\<^sub>C a\<close>
    apply transfer by (simp add: scaleC_left.add) 
  show \<open>s *\<^sub>C t *\<^sub>C a = (s * t) *\<^sub>C a\<close>
    apply transfer by auto
  show \<open>1 *\<^sub>C a = a\<close>
    apply transfer by auto
  show \<open>dist a b = norm (a - b)\<close>
    unfolding dist_cblinfun_def by simp
  show \<open>sgn a = (inverse (norm a)) *\<^sub>R a\<close>
    unfolding sgn_cblinfun_def unfolding scaleR_scaleC by auto
  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a \<Rightarrow>\<^sub>C\<^sub>L 'b)) y < e})\<close>
    by (simp add: uniformity_cblinfun_def)
  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a \<Rightarrow>\<^sub>C\<^sub>L 'b)) = x \<longrightarrow> y \<in> U)\<close> for U
    by (simp add: open_cblinfun_def)
  show \<open>(norm a = 0) = (a = 0)\<close>
    apply transfer using bounded_clinear.bounded_linear onorm_eq_0 by blast
  show \<open>norm (a + b) \<le> norm a + norm b\<close>
    apply transfer by (simp add: bounded_clinear.bounded_linear onorm_triangle)
  show \<open>norm (s *\<^sub>C a) = cmod s * norm a\<close>
    apply transfer using onorm_scalarC by blast
  show \<open>norm (r *\<^sub>R a) = \<bar>r\<bar> * norm a\<close>
    apply transfer using bounded_clinear.bounded_linear onorm_scaleR by blast
  show \<open>r *\<^sub>R (a + b) = r *\<^sub>R a +  r *\<^sub>R b\<close>
    apply transfer by (simp add: scaleR_add_right) 
  show \<open>(r + q) *\<^sub>R a = r *\<^sub>R a +  q *\<^sub>R a\<close>
    apply transfer by (simp add: scaleR_add_left)
  show \<open>r *\<^sub>R q *\<^sub>R a = (r * q) *\<^sub>R a\<close>
    apply transfer by auto
  show \<open>1 *\<^sub>R a = a\<close>
    apply transfer by auto
qed

end

declare uniformity_Abort[where 'a="('a :: complex_normed_vector) \<Rightarrow>\<^sub>C\<^sub>L ('b :: complex_normed_vector)", code]

lemma norm_cblinfun_eqI:
  assumes "n \<le> norm (cblinfun_apply f x) / norm x"
  assumes "\<And>x. norm (cblinfun_apply f x) \<le> n * norm x"
  assumes "0 \<le> n"
  shows "norm f = n"
  by (auto simp: norm_cblinfun_def
      intro!: antisym onorm_bound assms order_trans[OF _ le_onorm] bounded_clinear.bounded_linear
      bounded_linear_intros)

lemma norm_cblinfun: "norm (cblinfun_apply f x) \<le> norm f * norm x"
  apply transfer by (simp add: bounded_clinear.bounded_linear onorm)

lemma norm_cblinfun_bound: "0 \<le> b \<Longrightarrow> (\<And>x. norm (cblinfun_apply f x) \<le> b * norm x) \<Longrightarrow> norm f \<le> b"
  by transfer (rule onorm_bound)

lemma bounded_cbilinear_cblinfun_apply[bounded_cbilinear]: "bounded_cbilinear cblinfun_apply"
proof
  fix f g::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b" and a b::'a and r::complex
  show "(f + g) a = f a + g a" "(r *\<^sub>C f) a = r *\<^sub>C f a"
    by (transfer, simp)+
  interpret bounded_clinear f for f::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    by (auto intro!: bounded_linear_intros)
  show "f (a + b) = f a + f b" "f (r *\<^sub>C a) = r *\<^sub>C f a"
    by (simp_all add: add scaleC)
  show "\<exists>K. \<forall>a b. norm (cblinfun_apply a b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x=1] norm_cblinfun)
qed

interpretation cblinfun: bounded_cbilinear cblinfun_apply
  by (rule bounded_cbilinear_cblinfun_apply)

lemmas bounded_clinear_apply_cblinfun[intro, simp] = cblinfun.bounded_clinear_left

declare cblinfun.zero_left [simp] cblinfun.zero_right [simp]


context bounded_cbilinear
begin

named_theorems cbilinear_simps

lemmas [cbilinear_simps] =
  add_left
  add_right
  diff_left
  diff_right
  minus_left
  minus_right
  scaleC_left
  scaleC_right
  zero_left
  zero_right
  sum_left
  sum_right

end


instance cblinfun :: (complex_normed_vector, cbanach) cbanach
(* The proof is almost the same as for \<open>instance blinfun :: (real_normed_vector, banach) banach\<close> *)
proof
  fix X::"nat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  assume "Cauchy X"
  {
    fix x::'a
    {
      fix x::'a
      assume "norm x \<le> 1"
      have "Cauchy (\<lambda>n. X n x)"
      proof (rule CauchyI)
        fix e::real
        assume "0 < e"
        from CauchyD[OF \<open>Cauchy X\<close> \<open>0 < e\<close>] obtain M
          where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> norm (X m - X n) < e"
          by auto
        show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m x - X n x) < e"
        proof (safe intro!: exI[where x=M])
          fix m n
          assume le: "M \<le> m" "M \<le> n"
          have "norm (X m x - X n x) = norm ((X m - X n) x)"
            by (simp add: cblinfun.cbilinear_simps)
          also have "\<dots> \<le> norm (X m - X n) * norm x"
            by (rule norm_cblinfun)
          also have "\<dots> \<le> norm (X m - X n) * 1"
            using \<open>norm x \<le> 1\<close> norm_ge_zero by (rule mult_left_mono)
          also have "\<dots> = norm (X m - X n)" by simp
          also have "\<dots> < e" using le by fact
          finally show "norm (X m x - X n x) < e" .
        qed
      qed
      hence "convergent (\<lambda>n. X n x)"
        by (metis Cauchy_convergent_iff)
    } note convergent_norm1 = this
    define y where "y = x /\<^sub>R norm x"
    have y: "norm y \<le> 1" and xy: "x = norm x *\<^sub>R y"
      by (simp_all add: y_def inverse_eq_divide)
    have "convergent (\<lambda>n. norm x *\<^sub>R X n y)"
      by (intro bounded_bilinear.convergent[OF bounded_bilinear_scaleR] convergent_const
          convergent_norm1 y)
    also have "(\<lambda>n. norm x *\<^sub>R X n y) = (\<lambda>n. X n x)"
      by (metis cblinfun.scaleC_right scaleR_scaleC xy)
    finally have "convergent (\<lambda>n. X n x)" .
  }
  then obtain v where v: "\<And>x. (\<lambda>n. X n x) \<longlonglongrightarrow> v x"
    unfolding convergent_def
    by metis

  have "Cauchy (\<lambda>n. norm (X n))"
  proof (rule CauchyI)
    fix e::real
    assume "e > 0"
    from CauchyD[OF \<open>Cauchy X\<close> \<open>0 < e\<close>] obtain M
      where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> norm (X m - X n) < e"
      by auto
    show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (norm (X m) - norm (X n)) < e"
    proof (safe intro!: exI[where x=M])
      fix m n assume mn: "m \<ge> M" "n \<ge> M"
      have "norm (norm (X m) - norm (X n)) \<le> norm (X m - X n)"
        by (metis norm_triangle_ineq3 real_norm_def)
      also have "\<dots> < e" using mn by fact
      finally show "norm (norm (X m) - norm (X n)) < e" .
    qed
  qed
  then obtain K where K: "(\<lambda>n. norm (X n)) \<longlonglongrightarrow> K"
    unfolding Cauchy_convergent_iff convergent_def
    by metis

  have "bounded_clinear v"
  proof
    fix x y and r::complex
    from tendsto_add[OF v[of x] v [of y]] v[of "x + y", unfolded cblinfun.cbilinear_simps]
      tendsto_scaleC[OF tendsto_const[of r] v[of x]] v[of "r *\<^sub>C x", unfolded cblinfun.cbilinear_simps]
    show "v (x + y) = v x + v y" "v (r *\<^sub>C x) = r *\<^sub>C v x"
      by (metis (poly_guards_query) LIMSEQ_unique)+
    show "\<exists>K. \<forall>x. norm (v x) \<le> norm x * K"
    proof (safe intro!: exI[where x=K])
      fix x
      have "norm (v x) \<le> K * norm x"
        apply (rule tendsto_le[OF _ tendsto_mult[OF K tendsto_const] tendsto_norm[OF v]])
        by (auto simp: norm_cblinfun)
      thus "norm (v x) \<le> norm x * K"
        by (simp add: ac_simps)
    qed
  qed
  hence Bv: "\<And>x. (\<lambda>n. X n x) \<longlonglongrightarrow> CBlinfun v x"
    by (auto simp: bounded_clinear_CBlinfun_apply v)

  have "X \<longlonglongrightarrow> CBlinfun v"
  proof (rule LIMSEQ_I)
    fix r::real assume "r > 0"
    define r' where "r' = r / 2"
    have "0 < r'" "r' < r" using \<open>r > 0\<close> by (simp_all add: r'_def)
    from CauchyD[OF \<open>Cauchy X\<close> \<open>r' > 0\<close>]
    obtain M where M: "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> norm (X m - X n) < r'"
      by metis
    show "\<exists>no. \<forall>n\<ge>no. norm (X n - CBlinfun v) < r"
    proof (safe intro!: exI[where x=M])
      fix n assume n: "M \<le> n"
      have "norm (X n - CBlinfun v) \<le> r'"
      proof (rule norm_cblinfun_bound)
        fix x
        have "eventually (\<lambda>m. m \<ge> M) sequentially"
          by (metis eventually_ge_at_top)
        hence ev_le: "eventually (\<lambda>m. norm (X n x - X m x) \<le> r' * norm x) sequentially"
        proof eventually_elim
          case (elim m)
          have "norm (X n x - X m x) = norm ((X n - X m) x)"
            by (simp add: cblinfun.cbilinear_simps)
          also have "\<dots> \<le> norm ((X n - X m)) * norm x"
            by (rule norm_cblinfun)
          also have "\<dots> \<le> r' * norm x"
            using M[OF n elim] by (simp add: mult_right_mono)
          finally show ?case .
        qed
        have tendsto_v: "(\<lambda>m. norm (X n x - X m x)) \<longlonglongrightarrow> norm (X n x - CBlinfun v x)"
          by (auto intro!: tendsto_intros Bv)
        show "norm ((X n - CBlinfun v) x) \<le> r' * norm x"
          by (auto intro!: tendsto_upperbound tendsto_v ev_le simp: cblinfun.cbilinear_simps)
      qed (simp add: \<open>0 < r'\<close> less_imp_le)
      thus "norm (X n - CBlinfun v) < r"
        by (metis \<open>r' < r\<close> le_less_trans)
    qed
  qed
  thus "convergent X"
    by (rule convergentI)
qed

subsection\<^marker>\<open>tag unimportant\<close> \<open>On Euclidean Space\<close>

(* No different in complex case *)
(* lemma Zfun_sum:
  assumes "finite s"
  assumes f: "\<And>i. i \<in> s \<Longrightarrow> Zfun (f i) F"
  shows "Zfun (\<lambda>x. sum (\<lambda>i. f i x) s) F" *)

lemma norm_cblinfun_ceuclidean_le:
  fixes a::"'a::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
  shows "norm a \<le> sum (\<lambda>x. norm (a x)) CBasis"
  apply (rule norm_cblinfun_bound)
   apply (simp add: sum_nonneg)
  apply (subst ceuclidean_representation[symmetric, where 'a='a])
  apply (simp only: cblinfun.cbilinear_simps sum_distrib_right)
  apply (rule order.trans[OF norm_sum sum_mono])
  apply (simp add: abs_mult mult_right_mono ac_simps CBasis_le_norm)
  by (metis complex_inner_class.Cauchy_Schwarz_ineq2 mult.commute mult.left_neutral mult_right_mono norm_CBasis norm_ge_zero)

lemma ctendsto_componentwise1:
  fixes a::"'a::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  assumes "(\<And>j. j \<in> CBasis \<Longrightarrow> ((\<lambda>n. b n j) \<longlongrightarrow> a j) F)"
  shows "(b \<longlongrightarrow> a) F"
proof -
  have "\<And>j. j \<in> CBasis \<Longrightarrow> Zfun (\<lambda>x. norm (b x j - a j)) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  hence "Zfun (\<lambda>x. \<Sum>j\<in>CBasis. norm (b x j - a j)) F"
    by (auto intro!: Zfun_sum)
  thus ?thesis
    unfolding tendsto_Zfun_iff
    by (rule Zfun_le)
      (auto intro!: order_trans[OF norm_cblinfun_ceuclidean_le] simp: cblinfun.cbilinear_simps)
qed

lift_definition
  cblinfun_of_matrix::"('b::ceuclidean_space \<Rightarrow> 'a::ceuclidean_space \<Rightarrow> complex) \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  is "\<lambda>a x. \<Sum>i\<in>CBasis. \<Sum>j\<in>CBasis. ((j \<bullet>\<^sub>C x) * a i j) *\<^sub>C i"
  by (intro bounded_linear_intros)

lemma cblinfun_of_matrix_works:
  fixes f::"'a::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'b::ceuclidean_space"
  shows "cblinfun_of_matrix (\<lambda>i j. i \<bullet>\<^sub>C (f j)) = f"
proof (transfer, rule,  rule ceuclidean_eqI)
  fix f::"'a \<Rightarrow> 'b" and x::'a and b::'b assume "bounded_clinear f" and b: "b \<in> CBasis"
  then interpret bounded_clinear f by simp
  have "(\<Sum>j\<in>CBasis. \<Sum>i\<in>CBasis. (i \<bullet>\<^sub>C x * (j \<bullet>\<^sub>C f i)) *\<^sub>C j) \<bullet>\<^sub>C b
    = (\<Sum>j\<in>CBasis. if j = b then (\<Sum>i\<in>CBasis. (x \<bullet>\<^sub>C i * (f i \<bullet>\<^sub>C j))) else 0)"
    using b
    apply (simp add: cinner_sum_left cinner_CBasis if_distrib cong: if_cong) 
    by (simp add: sum.swap)
  also have "\<dots> = (\<Sum>i\<in>CBasis. ((x \<bullet>\<^sub>C i) * (f i \<bullet>\<^sub>C b)))"
    using b by (simp)
  also have "\<dots> = f x \<bullet>\<^sub>C b"
  proof -
    have \<open>(\<Sum>i\<in>CBasis. (x \<bullet>\<^sub>C i) * (f i \<bullet>\<^sub>C b)) = (\<Sum>i\<in>CBasis. (i \<bullet>\<^sub>C x) *\<^sub>C f i) \<bullet>\<^sub>C b\<close>
      by (auto simp: cinner_sum_left)
    also have \<open>\<dots> = f x \<bullet>\<^sub>C b\<close>
      by (simp add: ceuclidean_representation sum[symmetric] scale[symmetric])
    finally show ?thesis by -
  qed
  finally show "(\<Sum>j\<in>CBasis. \<Sum>i\<in>CBasis. (i \<bullet>\<^sub>C x * (j \<bullet>\<^sub>C f i)) *\<^sub>C j) \<bullet>\<^sub>C b = f x \<bullet>\<^sub>C b" .
qed


lemma cblinfun_of_matrix_apply:
  "cblinfun_of_matrix a x = (\<Sum>i\<in>CBasis. \<Sum>j\<in>CBasis. ((j \<bullet>\<^sub>C x) * a i j) *\<^sub>C i)"
  apply transfer by simp

lemma cblinfun_of_matrix_minus: "cblinfun_of_matrix x - cblinfun_of_matrix y = cblinfun_of_matrix (x - y)"
  by transfer (auto simp: algebra_simps sum_subtractf)

lemma norm_cblinfun_of_matrix:
  "norm (cblinfun_of_matrix a) \<le> (\<Sum>i\<in>CBasis. \<Sum>j\<in>CBasis. cmod (a i j))"
  apply (rule norm_cblinfun_bound)
   apply (simp add: sum_nonneg)
  apply (simp only: cblinfun_of_matrix_apply sum_distrib_right)
  apply (rule order_trans[OF norm_sum sum_mono])
  apply (rule order_trans[OF norm_sum sum_mono])
  apply (simp add: abs_mult mult_right_mono ac_simps Basis_le_norm)
  by (metis complex_inner_class.Cauchy_Schwarz_ineq2 complex_scaleC_def mult.left_neutral mult_right_mono norm_CBasis norm_ge_zero norm_scaleC)

lemma tendsto_cblinfun_of_matrix:
  assumes "\<And>i j. i \<in> CBasis \<Longrightarrow> j \<in> CBasis \<Longrightarrow> ((\<lambda>n. b n i j) \<longlongrightarrow> a i j) F"
  shows "((\<lambda>n. cblinfun_of_matrix (b n)) \<longlongrightarrow> cblinfun_of_matrix a) F"
proof -
  have "\<And>i j. i \<in> CBasis \<Longrightarrow> j \<in> CBasis \<Longrightarrow> Zfun (\<lambda>x. norm (b x i j - a i j)) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  hence "Zfun (\<lambda>x. (\<Sum>i\<in>CBasis. \<Sum>j\<in>CBasis. cmod (b x i j - a i j))) F"
    by (auto intro!: Zfun_sum)
  thus ?thesis
    unfolding tendsto_Zfun_iff cblinfun_of_matrix_minus
    by (rule Zfun_le) (auto intro!: order_trans[OF norm_cblinfun_of_matrix])
qed


lemma ctendsto_componentwise:
  fixes a::"'a::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'b::ceuclidean_space"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows "(\<And>i j. i \<in> CBasis \<Longrightarrow> j \<in> CBasis \<Longrightarrow> ((\<lambda>n. b n j \<bullet>\<^sub>C i) \<longlongrightarrow> a j \<bullet>\<^sub>C i) F) \<Longrightarrow> (b \<longlongrightarrow> a) F"
  apply (subst cblinfun_of_matrix_works[of a, symmetric])
  apply (subst cblinfun_of_matrix_works[of "b x" for x, symmetric, abs_def])
  apply (rule tendsto_cblinfun_of_matrix)
  apply (subst (1) cinner_commute, subst (2) cinner_commute)
  by (metis lim_cnj)

lemma
  continuous_cblinfun_componentwiseI:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'c::ceuclidean_space"
  assumes "\<And>i j. i \<in> CBasis \<Longrightarrow> j \<in> CBasis \<Longrightarrow> continuous F (\<lambda>x. (f x) j \<bullet>\<^sub>C i)"
  shows "continuous F f"
  using assms by (auto simp: continuous_def intro!: ctendsto_componentwise)

lemma
  continuous_cblinfun_componentwiseI1:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
  assumes "\<And>i. i \<in> CBasis \<Longrightarrow> continuous F (\<lambda>x. f x i)"
  shows "continuous F f"
  using assms by (auto simp: continuous_def intro!: ctendsto_componentwise1)

lemma
  continuous_on_cblinfun_componentwise:
  fixes f:: "'d::t2_space \<Rightarrow> 'e::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'f::complex_normed_vector"
  assumes "\<And>i. i \<in> CBasis \<Longrightarrow> continuous_on s (\<lambda>x. f x i)"
  shows "continuous_on s f"
  using assms
  by (auto intro!: continuous_at_imp_continuous_on intro!: ctendsto_componentwise1
      simp: continuous_on_eq_continuous_within continuous_def)

lemma bounded_antilinear_cblinfun_matrix: "bounded_antilinear (\<lambda>x. (x::_\<Rightarrow>\<^sub>C\<^sub>L _) j \<bullet>\<^sub>C i)"
  by (auto intro!: bounded_linear_intros)

lemma continuous_cblinfun_matrix:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner"
  assumes "continuous F f"
  shows "continuous F (\<lambda>x. (f x) j \<bullet>\<^sub>C i)"
  by (rule bounded_antilinear.continuous[OF bounded_antilinear_cblinfun_matrix assms])

lemma continuous_on_cblinfun_matrix:
  fixes f::"'a::t2_space \<Rightarrow> 'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner"
  assumes "continuous_on S f"
  shows "continuous_on S (\<lambda>x. (f x) j \<bullet>\<^sub>C i)"
  using assms
  by (auto simp: continuous_on_eq_continuous_within continuous_cblinfun_matrix)

lemma continuous_on_cblinfun_of_matrix[continuous_intros]:
  assumes "\<And>i j. i \<in> CBasis \<Longrightarrow> j \<in> CBasis \<Longrightarrow> continuous_on S (\<lambda>s. g s i j)"
  shows "continuous_on S (\<lambda>s. cblinfun_of_matrix (g s))"
  using assms
  by (auto simp: continuous_on intro!: tendsto_cblinfun_of_matrix)

(* Not specific to complex/real *)
(* lemma mult_if_delta:
  "(if P then (1::'a::comm_semiring_1) else 0) * q = (if P then q else 0)" *)

(* Needs that ceuclidean_space is heine_borel. This is shown for euclidean_space in Toplogy_Euclidean_Space
   which has not been ported to complex *)
(* lemma compact_cblinfun_lemma:
  fixes f :: "nat \<Rightarrow> 'a::ceuclidean_space \<Rightarrow>\<^sub>C\<^sub>L 'b::ceuclidean_space"
  assumes "bounded (range f)"
  shows "\<forall>d\<subseteq>CBasis. \<exists>l::'a \<Rightarrow>\<^sub>C\<^sub>L 'b. \<exists> r::nat\<Rightarrow>nat.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) i) (l i) < e) sequentially)"
  apply (rule compact_lemma_general[where unproj = "\<lambda>e. cblinfun_of_matrix (\<lambda>i j. e j \<bullet>\<^sub>C i)"])
  by (auto intro!: euclidean_eqI[where 'a='b] bounded_linear_image assms
    simp: blinfun_of_matrix_works blinfun_of_matrix_apply inner_Basis mult_if_delta sum.delta'
      scaleR_sum_left[symmetric]) *)


lemma cblinfun_euclidean_eqI: "(\<And>i. i \<in> CBasis \<Longrightarrow> cblinfun_apply x i = cblinfun_apply y i) \<Longrightarrow> x = y"
  apply (auto intro!: cblinfun_eqI)
  apply (subst (2) ceuclidean_representation[symmetric, where 'a='a])
  apply (subst (1) ceuclidean_representation[symmetric, where 'a='a])
  by (simp add: cblinfun.cbilinear_simps)

lemma CBlinfun_eq_matrix: "bounded_clinear f \<Longrightarrow> CBlinfun f = cblinfun_of_matrix (\<lambda>i j. i \<bullet>\<^sub>C f j)"
  apply (intro cblinfun_euclidean_eqI)
  by (auto simp: cblinfun_of_matrix_apply bounded_clinear_CBlinfun_apply cinner_CBasis if_distrib
      if_distribR sum.delta' ceuclidean_representation
      cong: if_cong)

(* Conflicts with: cblinfun :: (complex_normed_vector, cbanach) complete_space *)
(* instance cblinfun :: (ceuclidean_space, ceuclidean_space) heine_borel *)


subsection\<^marker>\<open>tag unimportant\<close> \<open>concrete bounded linear functions\<close>

lemma transfer_bounded_cbilinear_bounded_clinearI:
  assumes "g = (\<lambda>i x. (cblinfun_apply (f i) x))"
  shows "bounded_cbilinear g = bounded_clinear f"
proof
  assume "bounded_cbilinear g"
  then interpret bounded_cbilinear f by (simp add: assms)
  show "bounded_clinear f"
  proof (unfold_locales, safe intro!: cblinfun_eqI)
    fix i
    show "f (x + y) i = (f x + f y) i" "f (r *\<^sub>C x) i = (r *\<^sub>C f x) i" for r x y
      by (auto intro!: cblinfun_eqI simp: cblinfun.cbilinear_simps)
    from _ nonneg_bounded show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (rule ex_reg) (auto intro!: onorm_bound simp: norm_cblinfun.rep_eq ac_simps)
  qed
qed (auto simp: assms intro!: cblinfun.comp)

lemma transfer_bounded_cbilinear_bounded_clinear[transfer_rule]:
  "(rel_fun (rel_fun (=) (pcr_cblinfun (=) (=))) (=)) bounded_cbilinear bounded_clinear"
  by (auto simp: pcr_cblinfun_def cr_cblinfun_def rel_fun_def OO_def
      intro!: transfer_bounded_cbilinear_bounded_clinearI)

(* Not present in Bounded_Linear_Function *)
lemma transfer_bounded_sesquilinear_bounded_antilinearI:
  assumes "g = (\<lambda>i x. (cblinfun_apply (f i) x))"
  shows "bounded_sesquilinear g = bounded_antilinear f"
proof
  assume "bounded_sesquilinear g"
  then interpret bounded_sesquilinear f by (simp add: assms)
  show "bounded_antilinear f"
  proof (unfold_locales, safe intro!: cblinfun_eqI)
    fix i
    show "f (x + y) i = (f x + f y) i" "f (r *\<^sub>C x) i = (cnj r *\<^sub>C f x) i" for r x y
      by (auto intro!: cblinfun_eqI simp: cblinfun.scaleC_left scaleC_left add_left cblinfun.add_left)
    from _ nonneg_bounded show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (rule ex_reg) (auto intro!: onorm_bound simp: norm_cblinfun.rep_eq ac_simps)
  qed
next
  assume "bounded_antilinear f"
  then obtain K where K: \<open>norm (f x) \<le> norm x * K\<close> for x
    using bounded_antilinear.bounded by blast
  have \<open>norm (cblinfun_apply (f a) b) \<le> norm (f a) * norm b\<close> for a b
    by (simp add: norm_cblinfun)
  also have \<open>\<dots> a b \<le> norm a * norm b * K\<close> for a b
    by (smt (verit, best) K mult.assoc mult.commute mult_mono' norm_ge_zero)
  finally have *: \<open>norm (cblinfun_apply (f a) b) \<le> norm a * norm b * K\<close> for a b
    by simp
  show "bounded_sesquilinear g"
    using \<open>bounded_antilinear f\<close>
    apply (auto intro!: bounded_sesquilinear.intro simp: assms cblinfun.add_left cblinfun.add_right 
        linear_simps bounded_antilinear.bounded_linear antilinear.scaleC bounded_antilinear.antilinear
        cblinfun.scaleC_left cblinfun.scaleC_right)
    using * by blast
qed

lemma transfer_bounded_sesquilinear_bounded_antilinear[transfer_rule]:
  "(rel_fun (rel_fun (=) (pcr_cblinfun (=) (=))) (=)) bounded_sesquilinear bounded_antilinear"
  by (auto simp: pcr_cblinfun_def cr_cblinfun_def rel_fun_def OO_def
      intro!: transfer_bounded_sesquilinear_bounded_antilinearI)

context bounded_cbilinear
begin

lift_definition prod_left::"'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'c" is "(\<lambda>b a. prod a b)"
  by (rule bounded_clinear_left)
declare prod_left.rep_eq[simp]

lemma bounded_clinear_prod_left[bounded_clinear]: "bounded_clinear prod_left"
  by transfer (rule flip)

lift_definition prod_right::"'a \<Rightarrow> 'b \<Rightarrow>\<^sub>C\<^sub>L 'c" is "(\<lambda>a b. prod a b)"
  by (rule bounded_clinear_right)
declare prod_right.rep_eq[simp]

lemma bounded_clinear_prod_right[bounded_clinear]: "bounded_clinear prod_right"
  by transfer (rule bounded_cbilinear_axioms)

end

lift_definition id_cblinfun::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a" is "\<lambda>x. x"
  by (rule bounded_clinear_ident)

lemmas cblinfun_id_cblinfun_apply[simp] = id_cblinfun.rep_eq

(* Strong than norm_blinfun_id because we replaced the perfect_space typeclass by not_singleton *)
lemma norm_cblinfun_id[simp]:
  "norm (id_cblinfun::'a::{complex_normed_vector, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'a) = 1"
  apply transfer
  apply (rule onorm_id[internalize_sort' 'a])
   apply standard[1]
  by simp

lemma norm_blinfun_id_le:
  "norm (id_cblinfun::'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a) \<le> 1"
  by transfer (auto simp: onorm_id_le)

(* Skipped because we do not have "prod :: (cbanach, cbanach) cbanach" (Product_Vector not ported to complex)*)
(* lift_definition fst_cblinfun::"('a::complex_normed_vector \<times> 'b::complex_normed_vector) \<Rightarrow>\<^sub>C\<^sub>L 'a" is fst *)

(* lemma cblinfun_apply_fst_cblinfun[simp]: "cblinfun_apply fst_cblinfun = fst" *)

(* lift_definition snd_cblinfun::"('a::complex_normed_vector \<times> 'b::complex_normed_vector) \<Rightarrow>\<^sub>C\<^sub>L 'b" is snd *)

(* lemma blinfun_apply_snd_blinfun[simp]: "blinfun_apply snd_blinfun = snd" *)

lift_definition cblinfun_compose::
  "'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector \<Rightarrow>
    'c::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow>
    'c \<Rightarrow>\<^sub>C\<^sub>L 'b" (infixl "o\<^sub>C\<^sub>L" 55) is "(o)"
  parametric comp_transfer
  unfolding o_def
  by (rule bounded_clinear_compose)

lemma cblinfun_apply_cblinfun_compose[simp]: "(a o\<^sub>C\<^sub>L b) c = a (b c)"
  by (simp add: cblinfun_compose.rep_eq)

lemma norm_cblinfun_compose:
  "norm (f o\<^sub>C\<^sub>L g) \<le> norm f * norm g"
  apply transfer
  by (auto intro!: onorm_compose simp: bounded_clinear.bounded_linear)

lemma bounded_cbilinear_cblinfun_compose[bounded_cbilinear]: "bounded_cbilinear (o\<^sub>C\<^sub>L)"
  by unfold_locales
    (auto intro!: cblinfun_eqI exI[where x=1] simp: cblinfun.cbilinear_simps norm_cblinfun_compose)

lemma cblinfun_compose_zero[simp]:
  "blinfun_compose 0 = (\<lambda>_. 0)"
  "blinfun_compose x 0 = 0"
  by (auto simp: blinfun.bilinear_simps intro!: blinfun_eqI)

lemma cblinfun_bij2:
  fixes f::"'a \<Rightarrow>\<^sub>C\<^sub>L 'a::ceuclidean_space"
  assumes "f o\<^sub>C\<^sub>L g = id_cblinfun"
  shows "bij (cblinfun_apply g)"
proof (rule bijI)
  show "inj g"
    using assms
    by (metis cblinfun_id_cblinfun_apply cblinfun_compose.rep_eq injI inj_on_imageI2)
  then show "surj g"
    using bounded_clinear_def cblinfun.bounded_clinear_right ceucl.linear_inj_imp_surj by blast
qed

lemma cblinfun_bij1:
  fixes f::"'a \<Rightarrow>\<^sub>C\<^sub>L 'a::ceuclidean_space"
  assumes "f o\<^sub>C\<^sub>L g = id_cblinfun"
  shows "bij (cblinfun_apply f)"
proof (rule bijI)
  show "surj (cblinfun_apply f)"
    by (metis assms cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply surjI)
  then show "inj (cblinfun_apply f)"
    using bounded_clinear_def cblinfun.bounded_clinear_right ceucl.linear_surjective_imp_injective by blast
qed

lift_definition cblinfun_cinner_right::"'a::complex_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L complex" is "(\<bullet>\<^sub>C)"
  by (rule bounded_clinear_cinner_right)
declare cblinfun_cinner_right.rep_eq[simp]

lemma bounded_antilinear_cblinfun_cinner_right[bounded_antilinear]: "bounded_antilinear cblinfun_cinner_right"
  apply transfer by (simp add: bounded_sesquilinear_cinner)

(* Cannot be defined. cinner is antilinear in first argument. *)
(* lift_definition cblinfun_cinner_left::"'a::complex_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L complex" is "\<lambda>x y. y \<bullet>\<^sub>C x" *)
(* declare cblinfun_cinner_left.rep_eq[simp] *)

(* lemma bounded_clinear_cblinfun_cinner_left[bounded_clinear]: "bounded_clinear cblinfun_cinner_left" *)

lift_definition cblinfun_scaleC_right::"complex \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_normed_vector" is "(*\<^sub>C)"
  by (rule bounded_clinear_scaleC_right)
declare cblinfun_scaleC_right.rep_eq[simp]

lemma bounded_clinear_cblinfun_scaleC_right[bounded_clinear]: "bounded_clinear cblinfun_scaleC_right"
  by transfer (rule bounded_cbilinear_scaleC)

lift_definition cblinfun_scaleC_left::"'a::complex_normed_vector \<Rightarrow> complex \<Rightarrow>\<^sub>C\<^sub>L 'a" is "\<lambda>x y. y *\<^sub>C x"
  by (rule bounded_clinear_scaleC_left)
lemmas [simp] = cblinfun_scaleC_left.rep_eq

lemma bounded_clinear_cblinfun_scaleC_left[bounded_clinear]: "bounded_clinear cblinfun_scaleC_left"
  by transfer (rule bounded_cbilinear.flip[OF bounded_cbilinear_scaleC])

lift_definition cblinfun_mult_right::"'a \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_normed_algebra" is "(*)"
  by (rule bounded_clinear_mult_right)
declare cblinfun_mult_right.rep_eq[simp]

lemma bounded_clinear_cblinfun_mult_right[bounded_clinear]: "bounded_clinear cblinfun_mult_right"
  by transfer (rule bounded_cbilinear_mult)

lift_definition cblinfun_mult_left::"'a::complex_normed_algebra \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a" is "\<lambda>x y. y * x"
  by (rule bounded_clinear_mult_left)
lemmas [simp] = cblinfun_mult_left.rep_eq

lemma bounded_clinear_cblinfun_mult_left[bounded_clinear]: "bounded_clinear cblinfun_mult_left"
  by transfer (rule bounded_cbilinear.flip[OF bounded_cbilinear_mult])

lemmas bounded_clinear_function_uniform_limit_intros[uniform_limit_intros] =
  bounded_clinear.uniform_limit[OF bounded_clinear_apply_cblinfun]
  bounded_clinear.uniform_limit[OF bounded_clinear_cblinfun_apply]
  bounded_antilinear.uniform_limit[OF bounded_antilinear_cblinfun_matrix]


subsection \<open>The strong operator topology on continuous linear operators\<close>

text \<open>Let \<open>'a\<close> and \<open>'b\<close> be two normed real vector spaces. Then the space of linear continuous
operators from \<open>'a\<close> to \<open>'b\<close> has a canonical norm, and therefore a canonical corresponding topology
(the type classes instantiation are given in \<^file>\<open>Complex_Bounded_Linear_Function0.thy\<close>).

However, there is another topology on this space, the strong operator topology, where \<open>T\<^sub>n\<close> tends to
\<open>T\<close> iff, for all \<open>x\<close> in \<open>'a\<close>, then \<open>T\<^sub>n x\<close> tends to \<open>T x\<close>. This is precisely the product topology
where the target space is endowed with the norm topology. It is especially useful when \<open>'b\<close> is the set
of real numbers, since then this topology is compact.

We can not implement it using type classes as there is already a topology, but at least we
can define it as a topology.

Note that there is yet another (common and useful) topology on operator spaces, the weak operator
topology, defined analogously using the product topology, but where the target space is given the
weak-* topology, i.e., the pullback of the weak topology on the bidual of the space under the
canonical embedding of a space into its bidual. We do not define it there, although it could also be
defined analogously.
\<close>

definition\<^marker>\<open>tag important\<close> cstrong_operator_topology::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector) topology"
  where "cstrong_operator_topology = pullback_topology UNIV cblinfun_apply euclidean"

lemma cstrong_operator_topology_topspace:
  "topspace cstrong_operator_topology = UNIV"
  unfolding cstrong_operator_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma cstrong_operator_topology_basis:
  fixes f::"('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector)" and U::"'i \<Rightarrow> 'b set" and x::"'i \<Rightarrow> 'a"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)"
  shows "openin cstrong_operator_topology {f. \<forall>i\<in>I. cblinfun_apply f (x i) \<in> U i}"
proof -
  have "open {g::('a\<Rightarrow>'b). \<forall>i\<in>I. g (x i) \<in> U i}"
    by (rule product_topology_basis'[OF assms])
  moreover have "{f. \<forall>i\<in>I. cblinfun_apply f (x i) \<in> U i}
                = cblinfun_apply-`{g::('a\<Rightarrow>'b). \<forall>i\<in>I. g (x i) \<in> U i} \<inter> UNIV"
    by auto
  ultimately show ?thesis
    unfolding cstrong_operator_topology_def by (subst openin_pullback_topology) auto
qed

lemma cstrong_operator_topology_continuous_evaluation:
  "continuous_map cstrong_operator_topology euclidean (\<lambda>f. cblinfun_apply f x)"
proof -
  have "continuous_map cstrong_operator_topology euclidean ((\<lambda>f. f x) o cblinfun_apply)"
    unfolding cstrong_operator_topology_def apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  then show ?thesis unfolding comp_def by simp
qed

lemma continuous_on_cstrong_operator_topo_iff_coordinatewise:
  "continuous_map T cstrong_operator_topology f
    \<longleftrightarrow> (\<forall>x. continuous_map T euclidean (\<lambda>y. cblinfun_apply (f y) x))"
proof (auto)
  fix x::"'b"
  assume "continuous_map T cstrong_operator_topology f"
  with continuous_map_compose[OF this cstrong_operator_topology_continuous_evaluation]
  have "continuous_map T euclidean ((\<lambda>z. cblinfun_apply z x) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>y. cblinfun_apply (f y) x)"
    unfolding comp_def by auto
next
  assume *: "\<forall>x. continuous_map T euclidean (\<lambda>y. cblinfun_apply (f y) x)"
  have "\<And>i. continuous_map T euclidean (\<lambda>x. cblinfun_apply (f x) i)"
    using * unfolding comp_def by auto
  then have "continuous_map T euclidean (cblinfun_apply o f)"
    unfolding o_def
    by (metis (no_types) continuous_map_componentwise_UNIV euclidean_product_topology)
  show "continuous_map T cstrong_operator_topology f"
    unfolding cstrong_operator_topology_def
    apply (rule continuous_map_pullback')
    by (auto simp add: \<open>continuous_map T euclidean (cblinfun_apply o f)\<close>)
qed

lemma cstrong_operator_topology_weaker_than_euclidean:
  "continuous_map euclidean cstrong_operator_topology (\<lambda>f. f)"
  apply (subst continuous_on_cstrong_operator_topo_iff_coordinatewise)
  by (auto simp add: linear_continuous_on continuous_at_imp_continuous_on linear_continuous_at 
      bounded_clinear.bounded_linear)
end
