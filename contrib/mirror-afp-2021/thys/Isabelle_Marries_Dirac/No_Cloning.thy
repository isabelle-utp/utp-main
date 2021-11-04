(*
Authors:

  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk;
  Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

section \<open>The No-Cloning Theorem\<close>

theory No_Cloning
imports
  Quantum
  Tensor
begin


subsection \<open>The Cauchy-Schwarz Inequality\<close>

lemma inner_prod_expand:
  assumes "dim_vec a = dim_vec b" and "dim_vec a = dim_vec c" and "dim_vec a = dim_vec d"
  shows "\<langle>a + b|c + d\<rangle> = \<langle>a|c\<rangle> + \<langle>a|d\<rangle> + \<langle>b|c\<rangle> + \<langle>b|d\<rangle>"
    apply (simp add: inner_prod_def)
    using assms sum.cong by (simp add: sum.distrib algebra_simps)

lemma inner_prod_distrib_left:
  assumes "dim_vec a = dim_vec b"
  shows "\<langle>c \<cdot>\<^sub>v a|b\<rangle> = cnj(c) * \<langle>a|b\<rangle>"
  using assms inner_prod_def by (simp add: algebra_simps mult_hom.hom_sum)

lemma inner_prod_distrib_right:
  assumes "dim_vec a = dim_vec b"
  shows "\<langle>a|c \<cdot>\<^sub>v b\<rangle> = c * \<langle>a|b\<rangle>"
  using assms by (simp add: algebra_simps mult_hom.hom_sum)

lemma cauchy_schwarz_ineq:
  assumes "dim_vec v = dim_vec w"
  shows "(cmod(\<langle>v|w\<rangle>))\<^sup>2 \<le> Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)"
proof (cases "\<langle>v|v\<rangle> = 0")
  case c0:True
  then have "\<And>i. i < dim_vec v \<Longrightarrow> v $ i = 0"
    by(metis index_zero_vec(1) inner_prod_with_itself_nonneg_reals_non0)
  then have "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = 0" by (simp add: assms inner_prod_def)
  moreover have "Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>) = 0" by (simp add: c0)
  ultimately show ?thesis by simp
next
  case c1:False
  have "dim_vec w = dim_vec (- \<langle>v|w\<rangle> / \<langle>v|v\<rangle> \<cdot>\<^sub>v v)" by (simp add: assms)
  then have "\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> + \<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> +
\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> + \<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle>"
    using inner_prod_expand[of "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v"] by auto
  moreover have "\<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * \<langle>w|v\<rangle>"
    using assms inner_prod_distrib_right[of "w" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] by simp
  moreover have "\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|w\<rangle>"
    using assms inner_prod_distrib_left[of "v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] by simp
  moreover have "\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * (-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|v\<rangle>"
    using inner_prod_distrib_left[of "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"]
inner_prod_distrib_right[of "v" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] by simp
  ultimately have "\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> -  cmod(\<langle>v|w\<rangle>)^2 / \<langle>v|v\<rangle>"
    using assms inner_prod_cnj[of "w" "v"] inner_prod_cnj[of "v" "v"] complex_norm_square by simp
  moreover have "Re(\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle>) \<ge> 0"
    using inner_prod_with_itself_Re by blast
  ultimately have "Re(\<langle>w|w\<rangle>) \<ge> cmod(\<langle>v|w\<rangle>)^2/Re(\<langle>v|v\<rangle>)"
    using inner_prod_with_itself_real by simp
  moreover have c2:"Re(\<langle>v|v\<rangle>) > 0"
    using inner_prod_with_itself_Re_non0 inner_prod_with_itself_eq0 c1 by auto
  ultimately have "Re(\<langle>w|w\<rangle>) * Re(\<langle>v|v\<rangle>) \<ge> cmod(\<langle>v|w\<rangle>)^2/Re(\<langle>v|v\<rangle>) * Re(\<langle>v|v\<rangle>)"
    by (metis less_numeral_extra(3) nonzero_divide_eq_eq pos_divide_le_eq)
  thus ?thesis
    using inner_prod_with_itself_Im c2 by (simp add: mult.commute)
qed

lemma cauchy_schwarz_eq [simp]:
  assumes "v = (l \<cdot>\<^sub>v w)"
  shows "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)"
proof-
  have "cmod(\<langle>v|w\<rangle>) = cmod(cnj(l) * \<langle>w|w\<rangle>)"
    using assms inner_prod_distrib_left[of "w" "w" "l"] by simp
  then have "cmod(\<langle>v|w\<rangle>)^2 = cmod(l)^2 * \<langle>w|w\<rangle> * \<langle>w|w\<rangle>"
    using complex_norm_square inner_prod_cnj[of "w" "w"] by simp
  moreover have "\<langle>v|v\<rangle> = cmod(l)^2 * \<langle>w|w\<rangle>"
    using assms complex_norm_square inner_prod_distrib_left[of "w" "v" "l"]
inner_prod_distrib_right[of "w" "w" "l"] by simp
  ultimately show ?thesis by (metis Re_complex_of_real)
qed

lemma cauchy_schwarz_col [simp]:
  assumes "dim_vec v = dim_vec w" and "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)"
  shows "\<exists>l. v = (l \<cdot>\<^sub>v w) \<or> w = (l \<cdot>\<^sub>v v)"
proof (cases "\<langle>v|v\<rangle> = 0")
  case c0:True
  then have "\<And>i. i < dim_vec v \<Longrightarrow> v $ i = 0"
    by(metis index_zero_vec(1) inner_prod_with_itself_nonneg_reals_non0)
  then have "v = 0 \<cdot>\<^sub>v w" by (auto simp: assms)
  then show ?thesis by auto
next
  case c1:False
  have f0:"dim_vec w = dim_vec (- \<langle>v|w\<rangle> / \<langle>v|v\<rangle> \<cdot>\<^sub>v v)" by (simp add: assms(1))
  then have "\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> + \<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> +
\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> + \<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle>"
    using inner_prod_expand[of "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v"] by simp
  moreover have "\<langle>w|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * \<langle>w|v\<rangle>"
    using assms(1) inner_prod_distrib_right[of "w" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] by simp
  moreover have "\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|w\<rangle>"
    using assms(1) inner_prod_distrib_left[of "v" "w" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] by simp
  moreover have "\<langle>-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = cnj(-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * (-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>) * \<langle>v|v\<rangle>"
    using inner_prod_distrib_left[of "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"]
inner_prod_distrib_right[of "v" "v" "-\<langle>v|w\<rangle>/\<langle>v|v\<rangle>"] by simp
  ultimately have "\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = \<langle>w|w\<rangle> -  cmod(\<langle>v|w\<rangle>)^2 / \<langle>v|v\<rangle>"
    using inner_prod_cnj[of "w" "v"] inner_prod_cnj[of "v" "v"] assms(1) complex_norm_square by simp
  moreover have "\<langle>w|w\<rangle> = cmod(\<langle>v|w\<rangle>)^2 / \<langle>v|v\<rangle>"
    using assms(2) inner_prod_with_itself_real by(metis Reals_mult c1 nonzero_mult_div_cancel_left of_real_Re)
  ultimately have "\<langle>w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v|w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v\<rangle> = 0" by simp
  then have "\<And>i. i<dim_vec w \<Longrightarrow> (w + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v) $ i = 0"
    by (metis f0 index_add_vec(2) index_zero_vec(1) inner_prod_with_itself_nonneg_reals_non0)
  then have "\<And>i. i<dim_vec w \<Longrightarrow> w $ i + -\<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i = 0"
    by (metis assms(1) f0 index_add_vec(1) index_smult_vec(1))
  then have "\<And>i. i<dim_vec w \<Longrightarrow> w $ i = \<langle>v|w\<rangle>/\<langle>v|v\<rangle> * v $ i" by simp
  then have "w = \<langle>v|w\<rangle>/\<langle>v|v\<rangle> \<cdot>\<^sub>v v" by (auto simp add: assms(1))
  thus ?thesis by auto
qed

subsection \<open>The No-Cloning Theorem\<close>

lemma eq_from_inner_prod [simp]:
  assumes "dim_vec v = dim_vec w" and "\<langle>v|w\<rangle> = 1" and "\<langle>v|v\<rangle> = 1" and "\<langle>w|w\<rangle> = 1"
  shows "v = w"
proof-
  have "(cmod(\<langle>v|w\<rangle>))\<^sup>2 = Re (\<langle>v|v\<rangle> * \<langle>w|w\<rangle>)" by (simp add: assms)
  then have f0:"\<exists>l. v = (l \<cdot>\<^sub>v w) \<or> w = (l \<cdot>\<^sub>v v)" by (simp add: assms(1))
  then show ?thesis
  proof (cases "\<exists>l. v = (l \<cdot>\<^sub>v w)")
    case True
    then have "\<exists>l. v = (l \<cdot>\<^sub>v w) \<and> \<langle>v|w\<rangle> = cnj(l) * \<langle>w|w\<rangle>"
      using inner_prod_distrib_left by auto
    then show ?thesis by (simp add: assms(2,4))
  next
    case False
    then have "\<exists>l. w = (l \<cdot>\<^sub>v v) \<and> \<langle>v|w\<rangle> = l * \<langle>v|v\<rangle>"
      using f0 inner_prod_distrib_right by auto
    then show ?thesis by (simp add: assms(2,3))
  qed
qed

lemma hermite_cnj_of_tensor:
  shows "(A \<Otimes> B)\<^sup>\<dagger>  = (A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)"
proof
  show c0:"dim_row ((A \<Otimes> B)\<^sup>\<dagger>) = dim_row ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))" by simp
  show c1:"dim_col ((A \<Otimes> B)\<^sup>\<dagger>) = dim_col ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))" by simp
  show "\<And>i j. i < dim_row ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) \<Longrightarrow> j < dim_col ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) \<Longrightarrow>
((A \<Otimes> B)\<^sup>\<dagger>) $$ (i, j) = ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) $$ (i, j)"
  proof-
    fix i j assume a0:"i < dim_row ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))" and a1:"j < dim_col ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>))"
    then have "(A \<Otimes> B)\<^sup>\<dagger> $$ (i, j) = cnj((A \<Otimes> B) $$ (j, i))" by (simp add: dagger_def)
    also have "\<dots> = cnj(A $$ (j div dim_row(B), i div dim_col(B)) * B $$ (j mod dim_row(B), i mod dim_col(B)))"
      by (metis (mono_tags, lifting) a0 a1 c1 dim_row_tensor_mat dim_col_of_dagger dim_row_of_dagger
index_tensor_mat less_nat_zero_code mult_not_zero neq0_conv)
    moreover have "((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) $$ (i, j) =
(A\<^sup>\<dagger>) $$ (i div dim_col(B), j div dim_row(B)) * (B\<^sup>\<dagger>) $$ (i mod dim_col(B), j mod dim_row(B))"
      by (smt a0 a1 c1 dim_row_tensor_mat dim_col_of_dagger dim_row_of_dagger index_tensor_mat
less_nat_zero_code mult_eq_0_iff neq0_conv)
    moreover have "(B\<^sup>\<dagger>) $$ (i mod dim_col(B), j mod dim_row(B)) = cnj(B $$ (j mod dim_row(B), i mod dim_col(B)))"
    proof-
      have "i mod dim_col(B) < dim_col(B)"
        using a0 gr_implies_not_zero mod_div_trivial by fastforce
      moreover have "j mod dim_row(B) < dim_row(B)"
        using a1 gr_implies_not_zero mod_div_trivial by fastforce
      ultimately show ?thesis by (simp add: dagger_def)
    qed
    moreover have "(A\<^sup>\<dagger>) $$ (i div dim_col(B), j div dim_row(B)) = cnj(A $$ (j div dim_row(B), i div dim_col(B)))"
    proof-
      have "i div dim_col(B) < dim_col(A)"
        using a0 dagger_def by (simp add: less_mult_imp_div_less)
      moreover have "j div dim_row(B) < dim_row(A)"
        using a1 dagger_def by (simp add: less_mult_imp_div_less)
      ultimately show ?thesis by (simp add: dagger_def)
    qed
    ultimately show "((A \<Otimes> B)\<^sup>\<dagger>) $$ (i, j) = ((A\<^sup>\<dagger>) \<Otimes> (B\<^sup>\<dagger>)) $$ (i, j)" by simp
  qed
qed

locale quantum_machine =
  fixes n:: nat and s:: "complex Matrix.vec" and U:: "complex Matrix.mat"
  assumes dim_vec [simp]: "dim_vec s = 2^n"
    and dim_col [simp]: "dim_col U = 2^n * 2^n"
    and square [simp]: "square_mat U" and unitary [simp]: "unitary U"

lemma inner_prod_of_unit_vec:
  fixes n i:: nat
  assumes "i < n"
  shows "\<langle>unit_vec n i| unit_vec n i\<rangle> = 1"
  by (auto simp add: inner_prod_def unit_vec_def)
    (simp add: assms sum.cong[of "{0..<n}" "{0..<n}"
        "\<lambda>j. cnj (if j = i then 1 else 0) * (if j = i then 1 else 0)" "\<lambda>j. (if j = i then 1 else 0)"])

theorem (in quantum_machine) no_cloning:
  assumes [simp]: "dim_vec v = 2^n" and [simp]: "dim_vec w = 2^n" and
    cloning1: "\<And>s. U * ( |v\<rangle> \<Otimes> |s\<rangle>) = |v\<rangle> \<Otimes> |v\<rangle>" and
    cloning2: "\<And>s. U * ( |w\<rangle> \<Otimes> |s\<rangle>) = |w\<rangle> \<Otimes> |w\<rangle>" and
    "\<langle>v|v\<rangle> = 1" and "\<langle>w|w\<rangle> = 1"
  shows "v = w \<or> \<langle>v|w\<rangle> = 0"
proof-
  define s:: "complex Matrix.vec" where d0:"s = unit_vec (2^n) 0"
  have f0:"\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| = (( |v\<rangle> \<Otimes> |s\<rangle>)\<^sup>\<dagger>)"
    using hermite_cnj_of_tensor[of "|v\<rangle>" "|s\<rangle>"] bra_def dagger_def ket_vec_def by simp
  moreover have f1:"( |v\<rangle> \<Otimes> |v\<rangle>)\<^sup>\<dagger> * ( |w\<rangle> \<Otimes> |w\<rangle>) = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * ( |w\<rangle> \<Otimes> |s\<rangle>)"
  proof-
    have "(U * ( |v\<rangle> \<Otimes> |s\<rangle>))\<^sup>\<dagger> = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * (U\<^sup>\<dagger>)"
      using dagger_of_prod[of "U" "|v\<rangle> \<Otimes> |s\<rangle>"] f0 d0 by (simp add: ket_vec_def)
    then have "(U * ( |v\<rangle> \<Otimes> |s\<rangle>))\<^sup>\<dagger> * U * ( |w\<rangle> \<Otimes> |s\<rangle>) = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * (U\<^sup>\<dagger>) * U * ( |w\<rangle> \<Otimes> |s\<rangle>)" by simp
    moreover have "(U * ( |v\<rangle> \<Otimes> |s\<rangle>))\<^sup>\<dagger> * U * ( |w\<rangle> \<Otimes> |s\<rangle>) = (( |v\<rangle> \<Otimes> |v\<rangle>)\<^sup>\<dagger>) * ( |w\<rangle> \<Otimes> |w\<rangle>)"
      using assms(2-4) d0 unit_vec_def by (smt Matrix.dim_vec assoc_mult_mat carrier_mat_triv dim_row_mat(1)
dim_row_tensor_mat dim_col_of_dagger index_mult_mat(2) ket_vec_def square square_mat.elims(2))
    moreover have "(U\<^sup>\<dagger>) * U = 1\<^sub>m (2^n * 2^n)"
      using unitary_def dim_col unitary by simp
    moreover have "(\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * (U\<^sup>\<dagger>) * U = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * ((U\<^sup>\<dagger>) * U)"
      using d0 assms(1) unit_vec_def by (smt Matrix.dim_vec assoc_mult_mat carrier_mat_triv dim_row_mat(1)
dim_row_tensor_mat f0 dim_col_of_dagger dim_row_of_dagger ket_vec_def local.dim_col)
    moreover have "(\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| ) * 1\<^sub>m (2^n * 2^n) = (\<langle>|v\<rangle>| \<Otimes> \<langle>|s\<rangle>| )"
      using f0 ket_vec_def d0 by simp
    ultimately show ?thesis by simp
  qed
  then have f2:"(\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|v\<rangle>| * |w\<rangle>) = (\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|s\<rangle>| * |s\<rangle>)"
  proof-
    have "\<langle>|v\<rangle>| \<Otimes> \<langle>|v\<rangle>| = (( |v\<rangle> \<Otimes> |v\<rangle>)\<^sup>\<dagger>)"
      using hermite_cnj_of_tensor[of "|v\<rangle>" "|v\<rangle>"] bra_def dagger_def ket_vec_def by simp
    then show ?thesis
      using f1 d0 by (simp add: bra_def mult_distr_tensor ket_vec_def)
  qed
  then have "\<langle>v|w\<rangle> * \<langle>v|w\<rangle> = \<langle>v|w\<rangle> * \<langle>s|s\<rangle>"
  proof-
    have "((\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|v\<rangle>| * |w\<rangle>)) $$ (0,0) = \<langle>v|w\<rangle> * \<langle>v|w\<rangle>"
      using assms inner_prod_with_times_mat[of "v" "w"] by (simp add: bra_def ket_vec_def)
    moreover have "((\<langle>|v\<rangle>| * |w\<rangle>) \<Otimes> (\<langle>|s\<rangle>| * |s\<rangle>)) $$ (0,0) = \<langle>v|w\<rangle> * \<langle>s|s\<rangle>"
      using inner_prod_with_times_mat[of "v" "w"] inner_prod_with_times_mat[of "s" "s"] by(simp add: bra_def ket_vec_def)
    ultimately show ?thesis using f2 by auto
  qed
  then have "\<langle>v|w\<rangle> = 0 \<or> \<langle>v|w\<rangle> = \<langle>s|s\<rangle>" by (simp add: mult_left_cancel)
  moreover have "\<langle>s|s\<rangle> = 1" by(simp add: d0 inner_prod_of_unit_vec)
  ultimately show ?thesis using assms(1,2,5,6) by auto
qed

end