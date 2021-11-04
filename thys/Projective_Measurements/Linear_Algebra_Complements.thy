(*
Author: 
  Mnacho Echenim, Université Grenoble Alpes
*)

theory Linear_Algebra_Complements imports 
  "Isabelle_Marries_Dirac.Tensor" 
  "Isabelle_Marries_Dirac.More_Tensor"
  "QHLProver.Gates" 
  "HOL-Types_To_Sets.Group_On_With" 
  "HOL-Probability.Probability" 


begin
hide_const(open) S
section \<open>Preliminaries\<close>


subsection \<open>Misc\<close>

lemma mult_real_cpx:
  fixes a::complex
  fixes b::complex
  assumes "a\<in> Reals"
  shows "a* (Re b) = Re (a * b)" using assms
  by (metis Reals_cases complex.exhaust complex.sel(1) complex_of_real_mult_Complex of_real_mult)

lemma fct_bound:
  fixes f::"complex\<Rightarrow> real"
  assumes "f(-1) + f 1 = 1"
and "0 \<le> f 1"
and "0 \<le> f (-1)"
shows "-1 \<le> f 1  - f(-1) \<and> f 1  - f(-1) \<le> 1"
proof
  have "f 1  - f(-1) = 1 - f(-1) - f(-1)"  using assms by simp
  also have "...\<ge> -1" using assms by simp
  finally show "-1 \<le> f 1  - f(-1)" .
next
  have "f(-1) - f 1  = 1 - f 1  - f 1 " using assms by simp
  also have "... \<ge> -1" using assms by simp
  finally have "-1 \<le> f(-1) - f 1" .
  thus "f 1 - f (-1) \<le> 1" by simp
qed

lemma fct_bound':
  fixes f::"complex\<Rightarrow> real"
  assumes "f(-1) + f 1 = 1"
and "0 \<le> f 1"
and "0 \<le> f (-1)"
shows "\<bar>f 1  - f(-1)\<bar> \<le> 1" using assms fct_bound by auto

lemma pos_sum_1_le:
  assumes "finite I"
and "\<forall> i \<in> I. (0::real) \<le> f i"
and "(\<Sum>i\<in> I. f i) = 1"
and "j\<in> I"
shows "f j \<le> 1"
proof (rule ccontr)
  assume "\<not> f j \<le> 1"
  hence "1 < f j" by simp
  hence "1 < (\<Sum>i\<in> I. f i)" using assms by (metis \<open>\<not> f j \<le> 1\<close> sum_nonneg_leq_bound) 
  thus False using assms by simp
qed

lemma last_subset:
  assumes "A \<subseteq> {a,b}"
  and "a\<noteq> b"
and "A \<noteq> {a, b}"
and "A\<noteq> {}"
and "A \<noteq> {a}"
shows "A = {b}" using assms by blast

lemma disjoint_Un:
  assumes "disjoint_family_on A (insert x F)"
  and "x\<notin> F"
shows "(A x) \<inter> (\<Union> a\<in> F. A a) = {}" 
proof -
  have "(A x) \<inter> (\<Union> a\<in> F. A a) = (\<Union>i\<in>F. (A x) \<inter> A i)" using Int_UN_distrib by simp
  also have "... = (\<Union>i\<in>F. {})" using assms disjoint_family_onD by fastforce
  also have "... = {}" using SUP_bot_conv(2) by simp
  finally show ?thesis .
qed

lemma sum_but_one:
  assumes "\<forall>j < (n::nat). j \<noteq>i \<longrightarrow> f j = (0::'a::ring)"
  and "i < n"
  shows "(\<Sum> j \<in> {0 ..< n}. f j * g j) = f i * g i"
proof -
  have "sum (\<lambda>x. f x * g x) (({0 ..< n} - {i}) \<union> {i}) = sum (\<lambda>x. f x * g x) ({0 ..< n} - {i}) + 
    sum (\<lambda>x. f x * g x) {i}" by (rule sum.union_disjoint, auto)
  also have "... = sum (\<lambda>x. f x * g x) {i}" using assms by auto
  also have "... = f i * g i" by simp
  finally have "sum (\<lambda>x. f x * g x) (({0 ..< n} - {i}) \<union> {i}) = f i * g i" .
  moreover have "{0 ..< n} = ({0 ..< n} - {i}) \<union> {i}" using assms by auto
  ultimately show ?thesis by simp
qed

lemma sum_2_elems:
  assumes "I = {a,b}"
    and "a\<noteq> b"
  shows "(\<Sum>a\<in>I. f a) = f a + f b" 
proof -
  have "(\<Sum>a\<in>I. f a) = (\<Sum>a\<in>(insert a {b}). f a)" using assms by simp
  also have "... = f a + (\<Sum>a\<in>{b}. f a)" 
  proof (rule sum.insert)
    show "finite {b}" by simp
    show "a\<notin> {b}" using assms by simp
  qed
  also have "... = f a + f b" by simp
  finally show ?thesis .
qed

lemma sum_4_elems:
  shows "(\<Sum>i<(4::nat). f i) = f 0 + f 1 + f 2 + f 3" 
proof -
  have "(\<Sum>i<(4::nat). f i) = (\<Sum>i<(3::nat). f i)  + f 3"
    by (metis Suc_numeral semiring_norm(2) semiring_norm(8) sum.lessThan_Suc)
  moreover have "(\<Sum>i<(3::nat). f i) = (\<Sum>i<(2::nat). f i) + f 2"
    by (metis Suc_1 add_2_eq_Suc' nat_1_add_1 numeral_code(3) numerals(1) 
        one_plus_numeral_commute sum.lessThan_Suc)
  moreover have "(\<Sum>i<(2::nat). f i) = (\<Sum>i<(1::nat). f i) + f 1"
    by (metis Suc_1 sum.lessThan_Suc)
  ultimately show ?thesis by simp
qed

lemma disj_family_sum:
  shows "finite I \<Longrightarrow> disjoint_family_on A I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> finite (A i))  \<Longrightarrow> 
  (\<Sum> i \<in> (\<Union>n \<in> I. A n). f i) = (\<Sum> n\<in> I. (\<Sum> i \<in> A n. f i))" 
proof (induct rule:finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  hence "disjoint_family_on A F"
    by (meson disjoint_family_on_mono subset_insertI) 
  have "(\<Union>n \<in> (insert x F). A n) = A x \<union> (\<Union>n \<in> F. A n)" using insert by simp
  hence "(\<Sum> i \<in> (\<Union>n \<in> (insert x F). A n). f i) = (\<Sum> i \<in> (A x \<union> (\<Union>n \<in> F. A n)). f i)" by simp
  also have "... = (\<Sum> i \<in>  A x. f i) + (\<Sum> i \<in> (\<Union>n \<in> F. A n). f i)" 
    by (rule sum.union_disjoint, (simp add: insert disjoint_Un)+)
  also have "... = (\<Sum> i \<in>  A x. f i) + (\<Sum>n\<in>F. sum f (A n))" using  \<open>disjoint_family_on A F\<close> 
    by (simp add: insert)
  also have "... = (\<Sum>n\<in>(insert x F). sum f (A n))" using insert by simp
  finally show ?case .
qed

lemma integrable_real_mult_right:
  fixes c::real
  assumes "integrable M f"
  shows "integrable M (\<lambda>w. c * f w)" 
proof (cases "c = 0")
  case True
  thus ?thesis by simp
next
  case False
  thus ?thesis using integrable_mult_right[of c] assms by simp
qed


subsection \<open>Unifying notions between Isabelle Marries Dirac and QHLProver\<close>

lemma mult_conj_cmod_square:
  fixes z::complex
  shows "z * conjugate z = (cmod z)\<^sup>2"
proof -
  have "z * conjugate z = (Re z)\<^sup>2 + (Im z)\<^sup>2" using  complex_mult_cnj by auto
  also have "... = (cmod z)\<^sup>2" unfolding cmod_def by simp
  finally show ?thesis .
qed

lemma vec_norm_sq_cpx_vec_length_sq:
  shows "(vec_norm v)\<^sup>2 = (cpx_vec_length v)\<^sup>2"
proof -
  have "(vec_norm v)\<^sup>2 = inner_prod v v" unfolding vec_norm_def using power2_csqrt by blast
  also have "... = (\<Sum>i<dim_vec v. (cmod (Matrix.vec_index v i))\<^sup>2)" unfolding Matrix.scalar_prod_def
  proof -
    have "\<And>i. i < dim_vec v \<Longrightarrow> Matrix.vec_index v  i * conjugate (Matrix.vec_index v i) = 
      (cmod (Matrix.vec_index v i))\<^sup>2" using mult_conj_cmod_square by simp
    thus "(\<Sum>i = 0..<dim_vec (conjugate v). Matrix.vec_index v i * 
      Matrix.vec_index (conjugate v) i) =  (\<Sum>i<dim_vec v. (cmod (Matrix.vec_index v i))\<^sup>2)" 
      by (simp add: lessThan_atLeast0)
  qed
  finally show "(vec_norm v)\<^sup>2 = (cpx_vec_length v)\<^sup>2" unfolding cpx_vec_length_def
    by (simp add: sum_nonneg)
qed

lemma vec_norm_eq_cpx_vec_length:
  shows "vec_norm v = cpx_vec_length v" using vec_norm_sq_cpx_vec_length_sq
by (metis cpx_vec_length_inner_prod inner_prod_csqrt power2_csqrt vec_norm_def) 

lemma cpx_vec_length_square:
  shows "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>i = 0..<dim_vec v. (cmod (Matrix.vec_index v i))\<^sup>2)" unfolding cpx_vec_length_def
  by (simp add: lessThan_atLeast0 sum_nonneg)

lemma state_qbit_norm_sq:
  assumes "v\<in> state_qbit n"
  shows "(cpx_vec_length v)\<^sup>2 = 1"
proof -
  have "cpx_vec_length v = 1" using assms unfolding state_qbit_def by simp
  thus ?thesis by simp
qed

lemma dagger_adjoint:
shows "dagger M = Complex_Matrix.adjoint M" unfolding dagger_def Complex_Matrix.adjoint_def
  by (simp add: cong_mat)


subsection \<open>Types to sets lemmata transfers\<close>

context ab_group_add_on_with begin

context includes lifting_syntax assumes ltd: "\<exists>(Rep::'s \<Rightarrow> 'a) (Abs::'a \<Rightarrow> 's). 
  type_definition Rep Abs S" begin
interpretation local_typedef_ab_group_add_on_with pls z mns um S "TYPE('s)" by unfold_locales fact

lemmas lt_sum_union_disjoint = sum.union_disjoint
  [var_simplified explicit_ab_group_add,
    unoverload_type 'c,
    OF type.comm_monoid_add_axioms,
    untransferred]

lemmas lt_disj_family_sum = disj_family_sum
  [var_simplified explicit_ab_group_add,
    unoverload_type 'd,
OF type.comm_monoid_add_axioms,
    untransferred]

lemmas lt_sum_reindex_cong = sum.reindex_cong
  [var_simplified explicit_ab_group_add,
    unoverload_type 'd,
OF type.comm_monoid_add_axioms,
    untransferred]
end

lemmas sum_with_union_disjoint =
  lt_sum_union_disjoint
    [cancel_type_definition,
    OF carrier_ne,
    simplified pred_fun_def, simplified]

lemmas disj_family_sum_with =
  lt_disj_family_sum
    [cancel_type_definition,
    OF carrier_ne,
    simplified pred_fun_def, simplified]

lemmas sum_with_reindex_cong = 
  lt_sum_reindex_cong
    [cancel_type_definition,
    OF carrier_ne,
    simplified pred_fun_def, simplified]

end

lemma (in comm_monoid_add_on_with) sum_with_cong':
  shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> A i = B i) \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> A i \<in> S) \<Longrightarrow> 
    (\<And>i. i\<in> I \<Longrightarrow> B i \<in> S) \<Longrightarrow> sum_with pls z A I = sum_with pls z B I"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "sum_with pls z A (insert x F) = pls (A x) (sum_with pls z A F)" using insert 
      sum_with_insert[of A] by (simp add:  image_subset_iff) 
  also have "... = pls (B x)  (sum_with pls z B F)" using insert by simp
  also have "... = sum_with pls z B (insert x F)" using insert sum_with_insert[of B]
    by (simp add:  image_subset_iff) 
  finally show ?case .
qed


section \<open>Linear algebra complements\<close>

subsection \<open>Additional properties of matrices\<close>

lemma smult_one:
  shows "(1::'a::monoid_mult) \<cdot>\<^sub>m A = A" by (simp add:eq_matI)

lemma times_diag_index:
  fixes A::"'a::comm_ring Matrix.mat"
  assumes "A \<in> carrier_mat n n"
and "B\<in> carrier_mat n n"
and "diagonal_mat B"
and "j < n"
and "i < n"
shows "Matrix.vec_index (Matrix.row (A*B) j) i = diag_mat B ! i *A $$ (j, i)"
proof -
  have "Matrix.vec_index (Matrix.row (A*B) j) i = (A*B) $$ (j,i)" 
    using Matrix.row_def[of "A*B" ] assms by simp
  also have "... = Matrix.scalar_prod (Matrix.row A j) (Matrix.col B i)" using assms 
      times_mat_def[of A] by simp
  also have "... = Matrix.scalar_prod (Matrix.col B i) (Matrix.row A j)" 
    using comm_scalar_prod[of "Matrix.row A j" n] assms by auto
  also have "... = (Matrix.vec_index (Matrix.col B i) i) * (Matrix.vec_index  (Matrix.row A j) i)" 
    unfolding Matrix.scalar_prod_def 
  proof (rule sum_but_one)
    show "i < dim_vec (Matrix.row A j)" using assms by simp
    show "\<forall>ia<dim_vec (Matrix.row A j). ia \<noteq> i \<longrightarrow> Matrix.vec_index (Matrix.col B i) ia = 0" using assms
      by (metis carrier_matD(1) carrier_matD(2) diagonal_mat_def index_col index_row(2))
  qed
  also have "... = B $$(i,i) * (Matrix.vec_index  (Matrix.row A j) i)" using assms by auto
  also have "... = diag_mat B ! i * (Matrix.vec_index  (Matrix.row A j) i)" unfolding diag_mat_def 
    using assms by simp
  also have "... = diag_mat B ! i * A $$ (j, i)" using assms by simp
  finally show ?thesis .
qed

lemma inner_prod_adjoint_comp:
  assumes "(U::'a::conjugatable_field Matrix.mat) \<in> carrier_mat n n"
and "(V::'a::conjugatable_field Matrix.mat) \<in> carrier_mat n n"
and "i < n"
and "j < n"
shows "Complex_Matrix.inner_prod  (Matrix.col V i) (Matrix.col U j) = 
  ((Complex_Matrix.adjoint V) * U) $$ (i, j)"
proof -
  have "Complex_Matrix.inner_prod (Matrix.col V i) (Matrix.col U j) = 
    Matrix.scalar_prod (Matrix.col U j) (Matrix.row (Complex_Matrix.adjoint V) i)"
    using adjoint_row[of i V] assms  by simp  
  also have "... = Matrix.scalar_prod (Matrix.row (Complex_Matrix.adjoint V) i) (Matrix.col U j)"
    by (metis adjoint_row assms(1) assms(2) assms(3) carrier_matD(1) carrier_matD(2) Matrix.col_dim 
        conjugate_vec_sprod_comm)
  also have "... = ((Complex_Matrix.adjoint V) * U) $$ (i, j)" using assms 
    by (simp add:times_mat_def)
  finally show ?thesis .
qed

lemma mat_unit_vec_col:
  assumes "(A::'a::conjugatable_field Matrix.mat) \<in> carrier_mat n n"
and "i < n"
shows "A *\<^sub>v (unit_vec n i) = Matrix.col A i"
proof
  show "dim_vec (A *\<^sub>v unit_vec n i) = dim_vec (Matrix.col A i)" using assms by simp
  show "\<And>j. j < dim_vec (Matrix.col A i) \<Longrightarrow> Matrix.vec_index (A *\<^sub>v unit_vec n i)  j = 
    Matrix.vec_index (Matrix.col A i)  j"
  proof -
    fix j
    assume "j < dim_vec (Matrix.col A i)"
    hence "Matrix.vec_index (A *\<^sub>v unit_vec n i)  j = 
      Matrix.scalar_prod (Matrix.row A j) (unit_vec n i)" unfolding mult_mat_vec_def by simp
    also have "... = Matrix.scalar_prod  (unit_vec n i) (Matrix.row A j)" using comm_scalar_prod
        assms by auto
    also have "... = (Matrix.vec_index (unit_vec n i) i) * (Matrix.vec_index (Matrix.row A j) i)"
      unfolding Matrix.scalar_prod_def 
    proof (rule sum_but_one)
      show "i < dim_vec (Matrix.row A j)" using assms by auto
      show "\<forall>ia<dim_vec (Matrix.row A j). ia \<noteq> i \<longrightarrow> Matrix.vec_index (unit_vec n i) ia = 0" 
        using assms unfolding unit_vec_def by auto
    qed
    also have "... = (Matrix.vec_index (Matrix.row A j) i)" using assms by simp
    also have "... = A $$ (j, i)" using assms \<open>j < dim_vec (Matrix.col A i)\<close> by simp
    also have "... = Matrix.vec_index (Matrix.col A i)  j" using assms \<open>j < dim_vec (Matrix.col A i)\<close> by simp
    finally show "Matrix.vec_index (A *\<^sub>v unit_vec n i)  j = 
      Matrix.vec_index (Matrix.col A i)  j" .
  qed
qed

lemma mat_prod_unit_vec_cong:
  assumes "(A::'a::conjugatable_field Matrix.mat) \<in> carrier_mat n n"
and "B\<in> carrier_mat n n"
and "\<And>i. i < n \<Longrightarrow> A *\<^sub>v (unit_vec n i) = B *\<^sub>v (unit_vec n i)"
shows "A = B"
proof
  show "dim_row A = dim_row B" using assms by simp
  show "dim_col A = dim_col B" using assms by simp
  show "\<And>i j. i < dim_row B \<Longrightarrow> j < dim_col B \<Longrightarrow> A $$ (i, j) = B $$ (i, j)"
  proof -
    fix i j
    assume ij: "i < dim_row B" "j < dim_col B"
    hence "A $$ (i,j) = Matrix.vec_index (Matrix.col A j) i" using assms by simp
    also have "... = Matrix.vec_index (A *\<^sub>v (unit_vec n j)) i" using mat_unit_vec_col[of A] ij assms 
      by simp
    also have "... = Matrix.vec_index (B *\<^sub>v (unit_vec n j)) i" using assms ij by simp
    also have "... = Matrix.vec_index (Matrix.col B j) i" using mat_unit_vec_col ij assms by simp
    also have "... = B $$ (i,j)" using assms ij by simp
    finally show "A $$ (i, j) = B $$ (i, j)" .
  qed
qed

lemma smult_smult_times:
  fixes a::"'a::semigroup_mult"
  shows "a\<cdot>\<^sub>m (k \<cdot>\<^sub>m A) = (a * k)\<cdot>\<^sub>m A"
proof
  show r:"dim_row (a \<cdot>\<^sub>m (k \<cdot>\<^sub>m A)) = dim_row (a * k \<cdot>\<^sub>m A)" by simp
  show c:"dim_col (a \<cdot>\<^sub>m (k \<cdot>\<^sub>m A)) = dim_col (a * k \<cdot>\<^sub>m A)" by simp
  show "\<And>i j. i < dim_row (a * k \<cdot>\<^sub>m A) \<Longrightarrow>
           j < dim_col (a * k \<cdot>\<^sub>m A) \<Longrightarrow> (a \<cdot>\<^sub>m (k \<cdot>\<^sub>m A)) $$ (i, j) = (a * k \<cdot>\<^sub>m A) $$ (i, j)"
  proof -
    fix i j
    assume "i < dim_row (a * k \<cdot>\<^sub>m A)" and "j < dim_col (a * k \<cdot>\<^sub>m A)" note ij = this
    hence "(a \<cdot>\<^sub>m (k \<cdot>\<^sub>m A)) $$ (i, j) = a * (k \<cdot>\<^sub>m A) $$ (i, j)"  by simp
    also have "... = a * (k * A $$ (i,j))" using ij by simp
    also have "... = (a * k) * A $$ (i,j)"
      by (simp add: semigroup_mult_class.mult.assoc)
    also have "... = (a * k \<cdot>\<^sub>m A) $$ (i, j)" using r c ij by simp
    finally show "(a \<cdot>\<^sub>m (k \<cdot>\<^sub>m A)) $$ (i, j) = (a * k \<cdot>\<^sub>m A) $$ (i, j)" .
  qed
qed

lemma mat_minus_minus:
  fixes A :: "'a :: ab_group_add Matrix.mat"
  assumes "A \<in> carrier_mat n m"
  and "B\<in> carrier_mat n m"
  and "C\<in> carrier_mat n m"
shows "A - (B - C) = A - B + C"
proof
  show "dim_row (A - (B - C)) = dim_row (A - B + C)" using assms by simp
  show "dim_col (A - (B - C)) = dim_col (A - B + C)" using assms by simp
  show "\<And>i j. i < dim_row (A - B + C) \<Longrightarrow> j < dim_col (A - B + C) \<Longrightarrow> 
    (A - (B - C)) $$ (i, j) = (A - B + C) $$ (i, j)" 
  proof -
    fix i j
    assume "i < dim_row (A - B + C)" and "j < dim_col (A - B + C)" note ij = this
    have "(A - (B - C)) $$ (i, j) = (A $$ (i,j) - B $$ (i,j) + C $$ (i,j))" using ij assms by simp
    also have "... = (A - B + C) $$ (i, j)" using assms ij by simp
    finally show "(A - (B - C)) $$ (i, j) = (A - B + C) $$ (i, j)" .
  qed
qed


subsection \<open>Complements on complex matrices\<close>

lemma hermitian_square:
  assumes "hermitian M"
  shows "M \<in> carrier_mat (dim_row M) (dim_row M)"
proof -
  have "dim_col M = dim_row M" using assms unfolding hermitian_def adjoint_def
    by (metis adjoint_dim_col)
  thus ?thesis by auto
qed

lemma hermitian_add:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
and "hermitian A"
and "hermitian B"
shows "hermitian (A + B)" unfolding hermitian_def
  by (metis adjoint_add assms hermitian_def)

lemma hermitian_minus:
  assumes "A\<in> carrier_mat n n"
  and "B\<in> carrier_mat n n"
and "hermitian A"
and "hermitian B"
shows "hermitian (A - B)" unfolding hermitian_def
  by (metis adjoint_minus assms hermitian_def)

lemma hermitian_smult:
  fixes a::real
  fixes A::"complex Matrix.mat"
  assumes "A \<in> carrier_mat n n"
and "hermitian A"
shows "hermitian (a \<cdot>\<^sub>m  A)"    
proof -
  have dim: "Complex_Matrix.adjoint A \<in> carrier_mat n n" using assms by (simp add: adjoint_dim) 
  {
    fix i j
    assume "i < n" and "j < n"
    hence "Complex_Matrix.adjoint (a \<cdot>\<^sub>m A) $$ (i,j) = a * (Complex_Matrix.adjoint A $$ (i,j))" 
      using adjoint_scale[of a A] assms by simp
    also have "... = a * (A $$ (i,j))" using assms unfolding hermitian_def by simp
    also have "... = (a \<cdot>\<^sub>m A) $$ (i,j)" using \<open>i < n\<close> \<open>j < n\<close> assms by simp
    finally have "Complex_Matrix.adjoint (a \<cdot>\<^sub>m A) $$ (i,j) = (a \<cdot>\<^sub>m A) $$ (i,j)" .
  }
  thus ?thesis using dim assms unfolding hermitian_def by auto
qed

lemma unitary_eigenvalues_norm_square:
  fixes U::"complex Matrix.mat"
  assumes "unitary U"
  and "U \<in> carrier_mat n n"
  and "eigenvalue U k"
shows "conjugate k * k = 1"
proof -
  have "\<exists>v. eigenvector U v k" using assms unfolding eigenvalue_def by simp
  from this obtain v where "eigenvector U v k" by auto
  define vn where "vn = vec_normalize v"
  have "eigenvector U vn k" using normalize_keep_eigenvector \<open>eigenvector U v k\<close>
    using assms(2) eigenvector_def vn_def by blast
  have "vn \<in> carrier_vec n"
    using \<open>eigenvector U v k\<close> assms(2) eigenvector_def normalized_vec_dim vn_def by blast
  have "Complex_Matrix.inner_prod vn vn = 1" using \<open>vn = vec_normalize v\<close> \<open>eigenvector U v k\<close> 
        eigenvector_def normalized_vec_norm by blast
  hence "conjugate k * k = conjugate k * k * Complex_Matrix.inner_prod vn vn" by simp
  also have "... = conjugate k * Complex_Matrix.inner_prod vn (k \<cdot>\<^sub>v vn)"
  proof -
    have "k * Complex_Matrix.inner_prod vn vn = Complex_Matrix.inner_prod vn (k \<cdot>\<^sub>v vn)" 
      using inner_prod_smult_left[of vn n vn k] \<open>vn \<in> carrier_vec n\<close> by simp
    thus ?thesis by simp
  qed
  also have "... = Complex_Matrix.inner_prod (k \<cdot>\<^sub>v vn) (k \<cdot>\<^sub>v vn)"
    using inner_prod_smult_right[of vn n _ k] by (simp add: \<open>vn \<in> carrier_vec n\<close>)
  also have "... = Complex_Matrix.inner_prod (U *\<^sub>v vn) (U *\<^sub>v vn)" 
    using \<open>eigenvector U vn k\<close> unfolding eigenvector_def by simp
  also have "... =  
    Complex_Matrix.inner_prod (Complex_Matrix.adjoint U *\<^sub>v (U *\<^sub>v vn)) vn" 
    using adjoint_def_alter[of "U *\<^sub>v vn" n vn n U] assms
    by (metis \<open>eigenvector U vn k\<close> carrier_matD(1) carrier_vec_dim_vec dim_mult_mat_vec 
        eigenvector_def)
  also have "... = Complex_Matrix.inner_prod vn vn"
  proof -
    have "Complex_Matrix.adjoint U *\<^sub>v (U *\<^sub>v vn) = (Complex_Matrix.adjoint U * U) *\<^sub>v vn"
      using assms
      by (metis \<open>eigenvector U vn k\<close> adjoint_dim assoc_mult_mat_vec carrier_matD(1) eigenvector_def)
    also have "... = vn" using assms unfolding unitary_def inverts_mat_def
      by (metis \<open>eigenvector U vn k\<close> assms(1) eigenvector_def one_mult_mat_vec unitary_simps(1))
    finally show ?thesis by simp
  qed
  also have "... = 1" using \<open>vn = vec_normalize v\<close> \<open>eigenvector U v k\<close> eigenvector_def 
      normalized_vec_norm by blast
  finally show ?thesis .
qed

lemma outer_prod_smult_left:
  fixes v::"complex Matrix.vec"
  shows "outer_prod (a \<cdot>\<^sub>v v) w = a \<cdot>\<^sub>m outer_prod v w" 
proof -
  define paw where "paw = outer_prod (a \<cdot>\<^sub>v v) w"
  define apw where "apw = a \<cdot>\<^sub>m outer_prod v w"
  have "paw = apw"
  proof
    have "dim_row paw = dim_vec v" unfolding paw_def using outer_prod_dim
      by (metis carrier_matD(1) carrier_vec_dim_vec index_smult_vec(2))
    also have "... = dim_row apw" unfolding apw_def using outer_prod_dim
      by (metis carrier_matD(1) carrier_vec_dim_vec index_smult_mat(2))
    finally show dr: "dim_row paw = dim_row apw" .
    have "dim_col paw = dim_vec w" unfolding paw_def using outer_prod_dim
      using carrier_vec_dim_vec by blast
    also have "... = dim_col apw" unfolding apw_def using outer_prod_dim
      by (metis apw_def carrier_matD(2) carrier_vec_dim_vec smult_carrier_mat)
    finally show dc: "dim_col paw = dim_col apw" .
    show "\<And>i j. i < dim_row apw \<Longrightarrow> j < dim_col apw \<Longrightarrow> paw $$ (i, j) = apw $$ (i, j)"
    proof -
      fix i j
      assume  "i < dim_row apw" and "j < dim_col apw" note ij = this
      hence "paw $$ (i,j) = a * (Matrix.vec_index v i) * cnj (Matrix.vec_index w j)" 
        using dr dc unfolding  paw_def outer_prod_def by simp
      also have "... = apw $$ (i,j)" using dr dc ij unfolding apw_def outer_prod_def by simp
      finally show "paw $$ (i, j) = apw $$ (i, j)" .
    qed
  qed
  thus ?thesis unfolding paw_def apw_def by simp
qed

lemma outer_prod_smult_right:
  fixes v::"complex Matrix.vec"
  shows "outer_prod v (a \<cdot>\<^sub>v w) = (conjugate a) \<cdot>\<^sub>m outer_prod v w" 
proof -
  define paw where "paw = outer_prod v (a \<cdot>\<^sub>v w)"
  define apw where "apw = (conjugate a) \<cdot>\<^sub>m outer_prod v w"
  have "paw = apw"
  proof
    have "dim_row paw = dim_vec v" unfolding paw_def using outer_prod_dim
      by (metis carrier_matD(1) carrier_vec_dim_vec)
    also have "... = dim_row apw" unfolding apw_def using outer_prod_dim
      by (metis carrier_matD(1) carrier_vec_dim_vec index_smult_mat(2))
    finally show dr: "dim_row paw = dim_row apw" .
    have "dim_col paw = dim_vec w" unfolding paw_def using outer_prod_dim
      using carrier_vec_dim_vec by (metis carrier_matD(2) index_smult_vec(2)) 
    also have "... = dim_col apw" unfolding apw_def using outer_prod_dim
      by (metis apw_def carrier_matD(2) carrier_vec_dim_vec smult_carrier_mat)
    finally show dc: "dim_col paw = dim_col apw" .
    show "\<And>i j. i < dim_row apw \<Longrightarrow> j < dim_col apw \<Longrightarrow> paw $$ (i, j) = apw $$ (i, j)"
    proof -
      fix i j
      assume  "i < dim_row apw" and "j < dim_col apw" note ij = this
      hence "paw $$ (i,j) = (conjugate a) * (Matrix.vec_index v i) * cnj (Matrix.vec_index w j)" 
        using dr dc unfolding  paw_def outer_prod_def by simp
      also have "... = apw $$ (i,j)" using dr dc ij unfolding apw_def outer_prod_def by simp
      finally show "paw $$ (i, j) = apw $$ (i, j)" .
    qed
  qed
  thus ?thesis unfolding paw_def apw_def by simp
qed

lemma outer_prod_add_left:
  fixes v::"complex Matrix.vec"
  assumes "dim_vec v = dim_vec x"
  shows "outer_prod (v + x) w = outer_prod v w + (outer_prod x w)" 
proof -
  define paw where "paw = outer_prod (v+x) w"
  define apw where "apw = outer_prod v w + (outer_prod x w)"
  have "paw = apw"
  proof
    have rv: "dim_row paw = dim_vec v" unfolding paw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec index_add_vec(2) paw_def)
    also have "... = dim_row apw" unfolding apw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec index_add_mat(2))
    finally show dr: "dim_row paw = dim_row apw" .
    have cw: "dim_col paw = dim_vec w" unfolding paw_def using outer_prod_dim assms
      using carrier_vec_dim_vec by (metis carrier_matD(2)) 
    also have "... = dim_col apw" unfolding apw_def using outer_prod_dim
      by (metis apw_def carrier_matD(2) carrier_vec_dim_vec add_carrier_mat)
    finally show dc: "dim_col paw = dim_col apw" .
    show "\<And>i j. i < dim_row apw \<Longrightarrow> j < dim_col apw \<Longrightarrow> paw $$ (i, j) = apw $$ (i, j)"
    proof -
      fix i j
      assume  "i < dim_row apw" and "j < dim_col apw" note ij = this
      hence "paw $$ (i,j) = (Matrix.vec_index v i + Matrix.vec_index x i) * 
        cnj (Matrix.vec_index w j)" 
        using dr dc unfolding  paw_def outer_prod_def by simp
      also have "... = Matrix.vec_index v i * cnj (Matrix.vec_index w j) + 
        Matrix.vec_index x i * cnj (Matrix.vec_index w j)"
        by (simp add: ring_class.ring_distribs(2))
      also have "... = (outer_prod v w) $$ (i,j) + (outer_prod x w) $$ (i,j)" 
        using rv cw dr dc ij assms unfolding outer_prod_def by auto
      also have "... = apw $$ (i,j)" using dr dc ij unfolding apw_def outer_prod_def by simp
      finally show "paw $$ (i, j) = apw $$ (i, j)" .
    qed
  qed
  thus ?thesis unfolding paw_def apw_def by simp
qed

lemma outer_prod_add_right:
  fixes v::"complex Matrix.vec"
  assumes "dim_vec w = dim_vec x"
  shows "outer_prod v (w + x) = outer_prod v w + (outer_prod v x)" 
proof -
  define paw where "paw = outer_prod v (w+x)"
  define apw where "apw = outer_prod v w + (outer_prod v x)"
  have "paw = apw"
  proof
    have rv: "dim_row paw = dim_vec v" unfolding paw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec index_add_vec(2) paw_def)
    also have "... = dim_row apw" unfolding apw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec index_add_mat(2))
    finally show dr: "dim_row paw = dim_row apw" .
    have cw: "dim_col paw = dim_vec w" unfolding paw_def using outer_prod_dim assms
      using carrier_vec_dim_vec
      by (metis carrier_matD(2) index_add_vec(2) paw_def) 
    also have "... = dim_col apw" unfolding apw_def using outer_prod_dim
      by (metis assms carrier_matD(2) carrier_vec_dim_vec index_add_mat(3))
    finally show dc: "dim_col paw = dim_col apw" .
    show "\<And>i j. i < dim_row apw \<Longrightarrow> j < dim_col apw \<Longrightarrow> paw $$ (i, j) = apw $$ (i, j)"
    proof -
      fix i j
      assume  "i < dim_row apw" and "j < dim_col apw" note ij = this
      hence "paw $$ (i,j) = Matrix.vec_index v i * 
        (cnj (Matrix.vec_index w j + (Matrix.vec_index x j)))" 
        using dr dc unfolding  paw_def outer_prod_def by simp
      also have "... = Matrix.vec_index v i * cnj (Matrix.vec_index w j) + 
        Matrix.vec_index v i * cnj (Matrix.vec_index x j)"
        by (simp add: ring_class.ring_distribs(1))
      also have "... = (outer_prod v w) $$ (i,j) + (outer_prod v x) $$ (i,j)" 
        using rv cw dr dc ij assms unfolding outer_prod_def by auto
      also have "... = apw $$ (i,j)" using dr dc ij unfolding apw_def outer_prod_def by simp
      finally show "paw $$ (i, j) = apw $$ (i, j)" .
    qed
  qed
  thus ?thesis unfolding paw_def apw_def by simp
qed

lemma outer_prod_minus_left:
  fixes v::"complex Matrix.vec"
  assumes "dim_vec v = dim_vec x"
  shows "outer_prod (v - x) w = outer_prod v w - (outer_prod x w)" 
proof -
  define paw where "paw = outer_prod (v-x) w"
  define apw where "apw = outer_prod v w - (outer_prod x w)"
  have "paw = apw"
  proof
    have rv: "dim_row paw = dim_vec v" unfolding paw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec index_minus_vec(2) paw_def)
    also have "... = dim_row apw" unfolding apw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec index_minus_mat(2))
    finally show dr: "dim_row paw = dim_row apw" .
    have cw: "dim_col paw = dim_vec w" unfolding paw_def using outer_prod_dim assms
      using carrier_vec_dim_vec by (metis carrier_matD(2)) 
    also have "... = dim_col apw" unfolding apw_def using outer_prod_dim
      by (metis apw_def carrier_matD(2) carrier_vec_dim_vec minus_carrier_mat)
    finally show dc: "dim_col paw = dim_col apw" .
    show "\<And>i j. i < dim_row apw \<Longrightarrow> j < dim_col apw \<Longrightarrow> paw $$ (i, j) = apw $$ (i, j)"
    proof -
      fix i j
      assume  "i < dim_row apw" and "j < dim_col apw" note ij = this
      hence "paw $$ (i,j) = (Matrix.vec_index v i - Matrix.vec_index x i) * 
        cnj (Matrix.vec_index w j)" 
        using dr dc unfolding  paw_def outer_prod_def by simp
      also have "... = Matrix.vec_index v i * cnj (Matrix.vec_index w j) - 
        Matrix.vec_index x i * cnj (Matrix.vec_index w j)"
        by (simp add: ring_class.ring_distribs)
      also have "... = (outer_prod v w) $$ (i,j) - (outer_prod x w) $$ (i,j)" 
        using rv cw dr dc ij assms unfolding outer_prod_def by auto
      also have "... = apw $$ (i,j)" using dr dc ij unfolding apw_def outer_prod_def by simp
      finally show "paw $$ (i, j) = apw $$ (i, j)" .
    qed
  qed
  thus ?thesis unfolding paw_def apw_def by simp
qed

lemma outer_prod_minus_right:
  fixes v::"complex Matrix.vec"
  assumes "dim_vec w = dim_vec x"
  shows "outer_prod v (w - x) = outer_prod v w - (outer_prod v x)" 
proof -
  define paw where "paw = outer_prod v (w-x)"
  define apw where "apw = outer_prod v w - (outer_prod v x)"
  have "paw = apw"
  proof
    have rv: "dim_row paw = dim_vec v" unfolding paw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec paw_def)
    also have "... = dim_row apw" unfolding apw_def using outer_prod_dim assms
      by (metis carrier_matD(1) carrier_vec_dim_vec index_minus_mat(2))
    finally show dr: "dim_row paw = dim_row apw" .
    have cw: "dim_col paw = dim_vec w" unfolding paw_def using outer_prod_dim assms
      using carrier_vec_dim_vec
      by (metis carrier_matD(2) index_minus_vec(2) paw_def) 
    also have "... = dim_col apw" unfolding apw_def using outer_prod_dim
      by (metis assms carrier_matD(2) carrier_vec_dim_vec index_minus_mat(3))
    finally show dc: "dim_col paw = dim_col apw" .
    show "\<And>i j. i < dim_row apw \<Longrightarrow> j < dim_col apw \<Longrightarrow> paw $$ (i, j) = apw $$ (i, j)"
    proof -
      fix i j
      assume  "i < dim_row apw" and "j < dim_col apw" note ij = this
      hence "paw $$ (i,j) = Matrix.vec_index v i * 
        (cnj (Matrix.vec_index w j - (Matrix.vec_index x j)))" 
        using dr dc unfolding  paw_def outer_prod_def by simp
      also have "... = Matrix.vec_index v i * cnj (Matrix.vec_index w j) - 
        Matrix.vec_index v i * cnj (Matrix.vec_index x j)"
        by (simp add: ring_class.ring_distribs)
      also have "... = (outer_prod v w) $$ (i,j) - (outer_prod v x) $$ (i,j)" 
        using rv cw dr dc ij assms unfolding outer_prod_def by auto
      also have "... = apw $$ (i,j)" using dr dc ij unfolding apw_def outer_prod_def by simp
      finally show "paw $$ (i, j) = apw $$ (i, j)" .
    qed
  qed
  thus ?thesis unfolding paw_def apw_def by simp
qed

lemma outer_minus_minus:
  fixes a::"complex Matrix.vec" 
  assumes "dim_vec a = dim_vec b"
  and "dim_vec u = dim_vec v"
  shows "outer_prod (a - b) (u - v) = outer_prod a u - outer_prod a v -
      outer_prod b u +  outer_prod b v"
proof -
  have "outer_prod (a - b) (u - v) = outer_prod a (u - v)
    - outer_prod b (u - v)" using  outer_prod_minus_left assms by simp 
  also have "... = outer_prod a u - outer_prod a v -
    outer_prod b (u - v)" using assms outer_prod_minus_right by simp  
  also have "... = outer_prod a u - outer_prod a v -
    (outer_prod b u - outer_prod b v)" using assms outer_prod_minus_right by simp  
  also have "...  = outer_prod a u - outer_prod a v -
    outer_prod b u +  outer_prod b v"  
  proof (rule mat_minus_minus)
    show "outer_prod b u \<in> carrier_mat (dim_vec b) (dim_vec u)" by simp
    show "outer_prod b v \<in> carrier_mat (dim_vec b) (dim_vec u)" using assms by simp
    show "outer_prod a u - outer_prod a v \<in> carrier_mat (dim_vec b) (dim_vec u)" using assms
      by (metis carrier_vecI minus_carrier_mat outer_prod_dim)
  qed
  finally show ?thesis .
qed

lemma  outer_trace_inner:
  assumes "A \<in> carrier_mat n n"
  and "dim_vec u = n"
and "dim_vec v = n"
  shows "Complex_Matrix.trace (outer_prod u v * A) = Complex_Matrix.inner_prod v (A *\<^sub>v u)"
proof -
 have "Complex_Matrix.trace (outer_prod u v * A) = Complex_Matrix.trace (A * outer_prod u v)"
  proof (rule trace_comm)
    show "A \<in> carrier_mat n n" using assms  by simp
    show "outer_prod u v \<in> carrier_mat n n" using  assms
      by (metis carrier_vec_dim_vec outer_prod_dim)
  qed
  also have "... = Complex_Matrix.inner_prod v (A *\<^sub>v u)" using trace_outer_prod_right[of A n u v]
    assms   carrier_vec_dim_vec  by metis
  finally show ?thesis .
qed

lemma zero_hermitian:
  shows "hermitian (0\<^sub>m n n)" unfolding hermitian_def
    by (metis adjoint_minus hermitian_def hermitian_one minus_r_inv_mat one_carrier_mat)

lemma  trace_1: 
  shows "Complex_Matrix.trace ((1\<^sub>m n)::complex Matrix.mat) =(n::complex)" using one_mat_def
  by (simp add: Complex_Matrix.trace_def Matrix.mat_def)

lemma  trace_add: 
  assumes "square_mat A"
  and "square_mat B"
  and "dim_row A = dim_row B"
  shows "Complex_Matrix.trace (A + B) = Complex_Matrix.trace A + Complex_Matrix.trace B" 
  using  assms by (simp add: Complex_Matrix.trace_def sum.distrib)

lemma bra_vec_carrier:
  shows "bra_vec v \<in> carrier_mat 1 (dim_vec v)"
proof -
  have "dim_row (ket_vec v) = dim_vec v" unfolding ket_vec_def by simp
  thus ?thesis using bra_bra_vec[of v] bra_def[of "ket_vec v"] by simp
qed

lemma mat_mult_ket_carrier:
  assumes "A\<in> carrier_mat n m"
shows "A * |v\<rangle> \<in> carrier_mat n 1" using assms
      by (metis bra_bra_vec bra_vec_carrier carrier_matD(1) carrier_matI dagger_of_ket_is_bra 
          dim_row_of_dagger index_mult_mat(2) index_mult_mat(3)) 

lemma mat_mult_ket:
  assumes "A \<in> carrier_mat n m"
and "dim_vec v = m"
shows "A * |v\<rangle> = |A *\<^sub>v v\<rangle>"
proof -
  have rn: "dim_row (A * |v\<rangle>) = n" unfolding times_mat_def using assms by simp
  have co: "dim_col |A *\<^sub>v v\<rangle> = 1" using assms unfolding ket_vec_def by simp
  have cov: "dim_col |v\<rangle> = 1" using assms unfolding ket_vec_def by simp
  have er: "dim_row (A * |v\<rangle>) = dim_row |A *\<^sub>v v\<rangle>" using assms
    by (metis bra_bra_vec bra_vec_carrier carrier_matD(2) dagger_of_ket_is_bra dim_col_of_dagger 
        dim_mult_mat_vec index_mult_mat(2)) 
  have ec: "dim_col (A * |v\<rangle>) = dim_col |A *\<^sub>v v\<rangle>" using assms
    by (metis carrier_matD(2) index_mult_mat(3) mat_mult_ket_carrier)
  {
    fix i::nat 
    fix j::nat
    assume "i < n"
    and "j < 1"
    hence "j = 0" by simp
    have "(A * |v\<rangle>) $$ (i,0) = Matrix.scalar_prod (Matrix.row A i) (Matrix.col |v\<rangle> 0)" 
      using times_mat_def[of A] \<open>i < n\<close> rn cov by simp
    also have "... = Matrix.scalar_prod (Matrix.row A i) v"  using ket_vec_col  by simp
    also have "... =  |A *\<^sub>v v\<rangle> $$ (i,j)" unfolding mult_mat_vec_def
      using \<open>i < n\<close> \<open>j = 0\<close> assms(1) by auto
  } note idx = this
  have "A * |v\<rangle> = Matrix.mat n 1 (\<lambda>(i, j). Matrix.scalar_prod (Matrix.row A i) (Matrix.col |v\<rangle> j))" 
    using assms unfolding times_mat_def ket_vec_def by simp
  also have "... = |A *\<^sub>v v\<rangle>" using er ec idx rn co by auto
  finally show ?thesis .
qed

lemma unitary_density:
  assumes "density_operator R"
  and "unitary U"
  and "R\<in> carrier_mat n n"
  and "U\<in> carrier_mat n n"
shows "density_operator (U * R * (Complex_Matrix.adjoint U))" unfolding density_operator_def
proof (intro conjI)
  show "Complex_Matrix.positive (U * R * Complex_Matrix.adjoint U)" 
  proof (rule positive_close_under_left_right_mult_adjoint)
    show "U \<in> carrier_mat n n" using assms by simp
    show "R \<in> carrier_mat n n" using assms by simp
    show "Complex_Matrix.positive R" using assms unfolding density_operator_def by simp
  qed
  have "Complex_Matrix.trace (U * R * Complex_Matrix.adjoint U) = 
    Complex_Matrix.trace (Complex_Matrix.adjoint U * U * R)" 
    using trace_comm[of "U * R" n "Complex_Matrix.adjoint U"] assms
    by (metis adjoint_dim  mat_assoc_test(10))
  also have "... = Complex_Matrix.trace R" using assms by simp 
  also have "... = 1" using assms unfolding density_operator_def by simp
  finally show "Complex_Matrix.trace (U * R * Complex_Matrix.adjoint U) = 1" .
qed


subsection \<open>Tensor product complements\<close>

lemma tensor_vec_dim[simp]:
  shows "dim_vec (tensor_vec u v) = dim_vec u * (dim_vec v)" 
proof -
  have "length (mult.vec_vec_Tensor (*) (list_of_vec u) (list_of_vec v)) = 
    length (list_of_vec u) * length (list_of_vec v)" 
    using  mult.vec_vec_Tensor_length[of "1::real" "(*)" "list_of_vec u" "list_of_vec v"]
    by (simp add: Matrix_Tensor.mult_def)  
  thus ?thesis unfolding tensor_vec_def by simp
qed

lemma index_tensor_vec[simp]:
  assumes "0 < dim_vec v" 
  and "i < dim_vec u * dim_vec v"
shows "vec_index (tensor_vec u v) i = 
  vec_index u (i div (dim_vec v)) * vec_index v (i mod dim_vec v)" 
proof -
  have m: "Matrix_Tensor.mult (1::complex) (*)" by (simp add: Matrix_Tensor.mult_def) 
  have "length (list_of_vec v) = dim_vec v" using assms by simp
  hence "vec_index (tensor_vec u v) i = (*) (vec_index u (i div dim_vec v)) (vec_index v (i mod dim_vec v))"
    unfolding tensor_vec_def using mult.vec_vec_Tensor_elements assms m
    by (metis (mono_tags, lifting) length_greater_0_conv length_list_of_vec list_of_vec_index 
        mult.vec_vec_Tensor_elements vec_of_list_index)
  thus ?thesis by simp
qed

lemma  outer_prod_tensor_comm:
  fixes a::"complex Matrix.vec"
  fixes u::"complex Matrix.vec"
  assumes "0 < dim_vec a"
  and "0 < dim_vec b"
shows "outer_prod (tensor_vec u v) (tensor_vec a b) = tensor_mat (outer_prod u a) (outer_prod v b)"
proof -
  define ot where "ot = outer_prod (tensor_vec u v) (tensor_vec a b)"
  define to where "to = tensor_mat (outer_prod u a) (outer_prod v b)"
  define dv where "dv = dim_vec v"
  define db where "db = dim_vec b"
  have "ot = to"
  proof
    have ro: "dim_row ot = dim_vec u * dim_vec v" unfolding ot_def outer_prod_def by simp
    have "dim_row to = dim_row (outer_prod u a) * dim_row (outer_prod v b)" 
      unfolding to_def by simp 
    also have "... = dim_vec u * dim_vec v" using outer_prod_dim
      by (metis carrier_matD(1) carrier_vec_dim_vec) 
    finally have rt: "dim_row to = dim_vec u * dim_vec v" .
    show "dim_row ot = dim_row to" using ro rt by simp
    have co: "dim_col ot = dim_vec a * dim_vec b" unfolding ot_def outer_prod_def by simp
    have "dim_col to = dim_col (outer_prod u a) * dim_col (outer_prod v b)" unfolding to_def by simp
    also have "... = dim_vec a * dim_vec b" using outer_prod_dim
      by (metis carrier_matD(2) carrier_vec_dim_vec)
    finally have ct: "dim_col to = dim_vec a * dim_vec b" .
    show "dim_col ot = dim_col to" using co ct by simp
    show "\<And>i j. i < dim_row to \<Longrightarrow> j < dim_col to \<Longrightarrow> ot $$ (i, j) = to $$ (i, j)"
    proof -
      fix i j
      assume "i < dim_row to" and "j < dim_col to" note ij = this
      have "ot $$ (i,j) = Matrix.vec_index (tensor_vec u v) i * 
        (conjugate (Matrix.vec_index (tensor_vec a b) j))"
        unfolding ot_def outer_prod_def using ij rt ct by simp
      also have "... = vec_index u (i div dv) * vec_index v (i mod dv)  * 
        (conjugate (Matrix.vec_index (tensor_vec a b) j))" using ij rt assms 
        unfolding dv_def
        by (metis index_tensor_vec less_nat_zero_code nat_0_less_mult_iff neq0_conv)
      also have "... = vec_index u (i div dv) * vec_index v (i mod dv)  *
        (conjugate (vec_index a (j div db) * vec_index b (j mod db)))" using ij ct assms 
        unfolding db_def by simp
      also have "... = vec_index u (i div dv) * vec_index v (i mod dv)  *
        (conjugate (vec_index a (j div db))) * (conjugate (vec_index b (j mod db)))" by simp
      also have "... = vec_index u (i div dv) * (conjugate (vec_index a (j div db))) * 
        vec_index v (i mod dv) * (conjugate (vec_index b (j mod db)))" by simp
      also have "... = (outer_prod u a) $$ (i div dv, j div db) * 
        vec_index v (i mod dv) * (conjugate (vec_index b (j mod db)))" 
      proof -
        have "i div dv < dim_vec u" using ij rt unfolding dv_def
          by (simp add: less_mult_imp_div_less)
        moreover have "j div db < dim_vec a" using ij ct assms unfolding db_def
          by (simp add: less_mult_imp_div_less)
        ultimately have "vec_index u (i div dv) * (conjugate (vec_index a (j div db))) = 
          (outer_prod u a) $$ (i div dv, j div db)" unfolding outer_prod_def by simp
        thus ?thesis by simp
      qed
      also have "... = (outer_prod u a) $$ (i div dv, j div db) * 
        (outer_prod v b) $$ (i mod dv, j mod db)" 
      proof -
        have "i mod dv < dim_vec v" using ij rt unfolding dv_def
          using assms mod_less_divisor
          by (metis less_nat_zero_code mult.commute neq0_conv times_nat.simps(1))
        moreover have "j mod db < dim_vec b" using ij ct assms unfolding db_def
          by (simp add: less_mult_imp_div_less)
        ultimately have "vec_index v (i mod dv) * (conjugate (vec_index b (j mod db))) = 
          (outer_prod v b) $$ (i mod dv, j mod db)" unfolding outer_prod_def by simp
        thus ?thesis by simp
      qed
      also have "... = tensor_mat (outer_prod u a) (outer_prod v b) $$ (i, j)" 
      proof (rule index_tensor_mat[symmetric])
        show "dim_row (outer_prod u a) = dim_vec u" unfolding outer_prod_def by simp
        show "dim_row (outer_prod v b) = dv" unfolding outer_prod_def dv_def by simp
        show "dim_col (outer_prod v b) = db" unfolding db_def outer_prod_def by simp
        show "i < dim_vec u * dv" unfolding dv_def using ij rt by simp
        show "dim_col (outer_prod u a) = dim_vec a" unfolding outer_prod_def by simp
        show "j < dim_vec a * db" unfolding db_def using ij ct by simp
        show "0 < dim_vec a" using assms by simp
        show "0 < db" unfolding db_def using assms by simp
      qed
      finally show "ot $$ (i, j) = to $$ (i, j)" unfolding to_def .
    qed
  qed
  thus ?thesis unfolding ot_def to_def by simp
qed

lemma tensor_mat_adjoint:
  assumes "m1 \<in> carrier_mat r1 c1"
    and "m2 \<in> carrier_mat r2 c2"
    and "0 < c1"
    and "0 < c2"
and "0 < r1"
and "0 < r2"
  shows "Complex_Matrix.adjoint (tensor_mat m1 m2) = 
  tensor_mat (Complex_Matrix.adjoint m1) (Complex_Matrix.adjoint m2)"
  apply (rule eq_matI, auto)
proof -
  fix i j
  assume "i < dim_col m1 * dim_col m2" and "j < dim_row m1 * dim_row m2" note ij = this
  have c1: "dim_col m1 = c1" using assms by simp
  have r1: "dim_row m1 = r1" using assms by simp
  have c2: "dim_col m2 = c2" using assms by simp
  have r2: "dim_row m2 = r2" using assms by simp
  have "Complex_Matrix.adjoint (m1 \<Otimes> m2) $$ (i, j) = conjugate ((m1 \<Otimes> m2) $$ (j, i))" 
    using  ij by (simp add: adjoint_eval) 
  also have "... = conjugate (m1 $$ (j div r2, i div c2) * m2 $$ (j mod r2, i mod c2))" 
  proof -
    have "(m1 \<Otimes> m2) $$ (j, i) = m1 $$ (j div r2, i div c2) * m2 $$ (j mod r2, i mod c2)"
    proof (rule index_tensor_mat[of m1 r1 c1 m2 r2 c2 j i], (auto simp add: assms ij c1 c2 r1 r2))
      show "j < r1 * r2" using ij r1 r2 by simp
      show "i < c1 * c2" using ij c1 c2 by simp
    qed
    thus ?thesis by simp
  qed
  also have "... = conjugate (m1 $$ (j div r2, i div c2)) * conjugate ( m2 $$ (j mod r2, i mod c2))" 
    by simp
  also have "... = (Complex_Matrix.adjoint m1) $$ (i div c2, j div r2) * 
    conjugate ( m2 $$ (j mod r2, i mod c2))"
    by (metis adjoint_eval c2 ij less_mult_imp_div_less r2)
  also have "... = (Complex_Matrix.adjoint m1) $$ (i div c2, j div r2) *
    (Complex_Matrix.adjoint m2) $$ (i mod c2, j mod r2)"
    by (metis Euclidean_Division.div_eq_0_iff adjoint_eval assms(4) bits_mod_div_trivial c2 
        gr_implies_not_zero ij(2) mult_not_zero r2)
  also have "... = (tensor_mat (Complex_Matrix.adjoint m1) (Complex_Matrix.adjoint m2)) $$ (i,j)"
  proof (rule index_tensor_mat[symmetric], (simp add: ij c1 c2 r1 r2) +)
    show "i < c1 * c2" using ij c1 c2 by simp
    show "j < r1 * r2" using ij r1 r2 by simp
    show "0 < r1" using assms by simp
    show "0 < r2" using assms by simp
  qed
  finally show "Complex_Matrix.adjoint (m1 \<Otimes> m2) $$ (i, j) =
           (Complex_Matrix.adjoint m1 \<Otimes> Complex_Matrix.adjoint m2) $$ (i, j)" .
qed

lemma index_tensor_mat':
  assumes "0 < dim_col A"
  and "0 < dim_col B"
  and "i < dim_row A * dim_row B"
  and "j < dim_col A * dim_col B"
  shows "(A \<Otimes> B) $$ (i, j) = 
    A $$ (i div (dim_row B), j div (dim_col B)) * B $$ (i mod (dim_row B), j mod (dim_col B))"
  by (rule index_tensor_mat, (simp add: assms)+)

lemma tensor_mat_carrier:
  shows "tensor_mat U V \<in> carrier_mat (dim_row U * dim_row V) (dim_col U * dim_col V)" by auto

lemma tensor_mat_id:
  assumes "0 < d1"
  and "0 < d2"
shows "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) = 1\<^sub>m (d1 * d2)"
proof (rule eq_matI, auto)
  show "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) $$ (i, i) = 1" if "i < (d1 * d2)" for i
    using that index_tensor_mat'[of "1\<^sub>m d1" "1\<^sub>m d2"]   
    by (simp add: assms less_mult_imp_div_less)  
next
  show "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) $$ (i, j) = 0" if "i < d1 * d2" "j < d1 * d2" "i \<noteq> j" for i j
    using that index_tensor_mat[of "1\<^sub>m d1" d1 d1 "1\<^sub>m d2" d2 d2 i j]
    by (metis assms(1) assms(2) index_one_mat(1) index_one_mat(2) index_one_mat(3) 
        less_mult_imp_div_less mod_less_divisor mult_div_mod_eq mult_not_zero)
qed

lemma tensor_mat_hermitian:
  assumes "A \<in> carrier_mat n n"
  and "B \<in> carrier_mat n' n'"
  and "0 < n"
  and "0 < n'"
  and "hermitian A"
  and "hermitian B"
  shows "hermitian (tensor_mat A B)" using assms by (metis hermitian_def tensor_mat_adjoint)

lemma  tensor_mat_unitary:
  assumes "Complex_Matrix.unitary U"
  and "Complex_Matrix.unitary V"
and "0 < dim_row U"
and "0 < dim_row V"
shows "Complex_Matrix.unitary (tensor_mat U V)" 
proof -
  define UI where "UI = tensor_mat U V"
  have "Complex_Matrix.adjoint UI = 
    tensor_mat (Complex_Matrix.adjoint U) (Complex_Matrix.adjoint V)" unfolding UI_def
  proof (rule tensor_mat_adjoint)
    show "U \<in> carrier_mat (dim_row U) (dim_row U)" using assms unfolding Complex_Matrix.unitary_def 
      by simp
    show "V \<in> carrier_mat (dim_row V) (dim_row V)" using assms unfolding Complex_Matrix.unitary_def 
      by simp
    show "0 < dim_row V" using assms by simp
    show "0 < dim_row U" using assms by simp
    show "0 < dim_row V" using assms by simp
    show "0 < dim_row U" using assms by simp
  qed
  hence "UI * (Complex_Matrix.adjoint UI) = 
    tensor_mat (U * Complex_Matrix.adjoint U) (V * Complex_Matrix.adjoint V)"
    using mult_distr_tensor[of U "Complex_Matrix.adjoint U" "V" "Complex_Matrix.adjoint V"]
    unfolding UI_def
    by (metis (no_types, lifting) Complex_Matrix.unitary_def adjoint_dim_col adjoint_dim_row 
        assms carrier_matD(2) )    
  also have "... = tensor_mat (1\<^sub>m (dim_row U)) (1\<^sub>m (dim_row V))" using assms unitary_simps(2)
    by (metis Complex_Matrix.unitary_def)
  also have "... = (1\<^sub>m (dim_row U * dim_row V))" using tensor_mat_id assms by simp
  finally have "UI * (Complex_Matrix.adjoint UI) = (1\<^sub>m (dim_row U * dim_row V))" .
  hence "inverts_mat UI (Complex_Matrix.adjoint UI)" unfolding inverts_mat_def UI_def by simp
  thus ?thesis using assms unfolding Complex_Matrix.unitary_def UI_def
    by (metis carrier_matD(2) carrier_matI dim_col_tensor_mat dim_row_tensor_mat)
qed


subsection \<open>Fixed carrier matrices locale\<close>

text \<open>We define a locale for matrices with a fixed number of rows and columns, and define a
finite sum operation on this locale. The \verb+Type_To_Sets+ transfer tools then permits to obtain
lemmata on the locale for free. \<close>

locale fixed_carrier_mat =
  fixes fc_mats::"'a::field Matrix.mat set" 
  fixes dimR dimC
  assumes fc_mats_carrier: "fc_mats = carrier_mat dimR dimC"
begin

sublocale semigroup_add_on_with fc_mats "(+)"
proof (unfold_locales)
  show "\<And>a b. a \<in> fc_mats \<Longrightarrow> b \<in> fc_mats \<Longrightarrow> a + b \<in> fc_mats" using fc_mats_carrier by simp
  show "\<And>a b c. a \<in> fc_mats \<Longrightarrow> b \<in> fc_mats \<Longrightarrow> c \<in> fc_mats \<Longrightarrow> a + b + c = a + (b + c)" 
    using fc_mats_carrier by simp
qed

sublocale ab_semigroup_add_on_with fc_mats "(+)"
proof (unfold_locales)
  show "\<And>a b. a \<in> fc_mats \<Longrightarrow> b \<in> fc_mats \<Longrightarrow> a + b = b + a" using fc_mats_carrier 
    by (simp add: comm_add_mat) 
qed

sublocale comm_monoid_add_on_with fc_mats "(+)" "0\<^sub>m dimR dimC"
proof (unfold_locales)
  show "0\<^sub>m dimR dimC \<in> fc_mats" using fc_mats_carrier by simp
  show "\<And>a. a \<in> fc_mats \<Longrightarrow> 0\<^sub>m dimR dimC + a = a" using fc_mats_carrier by simp
qed

sublocale ab_group_add_on_with fc_mats "(+)" "0\<^sub>m dimR dimC" "(-)" "uminus"
proof (unfold_locales)
  show "\<And>a. a \<in> fc_mats \<Longrightarrow> - a + a = 0\<^sub>m dimR dimC" using fc_mats_carrier by simp
  show "\<And>a b. a \<in> fc_mats \<Longrightarrow> b \<in> fc_mats \<Longrightarrow> a - b = a + - b" using fc_mats_carrier
    by (simp add: add_uminus_minus_mat)
  show "\<And>a. a \<in> fc_mats \<Longrightarrow> - a \<in> fc_mats" using fc_mats_carrier by simp
qed
end

lemma (in fixed_carrier_mat) smult_mem:
  assumes "A \<in> fc_mats"
  shows "a \<cdot>\<^sub>m A \<in> fc_mats" using fc_mats_carrier assms by auto

definition (in fixed_carrier_mat) sum_mat where
"sum_mat A I = sum_with (+) (0\<^sub>m dimR dimC) A I"

lemma (in fixed_carrier_mat) sum_mat_empty[simp]:
  shows "sum_mat A {} = 0\<^sub>m dimR dimC" unfolding sum_mat_def by simp

lemma (in fixed_carrier_mat) sum_mat_carrier:
  shows "(\<And>i. i \<in> I \<Longrightarrow> (A i)\<in> fc_mats) \<Longrightarrow> sum_mat A I \<in> carrier_mat dimR dimC" 
  unfolding sum_mat_def using sum_with_mem[of A I] fc_mats_carrier by auto

lemma (in fixed_carrier_mat) sum_mat_insert:
  assumes "A x \<in> fc_mats" "A ` I \<subseteq> fc_mats"
    and A: "finite I" and x: "x \<notin> I"
  shows "sum_mat A (insert x I) = A x + sum_mat A I" unfolding sum_mat_def
  using assms sum_with_insert[of A x I] by simp


subsection \<open>A locale for square matrices\<close>

locale cpx_sq_mat = fixed_carrier_mat "fc_mats::complex Matrix.mat set" for fc_mats +
  assumes dim_eq: "dimR = dimC"
  and npos: "0 < dimR"

lemma (in cpx_sq_mat) one_mem:
  shows "1\<^sub>m dimR \<in> fc_mats" using fc_mats_carrier dim_eq by simp

lemma (in cpx_sq_mat) square_mats:
  assumes "A \<in> fc_mats"
  shows "square_mat A" using fc_mats_carrier dim_eq assms by simp

lemma (in cpx_sq_mat) cpx_sq_mat_mult:
  assumes "A \<in> fc_mats"
  and "B \<in> fc_mats"
shows "A * B \<in> fc_mats"
proof -
  have "dim_row (A * B) = dimR" using assms fc_mats_carrier by simp
  moreover have "dim_col (A * B) = dimR" using assms fc_mats_carrier dim_eq by simp
  ultimately show ?thesis using fc_mats_carrier carrier_mat_def dim_eq by auto
qed

lemma (in cpx_sq_mat) sum_mat_distrib_left:
  shows "finite I \<Longrightarrow> R\<in> fc_mats \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (A i)\<in> fc_mats) \<Longrightarrow> 
    sum_mat (\<lambda>i. R * (A i)) I = R * (sum_mat A I)"
proof (induct rule: finite_induct)
  case empty
  hence a: "sum_mat (\<lambda>i. R * (A i)) {} = 0\<^sub>m dimR dimC" unfolding sum_mat_def by simp 
  have "sum_mat A {} = 0\<^sub>m dimR dimC" unfolding sum_mat_def by simp
  hence "R * (sum_mat A {}) = 0\<^sub>m dimR dimC" using  fc_mats_carrier
      right_mult_zero_mat[of R dimR dimC dimC] empty dim_eq by simp
  thus ?case using a by simp
next
  case (insert x F)
  hence "sum_mat (\<lambda>i. R * A i) (insert x F) = R * (A x) + sum_mat (\<lambda>i. R * A i) F"  
    using sum_mat_insert[of "\<lambda>i. R * A i" x F] by (simp add: image_subsetI fc_mats_carrier dim_eq) 
  also have "... = R * (A x) + R * (sum_mat A F)" using insert by simp
  also have "... = R * (A x + (sum_mat A F))"
    by (metis dim_eq fc_mats_carrier insert.prems(1) insert.prems(2) insertCI mult_add_distrib_mat 
        sum_mat_carrier)
  also have "... = R * sum_mat A (insert x F)" 
  proof -
    have "A x + (sum_mat A F) = sum_mat A (insert x F)" 
      by (rule sum_mat_insert[symmetric], (auto simp add: insert))
    thus ?thesis by simp
  qed
  finally show ?case .
qed

lemma (in cpx_sq_mat) sum_mat_distrib_right:
  shows "finite I \<Longrightarrow> R\<in> fc_mats \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (A i)\<in> fc_mats) \<Longrightarrow> 
    sum_mat (\<lambda>i. (A i) * R) I = (sum_mat A I) * R"
proof (induct rule: finite_induct)
  case empty
  hence a: "sum_mat (\<lambda>i. (A i) * R) {} = 0\<^sub>m dimR dimC" unfolding sum_mat_def by simp 
  have "sum_mat A {} = 0\<^sub>m dimR dimC" unfolding sum_mat_def by simp
  hence "(sum_mat A {}) * R = 0\<^sub>m dimR dimC" using  fc_mats_carrier right_mult_zero_mat[of R ] 
      dim_eq empty by simp
  thus ?case using a by simp
next
  case (insert x F)
  have a: "(\<lambda>i. A i * R) ` F \<subseteq> fc_mats" using insert cpx_sq_mat_mult
    by (simp add: image_subsetI) 
  have "A x * R \<in> fc_mats" using insert 
      by (metis insertI1 local.fc_mats_carrier mult_carrier_mat dim_eq)
  hence "sum_mat (\<lambda>i. A i * R) (insert x F) = (A x) * R + sum_mat (\<lambda>i. A i * R) F"  using insert a
    using sum_mat_insert[of "\<lambda>i. A i * R" x F]  by (simp add: image_subsetI local.fc_mats_carrier) 
  also have "... = (A x) * R + (sum_mat A F) * R" using insert by simp
  also have "... = (A x + (sum_mat A F)) * R" 
  proof (rule add_mult_distrib_mat[symmetric])
    show "A x \<in> carrier_mat dimR dimC" using insert fc_mats_carrier by simp
    show "sum_mat A F \<in> carrier_mat dimR dimC" using insert fc_mats_carrier sum_mat_carrier by blast
    show "R \<in> carrier_mat dimC dimC" using insert fc_mats_carrier dim_eq by simp
  qed    
  also have "... = sum_mat A (insert x F) * R" 
  proof -
    have "A x + (sum_mat A F) = sum_mat A (insert x F)" 
      by (rule sum_mat_insert[symmetric], (auto simp add: insert))
    thus ?thesis by simp
  qed
  finally show ?case .
qed

lemma (in cpx_sq_mat)  trace_sum_mat:
  fixes A::"'b \<Rightarrow> complex Matrix.mat"
  shows "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (A i)\<in> fc_mats) \<Longrightarrow>
  Complex_Matrix.trace (sum_mat A I) = (\<Sum> i\<in> I. Complex_Matrix.trace (A i))" unfolding sum_mat_def
proof (induct rule: finite_induct)
  case empty
  then show ?case using trace_zero dim_eq by simp
next
  case (insert x F)
  have "Complex_Matrix.trace (sum_with (+) (0\<^sub>m dimR dimC) A (insert x F)) = 
    Complex_Matrix.trace (A x + sum_with (+) (0\<^sub>m dimR dimC) A F)" 
    using sum_with_insert[of A x F] insert by (simp add: image_subset_iff dim_eq) 
  also have "... = Complex_Matrix.trace (A x) + 
    Complex_Matrix.trace (sum_with (+) (0\<^sub>m dimR dimC) A F)" using trace_add square_mats insert 
    by (metis carrier_matD(1) fc_mats_carrier image_subset_iff insert_iff sum_with_mem) 
  also have "... = Complex_Matrix.trace (A x) + (\<Sum> i\<in> F. Complex_Matrix.trace (A i))" 
      using insert by simp
    also have "... = (\<Sum> i\<in> (insert x F). Complex_Matrix.trace (A i))" 
      using sum_with_insert[of A x F] insert by (simp add: image_subset_iff) 
  finally show ?case .
qed

lemma (in cpx_sq_mat) cpx_sq_mat_smult:
  assumes "A \<in> fc_mats"
  shows "x  \<cdot>\<^sub>m A \<in> fc_mats"
  using assms fc_mats_carrier by auto

lemma (in cpx_sq_mat) mult_add_distrib_right:
  assumes "A\<in> fc_mats" "B\<in> fc_mats" "C\<in> fc_mats"
  shows "A * (B + C) = A * B + A * C"
  using assms fc_mats_carrier mult_add_distrib_mat dim_eq by simp

lemma (in cpx_sq_mat) mult_add_distrib_left:
  assumes "A\<in> fc_mats" "B\<in> fc_mats" "C\<in> fc_mats"
  shows "(B + C) * A = B * A + C * A"
  using assms fc_mats_carrier add_mult_distrib_mat dim_eq by simp

lemma (in cpx_sq_mat)  mult_sum_mat_distrib_left:
  shows "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (A i)\<in> fc_mats) \<Longrightarrow> B \<in> fc_mats \<Longrightarrow>
  (sum_mat (\<lambda>i. B * (A i)) I) = B * (sum_mat A I)" 
proof (induct rule: finite_induct)
  case empty
  hence "sum_mat A {} = 0\<^sub>m dimR dimC" using sum_mat_empty by simp
  hence "B * (sum_mat A {}) = 0\<^sub>m dimR dimC" using empty by (simp add: fc_mats_carrier dim_eq)
  moreover have "sum_mat (\<lambda>i. B * (A i)) {} = 0\<^sub>m dimR dimC" using sum_mat_empty[of "\<lambda>i. B * (A i)"] 
    by simp
  ultimately show ?case by simp
next
  case (insert x F)
  have "sum_mat (\<lambda>i. B * (A i)) (insert x F) = B * (A x) + sum_mat (\<lambda>i. B * (A i)) F"
    using sum_with_insert[of "\<lambda>i. B * (A i)" x F] insert
    by (simp add: image_subset_iff local.sum_mat_def cpx_sq_mat_mult)
  also have "... = B * (A x) + B * (sum_mat A F)" using insert by simp
  also have "... = B * (A x + (sum_mat A F))" 
  proof (rule mult_add_distrib_right[symmetric])
    show "B\<in> fc_mats" using insert by simp
    show "A x \<in> fc_mats" using insert by simp
    show "sum_mat A F \<in> fc_mats" using insert by (simp add: fc_mats_carrier sum_mat_carrier) 
  qed
  also have "... = B * (sum_mat A (insert x F))" using sum_with_insert[of A x F] insert 
    by (simp add: image_subset_iff sum_mat_def)
  finally show ?case .
qed

lemma (in cpx_sq_mat)  mult_sum_mat_distrib_right:
  shows "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (A i)\<in> fc_mats) \<Longrightarrow> B \<in> fc_mats \<Longrightarrow>
  (sum_mat (\<lambda>i. (A i) * B) I) = (sum_mat A I) * B" 
proof (induct rule: finite_induct)
  case empty
  hence "sum_mat A {} = 0\<^sub>m dimR dimC" using sum_mat_empty by simp
  hence "(sum_mat A {}) * B = 0\<^sub>m dimR dimC" using empty by (simp add: fc_mats_carrier dim_eq)
  moreover have "sum_mat (\<lambda>i. (A i) * B) {} = 0\<^sub>m dimR dimC" by simp
  ultimately show ?case by simp
next
  case (insert x F)
  have "sum_mat (\<lambda>i. (A i) * B) (insert x F) = (A x) * B + sum_mat (\<lambda>i. (A i) * B) F"
    using sum_with_insert[of "\<lambda>i. (A i) * B" x F] insert
    by (simp add: image_subset_iff local.sum_mat_def cpx_sq_mat_mult)
  also have "... = (A x) * B + (sum_mat A F) * B" using insert by simp
  also have "... = (A x + (sum_mat A F)) * B" 
  proof (rule mult_add_distrib_left[symmetric])
    show "B\<in> fc_mats" using insert by simp
    show "A x \<in> fc_mats" using insert by simp
    show "sum_mat A F \<in> fc_mats" using insert by (simp add: fc_mats_carrier sum_mat_carrier) 
  qed
  also have "... = (sum_mat A (insert x F)) * B" using sum_with_insert[of A x F] insert 
    by (simp add: image_subset_iff sum_mat_def)
  finally show ?case .
qed

lemma (in cpx_sq_mat) trace_sum_mat_mat_distrib:
  assumes "finite I"
and "\<And>i. i\<in> I \<Longrightarrow> B i \<in> fc_mats"
and "A\<in> fc_mats"
and "C \<in> fc_mats"
shows "(\<Sum> i\<in> I. Complex_Matrix.trace(A * (B i) * C)) = 
  Complex_Matrix.trace (A * (sum_mat B I) * C)" 
proof -
  have seq: "sum_mat (\<lambda>i. A * (B i) * C) I = A * (sum_mat B I) * C"
  proof -
    have "sum_mat (\<lambda>i. A * (B i) * C) I = (sum_mat (\<lambda>i. A * (B i)) I) * C"
    proof (rule mult_sum_mat_distrib_right)
      show "finite I" using assms by simp
      show "C\<in> fc_mats" using assms by simp
      show "\<And>i. i \<in> I \<Longrightarrow> A * B i \<in> fc_mats" using assms cpx_sq_mat_mult by simp
    qed
    moreover have "sum_mat (\<lambda>i. A * (B i)) I = A * (sum_mat B I)"
      by (rule mult_sum_mat_distrib_left, (auto simp add: assms))
    ultimately show "sum_mat (\<lambda>i. A * (B i) * C) I = A * (sum_mat B I)  * C" by simp
  qed
  have "(\<Sum> i\<in> I. Complex_Matrix.trace(A * (B i) * C)) = 
    Complex_Matrix.trace (sum_mat (\<lambda>i. A * (B i) * C) I)" 
  proof (rule trace_sum_mat[symmetric])
    show "finite I" using assms by simp
    fix i
    assume "i\<in> I"
    thus "A * B i * C \<in> fc_mats" using assms by (simp add: cpx_sq_mat_mult) 
  qed
  also have "... = Complex_Matrix.trace (A * (sum_mat B I) * C)" using seq by simp
  finally show ?thesis .
qed

definition (in cpx_sq_mat) zero_col where
"zero_col U = (\<lambda>i. if i < dimR then Matrix.col U i else 0\<^sub>v dimR)"

lemma (in cpx_sq_mat) zero_col_dim:
  assumes "U \<in> fc_mats"
  shows "dim_vec (zero_col U i) = dimR" using assms fc_mats_carrier unfolding zero_col_def by simp

lemma (in cpx_sq_mat) zero_col_col:
  assumes "i < dimR"
  shows "zero_col U i = Matrix.col U i" using assms unfolding zero_col_def by simp

lemma (in cpx_sq_mat) sum_mat_index:
  shows "finite I \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> (A i)\<in> fc_mats) \<Longrightarrow> i < dimR \<Longrightarrow> j < dimC \<Longrightarrow> 
    (sum_mat (\<lambda>k. (A k)) I) $$ (i,j) = (\<Sum> k\<in>I. (A k) $$ (i,j))"
proof (induct rule: finite_induct)
  case empty
  thus ?case unfolding sum_mat_def by simp
next
  case (insert x F)
  hence "(sum_mat (\<lambda>k. (A k)) (insert x F)) $$ (i,j) = 
    (A x + (sum_mat (\<lambda>k. (A k)) F)) $$ (i,j)" using insert sum_mat_insert[of A] 
    by (simp add: image_subsetI local.fc_mats_carrier) 
  also have "... = (A x) $$ (i,j) + (sum_mat (\<lambda>k. (A k)) F) $$ (i,j)" using insert       
      sum_mat_carrier[of F A] fc_mats_carrier by simp
  also have "... = (A x) $$ (i,j) + (\<Sum> k\<in>F. (A k) $$ (i,j))" using insert by simp
  also have "... = (\<Sum> k\<in>(insert x F). (A k) $$ (i,j))" using insert by simp
  finally show ?case .
qed

lemma (in cpx_sq_mat) sum_mat_cong:
  shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> A i = B i) \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow> 
    (\<And>i. i\<in> I \<Longrightarrow> B i \<in> fc_mats) \<Longrightarrow> sum_mat A I = sum_mat B I"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "sum_mat A (insert x F) = A x + sum_mat A F" using insert sum_mat_insert[of A]
    by (simp add:  image_subset_iff) 
  also have "... = B x + sum_mat B F" using insert by simp
  also have "... = sum_mat B (insert x F)" using insert sum_mat_insert[of B]
    by (simp add:  image_subset_iff) 
  finally show ?case .
qed

lemma (in cpx_sq_mat) smult_sum_mat:
  shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow> a \<cdot>\<^sub>m sum_mat A I = sum_mat (\<lambda>i. a  \<cdot>\<^sub>m (A i)) I"
proof (induct rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  have "a \<cdot>\<^sub>m sum_mat A (insert x F) = a \<cdot>\<^sub>m (A x + sum_mat A F)" using insert sum_mat_insert[of A]
    by (simp add:  image_subset_iff) 
  also have "... = a \<cdot>\<^sub>m A x + a \<cdot>\<^sub>m (sum_mat A F)" using insert
    by (metis add_smult_distrib_left_mat fc_mats_carrier insert_iff sum_mat_carrier)
  also have "... = a \<cdot>\<^sub>m  A x + sum_mat (\<lambda>i. a  \<cdot>\<^sub>m (A i)) F" using insert by simp
  also have "... = sum_mat (\<lambda>i. a  \<cdot>\<^sub>m (A i)) (insert x F)" using insert 
      sum_mat_insert[of "(\<lambda>i. a  \<cdot>\<^sub>m (A i))"] by (simp add: image_subset_iff cpx_sq_mat_smult)
  finally show ?case .
qed

lemma (in cpx_sq_mat) zero_sum_mat:
  shows "finite I \<Longrightarrow> sum_mat (\<lambda>i. ((0\<^sub>m dimR dimR)::complex Matrix.mat)) I = ((0\<^sub>m dimR dimR)::complex Matrix.mat)"
proof (induct rule:finite_induct)
  case empty
  then show ?case using dim_eq sum_mat_empty by auto
next
  case (insert x F)
  have "sum_mat (\<lambda>i. ((0\<^sub>m dimR dimR)::complex Matrix.mat)) (insert x F) = 
    0\<^sub>m dimR dimR + sum_mat (\<lambda>i. 0\<^sub>m dimR dimR) F" 
    using insert dim_eq zero_mem sum_mat_insert[of "\<lambda>i. ((0\<^sub>m dimR dimR)::complex Matrix.mat)"]
    by fastforce
  also have "... = ((0\<^sub>m dimR dimR)::complex Matrix.mat)" using insert by auto
  finally show ?case .
qed

lemma (in cpx_sq_mat) sum_mat_adjoint:
  shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow> 
    Complex_Matrix.adjoint (sum_mat A I) = sum_mat (\<lambda>i. Complex_Matrix.adjoint (A i)) I"
proof (induct rule: finite_induct)
  case empty
  then show ?case using zero_hermitian[of dimR] 
    by (metis (no_types) dim_eq hermitian_def sum_mat_empty)
next
  case (insert x F)
  have "Complex_Matrix.adjoint (sum_mat A (insert x F)) = 
    Complex_Matrix.adjoint (A x + sum_mat A F)" using insert sum_mat_insert[of A]
    by (simp add:  image_subset_iff) 
  also have "... = Complex_Matrix.adjoint (A x) + Complex_Matrix.adjoint (sum_mat A F)"
  proof (rule adjoint_add)
    show "A x \<in> carrier_mat dimR dimC" using  insert fc_mats_carrier  by simp
    show "sum_mat A F \<in> carrier_mat dimR dimC" using  insert fc_mats_carrier sum_mat_carrier[of F]  
      by simp
  qed
  also have "... = Complex_Matrix.adjoint (A x) + sum_mat (\<lambda>i. Complex_Matrix.adjoint (A i)) F"
    using insert by simp
  also have "... = sum_mat (\<lambda>i. Complex_Matrix.adjoint (A i)) (insert x F)"
  proof (rule sum_mat_insert[symmetric], (auto simp add: insert))
    show "Complex_Matrix.adjoint (A x) \<in> fc_mats" using insert fc_mats_carrier dim_eq 
      by (simp add: adjoint_dim) 
    show "\<And>i. i \<in> F \<Longrightarrow> Complex_Matrix.adjoint (A i) \<in> fc_mats" using insert fc_mats_carrier dim_eq 
      by (simp add: adjoint_dim) 
  qed 
  finally show ?case .
qed

lemma (in cpx_sq_mat) sum_mat_hermitian:
  assumes "finite I"
and "\<forall>i\<in> I. hermitian (A i)"
and "\<forall>i\<in> I. A i\<in> fc_mats"
shows "hermitian (sum_mat A I)" 
proof -
  have "Complex_Matrix.adjoint (sum_mat A I) = sum_mat (\<lambda>i. Complex_Matrix.adjoint (A i)) I"
    using assms sum_mat_adjoint[of I] by simp
  also have "... = sum_mat A I" 
  proof (rule sum_mat_cong, (auto simp add: assms))
    show "\<And>i. i \<in> I \<Longrightarrow> Complex_Matrix.adjoint (A i) = A i" using assms 
      unfolding hermitian_def by simp
    show "\<And>i. i \<in> I \<Longrightarrow> Complex_Matrix.adjoint (A i) \<in> fc_mats" using assms fc_mats_carrier dim_eq
      by (simp add: adjoint_dim) 
  qed
  finally show ?thesis unfolding hermitian_def .
qed

lemma (in cpx_sq_mat) sum_mat_positive:
shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> Complex_Matrix.positive (A i)) \<Longrightarrow> 
  (\<And>i. i \<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow> Complex_Matrix.positive (sum_mat A I)" 
proof (induct rule: finite_induct)
  case empty
  then show ?case using positive_zero[of dimR] by (metis (no_types) dim_eq sum_mat_empty)
next
  case (insert x F)
  hence "sum_mat A (insert x F) = A x + (sum_mat A F)" using sum_mat_insert[of A]
    by (simp add:  image_subset_iff) 
  moreover have "Complex_Matrix.positive (A x + (sum_mat A F))"
  proof (rule positive_add, (auto simp add: insert))
    show "A x \<in> carrier_mat dimR dimR" using insert fc_mats_carrier dim_eq by simp
    show "sum_mat A F \<in> carrier_mat dimR dimR" using insert sum_mat_carrier dim_eq
      by (metis insertCI)
  qed
  ultimately show "Complex_Matrix.positive (sum_mat A (insert x F))" by simp
qed

lemma (in cpx_sq_mat) sum_mat_left_ortho_zero:
  shows "finite I \<Longrightarrow> 
    (\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow> (B \<in> fc_mats) \<Longrightarrow>
    (\<And> i. i\<in> I \<Longrightarrow> A i * B = (0\<^sub>m dimR dimR)) \<Longrightarrow> 
    (sum_mat A I) * B = 0\<^sub>m dimR dimR"
proof (induct rule:finite_induct)
  case empty
  then show ?case using dim_eq
    by (metis  finite.intros(1) sum_mat_empty mult_sum_mat_distrib_right)
next
  case (insert x F)
  have "(sum_mat A (insert x F)) * B = 
    (A x + sum_mat A F) * B" using insert sum_mat_insert[of A] 
    by (simp add: image_subset_iff) 
  also have "... = A x * B + sum_mat A F * B"
  proof (rule add_mult_distrib_mat)
    show "A x \<in> carrier_mat dimR dimC" using insert fc_mats_carrier by simp
    show "sum_mat A F \<in> carrier_mat dimR dimC" using insert
      by (metis insert_iff local.fc_mats_carrier sum_mat_carrier) 
    show "B \<in> carrier_mat dimC dimR" using insert fc_mats_carrier dim_eq by simp
  qed
  also have "... = A x * B + (0\<^sub>m dimR dimR)"  using insert by simp
  also have "... = 0\<^sub>m dimR dimR" using insert by simp
  finally show ?case .
qed

lemma (in cpx_sq_mat) sum_mat_right_ortho_zero:
  shows "finite I \<Longrightarrow> 
    (\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow> (B \<in> fc_mats) \<Longrightarrow>
    (\<And> i. i\<in> I \<Longrightarrow> B * A i = (0\<^sub>m dimR dimR)) \<Longrightarrow> 
    B * (sum_mat A I)  = 0\<^sub>m dimR dimR"
proof (induct rule:finite_induct)
  case empty
  then show ?case using dim_eq
    by (metis  finite.intros(1) sum_mat_empty mult_sum_mat_distrib_left)
next
  case (insert x F)
  have "B * (sum_mat A (insert x F)) = 
    B * (A x + sum_mat A F)" using insert sum_mat_insert[of A] 
    by (simp add: image_subset_iff) 
  also have "... = B * A x + B * sum_mat A F"
  proof (rule mult_add_distrib_mat)
    show "A x \<in> carrier_mat dimR dimC" using insert fc_mats_carrier by simp
    show "sum_mat A F \<in> carrier_mat dimR dimC" using insert
      by (metis insert_iff local.fc_mats_carrier sum_mat_carrier) 
    show "B \<in> carrier_mat dimC dimR" using insert fc_mats_carrier dim_eq by simp
  qed
  also have "... = B * A x + (0\<^sub>m dimR dimR)"  using insert by simp
  also have "... = 0\<^sub>m dimR dimR" using insert by simp
  finally show ?case .
qed
 
lemma (in cpx_sq_mat) sum_mat_ortho_square:
  shows "finite I \<Longrightarrow> (\<And>i. i\<in> I \<Longrightarrow> ((A i)::complex Matrix.mat) * (A i) = A i) \<Longrightarrow> 
    (\<And>i. i\<in> I \<Longrightarrow> A i \<in> fc_mats) \<Longrightarrow>
    (\<And> i j. i\<in> I \<Longrightarrow> j\<in> I \<Longrightarrow> i\<noteq> j \<Longrightarrow> A i * (A j) = (0\<^sub>m dimR dimR)) \<Longrightarrow> 
    (sum_mat A I) * (sum_mat A I) = (sum_mat A I)"
proof (induct rule:finite_induct)
  case empty
  then show ?case using dim_eq
    by (metis fc_mats_carrier right_mult_zero_mat sum_mat_empty zero_mem)
next
  case (insert x F)
  have "(sum_mat A (insert x F)) * (sum_mat A (insert x F)) = 
    (A x + sum_mat A F) * (A x + sum_mat A F)" using insert sum_mat_insert[of A]
    by (simp add: \<open>\<And>i. i \<in> insert x F \<Longrightarrow> A i * A i = A i\<close> image_subset_iff) 
  also have "... = A x * (A x + sum_mat A F) + sum_mat A F * (A x + sum_mat A F)"
  proof (rule add_mult_distrib_mat)
    show "A x \<in> carrier_mat dimR dimC" using insert fc_mats_carrier by simp
    show "sum_mat A F \<in> carrier_mat dimR dimC" using insert
      by (metis insert_iff local.fc_mats_carrier sum_mat_carrier) 
    thus "A x + sum_mat A F \<in> carrier_mat dimC dimC" using insert dim_eq by simp
  qed
  also have "... = A x * A x + A x * (sum_mat A F) + sum_mat A F * (A x + sum_mat A F)" 
  proof -
    have "A x * (A x + sum_mat A F) = A x * A x + A x * (sum_mat A F)"  
      using dim_eq insert.prems(2) mult_add_distrib_right sum_mat_carrier
      by (metis fc_mats_carrier insertI1 subsetD subset_insertI)
    thus ?thesis by simp
  qed
  also have "... = A x * A x + A x * (sum_mat A F) + sum_mat A F * A x + 
    sum_mat A F * (sum_mat A F)" 
  proof -
    have "sum_mat A F * (A x + local.sum_mat A F) = 
      sum_mat A F * A x + local.sum_mat A F * local.sum_mat A F"
      using insert dim_eq add_assoc add_mem mult_add_distrib_right cpx_sq_mat_mult sum_mat_carrier
      by (metis fc_mats_carrier insertI1 subsetD subset_insertI)
    hence "A x * A x + A x * sum_mat A F + sum_mat A F * (A x + sum_mat A F) =
      A x * A x + A x * sum_mat A F + (sum_mat A F * A x + sum_mat A F * sum_mat A F)" by simp
    also have "... = A x * A x + A x * sum_mat A F + sum_mat A F * A x + sum_mat A F * sum_mat A F"     
    proof (rule assoc_add_mat[symmetric])
      show "A x * A x + A x * sum_mat A F \<in> carrier_mat dimR dimR" using sum_mat_carrier insert 
        dim_eq fc_mats_carrier by (metis add_mem cpx_sq_mat_mult insertCI)
      show "sum_mat A F * A x \<in> carrier_mat dimR dimR" using sum_mat_carrier insert 
        dim_eq fc_mats_carrier by (metis cpx_sq_mat_mult insertCI)
      show "sum_mat A F * sum_mat A F \<in> carrier_mat dimR dimR" using sum_mat_carrier insert 
        dim_eq fc_mats_carrier by (metis cpx_sq_mat_mult insertCI)
    qed
    finally show ?thesis .
  qed 
  also have "... = A x +  sum_mat A F"
  proof -
    have "A x * A x = A x" using insert by simp
    moreover have "sum_mat A F * sum_mat A F = sum_mat A F" using insert by simp
    moreover have "A x * (sum_mat A F) = 0\<^sub>m dimR dimR"
    proof -
      have "A x * (sum_mat A F) = sum_mat (\<lambda>i. A x * (A i)) F"
        by (rule sum_mat_distrib_left[symmetric], (simp add: insert)+)
      also have "... = sum_mat (\<lambda>i. 0\<^sub>m dimR dimR) F"
      proof (rule sum_mat_cong, (auto simp add: insert zero_mem))
        show "\<And>i. i \<in> F \<Longrightarrow> A x * A i = 0\<^sub>m dimR dimR" using insert by auto
        show "\<And>i. i \<in> F \<Longrightarrow> A x * A i \<in> fc_mats" using insert cpx_sq_mat_mult by auto
        show "\<And>i. i \<in> F \<Longrightarrow> 0\<^sub>m dimR dimR \<in> fc_mats" using zero_mem dim_eq by simp
      qed
      also have "... = 0\<^sub>m dimR dimR" using zero_sum_mat insert by simp
      finally show ?thesis .
    qed
    moreover have "sum_mat A F * A x = 0\<^sub>m dimR dimR" 
    proof -
      have "sum_mat A F * A x = sum_mat (\<lambda>i. A i * (A x)) F"
        by (rule sum_mat_distrib_right[symmetric], (simp add: insert)+)
      also have "... = sum_mat (\<lambda>i. 0\<^sub>m dimR dimR) F"
      proof (rule sum_mat_cong, (auto simp add: insert zero_mem))
        show "\<And>i. i \<in> F \<Longrightarrow> A i * A x = 0\<^sub>m dimR dimR" using insert by auto
        show "\<And>i. i \<in> F \<Longrightarrow> A i * A x \<in> fc_mats" using insert cpx_sq_mat_mult by auto
        show "\<And>i. i \<in> F \<Longrightarrow> 0\<^sub>m dimR dimR \<in> fc_mats" using zero_mem dim_eq by simp
      qed
      also have "... = 0\<^sub>m dimR dimR" using zero_sum_mat insert by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis using add_commute add_zero insert.prems(2) zero_mem dim_eq by auto
  qed
  also have "... = sum_mat A (insert x F)" using insert sum_mat_insert[of A x F]
    by (simp add: \<open>\<And>i. i \<in> insert x F \<Longrightarrow> A i * A i = A i\<close> image_subsetI)
  finally show ?case .
qed

lemma diagonal_unit_vec:
  assumes "B \<in> carrier_mat n n"
and "diagonal_mat (B::complex Matrix.mat)"
shows "B *\<^sub>v (unit_vec n i) = B $$ (i,i)  \<cdot>\<^sub>v (unit_vec n i)"
proof -
  define v::"complex Matrix.vec" where "v = unit_vec n i"
  have "B *\<^sub>v v = Matrix.vec n (\<lambda> i. Matrix.scalar_prod (Matrix.row B i) v)" 
    using assms unfolding mult_mat_vec_def by simp
  also have "... = Matrix.vec n (\<lambda> i. B $$(i,i) * Matrix.vec_index v i)" 
  proof -
    have "\<forall>i < n. (Matrix.scalar_prod (Matrix.row B i) v = B $$(i,i) * Matrix.vec_index v i)"
    proof (intro allI impI)
      fix i
      assume "i < n"
      have "(Matrix.scalar_prod (Matrix.row B i) v) = 
        (\<Sum> j \<in> {0 ..< n}. Matrix.vec_index (Matrix.row B i) j * Matrix.vec_index v j)" using assms
        unfolding Matrix.scalar_prod_def v_def by simp
      also have "... = Matrix.vec_index (Matrix.row B i) i * Matrix.vec_index v i" 
      proof (rule sum_but_one)
        show "\<forall>j < n. j \<noteq> i \<longrightarrow> Matrix.vec_index (Matrix.row B i) j = 0"
        proof (intro allI impI)
          fix j
          assume "j < n" and "j \<noteq> i"
          hence "Matrix.vec_index (Matrix.row B i) j = B $$ (i,j)" using \<open>i < n\<close> \<open>j < n\<close> assms 
            by auto
          also have "... = 0" using assms \<open>i < n\<close> \<open>j < n\<close> \<open>j\<noteq> i\<close> unfolding diagonal_mat_def by simp
          finally show "Matrix.vec_index (Matrix.row B i) j = 0" .
        qed
        show "i < n" using \<open>i < n\<close> .
      qed
      also have "... = B $$(i,i) * Matrix.vec_index v i" using assms \<open>i < n\<close> by auto
      finally show "(Matrix.scalar_prod (Matrix.row B i) v) = B $$(i,i) * Matrix.vec_index v i" .
    qed
    thus ?thesis by auto
  qed
  also have "... = B $$ (i,i)  \<cdot>\<^sub>v v" unfolding v_def unit_vec_def by auto
  finally have "B *\<^sub>v v = B $$ (i,i)  \<cdot>\<^sub>v v" .
  thus ?thesis unfolding v_def by simp
qed

lemma mat_vec_mult_assoc:
  assumes "A \<in> carrier_mat n p"
and "B\<in> carrier_mat p q"
and "dim_vec v = q"
shows "A *\<^sub>v (B *\<^sub>v v) = (A * B) *\<^sub>v v" using assms by auto

lemma (in cpx_sq_mat) similar_eigenvectors:
  assumes "A\<in> fc_mats"
  and "B\<in> fc_mats"
  and "P\<in> fc_mats"
  and "similar_mat_wit A B P (Complex_Matrix.adjoint P)"
  and "diagonal_mat B"
  and "i < n"
shows "A *\<^sub>v (P *\<^sub>v (unit_vec dimR i)) = B $$ (i,i) \<cdot>\<^sub>v (P *\<^sub>v (unit_vec dimR i))"
proof -
  have "A *\<^sub>v (P *\<^sub>v (unit_vec dimR i)) = 
    (P * B * (Complex_Matrix.adjoint P)) *\<^sub>v (P *\<^sub>v (unit_vec dimR i))"
    using assms unfolding similar_mat_wit_def by metis
  also have "... = P * B * (Complex_Matrix.adjoint P) * P *\<^sub>v (unit_vec dimR i)" 
  proof (rule mat_vec_mult_assoc[of _ dimR dimR], (auto simp add: assms fc_mats_carrier))
    show "P \<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
    show "P * B * Complex_Matrix.adjoint P \<in> carrier_mat dimR dimR" 
        using assms fc_mats_carrier by auto
  qed
  also have "... = P * B * ((Complex_Matrix.adjoint P) * P) *\<^sub>v (unit_vec dimR i)" using assms dim_eq
    by (smt fc_mats_carrier mat_assoc_test(1) similar_mat_witD2(6) similar_mat_wit_sym)  
  also have "... = P * B *\<^sub>v (unit_vec dimR i)"
  proof -
    have "(Complex_Matrix.adjoint P) * P = 1\<^sub>m dimR" using assms dim_eq unfolding similar_mat_wit_def
      by (simp add: fc_mats_carrier)
    thus ?thesis using assms(2) local.fc_mats_carrier dim_eq by auto 
  qed
  also have "... = P *\<^sub>v (B *\<^sub>v (unit_vec dimR i))" using mat_vec_mult_assoc assms fc_mats_carrier 
      dim_eq by simp
  also have "... = P *\<^sub>v (B $$ (i,i) \<cdot>\<^sub>v (unit_vec dimR i))" using assms diagonal_unit_vec 
      fc_mats_carrier dim_eq by simp
  also have "... = B $$ (i,i) \<cdot>\<^sub>v (P *\<^sub>v (unit_vec dimR i))" 
  proof (rule mult_mat_vec)
    show "P \<in> carrier_mat dimR dimC" using assms fc_mats_carrier by simp
    show "unit_vec dimR i \<in> carrier_vec dimC" using dim_eq by simp
  qed
  finally show ?thesis .
qed


subsection \<open>Projectors\<close>

definition projector where
"projector M \<longleftrightarrow> (hermitian M \<and> M * M = M)"

lemma projector_hermitian:
  assumes "projector M"
  shows "hermitian M" using assms unfolding projector_def by simp

lemma zero_projector[simp]:
  shows "projector (0\<^sub>m n n)" unfolding projector_def
proof
  show "hermitian (0\<^sub>m n n)" using zero_hermitian[of n] by simp
  show "0\<^sub>m n n * 0\<^sub>m n n = 0\<^sub>m n n" by simp
qed

lemma projector_square_eq:
  assumes "projector M"
  shows "M * M = M" using assms unfolding projector_def by simp

lemma projector_positive:
  assumes "projector M"
  shows "Complex_Matrix.positive M"
proof (rule positive_if_decomp)
  show "M \<in> carrier_mat (dim_row M) (dim_row M)" using assms projector_hermitian hermitian_square 
    by auto
next
  have "M = Complex_Matrix.adjoint M" using assms projector_hermitian[of M] 
    unfolding hermitian_def by simp
  hence "M * Complex_Matrix.adjoint M = M * M" by simp
  also have "... = M" using assms projector_square_eq by auto
  finally have "M * Complex_Matrix.adjoint M = M" .
  thus "\<exists>Ma. Ma * Complex_Matrix.adjoint Ma = M" by auto
qed

lemma projector_collapse_trace:
  assumes "projector (P::complex Matrix.mat)"
  and "P \<in> carrier_mat n n"
  and "R\<in> carrier_mat n n"
shows "Complex_Matrix.trace (P * R * P) = Complex_Matrix.trace (R * P)"
proof -
  have "Complex_Matrix.trace (R * P) = Complex_Matrix.trace (P * R)" using trace_comm assms  by auto
  also have "... = Complex_Matrix.trace ((P * P) * R)" using assms projector_square_eq[of P] by simp
  also have "... = Complex_Matrix.trace (P * (P * R))" using assms by auto
  also have "... = Complex_Matrix.trace (P * R * P)" using trace_comm[of P n "P * R"] assms by auto
  finally have "Complex_Matrix.trace (R * P) = Complex_Matrix.trace (P * R * P)" .
  thus ?thesis by simp
qed

lemma positive_proj_trace:
  assumes "projector (P::complex Matrix.mat)"
  and "Complex_Matrix.positive R"
  and "P \<in> carrier_mat n n"
  and "R\<in> carrier_mat n n"
shows "Complex_Matrix.trace (R * P) \<ge> 0" 
proof -
  have "Complex_Matrix.trace (R * P) = Complex_Matrix.trace ((P * R) * P)" 
    using  assms projector_collapse_trace by auto
  also have "... = Complex_Matrix.trace ((P * R) * (Complex_Matrix.adjoint P))" 
    using assms projector_hermitian[of P]
    unfolding hermitian_def by simp
  also have "... \<ge> 0"
  proof (rule positive_trace)
    show " P * R * Complex_Matrix.adjoint P \<in> carrier_mat n n" using assms by auto
    show "Complex_Matrix.positive (P * R * Complex_Matrix.adjoint P)" 
      by (rule positive_close_under_left_right_mult_adjoint[of _ n], (auto simp add: assms))
  qed
  finally show ?thesis .
qed

lemma trace_proj_pos_real:
  assumes "projector (P::complex Matrix.mat)"
  and "Complex_Matrix.positive R"
  and "P \<in> carrier_mat n n"
  and "R\<in> carrier_mat n n"
shows "Re (Complex_Matrix.trace (R * P)) = Complex_Matrix.trace (R * P)" 
proof -
  have "Complex_Matrix.trace (R * P) \<ge> 0" using assms  positive_proj_trace by simp
  thus ?thesis by (simp add: complex_eqI) 
qed

lemma (in cpx_sq_mat) trace_sum_mat_proj_pos_real:
  fixes f::"'a \<Rightarrow> real"
  assumes "finite I"
  and "\<forall> i\<in> I. projector (P i)"
  and "Complex_Matrix.positive R"
  and "\<forall>i\<in> I. P i \<in> fc_mats"
  and "R \<in> fc_mats"
shows "Complex_Matrix.trace (R * (sum_mat (\<lambda>i. f i \<cdot>\<^sub>m (P i)) I)) = 
  Re (Complex_Matrix.trace (R * (sum_mat (\<lambda>i. f i \<cdot>\<^sub>m (P i)) I)))"
proof -
  have sm:  "\<And>x. x \<in> I \<Longrightarrow> Complex_Matrix.trace (f x \<cdot>\<^sub>m (R * P x)) = 
    f x * Complex_Matrix.trace (R * P x)"
  proof -
    fix i
    assume "i\<in> I"
    show "Complex_Matrix.trace (f i \<cdot>\<^sub>m (R * P i)) = f i * Complex_Matrix.trace (R * P i)" 
    proof (rule trace_smult)
      show "R * P i \<in> carrier_mat dimR dimR" using assms cpx_sq_mat_mult fc_mats_carrier \<open>i\<in> I\<close> 
          dim_eq by simp
    qed
  qed
  have sw: "\<And>x. x \<in> I \<Longrightarrow> R * (f x \<cdot>\<^sub>m P x) = f x \<cdot>\<^sub>m (R * P x)" 
  proof -
    fix i
    assume "i \<in> I"
    show "R * (f i \<cdot>\<^sub>m P i) = f i \<cdot>\<^sub>m (R * P i)"
    proof (rule mult_smult_distrib)
      show "R\<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
      show "P i \<in> carrier_mat dimR dimR" using assms \<open>i\<in> I\<close> fc_mats_carrier dim_eq by simp
    qed
  qed
  have dr: "Complex_Matrix.trace (R * (sum_mat (\<lambda>i. f i \<cdot>\<^sub>m (P i)) I)) = 
    Complex_Matrix.trace (sum_mat (\<lambda>i. (R * (f i \<cdot>\<^sub>m (P i)))) I)"
    using sum_mat_distrib_left[of I] assms by (simp add: cpx_sq_mat_smult)
  also have trs: "... = (\<Sum> i\<in> I. Complex_Matrix.trace (R * (f i \<cdot>\<^sub>m (P i))))" 
  proof (rule trace_sum_mat, (simp add: assms))
    show "\<And>i. i \<in> I \<Longrightarrow> R * (f i \<cdot>\<^sub>m P i) \<in> fc_mats" using assms 
      by (simp add: cpx_sq_mat_smult cpx_sq_mat_mult)
  qed
  also have "... = (\<Sum> i\<in> I. Complex_Matrix.trace (f i \<cdot>\<^sub>m (R * (P i))))" 
    by (rule sum.cong, (simp add: sw)+)    
  also have "... = (\<Sum> i\<in> I. f i * Complex_Matrix.trace (R * (P i)))" 
    by (rule sum.cong, (simp add: sm)+)
  also have "... = (\<Sum> i\<in> I. complex_of_real (f i * Re (Complex_Matrix.trace (R * (P i)))))" 
  proof (rule sum.cong, simp)
    show "\<And>x. x \<in> I \<Longrightarrow>
         complex_of_real (f x) * Complex_Matrix.trace (R * P x) =
         complex_of_real (f x * Re (Complex_Matrix.trace (R * P x)))"
    proof -
      fix x
      assume "x\<in> I"
      have "complex_of_real (f x) * Complex_Matrix.trace (R * P x) = 
        complex_of_real (f x) * complex_of_real (Re (Complex_Matrix.trace (R * P x)))"
        using assms sum.cong[of I I] fc_mats_carrier trace_proj_pos_real \<open>x \<in> I\<close> dim_eq by auto
      also have "... = complex_of_real (f x * Re (Complex_Matrix.trace (R * P x)))" by simp
      finally show "complex_of_real (f x) * Complex_Matrix.trace (R * P x) =
         complex_of_real (f x * Re (Complex_Matrix.trace (R * P x)))" .
    qed
  qed
  also have "... = (\<Sum> i\<in> I. f i * Re (Complex_Matrix.trace (R * (P i))))" by simp
  also have "... = (\<Sum> i\<in> I. Re (Complex_Matrix.trace (f i \<cdot>\<^sub>m (R * (P i)))))" 
  proof -
    have "(\<Sum> i\<in> I. f i * Re (Complex_Matrix.trace (R * (P i)))) = 
      (\<Sum> i\<in> I. Re (Complex_Matrix.trace (f i \<cdot>\<^sub>m (R * (P i)))))"
      by (rule sum.cong, (simp add: sm)+)
    thus ?thesis by simp
  qed
  also have "... = (\<Sum> i\<in> I. Re (Complex_Matrix.trace (R * (f i \<cdot>\<^sub>m (P i)))))"
  proof -
    have "\<And>i. i \<in> I \<Longrightarrow> f i \<cdot>\<^sub>m (R * (P i)) = R * (f i \<cdot>\<^sub>m (P i))" using sw by simp
    thus ?thesis by simp
  qed
  also have "... = Re (\<Sum> i\<in> I. (Complex_Matrix.trace (R * (f i \<cdot>\<^sub>m (P i)))))" by simp
  also have "... = Re (Complex_Matrix.trace (sum_mat (\<lambda>i. R * (f i \<cdot>\<^sub>m (P i))) I))" using trs by simp
  also have "... = Re (Complex_Matrix.trace (R * (sum_mat (\<lambda>i. f i \<cdot>\<^sub>m (P i))) I))" using dr by simp
  finally show ?thesis .
qed


subsection \<open>Rank 1 projection\<close>

definition rank_1_proj where
"rank_1_proj v = outer_prod v v"

lemma rank_1_proj_square_mat:
  shows "square_mat (rank_1_proj v)" using outer_prod_dim unfolding rank_1_proj_def
  by (metis carrier_matD(1) carrier_matD(2) carrier_vec_dim_vec  square_mat.simps)

lemma rank_1_proj_dim[simp]:
  shows "dim_row (rank_1_proj v) = dim_vec v" using outer_prod_dim unfolding rank_1_proj_def
  using carrier_vecI by blast

lemma rank_1_proj_carrier[simp]:
  shows "rank_1_proj v \<in> carrier_mat (dim_vec v) (dim_vec v)" using outer_prod_dim 
  unfolding rank_1_proj_def using carrier_vecI by blast

lemma rank_1_proj_coord:
  assumes "i < dim_vec v"
  and "j < dim_vec v"
shows "(rank_1_proj v) $$ (i, j) = Matrix.vec_index v i * (cnj (Matrix.vec_index v j))" using assms 
  unfolding rank_1_proj_def outer_prod_def by auto

lemma rank_1_proj_adjoint:
  shows "Complex_Matrix.adjoint (rank_1_proj (v::complex Matrix.vec)) = rank_1_proj v"
proof
  show "dim_row (Complex_Matrix.adjoint (rank_1_proj v)) = dim_row (rank_1_proj v)"
    using rank_1_proj_square_mat by auto
  thus "dim_col (Complex_Matrix.adjoint (rank_1_proj v)) = dim_col (rank_1_proj v)" by auto
  fix i j
  assume "i < dim_row (rank_1_proj v)" and "j < dim_col (rank_1_proj v)" note ij = this
  have "Complex_Matrix.adjoint (rank_1_proj v) $$ (i, j) = conjugate ((rank_1_proj v) $$ (j, i))" 
    using ij \<open>dim_col (Complex_Matrix.adjoint (rank_1_proj v)) = dim_col (rank_1_proj v)\<close> 
      adjoint_eval by fastforce
  also have "... = conjugate (Matrix.vec_index v j * (cnj (Matrix.vec_index v i)))" 
    using rank_1_proj_coord ij
    by (metis \<open>dim_col (Complex_Matrix.adjoint (rank_1_proj v)) = dim_col (rank_1_proj v)\<close> 
        adjoint_dim_col rank_1_proj_dim) 
  also have "... = Matrix.vec_index v i * (cnj (Matrix.vec_index v j))" by simp
  also have "... = rank_1_proj v $$ (i, j)" using ij rank_1_proj_coord
    by (metis \<open>dim_col (Complex_Matrix.adjoint (rank_1_proj v)) = dim_col (rank_1_proj v)\<close> 
        adjoint_dim_col rank_1_proj_dim) 
  finally show "Complex_Matrix.adjoint (rank_1_proj v) $$ (i, j) = rank_1_proj v $$ (i, j)".
qed

lemma rank_1_proj_hermitian:
  shows "hermitian (rank_1_proj (v::complex Matrix.vec))" using rank_1_proj_adjoint 
  unfolding hermitian_def by simp

lemma rank_1_proj_trace:
  assumes "\<parallel>v\<parallel> = 1"
  shows "Complex_Matrix.trace (rank_1_proj v) = 1"
proof -
  have "Complex_Matrix.trace (rank_1_proj v) = inner_prod v v" using trace_outer_prod 
    unfolding rank_1_proj_def using carrier_vecI by blast
  also have "... = (vec_norm v)\<^sup>2" unfolding vec_norm_def using power2_csqrt by presburger
  also have "... = \<parallel>v\<parallel>\<^sup>2" using vec_norm_sq_cpx_vec_length_sq by simp
  also have "... = 1" using assms by simp
  finally show ?thesis .
qed

lemma rank_1_proj_mat_col:
  assumes "A \<in> carrier_mat n n"
  and "i < n"
  and "j < n"
  and "k < n"
shows "(rank_1_proj (Matrix.col A i)) $$ (j, k) = A $$ (j, i) * conjugate (A $$ (k,i))"
proof -
  have "(rank_1_proj (Matrix.col A i)) $$ (j, k) = Matrix.vec_index (Matrix.col A i) j * 
    conjugate (Matrix.vec_index (Matrix.col A i) k)" using index_outer_prod[of "Matrix.col A i" n "Matrix.col A i" n] 
      assms unfolding rank_1_proj_def by simp
  also have "... = A $$ (j, i) * conjugate (A $$ (k,i))" using assms by simp
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) weighted_sum_rank_1_proj_unitary_index:
  assumes "A \<in> fc_mats"
and "B \<in> fc_mats"
and "diagonal_mat B"
and "Complex_Matrix.unitary A"
and "j < dimR"
and "k < dimR"
shows "(sum_mat (\<lambda>i. (diag_mat B)!i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i)) {..< dimR}) $$ (j,k) = 
  (A * B * (Complex_Matrix.adjoint A)) $$ (j,k)"
proof -
  have "(sum_mat (\<lambda>i. (diag_mat B)!i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i)) {..< dimR}) $$ (j,k) = 
    (\<Sum> i\<in> {..< dimR}. ((diag_mat B)!i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i)) $$ (j,k))" 
  proof (rule sum_mat_index, (auto simp add: fc_mats_carrier assms))
    show "\<And>i. i < dimR \<Longrightarrow> (diag_mat B)!i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i) \<in> carrier_mat dimR dimC" 
      using rank_1_proj_carrier assms fc_mats_carrier dim_eq 
      by (metis smult_carrier_mat zero_col_col zero_col_dim) 
    show "k < dimC" using assms dim_eq by simp
  qed
  also have "... = (\<Sum> i\<in> {..< dimR}. (diag_mat B)!i* A $$ (j, i) * conjugate (A $$ (k,i)))" 
  proof (rule sum.cong, simp)
    have idx: "\<And>x. x \<in> {..<dimR} \<Longrightarrow> (rank_1_proj (Matrix.col A x)) $$ (j, k) = 
      A $$ (j, x) * conjugate (A $$ (k, x))" using rank_1_proj_mat_col assms fc_mats_carrier dim_eq 
      by blast
    show "\<And>x. x \<in> {..<dimR} \<Longrightarrow> ((diag_mat B)!x \<cdot>\<^sub>m rank_1_proj (Matrix.col A x)) $$ (j, k) = 
      (diag_mat B)!x * A $$ (j, x) * conjugate (A $$ (k, x))" 
    proof -
      fix x
      assume "x\<in> {..< dimR}"
      have "((diag_mat B)!x \<cdot>\<^sub>m rank_1_proj (Matrix.col A x)) $$ (j, k) = 
        (diag_mat B)!x * (rank_1_proj (Matrix.col A x)) $$ (j, k)" 
      proof (rule index_smult_mat)
        show "j < dim_row (rank_1_proj (Matrix.col A x))" using \<open>x\<in> {..< dimR}\<close> assms fc_mats_carrier by simp
        show "k < dim_col (rank_1_proj (Matrix.col A x))" using \<open>x\<in> {..< dimR}\<close> assms fc_mats_carrier 
            rank_1_proj_carrier[of "Matrix.col A x"] by simp
      qed
      thus "((diag_mat B)!x \<cdot>\<^sub>m rank_1_proj (Matrix.col A x)) $$ (j, k) = 
        (diag_mat B)!x * A $$ (j, x) * conjugate (A $$ (k, x))" using idx \<open>x\<in> {..< dimR}\<close> by simp
    qed
  qed
  also have "... = Matrix.scalar_prod (Matrix.col (Complex_Matrix.adjoint A) k) (Matrix.row (A*B) j) " 
    unfolding Matrix.scalar_prod_def
  proof (rule sum.cong)
    show "{..<dimR} = {0..<dim_vec (Matrix.row (A*B) j)}" 
      using assms fc_mats_carrier dim_eq by auto
    show "\<And>x. x \<in> {0..<dim_vec (Matrix.row (A*B) j)} \<Longrightarrow>
      diag_mat B ! x * A $$ (j, x) * conjugate (A $$ (k, x)) = 
      Matrix.vec_index ((Matrix.col (Complex_Matrix.adjoint A) k)) x * 
      Matrix.vec_index (Matrix.row (A*B) j) x" 
    proof -
      fix x
      assume "x\<in> {0..<dim_vec (Matrix.row (A*B) j)}"
      hence "x\<in> {0..<dimR}" using assms fc_mats_carrier dim_eq by simp
      have "diag_mat B ! x *A $$ (j, x) = Matrix.vec_index (Matrix.row (A*B) j) x"
      proof (rule times_diag_index[symmetric, of _ dimR], (auto simp add: assms))
        show "A \<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
        show "B \<in> carrier_mat dimR dimR" using assms fc_mats_carrier dim_eq by simp
        show "x < dimR" using \<open>x\<in>{0..< dimR}\<close> by simp
      qed
      moreover have "conjugate (A $$ (k, x)) = 
        Matrix.vec_index ((Matrix.col (Complex_Matrix.adjoint A) k)) x" using \<open>x\<in> {0..<dimR}\<close> assms 
        fc_mats_carrier dim_eq by (simp add: adjoint_col)
      ultimately show "diag_mat B ! x * A $$ (j, x) * conjugate (A $$ (k, x)) = 
        Matrix.vec_index ((Matrix.col (Complex_Matrix.adjoint A) k)) x * 
        Matrix.vec_index (Matrix.row (A*B) j) x"  by simp
    qed
  qed
  also have "... = (A*B * (Complex_Matrix.adjoint A)) $$ (j,k)" 
  proof -
    have "Matrix.mat (dim_row (A*B)) (dim_col (Complex_Matrix.adjoint A))
     (\<lambda>(i, j). Matrix.scalar_prod (Matrix.row (A*B) i) (Matrix.col (Complex_Matrix.adjoint A) j)) $$
    (j, k) =  Matrix.scalar_prod (Matrix.row (A*B) j) (Matrix.col (Complex_Matrix.adjoint A) k)"
      using assms fc_mats_carrier by simp
    also have "... = Matrix.scalar_prod (Matrix.col (Complex_Matrix.adjoint A) k) (Matrix.row (A*B) j)" 
      using assms comm_scalar_prod[of "Matrix.row (A*B) j" dimR] fc_mats_carrier dim_eq
      by (metis adjoint_dim Matrix.col_carrier_vec row_carrier_vec cpx_sq_mat_mult) 
    thus ?thesis using assms fc_mats_carrier unfolding times_mat_def by simp
  qed  
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) weighted_sum_rank_1_proj_unitary:
  assumes "A \<in> fc_mats"
and "B \<in> fc_mats"
and "diagonal_mat B"
and "Complex_Matrix.unitary A"
shows "(sum_mat (\<lambda>i. (diag_mat B)!i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i)) {..< dimR}) = 
  (A * B * (Complex_Matrix.adjoint A))"
proof
  show "dim_row (sum_mat (\<lambda>i. diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i)) {..<dimR}) =
    dim_row (A * B * Complex_Matrix.adjoint A)" using assms fc_mats_carrier dim_eq
    by (metis (no_types, lifting) carrier_matD(1) cpx_sq_mat_smult dim_col index_mult_mat(2) 
        rank_1_proj_carrier sum_mat_carrier)
  show "dim_col (local.sum_mat (\<lambda>i. diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i)) {..<dimR}) =
    dim_col (A * B * Complex_Matrix.adjoint A)" using assms fc_mats_carrier dim_eq
    by (metis (mono_tags, lifting) adjoint_dim_col carrier_matD(1) carrier_matI dim_col 
        index_mult_mat(3) index_smult_mat(2) index_smult_mat(3) rank_1_proj_dim 
        rank_1_proj_square_mat square_mat.elims(2) square_mats sum_mat_carrier)
  show "\<And>i j. i < dim_row (A * B * Complex_Matrix.adjoint A) \<Longrightarrow>
           j < dim_col (A * B * Complex_Matrix.adjoint A) \<Longrightarrow>
           local.sum_mat (\<lambda>i. diag_mat B ! i \<cdot>\<^sub>m rank_1_proj (Matrix.col A i)) {..<dimR} $$ (i, j) =
           (A * B * Complex_Matrix.adjoint A) $$ (i, j)" 
    using weighted_sum_rank_1_proj_unitary_index[of A B] dim_eq fc_mats_carrier using assms by auto
qed

lemma rank_1_proj_projector:
  assumes "\<parallel>v\<parallel> = 1"
  shows "projector (rank_1_proj v)" 
proof -
  have  "Complex_Matrix.adjoint (rank_1_proj v) = rank_1_proj v" using rank_1_proj_adjoint by simp
  hence a: "hermitian (rank_1_proj v)" unfolding hermitian_def by simp
  have "rank_1_proj v * rank_1_proj v = inner_prod v v  \<cdot>\<^sub>m outer_prod v v" unfolding rank_1_proj_def 
    using outer_prod_mult_outer_prod assms using carrier_vec_dim_vec by blast
  also have "... = (vec_norm v)\<^sup>2  \<cdot>\<^sub>m outer_prod v v" unfolding vec_norm_def using power2_csqrt 
    by presburger
  also have "... =  (cpx_vec_length v)\<^sup>2 \<cdot>\<^sub>m outer_prod v v " using vec_norm_sq_cpx_vec_length_sq
    by simp
  also have "... = outer_prod v v" using assms state_qbit_norm_sq smult_one[of "outer_prod v v"]
    by simp
  also have "... = rank_1_proj v" unfolding rank_1_proj_def by simp
  finally show ?thesis using a unfolding projector_def by simp
qed

lemma rank_1_proj_positive:
  assumes "\<parallel>v\<parallel> = 1"
  shows "Complex_Matrix.positive (rank_1_proj v)"
proof -
  have "projector (rank_1_proj v)" using assms rank_1_proj_projector by simp
  thus ?thesis using projector_positive by simp
qed

lemma rank_1_proj_density:
  assumes "\<parallel>v\<parallel> = 1"
  shows "density_operator (rank_1_proj v)" unfolding density_operator_def using assms
  by (simp add: rank_1_proj_positive rank_1_proj_trace)

lemma (in cpx_sq_mat) sum_rank_1_proj_unitary_index:
  assumes "A \<in> fc_mats"
and "Complex_Matrix.unitary A"
and "j < dimR"
and "k < dimR"
shows "(sum_mat (\<lambda>i. rank_1_proj (Matrix.col A i)) {..< dimR}) $$ (j,k) = (1\<^sub>m dimR) $$ (j,k)"
proof -
  have "(sum_mat (\<lambda>i. rank_1_proj (Matrix.col A i)) {..< dimR}) $$ (j,k) = 
    (\<Sum> i\<in> {..< dimR}. (rank_1_proj (Matrix.col A i)) $$ (j,k))" 
  proof (rule sum_mat_index, (auto simp add: fc_mats_carrier assms))
    show "\<And>i. i < dimR \<Longrightarrow> rank_1_proj (Matrix.col A i) \<in> carrier_mat dimR dimC" 
    proof -
      fix i
      assume "i < dimR"
      hence "dim_vec (Matrix.col A i) = dimR" using assms fc_mats_carrier by simp
      thus "rank_1_proj (Matrix.col A i) \<in> carrier_mat dimR dimC" using rank_1_proj_carrier assms
        fc_mats_carrier dim_eq fc_mats_carrier by (metis dim_col fc_mats_carrier) 
    qed
    show "k < dimC" using assms dim_eq by simp
  qed
  also have "... = (\<Sum> i\<in> {..< dimR}. A $$ (j, i) * conjugate (A $$ (k,i)))" 
  proof (rule sum.cong, simp)
    show "\<And>x. x \<in> {..<dimR} \<Longrightarrow> rank_1_proj (Matrix.col A x) $$ (j, k) = 
      A $$ (j, x) * conjugate (A $$ (k, x))" 
      using rank_1_proj_mat_col assms using local.fc_mats_carrier dim_eq by blast 
  qed
  also have "... = Matrix.scalar_prod (Matrix.col (Complex_Matrix.adjoint A) k) (Matrix.row A j) " 
    unfolding Matrix.scalar_prod_def
  proof (rule sum.cong)
    show "{..<dimR} = {0..<dim_vec (Matrix.row A j)}" 
      using assms fc_mats_carrier dim_eq by auto
    show "\<And>x. x \<in> {0..<dim_vec (Matrix.row A j)} \<Longrightarrow>
      A $$ (j, x) * conjugate (A $$ (k, x)) = 
      Matrix.vec_index ((Matrix.col (Complex_Matrix.adjoint A) k)) x * Matrix.vec_index (Matrix.row A j) x" 
    proof -
      fix x
      assume "x\<in> {0..<dim_vec (Matrix.row A j)}"
      hence "x\<in> {0..<dimR}" using assms fc_mats_carrier dim_eq by simp
      hence "A $$ (j, x) = Matrix.vec_index (Matrix.row A j) x" using \<open>x\<in> {0..<dimR}\<close> 
          assms fc_mats_carrier dim_eq by simp
      moreover have "conjugate (A $$ (k, x)) = 
        Matrix.vec_index ((Matrix.col (Complex_Matrix.adjoint A) k)) x" using \<open>x\<in> {0..<dimR}\<close> 
        assms fc_mats_carrier dim_eq by (simp add: adjoint_col)
      ultimately show "A $$ (j, x) * conjugate (A $$ (k, x)) = 
        Matrix.vec_index ((Matrix.col (Complex_Matrix.adjoint A) k)) x * 
        Matrix.vec_index (Matrix.row A j) x" by simp
    qed
  qed
  also have "... = (A * (Complex_Matrix.adjoint A)) $$ (j,k)" 
  proof -
    have "Matrix.mat (dim_row A) (dim_col (Complex_Matrix.adjoint A))
     (\<lambda>(i, j). Matrix.scalar_prod (Matrix.row A i) (Matrix.col (Complex_Matrix.adjoint A) j)) $$
    (j, k) =  Matrix.scalar_prod (Matrix.row A j) (Matrix.col (Complex_Matrix.adjoint A) k)"
      using assms fc_mats_carrier by simp
    also have "... = Matrix.scalar_prod (Matrix.col (Complex_Matrix.adjoint A) k) (Matrix.row A j)" 
      using assms comm_scalar_prod[of "Matrix.row A j" dimR] fc_mats_carrier
      by (simp add: adjoint_dim dim_eq)
    thus ?thesis using assms fc_mats_carrier unfolding times_mat_def by simp
  qed
  also have "... = (1\<^sub>m dimR) $$ (j,k)" using assms dim_eq by (simp add: fc_mats_carrier)
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) rank_1_proj_sum_density:
  assumes "finite I"
  and "\<forall>i\<in> I. \<parallel>u i\<parallel> = 1" 
  and "\<forall>i\<in> I. dim_vec (u i) = dimR"
  and "\<forall>i\<in> I. 0 \<le> p i"
  and "(\<Sum>i\<in> I. p i) = 1"
shows "density_operator (sum_mat (\<lambda>i. p i \<cdot>\<^sub>m (rank_1_proj (u i))) I)" unfolding density_operator_def
proof
  have "Complex_Matrix.trace (sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (u i)) I) = 
    (\<Sum>i\<in> I. Complex_Matrix.trace (p i \<cdot>\<^sub>m rank_1_proj (u i)))" 
  proof (rule trace_sum_mat, (simp add: assms))
    show "\<And>i. i \<in> I \<Longrightarrow> p i \<cdot>\<^sub>m rank_1_proj (u i) \<in> fc_mats" using assms smult_mem fc_mats_carrier 
        dim_eq by auto
  qed
  also have "... = (\<Sum>i\<in> I. p i * Complex_Matrix.trace (rank_1_proj (u i)))" 
  proof -
    {
      fix i
      assume "i \<in> I"
      hence "Complex_Matrix.trace (p i \<cdot>\<^sub>m rank_1_proj (u i)) = 
        p i * Complex_Matrix.trace (rank_1_proj (u i))"
        using trace_smult[of "rank_1_proj (u i)" dimR] assms fc_mats_carrier dim_eq by auto
    }
    thus ?thesis by simp
  qed
  also have "... = 1" using assms rank_1_proj_trace assms by auto
  finally show "Complex_Matrix.trace (sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (u i)) I) = 1" .
next
  show "Complex_Matrix.positive (sum_mat (\<lambda>i. p i \<cdot>\<^sub>m rank_1_proj (u i)) I)"
  proof (rule sum_mat_positive, (simp add: assms))
    fix i
    assume "i\<in> I"
    thus "p i \<cdot>\<^sub>m rank_1_proj (u i) \<in> fc_mats" using assms smult_mem fc_mats_carrier dim_eq by auto
    show "Complex_Matrix.positive (p i \<cdot>\<^sub>m rank_1_proj (u i))" using assms \<open>i\<in> I\<close> 
        rank_1_proj_positive positive_smult[of "rank_1_proj (u i)" dimR] dim_eq by auto
  qed
qed



lemma (in cpx_sq_mat) sum_rank_1_proj_unitary:
  assumes "A \<in> fc_mats"
and "Complex_Matrix.unitary A"
shows "(sum_mat (\<lambda>i. rank_1_proj (Matrix.col A i)) {..< dimR})= (1\<^sub>m dimR)"
proof
  show "dim_row (sum_mat (\<lambda>i. rank_1_proj (Matrix.col A i)) {..<dimR}) = dim_row (1\<^sub>m dimR)" 
    using assms fc_mats_carrier
    by (metis carrier_matD(1) dim_col dim_eq index_one_mat(2) rank_1_proj_carrier sum_mat_carrier)
  show "dim_col (sum_mat (\<lambda>i. rank_1_proj (Matrix.col A i)) {..<dimR}) = dim_col (1\<^sub>m dimR)" 
    using assms fc_mats_carrier rank_1_proj_carrier sum_mat_carrier
    by (metis carrier_matD(2) dim_col dim_eq index_one_mat(3) square_mat.simps square_mats)
  show "\<And>i j. i < dim_row (1\<^sub>m dimR) \<Longrightarrow>
     j < dim_col (1\<^sub>m dimR) \<Longrightarrow> sum_mat (\<lambda>i. rank_1_proj (Matrix.col A i)) {..<dimR} $$ (i, j) = 
      1\<^sub>m dimR $$ (i, j)"
    using assms sum_rank_1_proj_unitary_index by simp
qed

lemma (in cpx_sq_mat) rank_1_proj_unitary:
  assumes "A \<in> fc_mats"
and "Complex_Matrix.unitary A"
and "j < dimR"
and "k < dimR"
shows "rank_1_proj (Matrix.col A j) * (rank_1_proj (Matrix.col A k)) =
  (1\<^sub>m dimR) $$ (j,k) \<cdot>\<^sub>m (outer_prod (Matrix.col A j) (Matrix.col A k))"
proof -
  have "rank_1_proj (Matrix.col A j) * (rank_1_proj (Matrix.col A k)) = 
    Complex_Matrix.inner_prod (Matrix.col A j) (Matrix.col A k) \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)"
    using outer_prod_mult_outer_prod assms Matrix.col_dim local.fc_mats_carrier unfolding rank_1_proj_def
    by blast
  also have "... = (Complex_Matrix.adjoint A * A) $$ (j, k)\<cdot>\<^sub>m (outer_prod (Matrix.col A j) (Matrix.col A k))" 
    using inner_prod_adjoint_comp[of A dimR A] assms fc_mats_carrier dim_eq by simp
  also have "... = (1\<^sub>m dimR) $$ (j,k) \<cdot>\<^sub>m (outer_prod (Matrix.col A j) (Matrix.col A k))" using assms 
    unfolding Complex_Matrix.unitary_def
    by (metis add_commute assms(2) index_add_mat(2) index_one_mat(2) one_mem unitary_simps(1))
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) rank_1_proj_unitary_ne:
  assumes "A \<in> fc_mats"
and "Complex_Matrix.unitary A"
and "j < dimR"
and "k < dimR"
and "j\<noteq> k"
shows "rank_1_proj (Matrix.col A j) * (rank_1_proj (Matrix.col A k)) =  (0\<^sub>m dimR dimR)"
proof -
  have "dim_row (0 \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)) = dim_row (outer_prod (Matrix.col A j) (Matrix.col A k))"
      by simp
  also have "... = dimR" using assms fc_mats_carrier dim_eq by auto
  finally have rw: "dim_row (0 \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)) = dimR" .
  have "dim_col (0 \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)) = dim_col (outer_prod (Matrix.col A j) (Matrix.col A k))"
      by simp
    also have "... = dimR" using assms fc_mats_carrier dim_eq by auto
    finally have cl: "dim_col (0 \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)) = dimR" .
    have "rank_1_proj (Matrix.col A j) * (rank_1_proj (Matrix.col A k)) = 
      (0::complex) \<cdot>\<^sub>m (outer_prod (Matrix.col A j) (Matrix.col A k))"
      using assms rank_1_proj_unitary by simp
  also have "... = (0\<^sub>m dimR dimR)" 
  proof
    show "dim_row (0 \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)) = dim_row (0\<^sub>m dimR dimR)" using rw by simp
  next
    show "dim_col (0 \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)) = dim_col (0\<^sub>m dimR dimR)" using cl by simp
  next
    show "\<And>i p. i < dim_row (0\<^sub>m dimR dimR) \<Longrightarrow> p < dim_col (0\<^sub>m dimR dimR) \<Longrightarrow> 
      (0 \<cdot>\<^sub>m outer_prod (Matrix.col A j) (Matrix.col A k)) $$ (i, p) = 0\<^sub>m dimR dimR $$ (i, p)" using rw cl by auto
  qed
  finally show ?thesis .
qed

lemma (in cpx_sq_mat) rank_1_proj_unitary_eq:
  assumes "A \<in> fc_mats"
and "Complex_Matrix.unitary A"
and "j < dimR"
shows "rank_1_proj (Matrix.col A j) * (rank_1_proj (Matrix.col A j)) =  rank_1_proj (Matrix.col A j)"
proof -
  have "rank_1_proj (Matrix.col A j) * (rank_1_proj (Matrix.col A j)) = (1::complex) \<cdot>\<^sub>m (rank_1_proj (Matrix.col A j))"
    using assms rank_1_proj_unitary unfolding rank_1_proj_def by simp
  also have "... = (rank_1_proj (Matrix.col A j))" by (simp add: smult_one)  
  finally show ?thesis .
qed
  

end