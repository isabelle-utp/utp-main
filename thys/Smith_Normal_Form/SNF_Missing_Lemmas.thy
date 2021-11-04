(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Missing results\<close>

theory SNF_Missing_Lemmas
  imports
    Hermite.Hermite
    Mod_Type_Connect
    Jordan_Normal_Form.DL_Rank_Submatrix
    "List-Index.List_Index"
begin

text \<open>This theory presents some missing lemmas that are required for the Smith normal form
development. Some of them could be added to different AFP entries, such as the Jordan Normal
Form AFP entry by Ren\'e Thiemann and Akihisa Yamada.

However, not all the lemmas can be added directly, since some imports are required.\<close>

hide_const (open) C
hide_const (open) measure

subsection \<open>Miscellaneous lemmas\<close>

lemma sum_two_rw: "(\<Sum>i = 0..<2. f i) = (\<Sum>i \<in> {0,1::nat}. f i)"
  by (rule sum.cong, auto)

lemma sum_common_left:
  fixes f::"'a \<Rightarrow> 'b::comm_ring_1"
  assumes "finite A"
  shows "sum (\<lambda>i. c * f i) A = c * sum f A"
  by (simp add: mult_hom.hom_sum)

lemma prod3_intro:
  assumes "fst A = a" and "fst (snd A) = b" and "snd (snd A) = c"
  shows "A = (a,b,c)" using assms by auto


subsection \<open>Transfer rules for the HMA\_Connect file of the Perron-Frobenius development\<close>

hide_const (open) HMA_M HMA_I to_hma\<^sub>m from_hma\<^sub>m
hide_fact (open) from_hma\<^sub>m_def from_hma_to_hma\<^sub>m HMA_M_def HMA_I_def dim_row_transfer_rule
                  dim_col_transfer_rule

context
  includes lifting_syntax
begin

lemma HMA_invertible_matrix[transfer_rule]:
  "((HMA_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'n ^ 'n \<Rightarrow> _) ===> (=)) invertible_mat invertible"
proof (intro rel_funI, goal_cases)
  case (1 x y)
  note rel_xy[transfer_rule] = "1"
  have eq_dim: "dim_col x = dim_row x"
    using HMA_Connect.dim_col_transfer_rule HMA_Connect.dim_row_transfer_rule rel_xy
    by fastforce
  moreover have "\<exists>A'. y ** A' = Finite_Cartesian_Product.mat 1 \<and> A' ** y = Finite_Cartesian_Product.mat 1"
    if xB: "x * B = 1\<^sub>m (dim_row x)" and Bx: "B * x = 1\<^sub>m (dim_row B)" for B
  proof -
    let ?A' = "HMA_Connect.to_hma\<^sub>m B:: 'a :: comm_ring_1 ^ 'n ^ 'n"
    have rel_BA[transfer_rule]: "HMA_M B ?A'"
      by (metis (no_types, lifting) Bx HMA_M_def eq_dim carrier_mat_triv dim_col_mat(1)
          from_hma\<^sub>m_def from_hma_to_hma\<^sub>m index_mult_mat(3) index_one_mat(3) rel_xy xB)
    have [simp]: "dim_row B = CARD('n)" using dim_row_transfer_rule rel_BA by blast
    have [simp]: "dim_row x = CARD('n)" using dim_row_transfer_rule rel_xy by blast
    have "y ** ?A' = Finite_Cartesian_Product.mat 1" using xB by (transfer, simp)
    moreover have "?A' ** y  = Finite_Cartesian_Product.mat 1" using Bx by (transfer, simp)
    ultimately show ?thesis by blast
  qed
  moreover have "\<exists>B. x * B = 1\<^sub>m (dim_row x) \<and> B * x = 1\<^sub>m (dim_row B)"
    if yA: "y ** A' = Finite_Cartesian_Product.mat 1" and Ay: "A' ** y = Finite_Cartesian_Product.mat 1" for A'
  proof -
    let ?B = "(from_hma\<^sub>m A')"
    have [simp]: "dim_row x = CARD('n)" using dim_row_transfer_rule rel_xy by blast
    have [transfer_rule]: "HMA_M ?B A'" by (simp add: HMA_M_def)
    hence [simp]: "dim_row ?B = CARD('n)" using dim_row_transfer_rule by auto
    have "x * ?B = 1\<^sub>m (dim_row x)" using yA by (transfer', auto)
    moreover have "?B * x = 1\<^sub>m (dim_row ?B)" using Ay by (transfer', auto)
    ultimately show ?thesis by auto
  qed
  ultimately show ?case unfolding invertible_mat_def invertible_def inverts_mat_def by auto
qed
end

subsection \<open>Lemmas obtained from HOL Analysis using local type definitions\<close>

thm Cartesian_Space.invertible_mult (*In HOL Analysis*)
thm invertible_iff_is_unit (*In HOL Analysis*)
thm det_non_zero_imp_unit (*In JNF, but only for fields*)
thm mat_mult_left_right_inverse (*In JNF, but only for fields*)

lemma invertible_mat_zero:
  assumes A: "A \<in> carrier_mat 0 0"
  shows "invertible_mat A"
  using A unfolding invertible_mat_def inverts_mat_def one_mat_def times_mat_def scalar_prod_def
    Matrix.row_def col_def carrier_mat_def
  by (auto, metis (no_types, lifting) cong_mat not_less_zero)

lemma invertible_mult_JNF:
  fixes A::"'a::comm_ring_1 mat"
  assumes A: "A\<in>carrier_mat n n" and B: "B\<in>carrier_mat n n"
    and inv_A: "invertible_mat A" and inv_B: "invertible_mat B"
shows "invertible_mat (A*B)"
proof (cases "n = 0")
  case True
  then show ?thesis using assms
    by (simp add: invertible_mat_zero)
next
  case False
  then show ?thesis using
      invertible_mult[where ?'a="'a::comm_ring_1", where ?'b="'n::finite", where ?'c="'n::finite",
      where ?'d="'n::finite", untransferred, cancel_card_constraint, OF assms] by auto
qed

lemma invertible_iff_is_unit_JNF:
  assumes A: "A \<in> carrier_mat n n"
  shows "invertible_mat A \<longleftrightarrow> (Determinant.det A) dvd 1"
proof (cases "n=0")
  case True
  then show ?thesis using det_dim_zero invertible_mat_zero A by auto
next
  case False
  then show ?thesis using invertible_iff_is_unit[untransferred, cancel_card_constraint] A by auto
qed


subsection \<open>Lemmas about matrices, submatrices and determinants\<close>

(*This is a generalization of thm mat_mult_left_right_inverse*)
thm mat_mult_left_right_inverse
lemma mat_mult_left_right_inverse:
  fixes A :: "'a::comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n n"
    and B: "B \<in> carrier_mat n n" and AB: "A * B = 1\<^sub>m n"
  shows "B * A = 1\<^sub>m n"
proof -
  have "Determinant.det (A * B) = Determinant.det (1\<^sub>m n)" using AB by auto
  hence "Determinant.det A * Determinant.det B = 1"
    using Determinant.det_mult[OF A B] det_one by auto
  hence det_A: "(Determinant.det A) dvd 1" and det_B: "(Determinant.det B) dvd 1"
    using dvd_triv_left dvd_triv_right by metis+
  hence inv_A: "invertible_mat A" and inv_B: "invertible_mat B"
    using A B invertible_iff_is_unit_JNF by blast+
  obtain B' where inv_BB': "inverts_mat B B'" and inv_B'B: "inverts_mat B' B"
    using inv_B unfolding invertible_mat_def by auto
  have B'_carrier: "B' \<in> carrier_mat n n"
    by (metis B inv_B'B inv_BB' carrier_matD(1) carrier_matD(2) carrier_mat_triv
        index_mult_mat(3) index_one_mat(3) inverts_mat_def)
  have "B * A * B = B" using A AB B by auto
  hence "B * A * (B * B') = B * B'"
    by (smt A AB B B'_carrier assoc_mult_mat carrier_matD(1) inv_BB' inverts_mat_def one_carrier_mat)
  thus ?thesis
    by (metis A B carrier_matD(1) carrier_matD(2) index_mult_mat(3) inv_BB'
        inverts_mat_def right_mult_one_mat')
qed

context comm_ring_1
begin

lemma col_submatrix_UNIV:
assumes "j < card {i. i < dim_col A \<and> i \<in> J}"
shows "col (submatrix A UNIV J) j = col A (pick J j)"
proof (rule eq_vecI)
  show dim_eq:"dim_vec (col (submatrix A UNIV J) j) = dim_vec (col A (pick J j))"
    by (simp add: dim_submatrix(1))
  fix i assume "i < dim_vec (col A (pick J j))"
  show "col (submatrix A UNIV J) j $v i = col A (pick J j) $v i"
    by (smt Collect_cong assms col_def dim_col dim_eq dim_submatrix(1)
        eq_vecI index_vec pick_UNIV submatrix_index)
qed

lemma submatrix_split2: "submatrix A I J = submatrix (submatrix A I UNIV) UNIV J" (is "?lhs = ?rhs")
proof (rule eq_matI)
  show dr: "dim_row ?lhs = dim_row ?rhs"
    by (simp add: dim_submatrix(1))
  show dc: "dim_col ?lhs = dim_col ?rhs"
    by (simp add: dim_submatrix(2))
  fix i j assume i: "i < dim_row ?rhs"
    and j: "j < dim_col ?rhs"
  have "?rhs $$ (i, j) = (submatrix A I UNIV) $$ (pick UNIV i, pick J j)"
  proof (rule submatrix_index)
    show "i < card {i. i < dim_row (submatrix A I UNIV) \<and> i \<in> UNIV}"
      by (metis (full_types) dim_submatrix(1) i)
    show "j < card {j. j < dim_col (submatrix A I UNIV) \<and> j \<in> J}"
      by (metis (full_types) dim_submatrix(2) j)
  qed
  also have "... = A $$ (pick I (pick UNIV i), pick UNIV (pick J j))"
  proof (rule submatrix_index)
    show "pick UNIV i < card {i. i < dim_row A \<and> i \<in> I}"
      by (metis (full_types) dr dim_submatrix(1) i pick_UNIV)
    show "pick J j < card {j. j < dim_col A \<and> j \<in> UNIV}"
      by (metis (full_types) dim_submatrix(2) j pick_le)
  qed
  also have "... = ?lhs $$ (i,j)"
  proof (unfold pick_UNIV, rule submatrix_index[symmetric])
    show "i < card {i. i < dim_row A \<and> i \<in> I}"
      by (metis (full_types) dim_submatrix(1) dr i)
    show "j < card {j. j < dim_col A \<and> j \<in> J}"
      by (metis (full_types) dim_submatrix(2) dc j)
  qed
  finally show "?lhs $$ (i, j) = ?rhs $$ (i, j)" ..
qed

lemma submatrix_mult:
  "submatrix (A*B) I J = submatrix A I UNIV * submatrix B UNIV J" (is "?lhs = ?rhs")
proof (rule eq_matI)
  show "dim_row ?lhs = dim_row ?rhs" unfolding submatrix_def by auto
  show "dim_col ?lhs = dim_col ?rhs" unfolding submatrix_def by auto
  fix i j assume i: "i < dim_row ?rhs" and j: "j < dim_col ?rhs"
  have i1: "i < card {i. i < dim_row (A * B) \<and> i \<in> I}"
    by (metis (full_types) dim_submatrix(1) i index_mult_mat(2))
  have j1: "j < card {j. j < dim_col (A * B) \<and> j \<in> J}"
    by (metis dim_submatrix(2) index_mult_mat(3) j)
  have pi: "pick I i < dim_row A" using i1 pick_le by auto
  have pj: "pick J j < dim_col B" using j1 pick_le by auto
  have row_rw: "Matrix.row (submatrix A I UNIV) i = Matrix.row A (pick I i)"
    using i1 row_submatrix_UNIV by auto
  have col_rw: "col (submatrix B UNIV J) j = col B (pick J j)" using j1 col_submatrix_UNIV by auto
  have "?lhs $$ (i,j) =  (A*B) $$ (pick I i, pick J j)" by (rule submatrix_index[OF i1 j1])
  also have "... = Matrix.row A (pick I i) \<bullet> col B (pick J j)" by (rule index_mult_mat(1)[OF pi pj])
  also have "... = Matrix.row (submatrix A I UNIV) i \<bullet> col (submatrix B UNIV J) j"
    using row_rw col_rw by simp
  also have "... = (?rhs) $$ (i,j)" by (rule index_mult_mat[symmetric], insert i j, auto)
  finally show "?lhs $$ (i, j) = ?rhs $$ (i, j)" .
qed

lemma det_singleton:
  assumes A: "A \<in> carrier_mat 1 1"
  shows "det A = A $$ (0,0)"
  using A unfolding carrier_mat_def Determinant.det_def by auto

lemma submatrix_singleton_index:
  assumes A: "A \<in> carrier_mat n m"
    and an: "a < n" and bm: "b < m"
    shows "submatrix A {a} {b} $$ (0,0) = A $$ (a,b)"
proof -
  have a: "{i. i = a \<and> i < dim_row A} = {a}" using an A unfolding carrier_mat_def by auto
  have b: "{i. i = b \<and> i < dim_col A} = {b}" using bm A unfolding carrier_mat_def by auto
  have "submatrix A {a} {b} $$ (0,0) = A $$ (pick {a} 0,pick {b} 0)"
    by (rule submatrix_index, insert a b, auto)
  moreover have "pick {a} 0 = a" by (auto, metis (full_types) LeastI)
  moreover have "pick {b} 0 = b" by (auto, metis (full_types) LeastI)
  ultimately show ?thesis by simp
qed
end

lemma det_not_inj_on:
  assumes not_inj_on: "\<not> inj_on f {0..<n}"
  shows "det (mat\<^sub>r n n (\<lambda>i. Matrix.row B (f i))) = 0"
proof -
  obtain i j where i: "i<n" and j: "j<n" and fi_fj: "f i = f j" and ij: "i\<noteq>j"
    using not_inj_on unfolding inj_on_def by auto
  show ?thesis
  proof (rule det_identical_rows[OF _ ij i j])
    let ?B="(mat\<^sub>r n n (\<lambda>i. row B (f i)))"
    show "row ?B i = row ?B j"
    proof (rule eq_vecI, auto)
      fix ia assume ia: "ia < n"
      have "row ?B i $ ia = ?B $$ (i, ia)" by (rule index_row(1), insert i ia, auto)
      also have "... = ?B $$ (j, ia)" by (simp add: fi_fj i ia j)
      also have "... = row ?B j $ ia" by (rule index_row(1)[symmetric], insert j ia, auto)
      finally show "row ?B i $ ia = row (mat\<^sub>r n n (\<lambda>i. row B (f i))) j $ ia" by simp
    qed
    show "mat\<^sub>r n n (\<lambda>i. Matrix.row B (f i)) \<in> carrier_mat n n" by auto
  qed
qed



lemma mat_row_transpose: "(mat\<^sub>r nr nc f)\<^sup>T = mat nc nr (\<lambda>(i,j). vec_index (f j) i)"
  by (rule eq_matI, auto)


lemma obtain_inverse_matrix:
  assumes A: "A \<in> carrier_mat n n" and i: "invertible_mat A"
  obtains B where "inverts_mat A B" and "inverts_mat B A" and "B \<in> carrier_mat n n"
proof -
  have "(\<exists>B. inverts_mat A B \<and> inverts_mat B A)" using i unfolding invertible_mat_def by auto
  from this obtain B where AB: "inverts_mat A B" and BA: "inverts_mat B A" by auto
  moreover have "B \<in> carrier_mat n n" using A AB BA unfolding carrier_mat_def inverts_mat_def
    by (auto, metis index_mult_mat(3) index_one_mat(3))+
  ultimately show ?thesis using that by blast
qed


lemma invertible_mat_smult_mat:
  fixes A :: "'a::comm_ring_1 mat"
  assumes inv_A: "invertible_mat A" and k: "k dvd 1"
  shows "invertible_mat (k \<cdot>\<^sub>m A)"
proof -
  obtain n where A: "A \<in> carrier_mat n n" using inv_A unfolding invertible_mat_def by auto
  have det_dvd_1: "Determinant.det A dvd 1" using inv_A invertible_iff_is_unit_JNF[OF A] by auto
  have "Determinant.det (k \<cdot>\<^sub>m A) = k ^ dim_col A * Determinant.det A" by simp
  also have "... dvd 1" by (rule unit_prod, insert k det_dvd_1 dvd_power_same, force+)
  finally show ?thesis using invertible_iff_is_unit_JNF by (metis A smult_carrier_mat)
qed

lemma invertible_mat_one[simp]: "invertible_mat (1\<^sub>m n)"
  unfolding invertible_mat_def using inverts_mat_def by fastforce

lemma four_block_mat_dim0:
  assumes A: "A \<in> carrier_mat n n"
  and B: "B \<in> carrier_mat n 0"
  and C: "C \<in> carrier_mat 0 n"
  and D: "D \<in> carrier_mat 0 0"
shows "four_block_mat A B C D = A"
  unfolding four_block_mat_def using assms by auto


lemma det_four_block_mat_lower_right_id:
  assumes A: "A \<in> carrier_mat m m"
and B: "B = 0\<^sub>m m (n-m)"
and C: "C = 0\<^sub>m (n-m) m"
and D: "D = 1\<^sub>m (n-m)"
and "n>m"
shows "Determinant.det (four_block_mat A B C D) = Determinant.det A"
  using assms
proof (induct n arbitrary: A B C D)
  case 0
  then show ?case by auto
next
  case (Suc n)
  let ?block = "(four_block_mat A B C D)"
  let ?B = "Matrix.mat m (n-m) (\<lambda>(i,j). 0)"
  let ?C = "Matrix.mat (n-m) m (\<lambda>(i,j). 0)"
  let ?D = "1\<^sub>m (n-m)"
  have mat_eq: "(mat_delete ?block n n) = four_block_mat A ?B ?C ?D" (is "?lhs = ?rhs")
  proof (rule eq_matI)
    fix i j assume i: "i < dim_row (four_block_mat A ?B ?C ?D)"
      and j: "j < dim_col (four_block_mat A ?B ?C ?D)"
    let ?f = " (if i < dim_row A then if j < dim_col A then A $$ (i, j) else B $$ (i, j - dim_col A)
     else if j < dim_col A then C $$ (i - dim_row A, j) else D $$ (i - dim_row A, j - dim_col A))"
    let ?g = "(if i < dim_row A then if j < dim_col A then A $$ (i, j) else ?B $$ (i, j - dim_col A)
     else if j < dim_col A then ?C $$ (i - dim_row A, j) else ?D $$ (i - dim_row A, j - dim_col A))"
    have "(mat_delete ?block n n) $$ (i,j) = ?block $$ (i,j)"
      using i j Suc.prems unfolding mat_delete_def by auto
    also have "... = ?f"
      by (rule index_mat_four_block, insert Suc.prems i j, auto)
    also have "... = ?g" using i j Suc.prems by auto
    also have "... = four_block_mat A ?B ?C ?D $$ (i,j)"
      by (rule index_mat_four_block[symmetric], insert Suc.prems i j, auto)
    finally show "?lhs $$ (i,j) = ?rhs $$ (i,j)" .
  qed (insert Suc.prems, auto)
  have nn_1: "?block $$ (n, n) = 1" using Suc.prems by auto
  have rw0: "(\<Sum>i<n. ?block $$ (i,n) * Determinant.cofactor ?block i n) = 0"
  proof (rule sum.neutral, rule)
    fix x assume x: "x \<in> {..<n}"
    have block_index: "?block $$ (x,n) = (if x < dim_row A then if n < dim_col A then A $$ (x, n)
      else B $$ (x, n - dim_col A) else if n < dim_col A then C $$ (x - dim_row A, n)
      else D $$ (x - dim_row A, n - dim_col A))"
      by (rule index_mat_four_block, insert Suc.prems x, auto)
    have "four_block_mat A B C D $$ (x,n) = 0" using x Suc.prems by auto
    thus "four_block_mat A B C D $$ (x, n) * Determinant.cofactor (four_block_mat A B C D) x n = 0"
      by simp
  qed
  have "Determinant.det ?block = (\<Sum>i<Suc n. ?block $$ (i, n) * Determinant.cofactor ?block i n)"
    by (rule laplace_expansion_column, insert Suc.prems, auto)
  also have "... = ?block $$ (n, n) * Determinant.cofactor ?block n n
    + (\<Sum>i<n. ?block $$ (i,n) * Determinant.cofactor ?block i n)"
    by simp
  also have "... = ?block $$ (n, n) * Determinant.cofactor ?block n n" using rw0 by auto
  also have "... = Determinant.cofactor ?block n n" using nn_1 by simp
  also have "... = Determinant.det (mat_delete ?block n n)" unfolding cofactor_def by auto
  also have "... = Determinant.det (four_block_mat A ?B ?C ?D)" using mat_eq by simp
  also have "... = Determinant.det A" (is "Determinant.det ?lhs = Determinant.det ?rhs")
  proof (cases "n = m")
    case True
    have "?lhs = ?rhs" by (rule four_block_mat_dim0, insert Suc.prems True, auto)
    then show ?thesis by simp
  next
    case False
    show ?thesis by (rule Suc.hyps, insert Suc.prems False, auto)
  qed
  finally show ?case .
qed


lemma mult_eq_first_row:
  assumes A: "A \<in> carrier_mat 1 n"
  and B: "B \<in> carrier_mat m n"
  and m0: "m \<noteq> 0"
  and r: "Matrix.row A 0 = Matrix.row B 0"
shows "Matrix.row (A * V) 0 = Matrix.row (B * V) 0"
proof (rule eq_vecI)
  show "dim_vec (Matrix.row (A * V) 0) = dim_vec (Matrix.row (B * V) 0)" using A B r by auto
  fix i assume i: "i < dim_vec (Matrix.row (B * V) 0)"
  have "Matrix.row (A * V) 0 $v i = (A * V) $$ (0,i)" by (rule index_row, insert i A, auto)
  also have "... = Matrix.row A 0 \<bullet> col V i" by (rule index_mult_mat, insert A i, auto)
  also have "... = Matrix.row B 0 \<bullet> col V i" using r by auto
  also have "... = (B * V) $$ (0,i)" by (rule index_mult_mat[symmetric], insert m0 B i, auto)
  also have "... = Matrix.row (B * V) 0 $v i" by (rule index_row[symmetric], insert i B m0, auto)
  finally show "Matrix.row (A * V) 0 $v i = Matrix.row (B * V) 0 $v i" .
qed


lemma smult_mat_mat_one_element:
  assumes A: "A \<in> carrier_mat 1 1" and B: "B \<in> carrier_mat 1 n"
  shows "A * B = A $$ (0,0) \<cdot>\<^sub>m B"
proof (rule eq_matI)
  fix i j assume i: "i < dim_row (A $$ (0, 0) \<cdot>\<^sub>m B)" and j: "j < dim_col (A $$ (0, 0) \<cdot>\<^sub>m B)"
  have i0: "i = 0" using A B i by auto
  have "(A * B) $$ (i, j) =  Matrix.row A i \<bullet> col B j"
    by (rule index_mult_mat, insert i j A B, auto)
  also have "... =  Matrix.row A i $v 0 * col B j $v 0" unfolding scalar_prod_def using B by auto
  also have "... = A$$(i,i) * B$$(i,j)" using A i i0 j by auto
  also have "... = (A $$ (i, i) \<cdot>\<^sub>m B) $$ (i, j)"
    unfolding i by (rule index_smult_mat[symmetric], insert i j B, auto)
  finally show "(A * B) $$ (i, j) = (A $$ (0, 0) \<cdot>\<^sub>m B) $$ (i, j)" using i0 by simp
qed (insert A B, auto)

lemma determinant_one_element:
  assumes A: "A \<in> carrier_mat 1 1" shows "Determinant.det A = A $$ (0,0)"
proof -
  have "Determinant.det A = prod_list (diag_mat A)"
    by (rule det_upper_triangular[OF _ A], insert A, unfold upper_triangular_def, auto)
  also have "... = A $$ (0,0)" using A unfolding diag_mat_def by auto
  finally show ?thesis .
qed



lemma invertible_mat_transpose:
  assumes inv_A: "invertible_mat (A::'a::comm_ring_1 mat)"
  shows "invertible_mat A\<^sup>T"
proof -
  obtain n where A: "A \<in> carrier_mat n n"
    using inv_A unfolding invertible_mat_def square_mat.simps by auto
  hence At: "A\<^sup>T \<in> carrier_mat n n" by simp
  have "Determinant.det A\<^sup>T = Determinant.det A"
    by (metis Determinant.det_def Determinant.det_transpose carrier_matI
        index_transpose_mat(2) index_transpose_mat(3))
  also have "... dvd 1" using invertible_iff_is_unit_JNF[OF A] inv_A by simp
  finally show ?thesis  using invertible_iff_is_unit_JNF[OF At] by auto
qed

lemma dvd_elements_mult_matrix_left:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier_mat m n"
  and P: "P \<in> carrier_mat m m"
  and x: "(\<forall>i j. i<m \<and> j<n \<longrightarrow> x dvd A$$(i,j))"
  shows "(\<forall>i j. i<m \<and> j<n \<longrightarrow> x dvd (P*A)$$(i,j))"
proof -
  have "x dvd (P * A) $$ (i, j)" if i: "i < m" and j: "j < n" for i j
  proof -
    have "(P * A) $$ (i, j) =  (\<Sum>ia = 0..<m. Matrix.row P i $v ia * col A j $v ia)"
      unfolding times_mat_def scalar_prod_def using A P j i by auto
    also have "... = (\<Sum>ia = 0..<m. Matrix.row P i $v ia *  A $$ (ia,j))"
      by (rule sum.cong, insert A j, auto)
    also have "x dvd ..." using x by (meson atLeastLessThan_iff dvd_mult dvd_sum j)
    finally show ?thesis .
  qed
  thus ?thesis by auto
qed


lemma dvd_elements_mult_matrix_right:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier_mat m n"
  and Q: "Q \<in> carrier_mat n n"
  and x: "(\<forall>i j. i<m \<and> j<n \<longrightarrow> x dvd A$$(i,j))"
  shows "(\<forall>i j. i<m \<and> j<n \<longrightarrow> x dvd (A*Q)$$(i,j))"
proof -
  have "x dvd (A*Q) $$ (i, j)" if i: "i < m" and j: "j < n" for i j
  proof -
    have "(A*Q) $$ (i, j) =  (\<Sum>ia = 0..<n. Matrix.row A i $v ia * col Q j $v ia)"
      unfolding times_mat_def scalar_prod_def using A Q j i by auto
    also have "... = (\<Sum>ia = 0..<n. A $$ (i, ia) * col Q j $v ia)"
      by (rule sum.cong, insert A Q i, auto)
    also have "x dvd ..." using x
      by (meson atLeastLessThan_iff dvd_mult2 dvd_sum i)
    finally show ?thesis .
  qed
  thus ?thesis by auto
qed


lemma dvd_elements_mult_matrix_left_right:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier_mat m n"
  and P: "P \<in> carrier_mat m m"
  and Q: "Q \<in> carrier_mat n n"
  and x: "(\<forall>i j. i<m \<and> j<n \<longrightarrow> x dvd A$$(i,j))"
shows "(\<forall>i j. i<m \<and> j<n \<longrightarrow> x dvd (P*A*Q)$$(i,j))"
  using dvd_elements_mult_matrix_left[OF A P x]
  by (meson P A Q dvd_elements_mult_matrix_right mult_carrier_mat)


definition append_cols :: "'a :: zero mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixr "@\<^sub>c" 65)where
  "A @\<^sub>c B = four_block_mat A B (0\<^sub>m 0 (dim_col A)) (0\<^sub>m 0 (dim_col B))"

lemma append_cols_carrier[simp,intro]:
  "A \<in> carrier_mat n a \<Longrightarrow> B \<in> carrier_mat n b \<Longrightarrow> (A @\<^sub>c B) \<in> carrier_mat n (a+b)"
  unfolding append_cols_def by auto

lemma append_cols_mult_left:
  assumes A: "A \<in> carrier_mat n a"
  and B: "B \<in> carrier_mat n b"
  and P: "P \<in> carrier_mat n n"
shows "P * (A @\<^sub>c B) = (P*A) @\<^sub>c (P*B)"
proof -
  let ?P = "four_block_mat P (0\<^sub>m n 0) (0\<^sub>m 0 n) (0\<^sub>m 0 0)"
  have "P = ?P" by (rule eq_matI, auto)
  hence "P * (A @\<^sub>c B) = ?P * (A @\<^sub>c B)" by simp
  also have "?P * (A @\<^sub>c B) = four_block_mat (P * A + 0\<^sub>m n 0 * 0\<^sub>m 0 (dim_col A))
  (P * B + 0\<^sub>m n 0 * 0\<^sub>m 0 (dim_col B)) (0\<^sub>m 0 n * A + 0\<^sub>m 0 0 * 0\<^sub>m 0 (dim_col A))
  (0\<^sub>m 0 n * B + 0\<^sub>m 0 0 * 0\<^sub>m 0 (dim_col B))" unfolding append_cols_def
    by (rule mult_four_block_mat, insert A B P, auto)
  also have "... = four_block_mat (P * A) (P * B) (0\<^sub>m 0 (dim_col (P*A))) (0\<^sub>m 0 (dim_col (P*B)))"
    by (rule cong_four_block_mat, insert P, auto)
  also have "... = (P*A) @\<^sub>c (P*B)" unfolding append_cols_def by auto
  finally show ?thesis .
qed

lemma append_cols_mult_right_id:
  assumes A: "(A::'a::semiring_1 mat) \<in> carrier_mat n 1"
  and B: "B \<in> carrier_mat n (m-1)"
  and C: "C = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m - 1)) (0\<^sub>m (m - 1) 1) D"
  and D: "D \<in> carrier_mat (m-1) (m-1)"
shows "(A @\<^sub>c B) * C = A @\<^sub>c (B * D)"
proof -
  let ?C = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m - 1)) (0\<^sub>m (m - 1) 1) D"
  have "(A @\<^sub>c B) * C = (A @\<^sub>c B) * ?C" unfolding C by auto
  also have "... = four_block_mat A B (0\<^sub>m 0 (dim_col A)) (0\<^sub>m 0 (dim_col B)) * ?C"
    unfolding append_cols_def by auto
  also have "... = four_block_mat (A * 1\<^sub>m 1 + B * 0\<^sub>m (m - 1) 1) (A * 0\<^sub>m 1 (m - 1) + B * D)
    (0\<^sub>m 0 (dim_col A) * 1\<^sub>m 1 + 0\<^sub>m 0 (dim_col B) * 0\<^sub>m (m - 1) 1)
    (0\<^sub>m 0 (dim_col A) * 0\<^sub>m 1 (m - 1) + 0\<^sub>m 0 (dim_col B) * D)"
    by (rule mult_four_block_mat, insert assms, auto)
  also have "... = four_block_mat A (B * D) (0\<^sub>m 0 (dim_col A)) (0\<^sub>m 0 (dim_col (B*D)))"
    by (rule cong_four_block_mat, insert assms, auto)
  also have "... = A @\<^sub>c (B * D)" unfolding append_cols_def by auto
  finally show ?thesis .
qed


lemma append_cols_mult_right_id2:
 assumes A: "(A::'a::semiring_1 mat) \<in> carrier_mat n a"
   and B: "B \<in> carrier_mat n b"
   and C: "C = four_block_mat D (0\<^sub>m a b) (0\<^sub>m b a) (1\<^sub>m b)"
   and D: "D \<in> carrier_mat a a"
shows "(A @\<^sub>c B) * C = (A * D) @\<^sub>c B"
proof -
  let ?C = "four_block_mat D (0\<^sub>m a b) (0\<^sub>m b a) (1\<^sub>m b)"
  have "(A @\<^sub>c B) * C = (A @\<^sub>c B) * ?C" unfolding C by auto
  also have "... = four_block_mat A B (0\<^sub>m 0 a) (0\<^sub>m 0 b) * ?C"
    unfolding append_cols_def using A B by auto
  also have "... = four_block_mat (A * D + B * 0\<^sub>m b a) (A * 0\<^sub>m a b + B * 1\<^sub>m b)
    (0\<^sub>m 0 a * D + 0\<^sub>m 0 b * 0\<^sub>m b a) (0\<^sub>m 0 a * 0\<^sub>m a b + 0\<^sub>m 0 b * 1\<^sub>m b)"
    by (rule mult_four_block_mat, insert A B C D, auto)
  also have "... = four_block_mat (A * D) B (0\<^sub>m 0 (dim_col (A*D))) (0\<^sub>m 0 (dim_col B))"
    by (rule cong_four_block_mat, insert assms, auto)
  also have "... = (A * D) @\<^sub>c B" unfolding append_cols_def by auto
  finally show ?thesis .
qed


lemma append_cols_nth:
  assumes A: "A \<in> carrier_mat n a"
  and B: "B \<in> carrier_mat n b"
  and i: "i<n" and j: "j < a + b"
shows "(A @\<^sub>c B) $$ (i, j) = (if j < dim_col A then A $$(i,j) else B$$(i,j-a))" (is "?lhs = ?rhs")
proof -
  let ?C = "(0\<^sub>m 0 (dim_col A))"
  let ?D = "(0\<^sub>m 0 (dim_col B))"
  have i2: "i < dim_row A + dim_row ?D" using i A by auto
  have j2: "j < dim_col A + dim_col (0\<^sub>m 0 (dim_col B))" using j B A by auto
  have "(A @\<^sub>c B) $$ (i, j) = four_block_mat A B ?C ?D $$ (i, j)"
    unfolding append_cols_def by auto
  also have "... = (if i < dim_row A then if j < dim_col A then A $$ (i, j)
  else B $$ (i, j - dim_col A) else if j < dim_col A then ?C $$ (i - dim_row A, j)
  else 0\<^sub>m 0 (dim_col B) $$ (i - dim_row A, j - dim_col A))"
    by (rule index_mat_four_block(1)[OF i2 j2])
  also have "... = ?rhs" using i A by auto
  finally show ?thesis .
qed

lemma append_cols_split:
  assumes d: "dim_col A > 0"
  shows "A = mat_of_cols (dim_row A) [col A 0] @\<^sub>c
             mat_of_cols (dim_row A) (map (col A) [1..<dim_col A])" (is "?lhs = ?A1 @\<^sub>c ?A2")
proof (rule eq_matI)
  fix i j assume i: "i < dim_row (?A1 @\<^sub>c ?A2)" and j: "j < dim_col (?A1 @\<^sub>c ?A2)"
  have "(?A1 @\<^sub>c ?A2) $$ (i, j) = (if j < dim_col ?A1 then ?A1 $$(i,j) else ?A2$$(i,j-(dim_col ?A1)))"
    by (rule append_cols_nth, insert i j, auto simp add: append_cols_def)
  also have "... = A $$ (i,j)"
  proof (cases "j< dim_col ?A1")
    case True
    then show ?thesis
      by (metis One_nat_def Suc_eq_plus1 add.right_neutral append_cols_def col_def i
          index_mat_four_block(2) index_vec index_zero_mat(2) less_one list.size(3) list.size(4)
          mat_of_cols_Cons_index_0 mat_of_cols_carrier(2) mat_of_cols_carrier(3))
  next
    case False
    then show ?thesis
      by (metis (no_types, lifting) Suc_eq_plus1 Suc_less_eq Suc_pred add_diff_cancel_right' append_cols_def
          diff_zero i index_col index_mat_four_block(2) index_mat_four_block(3) index_zero_mat(2)
          index_zero_mat(3) j length_map length_upt linordered_semidom_class.add_diff_inverse list.size(3)
          list.size(4) mat_of_cols_carrier(2) mat_of_cols_carrier(3) mat_of_cols_index nth_map_upt
          plus_1_eq_Suc upt_0)
  qed
  finally show "A $$ (i, j) = (?A1 @\<^sub>c ?A2) $$ (i, j)" ..
qed (auto simp add: append_cols_def d)


lemma append_rows_nth:
  assumes A: "A \<in> carrier_mat a n"
  and B: "B \<in> carrier_mat b n"
  and i: "i<a+b" and j: "j < n"
shows "(A @\<^sub>r B) $$ (i, j) = (if i < dim_row A then A $$(i,j) else B$$(i-a,j))" (is "?lhs = ?rhs")
proof -
  let ?C = "(0\<^sub>m (dim_row A) 0)"
  let ?D = "(0\<^sub>m (dim_row B) 0)"
  have i2: "i < dim_row A + dim_row ?D" using i j A B by auto
  have j2: "j < dim_col A + dim_col ?D" using i j A B by auto
  have "(A @\<^sub>r B) $$ (i, j) = four_block_mat A ?C B ?D $$ (i, j)"
    unfolding append_rows_def by auto
  also have "... =  (if i < dim_row A then if j < dim_col A then A $$ (i, j) else ?C $$ (i, j - dim_col A)
   else if j < dim_col A then B $$ (i - dim_row A, j) else ?D $$ (i - dim_row A, j - dim_col A))"
    by (rule index_mat_four_block(1)[OF i2 j2])
  also have "... = ?rhs" using i A j B by auto
  finally show ?thesis .
qed

lemma append_rows_split:
  assumes k: "k\<le>dim_row A"
  shows "A = (mat_of_rows (dim_col A) [Matrix.row A i. i \<leftarrow> [0..<k]]) @\<^sub>r
             (mat_of_rows (dim_col A) [Matrix.row A i. i \<leftarrow> [k..<dim_row A]])" (is "?lhs = ?A1 @\<^sub>r ?A2")
proof (rule eq_matI)
  have "(?A1 @\<^sub>r ?A2) \<in> carrier_mat (k + (dim_row A-k)) (dim_col A)"
    by (rule carrier_append_rows, insert k, auto)
  hence A1_A2: "(?A1 @\<^sub>r ?A2) \<in> carrier_mat (dim_row A) (dim_col A)" using k by simp
  thus "dim_row A = dim_row (?A1 @\<^sub>r ?A2)" and "dim_col A = dim_col (?A1 @\<^sub>r ?A2)" by auto
  fix i j assume i: "i < dim_row (?A1 @\<^sub>r ?A2)" and j: "j < dim_col (?A1 @\<^sub>r ?A2)"
  have "(?A1 @\<^sub>r ?A2) $$ (i, j) = (if i < dim_row ?A1 then ?A1 $$(i,j) else ?A2$$(i-(dim_row ?A1),j))"
    by (rule append_rows_nth, insert k i j, auto simp add: append_rows_def)
  also have "... = A $$ (i,j)"
  proof (cases "i<dim_row ?A1")
    case True
    then show ?thesis
      by (metis (no_types, lifting) Matrix.row_def add.left_neutral add.right_neutral append_rows_def
          index_mat(1) index_mat_four_block(3) index_vec index_zero_mat(3) j length_map length_upt
          mat_of_rows_carrier(2,3) mat_of_rows_def nth_map_upt prod.simps(2))
  next
    case False
    let ?xs = "(map (Matrix.row A) [k..<dim_row A])"
    have dim_row_A1: "dim_row ?A1 = k" by auto
    have "?A2 $$ (i-k,j) = ?xs ! (i-k) $v j"
      by (rule mat_of_rows_index, insert i k False A1_A2 j, auto)
    also have "... = A $$ (i,j)" using A1_A2 False i j by auto
    finally show ?thesis using A1_A2 False i j by auto
  qed
  finally show " A $$ (i, j) = (?A1 @\<^sub>r ?A2) $$ (i,j)" by simp
qed



lemma transpose_mat_append_rows:
 assumes A: "A \<in> carrier_mat a n" and B: "B \<in> carrier_mat b n"
 shows "(A @\<^sub>r B)\<^sup>T = A\<^sup>T @\<^sub>c B\<^sup>T"
  by (smt append_cols_def append_rows_def A B carrier_matD(1) index_transpose_mat(3)
      transpose_four_block_mat zero_carrier_mat zero_transpose_mat)

lemma transpose_mat_append_cols:
 assumes A: "A \<in> carrier_mat n a" and B: "B \<in> carrier_mat n b"
 shows "(A @\<^sub>c B)\<^sup>T = A\<^sup>T @\<^sub>r B\<^sup>T"
  by (metis Matrix.transpose_transpose A B carrier_matD(1) carrier_mat_triv
      index_transpose_mat(3) transpose_mat_append_rows)


lemma append_rows_mult_right:
  assumes A: "(A::'a::comm_semiring_1 mat) \<in> carrier_mat a n" and B: "B \<in> carrier_mat b n"
    and Q: "Q\<in> carrier_mat n n"
  shows "(A @\<^sub>r B) * Q = (A * Q) @\<^sub>r (B*Q)"
proof -
  have "transpose_mat ((A @\<^sub>r B) * Q) = Q\<^sup>T * (A @\<^sub>r B)\<^sup>T"
    by (rule transpose_mult, insert A B Q, auto)
  also have "... = Q\<^sup>T * (A\<^sup>T @\<^sub>c B\<^sup>T)" using transpose_mat_append_rows assms by metis
  also have "... = Q\<^sup>T * A\<^sup>T @\<^sub>c Q\<^sup>T * B\<^sup>T"
    using append_cols_mult_left assms by (metis transpose_carrier_mat)
  also have "transpose_mat ... = (A * Q) @\<^sub>r (B*Q)"
    by (smt A B Matrix.transpose_mult Matrix.transpose_transpose append_cols_def append_rows_def Q
        carrier_mat_triv index_mult_mat(2) index_transpose_mat(2) transpose_four_block_mat
        zero_carrier_mat zero_transpose_mat)
  finally show ?thesis by simp
qed

lemma append_rows_mult_left_id:
  assumes A: "(A::'a::comm_semiring_1 mat) \<in> carrier_mat 1 n"
  and B: "B \<in> carrier_mat (m-1) n"
  and C: "C = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m - 1)) (0\<^sub>m (m - 1) 1) D"
  and D: "D \<in> carrier_mat (m-1) (m-1)"
shows "C * (A @\<^sub>r B) = A @\<^sub>r (D * B)"
proof -
  have "transpose_mat (C * (A @\<^sub>r B)) = (A @\<^sub>r B)\<^sup>T * C\<^sup>T"
    by (metis (no_types, lifting) B C D Matrix.transpose_mult append_rows_def A carrier_matD
        carrier_mat_triv index_mat_four_block(2,3) index_zero_mat(2) one_carrier_mat)
  also have "... = (A\<^sup>T @\<^sub>c B\<^sup>T) * C\<^sup>T" using transpose_mat_append_rows[OF A B] by auto
  also have "... = A\<^sup>T @\<^sub>c (B\<^sup>T * D\<^sup>T)" by (rule append_cols_mult_right_id, insert A B C D, auto)
  also have "transpose_mat ... = A @\<^sub>r (D * B)"
    by (smt B D Matrix.transpose_mult Matrix.transpose_transpose append_cols_def append_rows_def A
        carrier_matD(2) carrier_mat_triv index_mult_mat(3) index_transpose_mat(3)
        transpose_four_block_mat zero_carrier_mat zero_transpose_mat)
  finally show ?thesis by auto
qed

lemma append_rows_mult_left_id2:
 assumes A: "(A::'a::comm_semiring_1 mat) \<in> carrier_mat a n"
   and B: "B \<in> carrier_mat b n"
   and C: "C = four_block_mat D (0\<^sub>m a b) (0\<^sub>m b a) (1\<^sub>m b)"
   and D: "D \<in> carrier_mat a a"
 shows "C * (A @\<^sub>r B) = (D * A) @\<^sub>r B"
proof -
  have "(C * (A @\<^sub>r B))\<^sup>T = (A @\<^sub>r B)\<^sup>T * C\<^sup>T" by (rule transpose_mult, insert assms, auto)
  also have "... = (A\<^sup>T @\<^sub>c B\<^sup>T) * C\<^sup>T" by (metis A B transpose_mat_append_rows)
  also have "... = (A\<^sup>T * D\<^sup>T @\<^sub>c B\<^sup>T)" by (rule append_cols_mult_right_id2, insert assms, auto)
  also have "...\<^sup>T = (D * A) @\<^sub>r B"
    by (metis A B D transpose_mult transpose_transpose mult_carrier_mat transpose_mat_append_rows)
  finally show ?thesis by simp
qed

lemma four_block_mat_preserves_column:
  assumes A: "(A::'a::semiring_1 mat) \<in> carrier_mat n m"
    and B: "B = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (m - 1)) (0\<^sub>m (m - 1) 1) C"
  and C: "C \<in> carrier_mat (m-1) (m-1)"
  and i: "i<n" and m: "0<m"
shows "(A*B) $$ (i,0) = A $$ (i,0)"
proof -
  let ?A1 = "mat_of_cols n [col A 0]"
  let ?A2 = "mat_of_cols n (map (col A) [1..<dim_col A])"
  have n2: "dim_row A = n" using A by auto
  have "A = ?A1 @\<^sub>c ?A2" by (rule append_cols_split[of A, unfolded n2], insert m A, auto)
  hence "A * B = (?A1 @\<^sub>c ?A2) * B" by simp
  also have "... = ?A1 @\<^sub>c (?A2 * C)" by (rule append_cols_mult_right_id[OF _ _ B C], insert A, auto)
  also have "... $$ (i,0) = ?A1 $$ (i,0)" using append_cols_nth by (simp add: append_cols_def i)
  also have "... = A $$ (i,0)"
    by (metis A i carrier_matD(1) col_def index_vec mat_of_cols_Cons_index_0)
  finally show ?thesis .
qed


definition "lower_triangular A = (\<forall>i j. i < j \<and> i < dim_row A \<and> j < dim_col A \<longrightarrow> A $$ (i,j) = 0)"

lemma lower_triangular_index:
  assumes "lower_triangular A" "i<j" "i < dim_row A" "j < dim_col A"
  shows "A $$ (i,j) = 0"
  using assms unfolding lower_triangular_def by auto

lemma commute_multiples_identity:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier_mat n n"
  shows "A * (k \<cdot>\<^sub>m (1\<^sub>m n)) = (k \<cdot>\<^sub>m (1\<^sub>m n)) * A"
proof -
  have "(\<Sum>ia = 0..<n. A $$ (i, ia) * (k * (if ia = j then 1 else 0)))
    = (\<Sum>ia = 0..<n. k * (if i = ia then 1 else 0) * A $$ (ia, j))" (is "?lhs=?rhs")
    if i: "i<n" and j: "j<n" for i j
  proof -
    let ?f = "\<lambda>ia. A $$ (i, ia) * (k * (if ia = j then 1 else 0))"
    let ?g = "\<lambda>ia. k * (if i = ia then 1 else 0) * A $$ (ia, j)"
    have rw0: "(\<Sum>ia \<in> ({0..<n}-{j}). ?f ia) = 0" by (rule sum.neutral, auto)
    have rw0': "(\<Sum>ia \<in> ({0..<n}-{i}). ?g ia) = 0" by (rule sum.neutral, auto)
    have "?lhs = ?f j + (\<Sum>ia \<in> ({0..<n}-{j}). ?f ia)"
      by (smt atLeast0LessThan finite_atLeastLessThan lessThan_iff sum.remove j)
    also have "... = A $$ (i, j) * k" using rw0 by auto
    also have "... = ?g i + (\<Sum>ia \<in> ({0..<n}-{i}). ?g ia)" using rw0' by auto
    also have "... = ?rhs"
      by (smt atLeast0LessThan finite_atLeastLessThan lessThan_iff sum.remove i)
    finally show ?thesis .
  qed
  thus ?thesis using A
  unfolding times_mat_def scalar_prod_def
  by auto (rule eq_matI, auto, smt sum.cong)
qed

(*This lemma is obtained using Mod_Type_Connect, otherwise we cannot prove HMA_I 0 0.
The lelma could also be obtained with no use of transfer rules, proving it directly.*)
lemma det_2:
  assumes A: "A \<in> carrier_mat 2 2"
  shows "Determinant.det A = A$$(0,0) * A $$ (1,1) - A$$(0,1)*A$$(1,0)"
proof -
  let ?A = "(Mod_Type_Connect.to_hma\<^sub>m A)::'a^2^2"
  have [transfer_rule]: "Mod_Type_Connect.HMA_M A ?A"
    unfolding Mod_Type_Connect.HMA_M_def using from_hma_to_hma\<^sub>m A by auto
  have [transfer_rule]: "Mod_Type_Connect.HMA_I 0 0"
    unfolding Mod_Type_Connect.HMA_I_def by (simp add: to_nat_0)
  have [transfer_rule]: "Mod_Type_Connect.HMA_I 1 1"
    unfolding Mod_Type_Connect.HMA_I_def by (simp add: to_nat_1)
  have "Determinant.det A = Determinants.det ?A" by (transfer, simp)
  also have "... = ?A $h 1 $h 1 * ?A $h 2 $h 2 - ?A $h 1 $h 2 * ?A $h 2 $h 1" unfolding det_2 by simp
  also have "... = ?A $h 0 $h 0 * ?A $h 1 $h 1 - ?A $h 0 $h 1 * ?A $h 1 $h 0"
    by (smt Groups.mult_ac(2) exhaust_2 semiring_norm(160))
  also have "... = A$$(0,0) * A $$ (1,1) - A$$(0,1)*A$$(1,0)"
    unfolding index_hma_def[symmetric] by (transfer, auto)
  finally show ?thesis .
qed

lemma mat_diag_smult: "mat_diag n (\<lambda> x. (k::'a::comm_ring_1)) = (k \<cdot>\<^sub>m 1\<^sub>m n)"
proof -
  have "mat_diag n (\<lambda> x. k) = mat_diag n (\<lambda> x. k * 1)" by auto
  also have "... = mat_diag n (\<lambda> x. k) * mat_diag n (\<lambda> x. 1)" using mat_diag_diag
    by (simp add: mat_diag_def)
  also have "... = mat_diag n (\<lambda> x. k) * (1\<^sub>m n)" by auto  thm mat_diag_mult_left
  also have "... = Matrix.mat n n (\<lambda>(i, j). k * (1\<^sub>m n) $$ (i, j))" by (rule mat_diag_mult_left, auto)
  also have "... = (k \<cdot>\<^sub>m 1\<^sub>m n)" unfolding smult_mat_def by auto
  finally show ?thesis .
qed

lemma invertible_mat_four_block_mat_lower_right:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier_mat n n" and inv_A: "invertible_mat A"
  shows "invertible_mat (four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) A)"
proof -
  let ?I = "(four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 n) (0\<^sub>m n 1) A)"
  have "Determinant.det ?I = Determinant.det (1\<^sub>m 1) * Determinant.det A"
    by (rule det_four_block_mat_lower_left_zero_col, insert assms, auto)
  also have "... = Determinant.det A" by auto
  finally have "Determinant.det ?I = Determinant.det A" .
  thus ?thesis
    by (metis (no_types, lifting) assms carrier_matD(1) carrier_matD(2) carrier_mat_triv
        index_mat_four_block(2) index_mat_four_block(3) index_one_mat(2) index_one_mat(3)
        invertible_iff_is_unit_JNF)
qed


lemma invertible_mat_four_block_mat_lower_right_id:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier_mat m m" and B: "B = 0\<^sub>m m (n-m)" and C: "C = 0\<^sub>m (n-m) m"
    and D: "D = 1\<^sub>m (n-m)" and "n>m" and inv_A: "invertible_mat A"
  shows "invertible_mat (four_block_mat A B C D)"
proof -
  have "Determinant.det (four_block_mat A B C D) = Determinant.det A"
    by (rule det_four_block_mat_lower_right_id, insert assms, auto)
  thus ?thesis using inv_A
    by (metis (no_types, lifting) assms(1) assms(4) carrier_matD(1) carrier_matD(2) carrier_mat_triv
        index_mat_four_block(2) index_mat_four_block(3) index_one_mat(2) index_one_mat(3)
        invertible_iff_is_unit_JNF)
qed

lemma split_block4_decreases_dim_row:
  assumes E: "(A,B,C,D) = split_block E 1 1"
    and E1: "dim_row E > 1" and E2: "dim_col E > 1"
  shows "dim_row D < dim_row E"
proof -
  have "D \<in> carrier_mat (1 + (dim_row E - 2)) (1 + (dim_col E - 2))"
    by (rule split_block(4)[OF E[symmetric]], insert E1 E2, auto)
  hence "D \<in> carrier_mat (dim_row E - 1) (dim_col E - 1)" using E1 E2 by auto
  thus ?thesis using E1 by auto
qed


lemma inv_P'PAQQ':
  assumes A: "A \<in> carrier_mat n n"
    and P: "P \<in> carrier_mat n n"
    and inv_P: "inverts_mat P' P"
    and inv_Q: "inverts_mat Q Q'"
    and Q: "Q \<in> carrier_mat n n"
    and P': "P' \<in> carrier_mat n n"
    and Q': "Q' \<in> carrier_mat n n"
shows  "(P'*(P*A*Q)*Q') = A"
proof -
  have "(P'*(P*A*Q)*Q') = (P'*(P*A*Q*Q'))"
    by (smt P P' Q Q' assoc_mult_mat carrier_matD(1) carrier_matD(2) carrier_mat_triv
        index_mult_mat(2) index_mult_mat(3))
  also have "... = ((P'*P)*A*(Q*Q'))"
    by (smt A P P' Q Q' assoc_mult_mat carrier_matD(1) carrier_matD(2) carrier_mat_triv
        index_mult_mat(3) inv_Q inverts_mat_def right_mult_one_mat')
  finally show ?thesis
    by (metis P' Q A inv_P inv_Q carrier_matD(1) inverts_mat_def
        left_mult_one_mat right_mult_one_mat)
qed

lemma
  assumes "U \<in> carrier_mat 2 2" and "V \<in> carrier_mat 2 2" and "A = U * V"
shows mat_mult2_00: "A $$ (0,0) = U $$ (0,0)*V $$ (0,0) + U $$ (0,1)*V $$ (1,0)"
  and mat_mult2_01: "A $$ (0,1) = U $$ (0,0)*V $$ (0,1) + U $$ (0,1)*V $$ (1,1)"
  and mat_mult2_10: "A $$ (1,0) = U $$ (1,0)*V $$ (0,0) + U $$ (1,1)*V $$ (1,0)"
  and mat_mult2_11: "A $$ (1,1) = U $$ (1,0)*V $$ (0,1) + U $$ (1,1)*V $$ (1,1)"
    using assms unfolding times_mat_def Matrix.row_def col_def scalar_prod_def
    using sum_two_rw by auto


subsection\<open>Lemmas about @{text "sorted lists"}, @{text "insort"} and @{text "pick"}\<close>


lemma sorted_distinct_imp_sorted_wrt:
  assumes "sorted xs" and "distinct xs"
  shows "sorted_wrt (<) xs"
  using assms
  by (induct xs, insert le_neq_trans, auto)


lemma sorted_map_strict:
  assumes "strict_mono_on g {0..<n}"
  shows "sorted (map g [0..<n])"
  using assms
  by (induct n, auto simp add: sorted_append strict_mono_on_def less_imp_le)


lemma sorted_list_of_set_map_strict:
  assumes "strict_mono_on g {0..<n}"
  shows "sorted_list_of_set (g ` {0..<n}) = map g [0..<n]"
  using assms
  proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note sg = Suc.prems
  have sg_n: "strict_mono_on g {0..<n}" using sg unfolding strict_mono_on_def by auto
  have g_image_rw: "g ` {0..<Suc n} = insert (g n) (g ` {0..<n})"
    by (simp add: set_upt_Suc)
  have "sorted_list_of_set (g ` {0..<Suc n}) = sorted_list_of_set (insert (g n) (g ` {0..<n}))"
    using g_image_rw by simp
  also have "... = insort (g n) (sorted_list_of_set (g ` {0..<n}))"
  proof (rule sorted_list_of_set.insert)
    have "inj_on g {0..<Suc n}" using sg strict_mono_on_imp_inj_on by blast
    thus "g n \<notin> g ` {0..<n}" unfolding inj_on_def by fastforce
  qed (simp)
  also have "... = insort (g n) (map g [0..<n])"
    using Suc.hyps sg unfolding strict_mono_on_def by auto
  also have "... = map g [0..<Suc n]"
  proof (simp, rule sorted_insort_is_snoc)
    show "sorted (map g [0..<n])" by (rule sorted_map_strict[OF sg_n])
    show "\<forall>x\<in>set (map g [0..<n]). x \<le> g n" using sg unfolding strict_mono_on_def
      by (simp add: less_imp_le)
  qed
  finally show ?case .
qed


lemma sorted_nth_strict_mono:
  "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow>i < j \<Longrightarrow> j < length xs \<Longrightarrow> xs!i < xs!j"
  by (simp add: less_le nth_eq_iff_index_eq sorted_iff_nth_mono_less)


lemma sorted_list_of_set_0_LEAST:
  assumes finI: "finite I" and I: "I \<noteq> {}"
  shows "sorted_list_of_set I ! 0 = (LEAST n. n\<in>I)"
proof (rule Least_equality[symmetric])
  show "sorted_list_of_set I ! 0 \<in> I"
    by (metis I Max_in finI gr_zeroI in_set_conv_nth not_less_zero set_sorted_list_of_set)
  fix y assume "y \<in> I"
  thus "sorted_list_of_set I ! 0 \<le> y"
    by (metis eq_iff finI in_set_conv_nth neq0_conv sorted_iff_nth_mono_less
        sorted_list_of_set(1) sorted_sorted_list_of_set)
qed

lemma sorted_list_of_set_eq_pick:
  assumes i: "i < length (sorted_list_of_set I)"
  shows "sorted_list_of_set I ! i = pick I i"
proof -
  have finI: "finite I"
  proof (rule ccontr)
    assume "infinite I"
    hence "length (sorted_list_of_set I) = 0" using sorted_list_of_set.infinite by auto
    thus False using i by simp
  qed
  show ?thesis
  using i
proof (induct i)
  case 0
  have I: "I \<noteq> {}" using "0.prems" sorted_list_of_set_empty by blast
  show ?case unfolding pick.simps by (rule sorted_list_of_set_0_LEAST[OF finI I])
next
  case (Suc i)
  note x_less = Suc.prems
  show ?case
  proof (unfold pick.simps, rule Least_equality[symmetric], rule conjI)
    show 1: "pick I i < sorted_list_of_set I ! Suc i"
      by (metis Suc.hyps Suc.prems Suc_lessD distinct_sorted_list_of_set find_first_unique lessI
          nat_less_le sorted_sorted_list_of_set sorted_sorted_wrt sorted_wrt_nth_less)
    show "sorted_list_of_set I ! Suc i \<in> I"
      using Suc.prems finI nth_mem set_sorted_list_of_set by blast
    have rw: "sorted_list_of_set I ! i = pick I i"
      using Suc.hyps Suc_lessD x_less by blast
    have sorted_less: "sorted_list_of_set I ! i < sorted_list_of_set I ! Suc i"
      by (simp add: 1 rw)
    fix y assume y: "y \<in> I \<and> pick I i < y"
    show "sorted_list_of_set I ! Suc i \<le> y"
      by (smt antisym_conv finI in_set_conv_nth less_Suc_eq less_Suc_eq_le nat_neq_iff rw
          sorted_iff_nth_mono_less sorted_list_of_set(1) sorted_sorted_list_of_set x_less y)
  qed
qed
qed

text\<open>$b$ is the position where we add, $a$ the element to be added and $i$ the position
  that is checked\<close>

lemma insort_nth':
  assumes "\<forall>j<b. xs ! j < a" and "sorted xs" and "a \<notin> set xs"
    and "i < length xs + 1" and "i < b"
    and "xs \<noteq> []" and "b < length xs"
  shows "insort a xs ! i = xs ! i"
  using assms
proof (induct xs arbitrary: a b i)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  note less = Cons.prems(1)
  note sorted = Cons.prems(2)
  note a_notin = Cons.prems(3)
  note i_length = Cons.prems(4)
  note i_b = Cons.prems(5)
  note b_length = Cons.prems(7)
  show ?case
  proof (cases "a \<le> x")
    case True
    have "insort a (x # xs) ! i = (a # x # xs) ! i" using True by simp
    also have "... =  (x # xs) ! i"
      using Cons.prems(1) Cons.prems(5) True by force
    finally show ?thesis .
  next
    case False note x_less_a = False
    have "insort a (x # xs) ! i = (x # insort a xs) ! i" using False by simp
    also have "... = (x # xs) ! i"
    proof (cases "i = 0")
      case True
      then show ?thesis by auto
    next
      case False
      have "(x # insort a xs) ! i = (insort a xs) ! (i-1)"
        by (simp add: False nth_Cons')
      also have "... = xs ! (i-1)"
      proof (rule Cons.hyps)
        show "sorted xs" using sorted by simp
        show "a \<notin> set xs" using a_notin by simp
        show "i - 1 < length xs + 1" using i_length False by auto
        show "xs \<noteq> []" using i_b b_length by force
        show "i - 1 < b - 1" by (simp add: False diff_less_mono i_b leI)
        show "b - 1 < length xs" using b_length i_b by auto
        show "\<forall>j<b - 1. xs ! j < a" using less less_diff_conv by auto
      qed
      also have "... = (x # xs) ! i" by (simp add: False nth_Cons')
      finally show ?thesis .
    qed
    finally show ?thesis .
  qed
qed


lemma insort_nth:
  assumes  "sorted xs" and "a \<notin> set xs"
    and "i < index (insort a xs) a"
    and "xs \<noteq> []"
  shows "insort a xs ! i = xs ! i"
  using assms
proof (induct xs arbitrary: a i)
case Nil
  then show ?case by auto
next
  case (Cons x xs)
  note sorted = Cons.prems(1)
  note a_notin = Cons.prems(2)
  note i_index = Cons.prems(3)
  show ?case
  proof (cases "a \<le> x")
    case True
    have "insort a (x # xs) ! i = (a # x # xs) ! i" using True by simp
    also have "... = (x # xs) ! i"
      using Cons.prems(1) Cons.prems(3) True by force
    finally show ?thesis .
  next
    case False note x_less_a = False
    show ?thesis
    proof (cases "xs = []")
      case True
      have "x \<noteq> a" using False by auto
      then show ?thesis  using True i_index False by auto
    next
      case False note xs_not_empty = False
      have "insort a (x # xs) ! i = (x # insort a xs) ! i" using x_less_a by simp
      also have "... = (x # xs) ! i"
      proof (cases "i = 0")
        case True
        then show ?thesis by auto
      next
        case False note i0 = False
        have "(x # insort a xs) ! i = (insort a xs) ! (i-1)"
          by (simp add: False nth_Cons')
        also have "... = xs ! (i-1)"
        proof (rule Cons.hyps[OF _ _ _ xs_not_empty])
          show "sorted xs" using sorted by simp
          show "a \<notin> set xs" using a_notin by simp
          have "index (insort a (x # xs)) a = index ((x # insort a xs)) a"
            using x_less_a by auto
          also have "... = index (insort a xs) a + 1"
            unfolding index_Cons using x_less_a by simp
          finally show "i - 1 < index (insort a xs) a" using False i_index by linarith
        qed
        also have "... = (x # xs) ! i" by (simp add: False nth_Cons')
        finally show ?thesis .
      qed
      finally show ?thesis .
    qed
  qed
qed

lemma insort_nth2:
  assumes "sorted xs" and "a \<notin> set xs"
    and "i < length xs" and "i \<ge> index (insort a xs) a"
    and "xs \<noteq> []"
  shows "insort a xs ! (Suc i) = xs ! i"
  using assms
proof (induct xs arbitrary: a i)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  note sorted = Cons.prems(1)
  note a_notin = Cons.prems(2)
  note i_length = Cons.prems(3)
  note index_i = Cons.prems(4)
  show ?case
  proof (cases "a \<le> x")
    case True
    have "insort a (x # xs) ! (Suc i) = (a # x # xs) ! (Suc i)" using True by simp
    also have "... =  (x # xs) ! i"
      using Cons.prems(1) Cons.prems(5) True by force
    finally show ?thesis .
  next
    case False note x_less_a = False
    have "insort a (x # xs) ! (Suc i) = (x # insort a xs) ! (Suc i)" using False by simp
    also have "... = (x # xs) ! i"
    proof (cases "i = 0")
        case True
        then show ?thesis using index_i linear x_less_a by fastforce
      next
        case False note i0 = False
        show ?thesis
        proof -
          have Suc_i: "Suc (i - 1) = i"
            using i0 by auto
          have "(x # insort a xs) ! (Suc i) = (insort a xs) ! i"
            by (simp add: nth_Cons')
          also have "... = (insort a xs) ! Suc (i - 1)" using Suc_i by simp
          also have "... = xs ! (i - 1)"
          proof (rule Cons.hyps)
            show "sorted xs" using sorted by simp
            show "a \<notin> set xs" using a_notin by simp
            show "i - 1 < length xs" using i_length using Suc_i by auto
            thus "xs \<noteq> []" by auto
            have "index (insort a (x # xs)) a = index ((x # insort a xs)) a" using x_less_a by simp
            also have "... = index (insort a xs) a + 1" unfolding index_Cons using x_less_a by simp
            finally show "index (insort a xs) a \<le> i - 1" using index_i i0 by auto
          qed
          also have "... = (x # xs) ! i" using Suc_i by auto
          finally show ?thesis .
        qed
      qed
      finally show ?thesis .
    qed
qed

lemma pick_index:
  assumes a: "a \<in> I" and a'_card: "a' < card I"
  shows "(pick I a' = a) = (index (sorted_list_of_set I) a = a')"
proof -
  have finI: "finite I" using a'_card card.infinite by force
  have length_I: "length (sorted_list_of_set I) = card I"
    by (metis a'_card card.infinite distinct_card distinct_sorted_list_of_set
        not_less_zero set_sorted_list_of_set)
  let ?i = "index (sorted_list_of_set I) a"
  have "(sorted_list_of_set I) ! a' = pick I a'"
    by (rule sorted_list_of_set_eq_pick, auto simp add: finI a'_card length_I)
  moreover have "(sorted_list_of_set I) ! ?i = a"
    by (rule nth_index, simp add: a finI)
  ultimately show ?thesis
    by (metis a'_card distinct_sorted_list_of_set index_nth_id length_I)
qed

end

