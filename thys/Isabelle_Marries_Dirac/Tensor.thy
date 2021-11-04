(* Author: Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk *)

section \<open>Tensor Products\<close>

theory Tensor
imports  
  Complex_Vectors
  Matrix_Tensor.Matrix_Tensor
  Jordan_Normal_Form.Matrix
begin


text \<open>
There is already a formalization of tensor products in the Archive of Formal Proofs, 
namely Matrix\_Tensor.thy in Tensor Product of Matrices[1] by T.V.H. Prathamesh, but it does not build 
on top of the formalization of vectors and matrices given in Matrices, Jordan Normal Forms, and 
Spectral Radius Theory[2] by René Thiemann and Akihisa Yamada. 
In the present theory our purpose consists in giving such a formalization. Of course, we will reuse 
Prathamesh's code as much as possible, and in order to achieve that we formalize some lemmas that
translate back and forth between vectors (resp. matrices) seen as lists (resp. lists of lists) and 
vectors (resp. matrices) as formalized in [2].
\<close>

subsection \<open>The Kronecker Product of Complex Vectors\<close>

definition tensor_vec:: "complex Matrix.vec \<Rightarrow> complex Matrix.vec \<Rightarrow> complex Matrix.vec" (infixl "\<otimes>" 63) 
where "tensor_vec u v \<equiv> vec_of_list (mult.vec_vec_Tensor (*) (list_of_vec u) (list_of_vec v))"

subsection \<open>The Tensor Product of Complex Matrices\<close>

text \<open>To see a matrix in the sense of [2] as a matrix in the sense of [1], we convert it into its list
of column vectors.\<close>

definition mat_to_cols_list:: "complex Matrix.mat \<Rightarrow> complex list list" where
  "mat_to_cols_list A = [[A $$ (i,j) . i <- [0..< dim_row A]] . j <- [0..< dim_col A]]"

lemma length_mat_to_cols_list [simp]:
  "length (mat_to_cols_list A) = dim_col A"
  by (simp add: mat_to_cols_list_def)

lemma length_cols_mat_to_cols_list [simp]:
  assumes "j < dim_col A"
  shows "length [A $$ (i,j) . i <- [0..< dim_row A]] = dim_row A"
  using assms by simp

lemma length_row_mat_to_cols_list [simp]:
  assumes "i < dim_row A"
  shows "length (row (mat_to_cols_list A) i) = dim_col A"
  using assms by (simp add: row_def)

lemma length_col_mat_to_cols_list [simp]:
  assumes "j < dim_col A"
  shows "length (col (mat_to_cols_list A) j) = dim_row A"
  using assms by (simp add: col_def mat_to_cols_list_def)

lemma mat_to_cols_list_is_not_Nil [simp]:
  assumes "dim_col A > 0"
  shows "mat_to_cols_list A \<noteq> []"
  using assms by (simp add: mat_to_cols_list_def)

text \<open>Link between Matrix\_Tensor.row\_length and Matrix.dim\_row\<close>

lemma row_length_mat_to_cols_list [simp]:
  assumes "dim_col A > 0"
  shows "mult.row_length (mat_to_cols_list A) = dim_row A"
proof -
  have "mat_to_cols_list A \<noteq> []" by (simp add: assms)
  then have "mult.row_length (mat_to_cols_list A) = length (hd (mat_to_cols_list A))"
    using mult.row_length_def[of "1" "(*)"]
    by (simp add: \<open>\<And>xs. Matrix_Tensor.mult 1 (*) \<Longrightarrow> mult.row_length xs \<equiv> if xs = [] then 0 else length (hd xs)\<close> mult.intro)
  thus ?thesis by (simp add: assms mat_to_cols_list_def upt_conv_Cons)
qed

text \<open>@{term mat_to_cols_list} is a matrix in the sense of @{theory Matrix.Matrix_Legacy}.\<close>

lemma mat_to_cols_list_is_mat [simp]:
  assumes "dim_col A > 0"
  shows "mat (mult.row_length (mat_to_cols_list A)) (length (mat_to_cols_list A)) (mat_to_cols_list A)"
proof -
  have "Ball (set (mat_to_cols_list A)) (Matrix_Legacy.vec (mult.row_length (mat_to_cols_list A)))"
    using assms row_length_mat_to_cols_list mat_to_cols_list_def Ball_def set_def vec_def by fastforce
  thus ?thesis by(auto simp: mat_def)
qed

definition mat_of_cols_list:: "nat \<Rightarrow> complex list list \<Rightarrow> complex Matrix.mat" where
  "mat_of_cols_list nr cs = Matrix.mat nr (length cs) (\<lambda> (i,j). cs ! j ! i)"

lemma index_mat_of_cols_list [simp]:
  assumes "i < nr" and "j < length cs"
  shows "mat_of_cols_list nr cs $$ (i,j) = cs ! j ! i"
  by (simp add: assms mat_of_cols_list_def) 

lemma mat_to_cols_list_to_mat [simp]:
  "mat_of_cols_list (dim_row A) (mat_to_cols_list A) = A"
proof
  show f1:"dim_row (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) = dim_row A" 
    by (simp add: mat_of_cols_list_def)
next
  show f2:"dim_col (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) = dim_col A"
    by (simp add: Tensor.mat_of_cols_list_def)
next
  show "\<And>i j. i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> 
    (mat_of_cols_list (dim_row A) (mat_to_cols_list A)) $$ (i, j) = A $$ (i, j)"
    by (simp add: mat_of_cols_list_def mat_to_cols_list_def)
qed

lemma plus_mult_cpx [simp]:
  "plus_mult 1 (*) 0 (+) (a_inv cpx_rng)"
  apply unfold_locales
  apply (auto intro: cpx_cring_is_field simp: field_simps)
proof -
  show "\<And>x. x + \<ominus>\<^bsub>cpx_rng\<^esub> x = 0"
    using group.r_inv[of "cpx_rng"] cpx_cring_is_field field_def domain_def cpx_rng_def
    by (metis UNIV_I cring.cring_simprules(17) ordered_semiring_record_simps(1) 
        ordered_semiring_record_simps(11) ordered_semiring_record_simps(12))
  show "\<And>x. x + \<ominus>\<^bsub>cpx_rng\<^esub> x = 0"
    using group.r_inv[of "cpx_rng"] cpx_cring_is_field field_def domain_def cpx_rng_def
    by (metis UNIV_I cring.cring_simprules(17) ordered_semiring_record_simps(1) 
        ordered_semiring_record_simps(11) ordered_semiring_record_simps(12))
qed

lemma list_to_mat_to_cols_list [simp]:
  fixes l::"complex list list"
  assumes "mat nr nc l"
  shows "mat_to_cols_list (mat_of_cols_list nr l) = l"
proof -
  have "length (mat_to_cols_list (mat_of_cols_list nr l)) = length l"
    by (simp add: mat_of_cols_list_def)
  moreover have f1:"\<forall>j<length l. length(l ! j) = mult.row_length l"
    using assms plus_mult.row_length_constant plus_mult_cpx by fastforce
  moreover have "\<And>j. j<length l \<longrightarrow> mat_to_cols_list (mat_of_cols_list nr l) ! j = l ! j"
  proof
    fix j
    assume a:"j < length l"
    then have f2:"length (mat_to_cols_list (mat_of_cols_list nr l) ! j) = length (l ! j)"
      by (metis col_def mat_def vec_def mat_of_cols_list_def assms dim_col_mat(1) dim_row_mat(1) 
length_col_mat_to_cols_list nth_mem)
    then have "\<forall>i<mult.row_length l. mat_to_cols_list (mat_of_cols_list nr l) ! j ! i = l ! j ! i"
      using a mat_to_cols_list_def mat_of_cols_list_def f1 by simp
    thus "mat_to_cols_list (Tensor.mat_of_cols_list nr l) ! j = l ! j"
      using f2 by(simp add: nth_equalityI a f1)
  qed
  ultimately show ?thesis using nth_equalityI by metis
qed

lemma col_mat_of_cols_list [simp]:
  assumes "j < length l"
  shows "Matrix.col (mat_of_cols_list (length (l ! j)) l) j = vec_of_list (l ! j)"
proof -
  define u where "u = Matrix.col (mat_of_cols_list (length (l ! j)) l) j"
  then have "dim_vec u = dim_vec (vec_of_list (l ! j))"
    by (auto simp: u_def mat_of_cols_list_def Matrix.col_def vec_of_list_def)
      (metis dim_vec_of_list vec_of_list.abs_eq)
  moreover have "\<forall>i<length(l ! j). u $ i = vec_of_list (l ! j) $ i"
    by (simp add: u_def vec_of_list_index mat_of_cols_list_def assms)
  ultimately show ?thesis by(simp add: vec_eq_iff u_def)
qed

definition tensor_mat:: "[complex Matrix.mat, complex Matrix.mat] \<Rightarrow> complex Matrix.mat" (infixl "\<Otimes>" 63) where 
"tensor_mat A B \<equiv> 
  mat_of_cols_list (dim_row A * dim_row B) (mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list B))"
  
lemma dim_row_tensor_mat [simp]:
  "dim_row (A \<Otimes> B) = dim_row A * dim_row B"
  by (simp add: mat_of_cols_list_def tensor_mat_def)

lemma dim_col_tensor_mat [simp]:
  "dim_col (A \<Otimes> B) = dim_col A * dim_col B"
  using tensor_mat_def mat_of_cols_list_def mult.length_Tensor[of "1" "(*)"]
  by(simp add: \<open>\<And>M2 M1. Matrix_Tensor.mult 1 (*) \<Longrightarrow> length (mult.Tensor (*) M1 M2) = length M1 * length M2\<close> mult.intro)

lemma index_tensor_mat [simp]:
  assumes a1:"dim_row A = rA" and a2:"dim_col A = cA" and a3:"dim_row B = rB" and a4:"dim_col B = cB"
    and a5:"i < rA * rB" and a6:"j < cA * cB" and a7:"cA > 0" and a8:"cB > 0"
  shows "(A \<Otimes> B) $$ (i,j) = A $$ (i div rB, j div cB) * B $$ (i mod rB, j mod cB)"
proof -
  have "(A \<Otimes> B) $$ (i,j) = (mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list B)) ! j ! i"
    using assms tensor_mat_def mat_of_cols_list_def dim_col_tensor_mat by simp
  moreover have f:"i < mult.row_length (mat_to_cols_list A) * mult.row_length (mat_to_cols_list B)"
    by (simp add: a1 a2 a3 a4 a5 a7 a8)
  moreover have "j < length (mat_to_cols_list A) * length (mat_to_cols_list B)"
    by (simp add: a2 a4 a6)
  moreover have "mat (mult.row_length (mat_to_cols_list A)) (length (mat_to_cols_list A)) (mat_to_cols_list A)"
    using a2 a7 mat_to_cols_list_is_mat by blast 
  moreover have "mat (mult.row_length (mat_to_cols_list B)) (length (mat_to_cols_list B)) (mat_to_cols_list B)"
    using a4 a8 mat_to_cols_list_is_mat by blast
  ultimately have "(A \<Otimes> B) $$ (i,j) = 
    (mat_to_cols_list A) ! (j div length (mat_to_cols_list B)) ! (i div mult.row_length (mat_to_cols_list B)) 
    * (mat_to_cols_list B) ! (j mod length (mat_to_cols_list B)) ! (i mod mult.row_length (mat_to_cols_list B))"
    using mult.matrix_Tensor_elements[of "1" "(*)"]
    by(simp add: \<open>\<And>M2 M1. mult 1 (*) \<Longrightarrow> \<forall>i j. (i<mult.row_length M1 * mult.row_length M2 
    \<and> j<length M1 * length M2) \<and> mat (mult.row_length M1) (length M1) M1 \<and> mat (mult.row_length M2) (length M2) M2 \<longrightarrow> 
    mult.Tensor (*) M1 M2 ! j ! i = M1 ! (j div length M2) ! (i div mult.row_length M2) * M2 ! (j mod length M2) ! (i mod mult.row_length M2)\<close>  mult.intro)
  thus ?thesis
    using mat_to_cols_list_def
    by (metis a2 a3 a4 a6 f index_mat_of_cols_list length_mat_to_cols_list less_mult_imp_div_less 
less_nat_zero_code mat_to_cols_list_to_mat mult_0_right neq0_conv row_length_mat_to_cols_list 
unique_euclidean_semiring_numeral_class.pos_mod_bound)
qed

text \<open>To go from @{term Matrix.row} to @{term Matrix_Legacy.row}\<close>

lemma Matrix_row_is_Legacy_row:
  assumes "i < dim_row A"
  shows "Matrix.row A i = vec_of_list (row (mat_to_cols_list A) i)"
proof
  show "dim_vec (Matrix.row A i) = dim_vec (vec_of_list (row (mat_to_cols_list A) i))"
    using length_mat_to_cols_list Matrix.dim_vec_of_list by (metis row_def index_row(2) length_map)
next
  show "\<And>j. j<dim_vec (vec_of_list (row (mat_to_cols_list A) i)) \<Longrightarrow> 
              Matrix.row A i $ j = vec_of_list (row (mat_to_cols_list A) i) $ j"
    using Matrix.row_def vec_of_list_def mat_to_cols_list_def
    by(smt row_def assms dim_vec_of_list index_mat_of_cols_list index_row(1) 
length_mat_to_cols_list length_row_mat_to_cols_list mat_to_cols_list_to_mat nth_map vec_of_list_index)
qed

text \<open>To go from @{term Matrix_Legacy.row} to @{term Matrix.row}\<close>

lemma Legacy_row_is_Matrix_row:
  assumes "i < mult.row_length A"
  shows "row A i = list_of_vec (Matrix.row (mat_of_cols_list (mult.row_length A) A) i)"
proof (rule nth_equalityI)
  show "length (row A i) = length (list_of_vec (Matrix.row (mat_of_cols_list (mult.row_length A) A) i))"
    using row_def length_list_of_vec by(metis mat_of_cols_list_def dim_col_mat(1) index_row(2) length_map)
next
  fix j:: nat
  assume "j < length (row A i)"
  then show "row A i ! j = list_of_vec (Matrix.row (mat_of_cols_list (mult.row_length A) A) i) ! j"
    using assms index_mat_of_cols_list
    by(metis row_def mat_of_cols_list_def dim_col_mat(1) dim_row_mat(1) index_row(1) length_map list_of_vec_index nth_map)
qed

text \<open>To go from @{term Matrix.col} to @{term Matrix_Legacy.col}\<close>

lemma Matrix_col_is_Legacy_col:
  assumes "j < dim_col A"
  shows "Matrix.col A j = vec_of_list (col (mat_to_cols_list A) j)"
proof
  show "dim_vec (Matrix.col A j) = dim_vec (vec_of_list (col (mat_to_cols_list A) j))"
    by (simp add: col_def assms mat_to_cols_list_def)
next
  show "\<And>i. i < dim_vec (vec_of_list (col (mat_to_cols_list A) j)) \<Longrightarrow>
         Matrix.col A j $ i = vec_of_list (col (mat_to_cols_list A) j) $ i"
    using mat_to_cols_list_def
    by (metis col_def assms col_mat_of_cols_list length_col_mat_to_cols_list length_mat_to_cols_list 
mat_to_cols_list_to_mat)
qed

text \<open>To go from @{term Matrix_Legacy.col} to @{term Matrix.col}\<close>

lemma Legacy_col_is_Matrix_col:
  assumes a1:"j < length A" and a2:"length (A ! j) = mult.row_length A"
  shows "col A j = list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)"
proof (rule nth_equalityI)
  have "length (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)) = 
dim_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)"
    using length_list_of_vec by blast
  also have "\<dots> = dim_row (mat_of_cols_list (mult.row_length A) A)"
    using Matrix.col_def by simp
  also have f1:"\<dots> = mult.row_length A"
    by (simp add: mat_of_cols_list_def)
  finally show f2:"length (col A j) = length (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j))"
    using a2 by (simp add: col_def)
next
  fix i:: nat
  assume "i<length (col A j)"
  then show "(col A j) ! i = (list_of_vec (Matrix.col (mat_of_cols_list (mult.row_length A) A) j)) ! i"
    by (metis col_def a1 a2 col_mat_of_cols_list list_vec) 
qed

text \<open>Link between @{term plus_mult.scalar_product} and @{term Matrix.scalar_prod}\<close>

lemma scalar_prod_is_Matrix_scalar_prod [simp]:
  fixes u::"complex list" and v::"complex list"
  assumes "length u = length v"
  shows "plus_mult.scalar_product (*) 0 (+) u v = (vec_of_list u) \<bullet> (vec_of_list v)"
proof -
  have f:"(vec_of_list u) \<bullet> (vec_of_list v) = (\<Sum>i=0..<length v. u ! i * v ! i)"
    using assms scalar_prod_def[of "vec_of_list u" "vec_of_list v"] Matrix.dim_vec_of_list[of v] index_vec_of_list
    by (metis (no_types, lifting) atLeastLessThan_iff sum.cong)
  thus ?thesis
  proof -
    have "plus_mult.scalar_product (*) 0 (+) u v = semiring_0_class.scalar_prod u v"
      using  plus_mult.scalar_product_def[of 1 "(*)" 0 "(+)" "a_inv cpx_rng" u v] by simp
    also have "\<dots> = sum_list (map (\<lambda>(x,y). x * y) (zip u v))"
      by (simp add: scalar_prod) 
    moreover have "\<forall>i<length v. (zip u v) ! i = (u ! i, v ! i)"
      using assms zip_def by simp
    then have "\<forall>i<length v. (map (\<lambda>(x,y). x * y) (zip u v)) ! i = u ! i * v ! i"
      by (simp add: assms)
    ultimately have "plus_mult.scalar_product (*) 0 (+) u v = (\<Sum>i=0..<length v. u ! i * v ! i)"
      by(metis (no_types, lifting) assms atLeastLessThan_iff length_map map_fst_zip sum.cong sum_list_sum_nth)
    thus ?thesis by (simp add: f)
  qed
qed

text \<open>Link between @{term times} and @{term plus_mult.matrix_mult}\<close>

lemma matrix_mult_to_times_mat:
  assumes "dim_col A > 0" and "dim_col B > 0" and "dim_col (A::complex Matrix.mat) = dim_row B"
  shows "A * B = mat_of_cols_list (dim_row A) (plus_mult.matrix_mult (*) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B))"
proof
  define M where "M = mat_of_cols_list (dim_row A) (plus_mult.matrix_mult (*) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B))"
  then show f1:"dim_row (A * B) = dim_row M"
    by (simp add: mat_of_cols_list_def times_mat_def)
  have "length (plus_mult.matrix_mult (*) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)) = dim_col B"
    by (simp add: mat_multI_def)
  then show f2:"dim_col (A * B) = dim_col M"
    by (simp add: M_def times_mat_def mat_of_cols_list_def)
  show "\<And>i j. i < dim_row M \<Longrightarrow> j < dim_col M \<Longrightarrow> (A * B) $$ (i, j) = M $$ (i, j)"
  proof -
    fix i j
    assume a1:"i < dim_row M" and a2:"j < dim_col M"
    then have "(A * B) $$ (i,j) = Matrix.row A i \<bullet> Matrix.col B j"
      using f1 f2 by simp
    also have "\<dots> = vec_of_list (row (mat_to_cols_list A) i) \<bullet> vec_of_list (col (mat_to_cols_list B) j)"
      using f1 f2 a1 a2 by (simp add: Matrix_row_is_Legacy_row Matrix_col_is_Legacy_col)
    also have "\<dots> = plus_mult.scalar_product (*) 0 (+) (row (mat_to_cols_list A) i) (col (mat_to_cols_list B) j)"
      using a1 a2 assms(3) f1 f2 by simp
    also have "M $$ (i,j) =  plus_mult.scalar_product (*) 0 (+) (row (mat_to_cols_list A) i) (col (mat_to_cols_list B) j)"
    proof-
      have "M $$ (i,j) = (plus_mult.matrix_mult (*) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)) ! j ! i"
        using M_def f1 f2 
\<open>length (mat_mult (mult.row_length (mat_to_cols_list A)) (mat_to_cols_list A) (mat_to_cols_list B)) = dim_col B\<close> a1 a2 by simp
      moreover have "mat (mult.row_length (mat_to_cols_list A)) (dim_col A) (mat_to_cols_list A)"
        using mat_to_cols_list_is_mat assms(1) by simp
      moreover have "mat (dim_col A) (dim_col B) (mat_to_cols_list B)"
        using assms(2) assms(3) mat_to_cols_list_is_mat by simp
      ultimately show ?thesis
        using assms(1) a1 a2 row_length_mat_to_cols_list plus_mult.matrix_index[of 1 "(*)" 0 "(+)"] plus_mult_cpx
        by (smt f1 f2 index_mult_mat(2) index_mult_mat(3))
    qed
    finally show "(A * B) $$ (i, j) = M $$ (i, j)" by simp
  qed
qed

lemma mat_to_cols_list_times_mat [simp]:
  assumes "dim_col A = dim_row B" and "dim_col A > 0"
  shows "mat_to_cols_list (A * B) = plus_mult.matrix_mult (*) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)"
proof (rule nth_equalityI)
  define M where "M = plus_mult.matrix_mult (*) 0 (+) (mat_to_cols_list A) (mat_to_cols_list B)"
  then show f0:"length (mat_to_cols_list (A * B)) = length M" by (simp add: mat_multI_def)
  moreover have f1:"\<And>j. j<length (mat_to_cols_list (A * B)) \<longrightarrow> mat_to_cols_list (A * B) ! j = M ! j"
  proof
    fix j:: nat
    assume a0:"j < length (mat_to_cols_list (A * B))"
    then have "length (mat_to_cols_list (A * B) ! j) = dim_row A"
      by (simp add: mat_to_cols_list_def)
    then also have f2:"length (M ! j) = dim_row A"
      using a0 M_def mat_multI_def[of 0 "(+)" "(*)" "dim_row A" "mat_to_cols_list A" "mat_to_cols_list B"] 
        row_length_mat_to_cols_list assms(2)
      by (metis assms(1) f0 length_greater_0_conv length_map length_mat_to_cols_list 
list_to_mat_to_cols_list mat_mult mat_to_cols_list_is_mat matrix_mult_to_times_mat)
    ultimately have "length (mat_to_cols_list (A * B) ! j) = length (M ! j)" by simp
    moreover have "\<And>i. i<dim_row A \<longrightarrow> mat_to_cols_list (A * B) ! j ! i = M ! j ! i"
    proof
      fix i
      assume a1:"i < dim_row A"
      have "mat (mult.row_length (mat_to_cols_list A)) (dim_col A) (mat_to_cols_list A)"
        using mat_to_cols_list_is_mat assms(2) by simp
      moreover have "mat (dim_col A) (dim_col B) (mat_to_cols_list B)"
        using mat_to_cols_list_is_mat assms(1) a0 by simp
      ultimately have "M ! j ! i = plus_mult.scalar_product (*) 0 (+) (row (mat_to_cols_list A) i) (col (mat_to_cols_list B) j)"
        using plus_mult.matrix_index a0 a1 row_length_mat_to_cols_list assms(2) plus_mult_cpx M_def
        by (metis index_mult_mat(3) length_mat_to_cols_list)
      also have "\<dots> = vec_of_list (row (mat_to_cols_list A) i) \<bullet> vec_of_list (col (mat_to_cols_list B) j)"
        using a0 a1 assms(1) by simp
      finally show "mat_to_cols_list (A * B) ! j ! i = M ! j ! i"
        using mat_to_cols_list_def index_mult_mat(1) a0 a1 
        by(simp add: Matrix_row_is_Legacy_row Matrix_col_is_Legacy_col)
    qed
    ultimately show "mat_to_cols_list (A * B) ! j = M ! j" by(simp add: nth_equalityI f2)
  qed
  fix i:: nat
  assume "i < length (mat_to_cols_list (A * B))"
  thus "mat_to_cols_list (A * B) ! i = M ! i" by (simp add: f1)
qed

text \<open> 
Finally, we prove that the tensor product of complex matrices is distributive over the 
multiplication of complex matrices. 
\<close>

lemma mult_distr_tensor:
  assumes a1:"dim_col A = dim_row B" and a2:"dim_col C = dim_row D" and a3:"dim_col A > 0" and 
    a4:"dim_col B > 0" and a5:"dim_col C > 0" and a6:"dim_col D > 0"
  shows "(A * B) \<Otimes> (C * D) = (A \<Otimes> C) * (B \<Otimes> D)"
proof -
  define A' B' C' D' M N where "A' = mat_to_cols_list A" and "B' = mat_to_cols_list B" and 
    "C' = mat_to_cols_list C" and "D' = mat_to_cols_list D" and
    "M = mat_of_cols_list (dim_row A * dim_row C) (mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list C))" and
    "N = mat_of_cols_list (dim_row B * dim_row D) (mult.Tensor (*) (mat_to_cols_list B) (mat_to_cols_list D))"
  then have "(A \<Otimes> C) * (B \<Otimes> D) = M * N"
    by (simp add: tensor_mat_def)
  also have "\<dots> = mat_of_cols_list (dim_row A * dim_row C) (plus_mult.matrix_mult (*) 0 (+) 
  (mat_to_cols_list M) (mat_to_cols_list N))"
    using assms M_def N_def dim_col_tensor_mat dim_row_tensor_mat tensor_mat_def 
    by(simp add: matrix_mult_to_times_mat)
  also have f1:"\<dots> = mat_of_cols_list (dim_row A * dim_row C) (plus_mult.matrix_mult (*) 0 (+) 
  (mult.Tensor (*) A' C') (mult.Tensor (*) B' D'))"
  proof -
    define M' N' where "M' = mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list C)" and
      "N' = mult.Tensor (*) (mat_to_cols_list B) (mat_to_cols_list D)"
    then have "mat (mult.row_length M') (length M') M'"
      using M'_def mult.effective_well_defined_Tensor[of 1 "(*)"] mat_to_cols_list_is_mat a3 a5
      by (smt mult.length_Tensor mult.row_length_mat plus_mult_cpx plus_mult_def)
    moreover have "mat (mult.row_length N') (length N') N'"
      using N'_def mult.effective_well_defined_Tensor[of 1 "(*)"] mat_to_cols_list_is_mat a4 a6
      by (smt mult.length_Tensor mult.row_length_mat plus_mult_cpx plus_mult_def)
    ultimately show ?thesis
      using list_to_mat_to_cols_list M_def N_def mult.row_length_mat row_length_mat_to_cols_list 
      assms(3) a4 a5 a6 A'_def B'_def C'_def D'_def by(metis M'_def N'_def plus_mult_cpx plus_mult_def)
   qed
   also have "\<dots> = mat_of_cols_list (dim_row A * dim_row C) (mult.Tensor (*)
    (plus_mult.matrix_mult (*) 0 (+) A' B')
    (plus_mult.matrix_mult (*) 0 (+) C' D'))"
   proof -
     have f2:"mat (mult.row_length A') (length A') A'"
       using A'_def a3 mat_to_cols_list_is_mat by simp
     moreover have "mat (mult.row_length B') (length B') B'"
       using B'_def a4 mat_to_cols_list_is_mat by simp
     moreover have "mat (mult.row_length C') (length C') C'"
       using C'_def a5 mat_to_cols_list_is_mat by simp
     moreover have "mat (mult.row_length D') (length D') D'"
       using D'_def a6 mat_to_cols_list_is_mat by simp
     moreover have "length A' = mult.row_length B'"
       using A'_def B'_def a1 a4 by simp
     moreover have "length C' = mult.row_length D'"
       using C'_def D'_def a2 a6 by simp
     moreover have "A' \<noteq> [] \<and> B' \<noteq> [] \<and> C' \<noteq> [] \<and> D' \<noteq> []"
       using A'_def B'_def C'_def D'_def a3 a4 a5 a6 by simp
     ultimately have "plus_mult.matrix_match A' B' C' D'"
       using plus_mult.matrix_match_def[of 1 "(*)" 0 "(+)" "a_inv cpx_rng"] by simp
     thus ?thesis
       using f1 plus_mult.distributivity plus_mult_cpx by fastforce
   qed
   also have "\<dots> = mat_of_cols_list (dim_row A * dim_row C) (mult.Tensor (*) 
   (mat_to_cols_list (A * B)) (mat_to_cols_list (C * D)))"
     using A'_def B'_def C'_def D'_def a1 a2 a3 a5 by simp
   finally show ?thesis by(simp add: tensor_mat_def)
 qed

lemma tensor_mat_is_assoc:
  fixes A B C:: "complex Matrix.mat"
  shows "A \<Otimes> (B \<Otimes> C) = (A \<Otimes> B) \<Otimes> C"
proof-
  define M where d:"M = mat_of_cols_list (dim_row B * dim_row C) (mult.Tensor (*) (mat_to_cols_list B) (mat_to_cols_list C))"
  then have "B \<Otimes> C = M" 
    using tensor_mat_def by simp
  moreover have "A \<Otimes> (B \<Otimes> C) = mat_of_cols_list (dim_row A * (dim_row B * dim_row C))
(mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list M))"
    using tensor_mat_def d dim_row_tensor_mat by simp
  moreover have "mat_to_cols_list M = mult.Tensor (*) (mat_to_cols_list B) (mat_to_cols_list C)"
    using d list_to_mat_to_cols_list
    by (smt calculation(1) dim_col_tensor_mat length_greater_0_conv length_mat_to_cols_list mat_to_cols_list_is_mat 
mult.Tensor.simps(1) mult.Tensor_null mult.well_defined_Tensor nat_0_less_mult_iff plus_mult_cpx plus_mult_def row_length_mat_to_cols_list)
  ultimately have "A \<Otimes> (B \<Otimes> C) = mat_of_cols_list (dim_row A * (dim_row B * dim_row C))
(mult.Tensor (*) (mat_to_cols_list A) (mult.Tensor (*) (mat_to_cols_list B) (mat_to_cols_list C)))" by simp
  moreover have "\<dots> = mat_of_cols_list ((dim_row A * dim_row B) * dim_row C) 
(mult.Tensor (*) (mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list B)) (mat_to_cols_list C))"
    using Matrix_Tensor.mult.associativity
    by (smt ab_semigroup_mult_class.mult_ac(1) length_greater_0_conv length_mat_to_cols_list
mat_to_cols_list_is_mat mult.Tensor.simps(1) mult.Tensor_null plus_mult_cpx plus_mult_def)
  ultimately show ?thesis
    using tensor_mat_def
    by (smt Tensor.mat_of_cols_list_def dim_col_mat(1) dim_col_tensor_mat dim_row_tensor_mat length_0_conv 
list_to_mat_to_cols_list mat_to_cols_list_is_mat mult.well_defined_Tensor mult_is_0 neq0_conv 
plus_mult_cpx plus_mult_def row_length_mat_to_cols_list)
qed

end