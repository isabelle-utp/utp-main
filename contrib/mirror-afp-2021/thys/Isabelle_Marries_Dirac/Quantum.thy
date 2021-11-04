(*
Authors: 

  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
  Yijun He, University of Cambridge, yh403@cam.ac.uk
  with contributions by Hanna Lachnitt
*)

section \<open>Qubits and Quantum Gates\<close>

theory Quantum
imports
  Jordan_Normal_Form.Matrix
  "HOL-Library.Nonpos_Ints"
  Basics
  Binary_Nat
begin


subsection \<open>Qubits\<close>

text\<open>In this theory @{text cpx} stands for @{text complex}.\<close>

definition cpx_vec_length :: "complex vec \<Rightarrow> real" ("\<parallel>_\<parallel>") where
"cpx_vec_length v \<equiv> sqrt(\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"

lemma cpx_length_of_vec_of_list [simp]:
  "\<parallel>vec_of_list l\<parallel> = sqrt(\<Sum>i<length l. (cmod (l ! i))\<^sup>2)"
  by (auto simp: cpx_vec_length_def vec_of_list_def vec_of_list_index)
    (metis (no_types, lifting) dim_vec_of_list sum.cong vec_of_list.abs_eq vec_of_list_index)

lemma norm_vec_index_unit_vec_is_0 [simp]:
  assumes "j < n" and "j \<noteq> i"
  shows "cmod ((unit_vec n i) $ j) = 0"
  using assms by (simp add: unit_vec_def)

lemma norm_vec_index_unit_vec_is_1 [simp]:
  assumes "j < n" and "j = i"
  shows "cmod ((unit_vec n i) $ j) = 1"
proof -
  have f:"(unit_vec n i) $ j = 1"
    using assms by simp
  thus ?thesis
    by (simp add: f cmod_def) 
qed

lemma unit_cpx_vec_length [simp]:
  assumes "i < n"
  shows "\<parallel>unit_vec n i\<parallel> = 1"
proof -
  have "(\<Sum>j<n. (cmod((unit_vec n i) $ j))\<^sup>2) = (\<Sum>j<n. if j = i then 1 else 0)"
    using norm_vec_index_unit_vec_is_0 norm_vec_index_unit_vec_is_1
    by (smt lessThan_iff one_power2 sum.cong zero_power2) 
  also have "\<dots> = 1"
    using assms by simp
  finally have "sqrt (\<Sum>j<n. (cmod((unit_vec n i) $ j))\<^sup>2) = 1" 
    by simp
  thus ?thesis
    using cpx_vec_length_def by simp
qed

lemma smult_vec_length [simp]:
  assumes "x \<ge> 0"
  shows "\<parallel>complex_of_real(x) \<cdot>\<^sub>v v\<parallel> = x * \<parallel>v\<parallel>"
proof-
  have "(\<lambda>i::nat.(cmod (complex_of_real x * v $ i))\<^sup>2) = (\<lambda>i::nat. (cmod (v $ i))\<^sup>2 * x\<^sup>2)" 
    by (auto simp: norm_mult power_mult_distrib)
  then have "(\<Sum>i<dim_vec v. (cmod (complex_of_real x * v $ i))\<^sup>2) = 
             (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2 * x\<^sup>2)" by meson
  moreover have "(\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2 * x\<^sup>2) = x\<^sup>2 * (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
    by (metis (no_types) mult.commute sum_distrib_right)
  moreover have "sqrt(x\<^sup>2 * (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)) = 
                 sqrt(x\<^sup>2) * sqrt (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)" 
    using real_sqrt_mult by blast
  ultimately show ?thesis
    by(simp add: cpx_vec_length_def assms)
qed

locale state =
  fixes n:: nat and v:: "complex mat"
  assumes is_column [simp]: "dim_col v = 1"
    and dim_row [simp]: "dim_row v = 2^n"
    and is_normal [simp]: "\<parallel>col v 0\<parallel> = 1"

text\<open> 
Below the natural number n codes for the dimension of the complex vector space whose elements of norm
1 we call states. 
\<close>

lemma unit_vec_of_right_length_is_state [simp]:
  assumes "i < 2^n"
  shows "unit_vec (2^n) i \<in> {v| n v::complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"
proof-
  have "dim_vec (unit_vec (2^n) i) = 2^n" 
    by simp
  moreover have "\<parallel>unit_vec (2^n) i\<parallel> = 1"
    using assms by simp
  ultimately show ?thesis 
    by simp
qed

definition state_qbit :: "nat \<Rightarrow> complex vec set" where
"state_qbit n \<equiv> {v| v:: complex vec. dim_vec v = 2^n \<and> \<parallel>v\<parallel> = 1}"

lemma (in state) state_to_state_qbit [simp]:
  shows "col v 0 \<in> state_qbit n"
  using state_def state_qbit_def by simp

subsection "The Hermitian Conjugation"

text \<open>The Hermitian conjugate of a complex matrix is the complex conjugate of its transpose. \<close>

definition dagger :: "complex mat \<Rightarrow> complex mat" ("_\<^sup>\<dagger>") where
  "M\<^sup>\<dagger> \<equiv> mat (dim_col M) (dim_row M) (\<lambda>(i,j). cnj(M $$ (j,i)))"

text \<open>We introduce the type of complex square matrices.\<close>

typedef cpx_sqr_mat = "{M | M::complex mat. square_mat M}"
proof-
  have "square_mat (1\<^sub>m n)" for n
    using one_mat_def by simp
  thus ?thesis by blast
qed

definition cpx_sqr_mat_to_cpx_mat :: "cpx_sqr_mat => complex mat" where
"cpx_sqr_mat_to_cpx_mat M \<equiv> Rep_cpx_sqr_mat M"

text \<open>
We introduce a coercion from the type of complex square matrices to the type of complex 
matrices.
\<close>

declare [[coercion cpx_sqr_mat_to_cpx_mat]]

lemma dim_row_of_dagger [simp]:
  "dim_row (M\<^sup>\<dagger>) = dim_col M"
  using dagger_def by simp

lemma dim_col_of_dagger [simp]:
  "dim_col (M\<^sup>\<dagger>) = dim_row M"
  using dagger_def by simp

lemma col_of_dagger [simp]:
  assumes "j < dim_row M"
  shows "col (M\<^sup>\<dagger>) j = vec (dim_col M) (\<lambda>i. cnj (M $$ (j,i)))"
  using assms col_def dagger_def by simp

lemma row_of_dagger [simp]:
  assumes "i < dim_col M"
  shows "row (M\<^sup>\<dagger>) i = vec (dim_row M) (\<lambda>j. cnj (M $$ (j,i)))"
  using assms row_def dagger_def by simp

lemma dagger_of_dagger_is_id:
  fixes M :: "complex Matrix.mat"
  shows "(M\<^sup>\<dagger>)\<^sup>\<dagger> = M"
proof
  show "dim_row ((M\<^sup>\<dagger>)\<^sup>\<dagger>) = dim_row M" by simp
  show "dim_col ((M\<^sup>\<dagger>)\<^sup>\<dagger>) = dim_col M" by simp
  fix i j assume a0:"i < dim_row M" and a1:"j < dim_col M"
  then show "(M\<^sup>\<dagger>)\<^sup>\<dagger> $$ (i,j) = M $$ (i,j)"
  proof-
    show ?thesis
      using dagger_def a0 a1 by auto
  qed
qed

lemma dagger_of_sqr_is_sqr [simp]:
  "square_mat ((M::cpx_sqr_mat)\<^sup>\<dagger>)"
proof-
  have "square_mat M"
    using cpx_sqr_mat_to_cpx_mat_def Rep_cpx_sqr_mat by simp
  then have "dim_row M = dim_col M" by simp
  then have "dim_col (M\<^sup>\<dagger>) = dim_row (M\<^sup>\<dagger>)" by simp
  thus "square_mat (M\<^sup>\<dagger>)" by simp
qed

lemma dagger_of_id_is_id [simp]:
  "(1\<^sub>m n)\<^sup>\<dagger> = 1\<^sub>m n"
  using dagger_def one_mat_def by auto

subsection "Unitary Matrices and Quantum Gates"

definition unitary :: "complex mat \<Rightarrow> bool" where
"unitary M \<equiv> (M\<^sup>\<dagger>) * M = 1\<^sub>m (dim_col M) \<and> M * (M\<^sup>\<dagger>) = 1\<^sub>m (dim_row M)"

lemma id_is_unitary [simp]:
  "unitary (1\<^sub>m n)"
  by (simp add: unitary_def)

locale gate =
  fixes n:: nat and A:: "complex mat"
  assumes dim_row [simp]: "dim_row A = 2^n"
    and square_mat [simp]: "square_mat A"
    and unitary [simp]: "unitary A"

text \<open>
We prove that a quantum gate is invertible and its inverse is given by its Hermitian conjugate.
\<close>

lemma mat_unitary_mat [intro]:
  assumes "unitary M"
  shows "inverts_mat M (M\<^sup>\<dagger>)"
  using assms by (simp add: unitary_def inverts_mat_def)

lemma unitary_mat_mat [intro]:
  assumes "unitary M"
  shows "inverts_mat (M\<^sup>\<dagger>) M"
  using assms by (simp add: unitary_def inverts_mat_def)

lemma (in gate) gate_is_inv:
  "invertible_mat A"
  using square_mat unitary invertible_mat_def by blast

subsection "Relations Between Complex Conjugation, Hermitian Conjugation, Transposition and Unitarity"

notation transpose_mat ("(_\<^sup>t)")

lemma col_tranpose [simp]:
  assumes "dim_row M = n" and "i < n"
  shows "col (M\<^sup>t) i = row M i"
proof
  show "dim_vec (col (M\<^sup>t) i) = dim_vec (row M i)"
    by (simp add: row_def col_def transpose_mat_def)
next
  show "\<And>j. j < dim_vec (row M i) \<Longrightarrow> col M\<^sup>t i $ j = row M i $ j"
    using assms by (simp add: transpose_mat_def)
qed

lemma row_transpose [simp]:
  assumes "dim_col M = n" and "i < n"
  shows "row (M\<^sup>t) i = col M i"
  using assms by simp

definition cpx_mat_cnj :: "complex mat \<Rightarrow> complex mat" ("(_\<^sup>\<star>)") where
"cpx_mat_cnj M \<equiv> mat (dim_row M) (dim_col M) (\<lambda>(i,j). cnj (M $$ (i,j)))"

lemma cpx_mat_cnj_id [simp]:
  "(1\<^sub>m n)\<^sup>\<star> = 1\<^sub>m n" 
  by (auto simp: cpx_mat_cnj_def)

lemma cpx_mat_cnj_cnj [simp]:
  "(M\<^sup>\<star>)\<^sup>\<star> = M"
  by (auto simp: cpx_mat_cnj_def)

lemma dim_row_of_cjn_prod [simp]: 
  "dim_row ((M\<^sup>\<star>) * (N\<^sup>\<star>)) = dim_row M"
  by (simp add: cpx_mat_cnj_def)

lemma dim_col_of_cjn_prod [simp]: 
  "dim_col ((M\<^sup>\<star>) * (N\<^sup>\<star>)) = dim_col N"
  by (simp add: cpx_mat_cnj_def)

lemma cpx_mat_cnj_prod:
  assumes "dim_col M = dim_row N"
  shows "(M * N)\<^sup>\<star> = (M\<^sup>\<star>) * (N\<^sup>\<star>)"
proof
  show "dim_row (M * N)\<^sup>\<star> = dim_row ((M\<^sup>\<star>) * (N\<^sup>\<star>))" 
    by (simp add: cpx_mat_cnj_def)
next
  show "dim_col ((M * N)\<^sup>\<star>) = dim_col ((M\<^sup>\<star>) * (N\<^sup>\<star>))" 
    by (simp add: cpx_mat_cnj_def)
next 
  fix i j::nat
  assume a1:"i < dim_row ((M\<^sup>\<star>) * (N\<^sup>\<star>))" and a2:"j < dim_col ((M\<^sup>\<star>) * (N\<^sup>\<star>))"
  then have "(M * N)\<^sup>\<star> $$ (i,j) = cnj (\<Sum>k<(dim_row N). M $$ (i,k) * N $$ (k,j))"
    using assms cpx_mat_cnj_def index_mat times_mat_def scalar_prod_def row_def col_def 
dim_row_of_cjn_prod dim_col_of_cjn_prod
    by (smt case_prod_conv dim_col index_mult_mat(2) index_mult_mat(3) index_vec lessThan_atLeast0 
        lessThan_iff sum.cong)
  also have "\<dots> = (\<Sum>k<(dim_row N). cnj(M $$ (i,k)) * cnj(N $$ (k,j)))" by simp
  also have "((M\<^sup>\<star>) * (N\<^sup>\<star>)) $$ (i,j) = 
    (\<Sum>k<(dim_row N). cnj(M $$ (i,k)) * cnj(N $$ (k,j)))"
    using assms a1 a2 cpx_mat_cnj_def index_mat times_mat_def scalar_prod_def row_def col_def
    by (smt case_prod_conv dim_col dim_col_mat(1) dim_row_mat(1) index_vec lessThan_atLeast0 
        lessThan_iff sum.cong)
  finally show "(M * N)\<^sup>\<star> $$ (i, j) = ((M\<^sup>\<star>) * (N\<^sup>\<star>)) $$ (i, j)" by simp
qed

lemma transpose_of_prod:
  fixes M N::"complex Matrix.mat"
  assumes "dim_col M = dim_row N"
  shows "(M * N)\<^sup>t = N\<^sup>t * (M\<^sup>t)"
proof
  fix i j::nat
  assume a0: "i < dim_row (N\<^sup>t * (M\<^sup>t))" and a1: "j < dim_col (N\<^sup>t * (M\<^sup>t))"  
  then have "(M * N)\<^sup>t $$ (i,j) = (M * N) $$ (j,i)" by auto
  also have "... = (\<Sum>k<dim_row M\<^sup>t.  M $$ (j,k) * N $$ (k,i))"
    using assms a0 a1 by auto
  also have "... = (\<Sum>k<dim_row M\<^sup>t. N $$ (k,i) * M $$ (j,k))"
   by (simp add: semiring_normalization_rules(7))
  also have "... = (\<Sum>k<dim_row M\<^sup>t. ((N\<^sup>t) $$ (i,k)) * (M\<^sup>t) $$ (k,j))" 
    using assms a0 a1 by auto
  finally show "((M * N)\<^sup>t) $$ (i,j) = (N\<^sup>t * (M\<^sup>t)) $$ (i,j)" 
    using assms a0 a1 by auto
next
  show "dim_row ((M * N)\<^sup>t) = dim_row (N\<^sup>t * (M\<^sup>t))" by auto
next
  show "dim_col ((M * N)\<^sup>t) = dim_col (N\<^sup>t * (M\<^sup>t))" by auto
qed

lemma transpose_cnj_is_dagger [simp]:
  "(M\<^sup>t)\<^sup>\<star> = (M\<^sup>\<dagger>)"
proof
  show f1:"dim_row ((M\<^sup>t)\<^sup>\<star>) = dim_row (M\<^sup>\<dagger>)"
    by (simp add: cpx_mat_cnj_def transpose_mat_def dagger_def)
next
  show f2:"dim_col ((M\<^sup>t)\<^sup>\<star>) = dim_col (M\<^sup>\<dagger>)" 
    by (simp add: cpx_mat_cnj_def transpose_mat_def dagger_def)
next
  fix i j::nat
  assume "i < dim_row M\<^sup>\<dagger>" and "j < dim_col M\<^sup>\<dagger>"
  then show "M\<^sup>t\<^sup>\<star> $$ (i, j) = M\<^sup>\<dagger> $$ (i, j)" 
    by (simp add: cpx_mat_cnj_def transpose_mat_def dagger_def)
qed

lemma cnj_transpose_is_dagger [simp]:
  "(M\<^sup>\<star>)\<^sup>t = (M\<^sup>\<dagger>)"
proof
  show "dim_row ((M\<^sup>\<star>)\<^sup>t) = dim_row (M\<^sup>\<dagger>)" 
    by (simp add: transpose_mat_def cpx_mat_cnj_def dagger_def)
next
  show "dim_col ((M\<^sup>\<star>)\<^sup>t) = dim_col (M\<^sup>\<dagger>)" 
    by (simp add: transpose_mat_def cpx_mat_cnj_def dagger_def)
next
  fix i j::nat
  assume "i < dim_row M\<^sup>\<dagger>" and "j < dim_col M\<^sup>\<dagger>"
  then show "M\<^sup>\<star>\<^sup>t $$ (i, j) = M\<^sup>\<dagger> $$ (i, j)" 
    by (simp add: transpose_mat_def cpx_mat_cnj_def dagger_def)
qed

lemma dagger_of_transpose_is_cnj [simp]:
  "(M\<^sup>t)\<^sup>\<dagger> = (M\<^sup>\<star>)"
  by (metis transpose_transpose transpose_cnj_is_dagger)

lemma dagger_of_prod:
  fixes M N::"complex Matrix.mat"
  assumes "dim_col M = dim_row N"
  shows "(M * N)\<^sup>\<dagger> = N\<^sup>\<dagger> * (M\<^sup>\<dagger>)"
proof-
  have "(M * N)\<^sup>\<dagger> = ((M * N)\<^sup>\<star>)\<^sup>t" by auto
  also have "... = ((M\<^sup>\<star>) * (N\<^sup>\<star>))\<^sup>t" using assms cpx_mat_cnj_prod by auto
  also have "... = (N\<^sup>\<star>)\<^sup>t * ((M\<^sup>\<star>)\<^sup>t)" using assms transpose_of_prod 
    by (metis cnj_transpose_is_dagger dim_col_of_dagger dim_row_of_dagger index_transpose_mat(2) index_transpose_mat(3))
  finally show "(M * N)\<^sup>\<dagger> = N\<^sup>\<dagger> * (M\<^sup>\<dagger>)" by auto
qed

text \<open>The product of two quantum gates is a quantum gate.\<close>

lemma prod_of_gate_is_gate: 
  assumes "gate n G1" and "gate n G2"
  shows "gate n (G1 * G2)"
proof
  show "dim_row (G1 * G2) = 2^n" using assms by (simp add: gate_def)
next
  show "square_mat (G1 * G2)" 
    using assms gate.dim_row gate.square_mat by simp
next
  show "unitary (G1 * G2)" 
  proof-
    have "((G1 * G2)\<^sup>\<dagger>) * (G1 * G2) = 1\<^sub>m (dim_col (G1 * G2))" 
    proof-
      have f0: "G1 \<in> carrier_mat (2^n) (2^n) \<and> G2 \<in> carrier_mat (2^n) (2^n)
              \<and> G1\<^sup>\<dagger> \<in> carrier_mat (2^n) (2^n) \<and> G2\<^sup>\<dagger> \<in> carrier_mat (2^n) (2^n)
              \<and> G1 * G2 \<in> carrier_mat (2^n) (2^n)" 
        using assms gate.dim_row gate.square_mat by auto
      have "((G1 * G2)\<^sup>\<dagger>) * (G1 * G2) = ((G2\<^sup>\<dagger>) * (G1\<^sup>\<dagger>)) * (G1 * G2)" 
        using assms dagger_of_prod gate.dim_row gate.square_mat by simp
      also have "... = (G2\<^sup>\<dagger>) * ((G1\<^sup>\<dagger>) * (G1 * G2))" 
        using assms f0 by auto
      also have "... = (G2\<^sup>\<dagger>) * (((G1\<^sup>\<dagger>) * G1) * G2)" 
        using assms f0 f0 by auto
      also have "... = (G2\<^sup>\<dagger>) * ((1\<^sub>m (dim_col G1)) * G2)" 
        using gate.unitary[of n G1] assms unitary_def[of G1] by simp
      also have "... = (G2\<^sup>\<dagger>) * ((1\<^sub>m (dim_col G2)) * G2)" 
        using assms f0 by (metis carrier_matD(2))
      also have "... = (G2\<^sup>\<dagger>) * G2" 
        using f0 by (metis carrier_matD(2) left_mult_one_mat)
      finally show "((G1 * G2)\<^sup>\<dagger>) * (G1 * G2) = 1\<^sub>m (dim_col (G1 * G2))" 
        using assms gate.unitary unitary_def by simp
    qed
    moreover have "(G1 * G2) * ((G1 * G2)\<^sup>\<dagger>) = 1\<^sub>m (dim_row (G1 * G2))"
      using assms calculation
      by (smt carrier_matI dim_col_of_dagger dim_row_of_dagger gate.dim_row gate.square_mat index_mult_mat(2) index_mult_mat(3) 
          mat_mult_left_right_inverse square_mat.elims(2))
    ultimately show ?thesis using unitary_def by simp
  qed
qed

lemma left_inv_of_unitary_transpose [simp]:
  assumes "unitary U"
  shows "(U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t) =  1\<^sub>m(dim_row U)"
proof -
  have "dim_col U = dim_row ((U\<^sup>t)\<^sup>\<star>)" by simp
  then have "(U * ((U\<^sup>t)\<^sup>\<star>))\<^sup>\<star> = (U\<^sup>\<star>) * (U\<^sup>t)"
    using cpx_mat_cnj_prod cpx_mat_cnj_cnj by presburger
  also have "\<dots> = (U\<^sup>t)\<^sup>\<dagger> * (U\<^sup>t)" by simp
  finally show ?thesis 
    using assms by (metis transpose_cnj_is_dagger cpx_mat_cnj_id unitary_def)
qed

lemma right_inv_of_unitary_transpose [simp]:
  assumes "unitary U"
  shows "U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = 1\<^sub>m(dim_col U)"
proof -
  have "dim_col ((U\<^sup>t)\<^sup>\<star>) = dim_row U" by simp
  then have "U\<^sup>t * ((U\<^sup>t)\<^sup>\<dagger>) = (((U\<^sup>t)\<^sup>\<star> * U)\<^sup>\<star>)"
    using cpx_mat_cnj_cnj cpx_mat_cnj_prod dagger_of_transpose_is_cnj by presburger
  also have "\<dots> = (U\<^sup>\<dagger> * U)\<^sup>\<star>" by simp
  finally show ?thesis
    using assms by (metis cpx_mat_cnj_id unitary_def)
qed

lemma transpose_of_unitary_is_unitary [simp]:
  assumes "unitary U"
  shows "unitary (U\<^sup>t)" 
  using unitary_def assms left_inv_of_unitary_transpose right_inv_of_unitary_transpose by simp


subsection "The Inner Product"

text \<open>We introduce a coercion between complex vectors and (column) complex matrices.\<close>

definition ket_vec :: "complex vec \<Rightarrow> complex mat" ("|_\<rangle>") where
"|v\<rangle> \<equiv> mat (dim_vec v) 1 (\<lambda>(i,j). v $ i)"

lemma ket_vec_index [simp]:
  assumes "i < dim_vec v"
  shows "|v\<rangle> $$ (i,0) = v $ i"
  using assms ket_vec_def by simp

lemma ket_vec_col [simp]:
  "col |v\<rangle> 0 = v"
  by (auto simp: col_def ket_vec_def)

lemma smult_ket_vec [simp]:
  "|x \<cdot>\<^sub>v v\<rangle> = x \<cdot>\<^sub>m |v\<rangle>"
  by (auto simp: ket_vec_def)

lemma smult_vec_length_bis [simp]:
  assumes "x \<ge> 0"
  shows "\<parallel>col (complex_of_real(x) \<cdot>\<^sub>m |v\<rangle>) 0\<parallel> = x * \<parallel>v\<parallel>"
  using assms smult_ket_vec smult_vec_length ket_vec_col by metis

declare [[coercion ket_vec]]

definition row_vec :: "complex vec \<Rightarrow> complex mat" where
"row_vec v \<equiv> mat 1 (dim_vec v) (\<lambda>(i,j). v $ j)" 

definition bra_vec :: "complex vec \<Rightarrow> complex mat" where
"bra_vec v \<equiv> (row_vec v)\<^sup>\<star>"

lemma row_bra_vec [simp]:
  "row (bra_vec v) 0 = vec (dim_vec v) (\<lambda>i. cnj(v $ i))"
  by (auto simp: row_def bra_vec_def cpx_mat_cnj_def row_vec_def)

text \<open>We introduce a definition called @{term "bra"} to see a vector as a column matrix.\<close>

definition bra :: "complex mat \<Rightarrow> complex mat" ("\<langle>_|") where
"\<langle>v| \<equiv> mat 1 (dim_row v) (\<lambda>(i,j). cnj(v $$ (j,i)))"

text \<open>The relation between @{term "bra"}, @{term "bra_vec"} and @{term "ket_vec"} is given as follows.\<close>

lemma bra_bra_vec [simp]:
  "bra (ket_vec v) = bra_vec v"
  by (auto simp: bra_def ket_vec_def bra_vec_def cpx_mat_cnj_def row_vec_def)

lemma row_bra [simp]:
  fixes v::"complex vec"
  shows "row \<langle>v| 0 = vec (dim_vec v) (\<lambda>i. cnj (v $ i))" by simp

text \<open>We introduce the inner product of two complex vectors in @{text "\<complex>\<^sup>n"}.\<close>

definition inner_prod :: "complex vec \<Rightarrow> complex vec \<Rightarrow> complex" ("\<langle>_|_\<rangle>") where
"inner_prod u v \<equiv> \<Sum> i \<in> {0..< dim_vec v}. cnj(u $ i) * (v $ i)"

lemma inner_prod_with_row_bra_vec [simp]:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = row (bra_vec u) 0 \<bullet> v"
  using assms inner_prod_def scalar_prod_def row_bra_vec index_vec
  by (smt lessThan_atLeast0 lessThan_iff sum.cong)

lemma inner_prod_with_row_bra_vec_col_ket_vec [simp]:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = (row \<langle>u| 0) \<bullet> (col |v\<rangle> 0)"
  using assms by (simp add: inner_prod_def scalar_prod_def)

lemma inner_prod_with_times_mat [simp]:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>u|v\<rangle> = (\<langle>u| * |v\<rangle>) $$ (0,0)"
  using assms inner_prod_with_row_bra_vec_col_ket_vec 
  by (simp add: inner_prod_def times_mat_def ket_vec_def bra_def)

lemma orthogonal_unit_vec [simp]:
  assumes "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>unit_vec n i|unit_vec n j\<rangle> = 0"
proof-
  have "\<langle>unit_vec n i|unit_vec n j\<rangle> = unit_vec n i \<bullet> unit_vec n j"
    using assms unit_vec_def inner_prod_def scalar_prod_def
    by (smt complex_cnj_zero index_unit_vec(3) index_vec inner_prod_with_row_bra_vec row_bra_vec 
        scalar_prod_right_unit)
  thus ?thesis
    using assms scalar_prod_def unit_vec_def by simp 
qed

text \<open>We prove that our inner product is linear in its second argument.\<close>

lemma vec_index_is_linear [simp]:
  assumes "dim_vec u = dim_vec v" and "j < dim_vec u"
  shows "(k \<cdot>\<^sub>v u + l \<cdot>\<^sub>v v) $ j = k * (u $ j) + l * (v $ j)"
  using assms vec_index_def smult_vec_def plus_vec_def by simp

lemma inner_prod_is_linear [simp]:
  fixes u::"complex vec" and v::"nat \<Rightarrow> complex vec" and l::"nat \<Rightarrow> complex"
  assumes "\<forall>i\<in>{0, 1}. dim_vec u = dim_vec (v i)"
  shows "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = (\<Sum>i\<le>1. l i * \<langle>u|v i\<rangle>)"
proof -
  have f1:"dim_vec (l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1) = dim_vec u"
    using assms by simp
  then have "\<langle>u|l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1\<rangle> = (\<Sum>i\<in>{0 ..< dim_vec u}. cnj (u $ i) * ((l 0 \<cdot>\<^sub>v v 0 + l 1 \<cdot>\<^sub>v v 1) $ i))"
    by (simp add: inner_prod_def)
  also have "\<dots> = (\<Sum>i\<in>{0 ..< dim_vec u}. cnj (u $ i) * (l 0 * v 0 $ i + l 1 * v 1 $ i))"
    using assms by simp
  also have "\<dots> = l 0 * (\<Sum>i\<in>{0 ..< dim_vec u}. cnj(u $ i) * (v 0 $ i)) + l 1 * (\<Sum>i\<in>{0 ..< dim_vec u}. cnj(u $ i) * (v 1 $ i))"
    by (auto simp: algebra_simps)
      (simp add: sum.distrib sum_distrib_left)
  also have "\<dots> = l 0 * \<langle>u|v 0\<rangle> + l 1 * \<langle>u|v 1\<rangle>"
    using assms inner_prod_def by auto
  finally show ?thesis by simp
qed

lemma inner_prod_cnj:
  assumes "dim_vec u = dim_vec v"
  shows "\<langle>v|u\<rangle> = cnj (\<langle>u|v\<rangle>)"
  by (simp add: assms inner_prod_def algebra_simps)

lemma inner_prod_with_itself_Im [simp]:
  "Im (\<langle>u|u\<rangle>) = 0"
  using inner_prod_cnj by (metis Reals_cnj_iff complex_is_Real_iff)

lemma inner_prod_with_itself_real [simp]:
  "\<langle>u|u\<rangle> \<in> \<real>"
  using inner_prod_with_itself_Im by (simp add: complex_is_Real_iff)

lemma inner_prod_with_itself_eq0 [simp]:
  assumes "u = 0\<^sub>v (dim_vec u)"
  shows "\<langle>u|u\<rangle> = 0"
  using assms inner_prod_def zero_vec_def
  by (smt atLeastLessThan_iff complex_cnj_zero index_zero_vec(1) mult_zero_left sum.neutral)

lemma inner_prod_with_itself_Re:
  "Re (\<langle>u|u\<rangle>) \<ge> 0"
proof -
  have "Re (\<langle>u|u\<rangle>) = (\<Sum>i<dim_vec u. Re (cnj(u $ i) * (u $ i)))"
    by (simp add: inner_prod_def lessThan_atLeast0)
  moreover have "\<dots> = (\<Sum>i<dim_vec u. (Re (u $ i))\<^sup>2 + (Im (u $ i))\<^sup>2)"
    using complex_mult_cnj
    by (metis (no_types, lifting) Re_complex_of_real semiring_normalization_rules(7))
  ultimately show "Re (\<langle>u|u\<rangle>) \<ge> 0" by (simp add: sum_nonneg)
qed

lemma inner_prod_with_itself_nonneg_reals:
  fixes u::"complex vec"
  shows "\<langle>u|u\<rangle> \<in> nonneg_Reals"
  using inner_prod_with_itself_real inner_prod_with_itself_Re complex_nonneg_Reals_iff 
inner_prod_with_itself_Im by auto

lemma inner_prod_with_itself_Re_non0:
  assumes "u \<noteq> 0\<^sub>v (dim_vec u)"
  shows "Re (\<langle>u|u\<rangle>) > 0"
proof -
  obtain i where a1:"i < dim_vec u" and "u $ i \<noteq> 0"
    using assms zero_vec_def by (metis dim_vec eq_vecI index_zero_vec(1))
  then have f1:"Re (cnj (u $ i) * (u $ i)) > 0"
    by (metis Re_complex_of_real complex_mult_cnj complex_neq_0 mult.commute)
  moreover have f2:"Re (\<langle>u|u\<rangle>) = (\<Sum>i<dim_vec u. Re (cnj(u $ i) * (u $ i)))"
    using inner_prod_def by (simp add: lessThan_atLeast0)
  moreover have f3:"\<forall>i<dim_vec u. Re (cnj(u $ i) * (u $ i)) \<ge> 0"
    using complex_mult_cnj by simp
  ultimately show ?thesis
    using a1 inner_prod_def lessThan_iff
    by (metis (no_types, lifting) finite_lessThan sum_pos2)
qed

lemma inner_prod_with_itself_nonneg_reals_non0:
  assumes "u \<noteq> 0\<^sub>v (dim_vec u)"
  shows "\<langle>u|u\<rangle> \<noteq> 0"
  using assms inner_prod_with_itself_Re_non0 by fastforce

lemma cpx_vec_length_inner_prod [simp]:
  "\<parallel>v\<parallel>\<^sup>2 = \<langle>v|v\<rangle>"
proof -
  have "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>i<dim_vec v. (cmod (v $ i))\<^sup>2)"
    using cpx_vec_length_def complex_of_real_def
    by (metis (no_types, lifting) real_sqrt_power real_sqrt_unique sum_nonneg zero_le_power2)
  also have "\<dots> = (\<Sum>i<dim_vec v. cnj (v $ i) * (v $ i))"
    using complex_norm_square mult.commute by (smt of_real_sum sum.cong)
  finally show ?thesis
    using inner_prod_def by (simp add: lessThan_atLeast0)
qed

lemma inner_prod_csqrt [simp]:
  "csqrt \<langle>v|v\<rangle> = \<parallel>v\<parallel>"
  using inner_prod_with_itself_Re inner_prod_with_itself_Im csqrt_of_real_nonneg cpx_vec_length_def
  by (metis (no_types, lifting) Re_complex_of_real cpx_vec_length_inner_prod real_sqrt_ge_0_iff 
      real_sqrt_unique sum_nonneg zero_le_power2)


subsection "Unitary Matrices and Length-Preservation"

subsubsection "Unitary Matrices are Length-Preserving"

text \<open>The bra-vector @{text "\<langle>A * v|"} is given by @{text "\<langle>v| * A\<^sup>\<dagger>"}\<close>

lemma dagger_of_ket_is_bra:
  fixes v:: "complex vec"
  shows "( |v\<rangle> )\<^sup>\<dagger> = \<langle>v|"
  by (simp add: bra_def dagger_def ket_vec_def)

lemma bra_mat_on_vec:
  fixes v::"complex vec" and A::"complex mat"
  assumes "dim_col A = dim_vec v"
  shows "\<langle>A * v| = \<langle>v| * (A\<^sup>\<dagger>)"
proof
  show "dim_row \<langle>A * v| = dim_row (\<langle>v| * (A\<^sup>\<dagger>))"
    by (simp add: bra_def times_mat_def)
next
  show "dim_col \<langle>A * v| = dim_col (\<langle>v| * (A\<^sup>\<dagger>))"
    by (simp add: bra_def times_mat_def)
next
  fix i j::nat
  assume a1:"i < dim_row (\<langle>v| * (A\<^sup>\<dagger>))" and a2:"j < dim_col (\<langle>v| * (A\<^sup>\<dagger>))" 
  then have "cnj((A * v) $$ (j,0)) = cnj (row A j \<bullet> v)"
    using bra_def times_mat_def ket_vec_col ket_vec_def by simp
  also have f7:"\<dots>= (\<Sum>i\<in>{0 ..< dim_vec v}. cnj(v $ i) * cnj(A $$ (j,i)))"
    using row_def scalar_prod_def cnj_sum complex_cnj_mult mult.commute
    by (smt assms index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  moreover have f8:"(row \<langle>v| 0) \<bullet> (col (A\<^sup>\<dagger>) j) = 
    vec (dim_vec v) (\<lambda>i. cnj (v $ i)) \<bullet> vec (dim_col A) (\<lambda>i. cnj (A $$ (j,i)))"
    using a2 by simp 
  ultimately have "cnj((A * v) $$ (j,0)) = (row \<langle>v| 0) \<bullet> (col (A\<^sup>\<dagger>) j)"
    using assms scalar_prod_def
    by (smt dim_vec index_vec lessThan_atLeast0 lessThan_iff sum.cong)
  then have "\<langle>A * v| $$ (0,j) = (\<langle>v| * (A\<^sup>\<dagger>)) $$ (0,j)"
    using bra_def times_mat_def a2 by simp
  thus "\<langle>A * |v\<rangle>| $$ (i, j) = (\<langle>v| * (A\<^sup>\<dagger>)) $$ (i, j)" 
    using a1 by (simp add: times_mat_def bra_def)
qed

lemma mat_on_ket:
  fixes v:: "complex vec" and A:: "complex mat"
  assumes "dim_col A = dim_vec v"
  shows "A * |v\<rangle> = |col (A * v) 0\<rangle>"
  using assms ket_vec_def by auto

lemma dagger_of_mat_on_ket:
  fixes v:: "complex vec" and A :: "complex mat"
  assumes "dim_col A = dim_vec v"
  shows "(A * |v\<rangle> )\<^sup>\<dagger> = \<langle>v| * (A\<^sup>\<dagger>)"
  using assms by (metis bra_mat_on_vec dagger_of_ket_is_bra mat_on_ket)

definition col_fst :: "'a mat \<Rightarrow> 'a vec" where 
  "col_fst A = vec (dim_row A) (\<lambda> i. A $$ (i,0))"

lemma col_fst_is_col [simp]:
  "col_fst M = col M 0"
  by (simp add: col_def col_fst_def)

text \<open>
We need to declare @{term "col_fst"} as a coercion from matrices to vectors in order to see a column 
matrix as a vector. 
\<close>

declare 
  [[coercion_delete ket_vec]]
  [[coercion col_fst]]

lemma unit_vec_to_col:
  assumes "dim_col A = n" and "i < n"
  shows "col A i = A * |unit_vec n i\<rangle>"
proof
  show "dim_vec (col A i) = dim_vec (A * |unit_vec n i\<rangle>)"
    using col_def times_mat_def by simp
next
  fix j::nat
  assume "j < dim_vec (col_fst (A * |unit_vec n i\<rangle>))"
  then show "col A i $ j = (A * |unit_vec n i\<rangle>) $ j"
    using assms times_mat_def ket_vec_def
    by (smt col_fst_is_col dim_col dim_col_mat(1) index_col index_mult_mat(1) index_mult_mat(2) 
index_row(1) ket_vec_col less_numeral_extra(1) scalar_prod_right_unit)
qed

lemma mult_ket_vec_is_ket_vec_of_mult:
  fixes A::"complex mat" and v::"complex vec"
  assumes "dim_col A = dim_vec v"
  shows "|A * |v\<rangle> \<rangle> = A * |v\<rangle>"
  using assms ket_vec_def
  by (metis One_nat_def col_fst_is_col dim_col dim_col_mat(1) index_mult_mat(3) ket_vec_col less_Suc0 
mat_col_eqI)

lemma unitary_is_sq_length_preserving [simp]:
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2"
proof -
  have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<^sup>\<dagger>) * |U * |v\<rangle>\<rangle>) $$ (0,0)"
    using assms(2) bra_mat_on_vec
    by (metis inner_prod_with_times_mat mult_ket_vec_is_ket_vec_of_mult)
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * (U\<^sup>\<dagger>) * (U * |v\<rangle>)) $$ (0,0)"
    using assms(2) mult_ket_vec_is_ket_vec_of_mult by simp
  moreover have f1:"dim_col \<langle>|v\<rangle>| = dim_vec v"
    using ket_vec_def bra_def by simp
  moreover have "dim_row (U\<^sup>\<dagger>) = dim_vec v"
    using assms(2) by simp
  ultimately have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * ((U\<^sup>\<dagger>) * U) * |v\<rangle>) $$ (0,0)"
    using assoc_mult_mat
    by(smt carrier_mat_triv dim_row_mat(1) dagger_def ket_vec_def mat_carrier times_mat_def)
  then have "\<langle>U * |v\<rangle>|U * |v\<rangle> \<rangle> = (\<langle>|v\<rangle>| * |v\<rangle>) $$ (0,0)"
    using assms f1 unitary_def by simp
  thus ?thesis
    using cpx_vec_length_inner_prod by(metis Re_complex_of_real inner_prod_with_times_mat)
qed

lemma col_ket_vec [simp]:
  assumes "dim_col M = 1"
  shows "|col M 0\<rangle> = M"
  using eq_matI assms ket_vec_def by auto

lemma state_col_ket_vec:
  assumes "state 1 v"
  shows "state 1 |col v 0\<rangle>"
  using assms by (simp add: state_def)

lemma col_ket_vec_index [simp]:
  assumes "i < dim_row v"
  shows "|col v 0\<rangle> $$ (i,0) = v $$ (i,0)"
  using assms ket_vec_def by (simp add: col_def)

lemma col_index_of_mat_col [simp]:
  assumes "dim_col v = 1" and "i < dim_row v"
  shows "col v 0 $ i = v $$ (i,0)"
  using assms by simp

lemma unitary_is_sq_length_preserving_bis [simp]:
  assumes "unitary U" and "dim_row v = dim_col U" and "dim_col v = 1"
  shows "\<parallel>col (U * v) 0\<parallel>\<^sup>2 = \<parallel>col v 0\<parallel>\<^sup>2"
proof -
  have "dim_vec (col v 0) = dim_col U"
    using assms(2) by simp
  then have "\<parallel>col_fst (U * |col v 0\<rangle>)\<parallel>\<^sup>2 = \<parallel>col v 0\<parallel>\<^sup>2"
    using unitary_is_sq_length_preserving[of "U" "col v 0"] assms(1) by simp
  thus ?thesis
    using assms(3) by simp
qed

text \<open> 
A unitary matrix is length-preserving, i.e. it acts on a vector to produce another vector of the 
same length. 
\<close>

lemma unitary_is_length_preserving_bis [simp]:
  fixes U::"complex mat" and v::"complex mat"
  assumes "unitary U" and "dim_row v = dim_col U" and "dim_col v = 1"
  shows "\<parallel>col (U * v) 0\<parallel> = \<parallel>col v 0\<parallel>"
  using assms unitary_is_sq_length_preserving_bis
  by (metis cpx_vec_length_inner_prod inner_prod_csqrt of_real_hom.injectivity)

lemma unitary_is_length_preserving [simp]:
  fixes U:: "complex mat" and v:: "complex vec"
  assumes "unitary U" and "dim_vec v = dim_col U"
  shows "\<parallel>U * |v\<rangle>\<parallel> = \<parallel>v\<parallel>"
  using assms unitary_is_sq_length_preserving
  by (metis cpx_vec_length_inner_prod inner_prod_csqrt of_real_hom.injectivity)


subsubsection "Length-Preserving Matrices are Unitary"

lemma inverts_mat_sym:
  fixes A B:: "complex mat"
  assumes "inverts_mat A B" and "dim_row B = dim_col A" and "square_mat B"
  shows "inverts_mat B A"
proof-
  define n where d0:"n = dim_row B"
  have "A * B = 1\<^sub>m (dim_row A)" using assms(1) inverts_mat_def by auto
  moreover have "dim_col B = dim_col (A * B)" using times_mat_def by simp
  ultimately have "dim_col B = dim_row A" by simp
  then have c0:"A \<in> carrier_mat n n" using assms(2,3) d0 by auto
  have c1:"B \<in> carrier_mat n n" using assms(3) d0 by auto
  have f0:"A * B = 1\<^sub>m n" using inverts_mat_def c0 c1 assms(1) by auto
  have f1:"det B \<noteq> 0"
  proof
    assume "det B = 0"
    then have "\<exists>v. v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> B *\<^sub>v v = 0\<^sub>v n"
      using det_0_iff_vec_prod_zero assms(3) c1 by blast
    then obtain v where d1:"v \<in> carrier_vec n \<and> v \<noteq> 0\<^sub>v n \<and> B *\<^sub>v v = 0\<^sub>v n" by auto
    then have d2:"dim_vec v = n" by simp
    have "B * |v\<rangle> = |0\<^sub>v n\<rangle>"
    proof
      show "dim_row (B * |v\<rangle>) = dim_row |0\<^sub>v n\<rangle>" using ket_vec_def d0 by simp
    next
      show "dim_col (B * |v\<rangle>) = dim_col |0\<^sub>v n\<rangle>" using ket_vec_def d0 by simp
    next
      fix i j assume "i < dim_row |0\<^sub>v n\<rangle>" and "j < dim_col |0\<^sub>v n\<rangle>"
      then have f2:"i < n \<and> j = 0" using ket_vec_def by simp
      moreover have "vec (dim_row B) (($) v) = v" using d0 d1 by auto
      moreover have "(B *\<^sub>v v) $ i = (\<Sum>ia = 0..<dim_row B. row B i $ ia * v $ ia)"
        using d0 d2 f2 by (auto simp add: scalar_prod_def)
      ultimately show "(B * |v\<rangle>) $$ (i, j) = |0\<^sub>v n\<rangle> $$ (i, j)"
        using ket_vec_def d0 d1 times_mat_def mult_mat_vec_def by (auto simp add: scalar_prod_def)
    qed
    moreover have "|v\<rangle> \<in> carrier_mat n 1" using d2 ket_vec_def by simp
    ultimately have "(A * B) * |v\<rangle> = A * |0\<^sub>v n\<rangle>" using c0 c1 by simp
    then have f3:"|v\<rangle> = A * |0\<^sub>v n\<rangle>" using d2 f0 ket_vec_def by auto
    have "v = 0\<^sub>v n"
    proof
      show "dim_vec v = dim_vec (0\<^sub>v n)" using d2 by simp
    next
      fix i assume f4:"i < dim_vec (0\<^sub>v n)"
      then have "|v\<rangle> $$ (i,0) = v $ i" using d2 ket_vec_def by simp
      moreover have "(A * |0\<^sub>v n\<rangle>) $$ (i, 0) = 0"
        using ket_vec_def times_mat_def scalar_prod_def f4 c0 by auto
      ultimately show "v $ i = 0\<^sub>v n $ i" using f3 f4 by simp
    qed
    then show False using d1 by simp
  qed
  have f5:"adj_mat B \<in> carrier_mat n n \<and> B * adj_mat B = det B \<cdot>\<^sub>m 1\<^sub>m n" using c1 adj_mat by auto
  then have c2:"((1/det B) \<cdot>\<^sub>m adj_mat B) \<in> carrier_mat n n" by simp
  have f6:"B * ((1/det B) \<cdot>\<^sub>m adj_mat B) = 1\<^sub>m n" using c1 f1 f5 mult_smult_distrib[of "B"] by auto
  then have "A = (A * B) * ((1/det B) \<cdot>\<^sub>m adj_mat B)" using c0 c1 c2 by simp
  then have "A = (1/det B) \<cdot>\<^sub>m adj_mat B" using f0 c2 by auto
  then show ?thesis using c0 c1 f6 inverts_mat_def by auto
qed

lemma sum_of_unit_vec_length:
  fixes i j n:: nat and c:: complex
  assumes "i < n" and "j < n" and "i \<noteq> j"
  shows "\<parallel>unit_vec n i + c \<cdot>\<^sub>v unit_vec n j\<parallel>\<^sup>2 = 1 + cnj(c) * c"
proof-
  define v where d0:"v = unit_vec n i + c \<cdot>\<^sub>v unit_vec n j"
  have "\<forall>k<n. v $ k = (if k = i then 1 else (if k = j then c else 0))"
    using d0 assms(1,2,3) by auto
  then have "\<forall>k<n. cnj (v $ k) * v $ k = (if k = i then 1 else 0) + (if k = j then cnj(c) * c else 0)"
    using assms(3) by auto
  moreover have "\<parallel>v\<parallel>\<^sup>2 = (\<Sum>k = 0..<n. cnj (v $ k) * v $ k)"
    using d0 assms cpx_vec_length_inner_prod inner_prod_def by simp
  ultimately show ?thesis
    using d0 assms by (auto simp add: sum.distrib)
qed

lemma sum_of_unit_vec_to_col:
  assumes "dim_col A = n" and "i < n" and "j < n"
  shows "col A i + c \<cdot>\<^sub>v col A j = A * |unit_vec n i + c \<cdot>\<^sub>v unit_vec n j\<rangle>"
proof
  show "dim_vec (col A i + c \<cdot>\<^sub>v col A j) = dim_vec (col_fst (A * |unit_vec n i + c \<cdot>\<^sub>v unit_vec n j\<rangle>))"
    using assms(1) by auto
next
  fix k assume "k < dim_vec (col_fst (A * |unit_vec n i + c \<cdot>\<^sub>v unit_vec n j\<rangle>))"
  then have f0:"k < dim_row A" using assms(1) by auto
  have "(col A i + c \<cdot>\<^sub>v col A j) $ k = A $$ (k, i) + c * A $$ (k, j)"
    using f0 assms(1-3) by auto
  moreover have "(\<Sum>x<n. A $$ (k, x) * ((if x = i then 1 else 0) + c * (if x = j then 1 else 0))) = 
                 (\<Sum>x<n. A $$ (k, x) * (if x = i then 1 else 0)) + 
                 (\<Sum>x<n. A $$ (k, x) * c * (if x = j then 1 else 0))"
    by (auto simp add: sum.distrib algebra_simps)
  moreover have "\<forall>x<n. A $$ (k, x) * (if x = i then 1 else 0) = (if x = i then A $$ (k, x) else 0)"
    by simp
  moreover have "\<forall>x<n. A $$ (k, x) * c * (if x = j then 1 else 0) = (if x = j then A $$ (k, x) * c else 0)"
    by simp
  ultimately show "(col A i + c \<cdot>\<^sub>v col A j) $ k = col_fst (A * |unit_vec n i + c \<cdot>\<^sub>v unit_vec n j\<rangle>) $ k"
    using f0 assms(1-3) times_mat_def scalar_prod_def ket_vec_def by auto
qed

lemma inner_prod_is_sesquilinear:
  fixes u1 u2 v1 v2:: "complex vec" and c1 c2 c3 c4:: complex and n:: nat
  assumes "dim_vec u1 = n" and "dim_vec u2 = n" and "dim_vec v1 = n" and "dim_vec v2 = n"
  shows "\<langle>c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2|c3 \<cdot>\<^sub>v v1 + c4 \<cdot>\<^sub>v v2\<rangle> = cnj (c1) * c3 * \<langle>u1|v1\<rangle> + cnj (c2) * c3 * \<langle>u2|v1\<rangle> + 
                                                 cnj (c1) * c4 * \<langle>u1|v2\<rangle> + cnj (c2) * c4 * \<langle>u2|v2\<rangle>"
proof-
  have "\<langle>c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2|c3 \<cdot>\<^sub>v v1 + c4 \<cdot>\<^sub>v v2\<rangle> = c3 * \<langle>c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2|v1\<rangle> + c4 * \<langle>c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2|v2\<rangle>"
    using inner_prod_is_linear[of "c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2" "\<lambda>i. if i = 0 then v1 else v2" 
                                  "\<lambda>i. if i = 0 then c3 else c4"] assms
    by simp
  also have "... = c3 * cnj(\<langle>v1|c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2\<rangle>) + c4 * cnj(\<langle>v2|c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2\<rangle>)"
    using assms inner_prod_cnj[of "v1" "c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2"] inner_prod_cnj[of "v2" "c1 \<cdot>\<^sub>v u1 + c2 \<cdot>\<^sub>v u2"] 
    by simp
  also have "... = c3 * cnj(c1 * \<langle>v1|u1\<rangle> + c2 * \<langle>v1|u2\<rangle>) + c4 * cnj(c1 * \<langle>v2|u1\<rangle> + c2 * \<langle>v2|u2\<rangle>)"
    using inner_prod_is_linear[of "v1" "\<lambda>i. if i = 0 then u1 else u2" "\<lambda>i. if i = 0 then c1 else c2"] 
          inner_prod_is_linear[of "v2" "\<lambda>i. if i = 0 then u1 else u2" "\<lambda>i. if i = 0 then c1 else c2"] assms
    by simp
  also have "... = c3 * (cnj(c1) * \<langle>u1|v1\<rangle> + cnj(c2) * \<langle>u2|v1\<rangle>) + 
                   c4 * (cnj(c1) * \<langle>u1|v2\<rangle> + cnj(c2) * \<langle>u2|v2\<rangle>)"
    using inner_prod_cnj[of "v1" "u1"] inner_prod_cnj[of "v1" "u2"] 
          inner_prod_cnj[of "v2" "u1"] inner_prod_cnj[of "v2" "u2"] assms
    by simp
  finally show ?thesis
    by (auto simp add: algebra_simps)
qed

text \<open>
A length-preserving matrix is unitary. So, unitary matrices are exactly the length-preserving
matrices.
\<close>

lemma length_preserving_is_unitary:
  fixes U:: "complex mat"
  assumes "square_mat U" and "\<forall>v::complex vec. dim_vec v = dim_col U \<longrightarrow> \<parallel>U * |v\<rangle>\<parallel> = \<parallel>v\<parallel>"
  shows "unitary U"
proof-
  define n where "n = dim_col U"
  then have c0:"U \<in> carrier_mat n n" using assms(1) by auto
  then have c1:"U\<^sup>\<dagger> \<in> carrier_mat n n" using assms(1) dagger_def by auto
  have f0:"(U\<^sup>\<dagger>) * U = 1\<^sub>m (dim_col U)"
  proof
    show "dim_row (U\<^sup>\<dagger> * U) = dim_row (1\<^sub>m (dim_col U))" using c0 by simp
  next
    show "dim_col (U\<^sup>\<dagger> * U) = dim_col (1\<^sub>m (dim_col U))" using c0 by simp
  next
    fix i j assume "i < dim_row (1\<^sub>m (dim_col U))" and "j < dim_col (1\<^sub>m (dim_col U))"
    then have a0:"i < n \<and> j < n" using c0 by simp
    have f1:"\<And>l. l<n \<longrightarrow> (\<Sum>k<n. cnj (U $$ (k, l)) * U $$ (k, l)) = 1"
    proof
      fix l assume a1:"l<n"
      define v::"complex vec" where d1:"v = unit_vec n l"
      have "\<parallel>col U l\<parallel>\<^sup>2 = (\<Sum>k<n. cnj (U $$ (k, l)) * U $$ (k, l))"
        using c0 a1 cpx_vec_length_inner_prod inner_prod_def lessThan_atLeast0 by simp
      moreover have "\<parallel>col U l\<parallel>\<^sup>2 = \<parallel>v\<parallel>\<^sup>2" using c0 d1 a1 assms(2) unit_vec_to_col by simp
      moreover have "\<parallel>v\<parallel>\<^sup>2 = 1" using d1 a1 cpx_vec_length_inner_prod by simp
      ultimately show "(\<Sum>k<n. cnj (U $$ (k, l)) * U $$ (k, l)) = 1" by simp
    qed
    moreover have "i \<noteq> j \<longrightarrow> (\<Sum>k<n. cnj (U $$ (k, i)) * U $$ (k, j)) = 0"
    proof
      assume a2:"i \<noteq> j"
      define v1::"complex vec" where d1:"v1 = unit_vec n i + 1 \<cdot>\<^sub>v unit_vec n j"
      define v2::"complex vec" where d2:"v2 = unit_vec n i + \<i> \<cdot>\<^sub>v unit_vec n j"
      have "\<parallel>v1\<parallel>\<^sup>2 = 1 + cnj 1 * 1" using d1 a0 a2 sum_of_unit_vec_length by blast
      then have "\<parallel>v1\<parallel>\<^sup>2 = 2"
        by (metis complex_cnj_one cpx_vec_length_inner_prod mult.left_neutral of_real_eq_iff 
            of_real_numeral one_add_one)
      then have "\<parallel>U * |v1\<rangle>\<parallel>\<^sup>2 = 2" using c0 d1 assms(2) unit_vec_to_col by simp
      moreover have "col U i + 1 \<cdot>\<^sub>v col U j = U * |v1\<rangle>"
        using c0 d1 a0 sum_of_unit_vec_to_col by blast
      moreover have "col U i + 1 \<cdot>\<^sub>v col U j = col U i + col U j" by simp
      ultimately have "\<langle>col U i + col U j|col U i + col U j\<rangle> = 2"
        using cpx_vec_length_inner_prod by (metis of_real_numeral)
      moreover have "\<langle>col U i + col U j|col U i + col U j\<rangle> = 
               \<langle>col U i|col U i\<rangle> + \<langle>col U j|col U i\<rangle> + \<langle>col U i|col U j\<rangle> + \<langle>col U j|col U j\<rangle>"
        using inner_prod_is_sesquilinear[of "col U i" "dim_row U" "col U j" "col U i" "col U j" "1" "1" "1" "1"]
        by simp
      ultimately have f2:"\<langle>col U j|col U i\<rangle> + \<langle>col U i|col U j\<rangle> = 0"
        using c0 a0 f1 inner_prod_def lessThan_atLeast0 by simp

      have "\<parallel>v2\<parallel>\<^sup>2 = 1 + cnj \<i> * \<i>" using a0 a2 d2 sum_of_unit_vec_length by simp
      then have "\<parallel>v2\<parallel>\<^sup>2 = 2"
        by (metis Re_complex_of_real complex_norm_square mult.commute norm_ii numeral_Bit0 
            numeral_One numeral_eq_one_iff of_real_numeral one_power2)
      moreover have "\<parallel>U * |v2\<rangle>\<parallel>\<^sup>2 = \<parallel>v2\<parallel>\<^sup>2" using c0 d2 assms(2) unit_vec_to_col by simp
      moreover have "\<langle>col U i + \<i> \<cdot>\<^sub>v col U j|col U i + \<i> \<cdot>\<^sub>v col U j\<rangle> = \<parallel>U * |v2\<rangle>\<parallel>\<^sup>2"
        using c0 a0 d2 sum_of_unit_vec_to_col cpx_vec_length_inner_prod by auto
      moreover have "\<langle>col U i + \<i> \<cdot>\<^sub>v col U j|col U i + \<i> \<cdot>\<^sub>v col U j\<rangle> = 
                     \<langle>col U i|col U i\<rangle> + (-\<i>) * \<langle>col U j|col U i\<rangle> + \<i> * \<langle>col U i|col U j\<rangle> + \<langle>col U j|col U j\<rangle>"
        using inner_prod_is_sesquilinear[of "col U i" "dim_row U" "col U j" "col U i" "col U j" "1" "\<i>" "1" "\<i>"]
        by simp
      ultimately have "\<langle>col U j|col U i\<rangle> - \<langle>col U i|col U j\<rangle> = 0"
        using c0 a0 f1 inner_prod_def lessThan_atLeast0 by auto
      then show "(\<Sum>k<n. cnj (U $$ (k, i)) * U $$ (k, j)) = 0"
        using c0 a0 f2 lessThan_atLeast0 inner_prod_def by auto
    qed
    ultimately show "(U\<^sup>\<dagger> * U) $$ (i, j) = 1\<^sub>m (dim_col U) $$ (i, j)"
      using c0 assms(1) a0 one_mat_def dagger_def by auto
qed
  then have "(U\<^sup>\<dagger>) * U = 1\<^sub>m n" using c0 by simp
  then have "inverts_mat (U\<^sup>\<dagger>) U" using c1 inverts_mat_def by auto
  then have "inverts_mat U (U\<^sup>\<dagger>)" using c0 c1 inverts_mat_sym by simp
  then have "U * (U\<^sup>\<dagger>) = 1\<^sub>m (dim_row U)" using c0 inverts_mat_def by auto
  then show ?thesis using f0 unitary_def by simp
qed

lemma inner_prod_with_unitary_mat [simp]:
  assumes "unitary U" and "dim_vec u = dim_col U" and "dim_vec v = dim_col U"
  shows "\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = \<langle>u|v\<rangle>"
proof -
  have f1:"\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = (\<langle>|u\<rangle>| * (U\<^sup>\<dagger>) * U * |v\<rangle>) $$ (0,0)"
    using assms(2-3) bra_mat_on_vec mult_ket_vec_is_ket_vec_of_mult
    by (smt assoc_mult_mat carrier_mat_triv col_fst_def dim_vec dim_col_of_dagger index_mult_mat(2) 
        index_mult_mat(3) inner_prod_with_times_mat ket_vec_def mat_carrier)
  moreover have f2:"\<langle>|u\<rangle>| \<in> carrier_mat 1 (dim_vec v)"
    using bra_def ket_vec_def assms(2-3) by simp
  moreover have f3:"U\<^sup>\<dagger> \<in> carrier_mat (dim_col U) (dim_row U)"
    using dagger_def by simp
  ultimately have "\<langle>U * |u\<rangle>|U * |v\<rangle>\<rangle> = (\<langle>|u\<rangle>| * (U\<^sup>\<dagger> * U) * |v\<rangle>) $$ (0,0)"
    using assms(3) assoc_mult_mat by (metis carrier_mat_triv)
  also have "\<dots> = (\<langle>|u\<rangle>| * |v\<rangle>) $$ (0,0)"
    using assms(1) unitary_def
    by (simp add: assms(2) bra_def ket_vec_def)
  finally show ?thesis
    using assms(2-3) inner_prod_with_times_mat by presburger
qed

text \<open>As a consequence we prove that columns and rows of a unitary matrix are orthonormal vectors.\<close>

lemma unitary_unit_col [simp]:
  assumes "unitary U" and "dim_col U = n" and "i < n"
  shows "\<parallel>col U i\<parallel> = 1"
  using assms unit_vec_to_col unitary_is_length_preserving by simp

lemma unitary_unit_row [simp]:
  assumes "unitary U" and "dim_row U = n" and "i < n"
  shows "\<parallel>row U i\<parallel> = 1"
proof -
  have "row U i = col (U\<^sup>t) i"
    using  assms(2-3) by simp
  thus ?thesis
    using assms transpose_of_unitary_is_unitary unitary_unit_col
    by (metis index_transpose_mat(3))
qed

lemma orthogonal_col_of_unitary [simp]:
  assumes "unitary U" and "dim_col U = n" and "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>col U i|col U j\<rangle> = 0"
proof -
  have "\<langle>col U i|col U j\<rangle> = \<langle>U * |unit_vec n i\<rangle>| U * |unit_vec n j\<rangle>\<rangle>"
    using assms(2-4) unit_vec_to_col by simp
  also have "\<dots> = \<langle>unit_vec n i |unit_vec n j\<rangle>"
    using assms(1-2) inner_prod_with_unitary_mat index_unit_vec(3) by simp
  finally show ?thesis
    using assms(3-5) by simp
qed

lemma orthogonal_row_of_unitary [simp]:
  fixes U::"complex mat"
  assumes "unitary U" and "dim_row U = n" and "i < n" and "j < n" and "i \<noteq> j"
  shows "\<langle>row U i|row U j\<rangle> = 0"
  using assms orthogonal_col_of_unitary transpose_of_unitary_is_unitary col_transpose
  by (metis index_transpose_mat(3))


text\<open>
As a consequence, we prove that a quantum gate acting on a state of a system of n qubits give 
another state of that same system.
\<close>

lemma gate_on_state_is_state [intro, simp]:
  assumes a1:"gate n A" and a2:"state n v"
  shows "state n (A * v)"
proof
  show "dim_row (A * v) = 2^n"
    using gate_def state_def a1 by simp
next
  show "dim_col (A * v) = 1"
    using state_def a2 by simp
next
  have "square_mat A"
    using a1 gate_def by simp
  then have "dim_col A = 2^n"
    using a1 gate.dim_row by simp
  then have "dim_col A = dim_row v"
    using a2 state.dim_row by simp
  then have "\<parallel>col (A * v) 0\<parallel> = \<parallel>col v 0\<parallel>"
    using unitary_is_length_preserving_bis assms gate_def state_def by simp
  thus"\<parallel>col (A * v) 0\<parallel> = 1"
    using a2 state.is_normal by simp
qed


subsection \<open>A Few Well-known Quantum Gates\<close>

text \<open>
Any unitary operation on n qubits can be implemented exactly by composing single qubits and
CNOT-gates (controlled-NOT gates). However, no straightforward method is known to implement these 
gates in a fashion which is resistant to errors. But, the Hadamard gate, the phase gate, the 
CNOT-gate and the @{text "\<pi>/8"} gate are also universal for quantum computations, i.e. any quantum circuit on 
n qubits can be approximated to an arbitrary accuracy by using only these gates, and these gates can 
be implemented in a fault-tolerant way. 
\<close>

text \<open>We introduce a coercion from real matrices to complex matrices.\<close>

definition real_to_cpx_mat:: "real mat \<Rightarrow> complex mat" where
"real_to_cpx_mat A \<equiv> mat (dim_row A) (dim_col A) (\<lambda>(i,j). A $$ (i,j))"

text \<open>Our first quantum gate: the identity matrix! Arguably, not a very interesting one though!\<close>

definition Id :: "nat \<Rightarrow> complex mat" where
"Id n \<equiv> 1\<^sub>m (2^n)"

lemma id_is_gate [simp]:
  "gate n (Id n)"
proof
  show "dim_row (Id n) = 2^n"
    using Id_def by simp
next
  show "square_mat (Id n)"
    using Id_def by simp
next
  show "unitary (Id n)" 
    by (simp add: Id_def)
qed

text \<open>More interesting: the Pauli matrices.\<close>

definition X ::"complex mat" where
"X \<equiv> mat 2 2 (\<lambda>(i,j). if i=j then 0 else 1)"

text\<open> 
Be aware that @{text "gate n A"} means that the matrix A has dimension @{text "2^n * 2^n"}. 
For instance, with this convention a 2 X 2 matrix A which is unitary satisfies @{text "gate 1 A"}
 but not @{text "gate 2 A"} as one might have been expected.
\<close>

lemma dagger_of_X [simp]:
  "X\<^sup>\<dagger> = X"
  using dagger_def by (simp add: X_def cong_mat)

lemma X_inv [simp]:
  "X * X = 1\<^sub>m 2"
  apply(simp add: X_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma X_is_gate [simp]:
  "gate 1 X"
  by (simp add: gate_def unitary_def)
    (simp add: X_def)

definition Y ::"complex mat" where
"Y \<equiv> mat 2 2 (\<lambda>(i,j). if i=j then 0 else (if i=0 then -\<i> else \<i>))"

lemma dagger_of_Y [simp]:
  "Y\<^sup>\<dagger> = Y"
  using dagger_def by (simp add: Y_def cong_mat)

lemma Y_inv [simp]:
  "Y * Y = 1\<^sub>m 2"
  apply(simp add: Y_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma Y_is_gate [simp]:
  "gate 1 Y"
  by (simp add: gate_def unitary_def)
    (simp add: Y_def)

definition Z ::"complex mat" where
"Z \<equiv> mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 0 else (if i=0 then 1 else -1))"

lemma dagger_of_Z [simp]:
  "Z\<^sup>\<dagger> = Z"
  using dagger_def by (simp add: Z_def cong_mat)

lemma Z_inv [simp]:
  "Z * Z = 1\<^sub>m 2"
  apply(simp add: Z_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma Z_is_gate [simp]:
  "gate 1 Z"
  by (simp add: gate_def unitary_def)
    (simp add: Z_def)

text \<open>The Hadamard gate\<close>

definition H ::"complex mat" where
"H \<equiv> 1/sqrt(2) \<cdot>\<^sub>m (mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1 else (if i=0 then 1 else -1)))"

lemma H_without_scalar_prod:
  "H = mat 2 2 (\<lambda>(i,j). if i\<noteq>j then 1/sqrt(2) else (if i=0 then 1/sqrt(2) else -(1/sqrt(2))))"
  using cong_mat by (auto simp: H_def)

lemma dagger_of_H [simp]:
  "H\<^sup>\<dagger> = H"
  using dagger_def by (auto simp: H_def cong_mat)

lemma H_inv [simp]:
  "H * H = 1\<^sub>m 2"
  apply(simp add: H_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def complex_eqI)

lemma H_is_gate [simp]:
  "gate 1 H"
  by (simp add: gate_def unitary_def)
    (simp add: H_def)

lemma H_values:
  fixes i j:: nat
  assumes "i < dim_row H" and "j < dim_col H" and "i \<noteq> 1 \<or> j \<noteq> 1" 
  shows "H $$ (i,j) = 1/sqrt 2"
proof-
  have "i < 2"
    using assms(1) by (simp add: H_without_scalar_prod less_2_cases)
  moreover have "j < 2"
    using assms(2) by (simp add: H_without_scalar_prod less_2_cases)
  ultimately show ?thesis 
    using assms(3) H_without_scalar_prod by(smt One_nat_def index_mat(1) less_2_cases old.prod.case)
qed

lemma H_values_right_bottom:
  fixes i j:: nat
  assumes "i = 1 \<and> j = 1"
  shows "H $$ (i,j) = - 1/sqrt 2"     
  using assms by (simp add: H_without_scalar_prod)

text \<open>The controlled-NOT gate\<close>

definition CNOT ::"complex mat" where
"CNOT \<equiv> mat 4 4 
  (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else 
    (if i=1 \<and> j=1 then 1 else 
      (if i=2 \<and> j=3 then 1 else 
        (if i=3 \<and> j=2 then 1 else 0))))"

lemma dagger_of_CNOT [simp]:
  "CNOT\<^sup>\<dagger> = CNOT"
  using dagger_def by (simp add: CNOT_def cong_mat)

lemma CNOT_inv [simp]:
  "CNOT * CNOT = 1\<^sub>m 4"
  apply(simp add: CNOT_def times_mat_def one_mat_def)
  apply(rule cong_mat)
  by(auto simp: scalar_prod_def)

lemma CNOT_is_gate [simp]:
  "gate 2 CNOT"
  by (simp add: gate_def unitary_def)
    (simp add: CNOT_def)

text \<open>The phase gate, also known as the S-gate\<close>

definition S ::"complex mat" where
"S \<equiv> mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else (if i=1 \<and> j=1 then \<i> else 0))"

text \<open>The @{text "\<pi>/8"} gate, also known as the T-gate\<close>

definition T ::"complex mat" where
"T \<equiv> mat 2 2 (\<lambda>(i,j). if i=0 \<and> j=0 then 1 else (if i=1 \<and> j=1 then exp(\<i>*(pi/4)) else 0))"

text \<open>A few relations between the Hadamard gate and the Pauli matrices\<close>

lemma HXH_is_Z [simp]:
  "H * X * H = Z" 
  apply(simp add: X_def Z_def H_def times_mat_def)
  apply(rule cong_mat)
  by(auto simp add: scalar_prod_def complex_eqI)

lemma HYH_is_minusY [simp]:
  "H * Y * H = - Y" 
  apply(simp add: Y_def H_def times_mat_def)
  apply(rule eq_matI)
  by(auto simp add: scalar_prod_def complex_eqI)

lemma HZH_is_X [simp]:
  shows "H * Z * H = X"  
  apply(simp add: X_def Z_def H_def times_mat_def)
  apply(rule cong_mat)
  by(auto simp add: scalar_prod_def complex_eqI)


subsection \<open>The Bell States\<close>

text \<open>
We introduce below the so-called Bell states, also known as EPR pairs (EPR stands for Einstein,
Podolsky and Rosen).
\<close>

definition bell00 ::"complex mat" ("|\<beta>\<^sub>0\<^sub>0\<rangle>") where
"bell00 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=0 \<or> i=3 then 1 else 0)\<rangle>"

definition bell01 ::"complex mat" ("|\<beta>\<^sub>0\<^sub>1\<rangle>") where
"bell01 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=1 \<or> i=2 then 1 else 0)\<rangle>"

definition bell10 ::"complex mat" ("|\<beta>\<^sub>1\<^sub>0\<rangle>") where
"bell10 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=0 then 1 else if i=3 then -1 else 0)\<rangle>"

definition bell11 ::"complex mat" ("|\<beta>\<^sub>1\<^sub>1\<rangle>") where
"bell11 \<equiv> 1/sqrt(2) \<cdot>\<^sub>m |vec 4 (\<lambda>i. if i=1 then 1 else if i=2 then -1 else 0)\<rangle>"

lemma
  shows bell00_is_state [simp]:"state 2 |\<beta>\<^sub>0\<^sub>0\<rangle>" and bell01_is_state [simp]:"state 2 |\<beta>\<^sub>0\<^sub>1\<rangle>" and 
    bell10_is_state [simp]:"state 2 |\<beta>\<^sub>1\<^sub>0\<rangle>" and bell11_is_state [simp]:"state 2 |\<beta>\<^sub>1\<^sub>1\<rangle>"
  by (auto simp: state_def bell00_def bell01_def bell10_def bell11_def ket_vec_def)
    (auto simp: cpx_vec_length_def Set_Interval.lessThan_atLeast0 cmod_def power2_eq_square) 

lemma bell00_index [simp]:
  shows "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (0,0) = 1/sqrt 2" and "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (1,0) = 0" and "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (2,0) = 0" and 
    "|\<beta>\<^sub>0\<^sub>0\<rangle> $$ (3,0) = 1/sqrt 2"
  by (auto simp: bell00_def ket_vec_def)

lemma bell01_index [simp]:
  shows "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (0,0) = 0" and "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (1,0) = 1/sqrt 2" and "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (2,0) = 1/sqrt 2" and 
    "|\<beta>\<^sub>0\<^sub>1\<rangle> $$ (3,0) = 0"
  by (auto simp: bell01_def ket_vec_def)

lemma bell10_index [simp]:
  shows "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (0,0) = 1/sqrt 2" and "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (1,0) = 0" and "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (2,0) = 0" and 
    "|\<beta>\<^sub>1\<^sub>0\<rangle> $$ (3,0) = - 1/sqrt 2"
  by (auto simp: bell10_def ket_vec_def)

lemma bell_11_index [simp]:
  shows "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (0,0) = 0" and "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (1,0) = 1/sqrt 2" and "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (2,0) = - 1/sqrt 2" and 
    "|\<beta>\<^sub>1\<^sub>1\<rangle> $$ (3,0) = 0"
  by (auto simp: bell11_def ket_vec_def)


subsection \<open>The Bitwise Inner Product\<close>

definition bitwise_inner_prod:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where 
"bitwise_inner_prod n i j = (\<Sum>k\<in>{0..<n}. (bin_rep n i) ! k * (bin_rep n j) ! k)"

abbreviation bip:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" ("_ \<cdot>\<^bsub>_\<^esub>  _") where
"bip i n j \<equiv> bitwise_inner_prod n i j"

lemma bitwise_inner_prod_fst_el_0: 
  assumes "i < 2^n \<or> j < 2^n" 
  shows "(i \<cdot>\<^bsub>Suc n\<^esub> j) = (i mod 2^n) \<cdot>\<^bsub>n\<^esub> (j mod 2^n)" 
proof-
  have "bip i (Suc n) j = (\<Sum>k\<in>{0..<(Suc n)}. (bin_rep (Suc n) i) ! k * (bin_rep (Suc n) j) ! k)" 
    using bitwise_inner_prod_def by simp
  also have "... = bin_rep (Suc n) i ! 0 * bin_rep (Suc n) j ! 0 + 
             (\<Sum>k\<in>{1..<(Suc n)}. bin_rep (Suc n) i ! k * bin_rep (Suc n) j ! k)"
    by (simp add: sum.atLeast_Suc_lessThan)
  also have "... = (\<Sum>k\<in>{1..<(Suc n)}. bin_rep (Suc n) i ! k * bin_rep (Suc n) j ! k)"
    using bin_rep_index_0[of i n] bin_rep_index_0[of j n] assms by auto
  also have "... = (\<Sum>k\<in>{0..<n}. bin_rep (Suc n) i !(k+1) * bin_rep (Suc n) j ! (k+1))" 
     using sum.shift_bounds_Suc_ivl[of "\<lambda>k. bin_rep (Suc n) i ! k * bin_rep (Suc n) j ! k" "0" "n"] 
     by (metis (no_types, lifting) One_nat_def add.commute plus_1_eq_Suc sum.cong)
  finally have "bip i (Suc n) j = (\<Sum>k\<in>{0..<n}. bin_rep (Suc n) i ! (k+1) * bin_rep (Suc n) j ! (k+1))" 
    by simp
  moreover have "k\<in>{0..n} \<longrightarrow> bin_rep (Suc n) i ! (k+1) = bin_rep n (i mod 2^n) ! k" for k
    using bin_rep_def by (simp add: bin_rep_aux_neq_nil)
  moreover have "k\<in>{0..n} \<longrightarrow> bin_rep (Suc n) j !(k+1) = bin_rep n (j mod 2^n) ! k" for k 
    using bin_rep_def by (simp add: bin_rep_aux_neq_nil)
  ultimately show ?thesis
    using assms bin_rep_index_0 bitwise_inner_prod_def by simp
qed

lemma bitwise_inner_prod_fst_el_is_1:
  fixes n i j:: nat
  assumes "i \<ge> 2^n \<and> j \<ge> 2^n" and "i < 2^(n+1) \<and> j < 2^(n+1)"
  shows "(i \<cdot>\<^bsub>(n+1)\<^esub> j) = 1 + ((i mod 2^n) \<cdot>\<^bsub>n\<^esub> (j mod 2^n))" 
proof-
  have "bip i (Suc n) j = (\<Sum>k\<in>{0..<(Suc n)}. bin_rep (Suc n) i ! k * bin_rep (Suc n) j ! k)" 
    using bitwise_inner_prod_def by simp
  also have "... = bin_rep (Suc n) i ! 0 * bin_rep (Suc n) j ! 0 + 
            (\<Sum>k\<in>{1..<(Suc n)}. bin_rep (Suc n) i ! k * bin_rep (Suc n) j ! k)"
    by (simp add: sum.atLeast_Suc_lessThan)
  also have "... = 1 + (\<Sum>k\<in>{1..<(Suc n)}. bin_rep (Suc n) i ! k * bin_rep (Suc n) j ! k)"
    using bin_rep_index_0_geq[of n i] bin_rep_index_0_geq[of n j] assms by simp
  also have "... = 1 + (\<Sum>k \<in> {0..<n}. bin_rep (Suc n) i ! (k+1) * bin_rep (Suc n) j ! (k+1))" 
    using sum.shift_bounds_Suc_ivl[of "\<lambda>k. (bin_rep (Suc n) i)!k * (bin_rep (Suc n) j)!k" "0" "n"] 
    by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 sum.cong)
  finally have f0:"bip i (Suc n) j = 1 + (\<Sum>k\<in>{0..<n}. bin_rep (Suc n) i ! (k+1) * bin_rep (Suc n) j ! (k+1))"
    by simp
  moreover have "k\<in>{0..n} \<longrightarrow> bin_rep (Suc n) i ! (k+1) = bin_rep n (i mod 2^n) ! k
\<and> bin_rep (Suc n) j ! (k+1) = bin_rep n (j mod 2^n) ! k" for k
    using bin_rep_def by(metis Suc_eq_plus1 bin_rep_aux.simps(2) bin_rep_aux_neq_nil butlast.simps(2) nth_Cons_Suc)
  ultimately show ?thesis
    using bitwise_inner_prod_def by simp
qed

lemma bitwise_inner_prod_with_zero:
  assumes "m < 2^n"
  shows "(0 \<cdot>\<^bsub>n\<^esub>  m) = 0" 
proof-
  have "(0 \<cdot>\<^bsub>n\<^esub>  m) = (\<Sum>j\<in>{0..<n}. bin_rep n 0 ! j * bin_rep n m ! j)" 
    using bitwise_inner_prod_def by simp
  moreover have "(\<Sum>j\<in>{0..<n}. bin_rep n 0 ! j * bin_rep n m ! j) 
               = (\<Sum>j\<in>{0..<n}. 0 * (bin_rep n m) ! j)"
    by (simp add: bin_rep_index)
  ultimately show "?thesis" 
    by simp
qed

(*
Biblio:

@book{MikeandIke,
  author = {Nielsen, Michael A. and Chuang, Isaac L.},
  publisher = {Cambridge University Press},
  title = {Quantum Computation and Quantum Information},
  year = 2010
}
*)
end