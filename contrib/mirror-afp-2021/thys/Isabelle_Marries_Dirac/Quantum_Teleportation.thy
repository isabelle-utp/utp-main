(* 
Authors: 

  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk;
  Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

section \<open>Quantum Teleportation\<close>

theory Quantum_Teleportation
imports 
  More_Tensor
  Basics
  Measurement
begin


definition alice:: "complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
"alice \<phi> \<equiv> (H \<Otimes> Id 2) * ((CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))"

abbreviation M1:: "complex Matrix.mat" where
"M1 \<equiv> mat_of_cols_list 8 [[1, 0, 0, 0, 0, 0, 0, 0],
                          [0, 1, 0, 0, 0, 0, 0, 0],
                          [0, 0, 1, 0, 0, 0, 0, 0],
                          [0, 0, 0, 1, 0, 0, 0, 0],
                          [0, 0, 0, 0, 0, 0, 1, 0],
                          [0, 0, 0, 0, 0, 0, 0, 1],
                          [0, 0, 0, 0, 1, 0, 0, 0],
                          [0, 0, 0, 0, 0, 1, 0, 0]]"

lemma tensor_prod_of_cnot_id_1: 
  shows "(CNOT \<Otimes> Id 1) = M1"
proof
  show "dim_col (CNOT \<Otimes> Id 1) = dim_col M1" 
    by(simp add: CNOT_def Id_def mat_of_cols_list_def)
  show "dim_row (CNOT \<Otimes> Id 1) = dim_row M1"
    by(simp add: CNOT_def Id_def  mat_of_cols_list_def)
  fix i j::nat assume "i < dim_row M1" and "j < dim_col M1"
  then have "i \<in> {0..<8} \<and> j \<in> {0..<8}"
    by (auto simp add:  mat_of_cols_list_def)
  then show "(CNOT \<Otimes> Id 1) $$ (i, j) = M1 $$ (i, j)"
    by (auto simp add: Id_def CNOT_def mat_of_cols_list_def)
qed

abbreviation M2:: "complex Matrix.mat" where
"M2 \<equiv> mat_of_cols_list 8 [[1/sqrt(2), 0, 0, 0, 1/sqrt(2), 0, 0, 0],
                          [0, 1/sqrt(2), 0, 0, 0, 1/sqrt(2), 0, 0],
                          [0, 0, 1/sqrt(2), 0, 0, 0, 1/sqrt(2), 0],
                          [0, 0, 0, 1/sqrt(2), 0, 0, 0, 1/sqrt(2)],
                          [1/sqrt(2), 0, 0, 0, -1/sqrt(2), 0, 0, 0],
                          [0, 1/sqrt(2), 0, 0, 0, -1/sqrt(2), 0, 0],
                          [0, 0, 1/sqrt(2), 0, 0, 0, -1/sqrt(2), 0],
                          [0, 0, 0, 1/sqrt(2), 0, 0, 0, -1/sqrt(2)]]"

lemma tensor_prod_of_h_id_2: 
  shows "(H \<Otimes> Id 2) = M2"
proof
  show "dim_col (H \<Otimes> Id 2) = dim_col M2"
    by(simp add: H_def Id_def mat_of_cols_list_def)
  show "dim_row (H \<Otimes> Id 2) = dim_row M2"
    by(simp add: H_def Id_def mat_of_cols_list_def)
  fix i j::nat assume "i < dim_row M2" and "j < dim_col M2"
  then have "i \<in> {0..<8} \<and> j \<in> {0..<8}"
    by (auto simp add:  mat_of_cols_list_def)
  then show "(H \<Otimes> Id 2) $$ (i, j) = M2 $$ (i, j)"
    by (auto simp add: Id_def H_def mat_of_cols_list_def)
qed

lemma alice_step_1_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)"
  using assms bell00_is_state tensor_state by(metis One_nat_def Suc_1 numeral_3_eq_3 plus_1_eq_Suc)

lemma alice_step_2_state:
  assumes "state 1 \<phi>"
  shows "state 3 ((CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))"
proof-
  have "gate 3 (CNOT \<Otimes> Id 1)"
    using CNOT_is_gate id_is_gate tensor_gate by (metis numeral_plus_one semiring_norm(5))
  then show "state 3 ((CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>))" using assms by simp
qed

lemma alice_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 (alice \<phi>) "
proof-
  have "gate 3 (H \<Otimes> Id 2)"
    using tensor_gate id_is_gate H_is_gate by(metis eval_nat_numeral(3) plus_1_eq_Suc)
  then show ?thesis 
    using assms alice_step_2_state by(simp add: alice_def)
qed

lemma alice_step_1:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "(\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = mat_of_cols_list 8 [[\<alpha>/sqrt(2),0,0,\<alpha>/sqrt(2),\<beta>/sqrt(2),0,0,\<beta>/sqrt(2)]]"
proof
  define v where asm:"v = mat_of_cols_list 8 [[\<alpha>/sqrt(2),0,0,\<alpha>/sqrt(2),\<beta>/sqrt(2),0,0,\<beta>/sqrt(2)]]"
  then show "dim_row (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = dim_row v"
    using assms(1) alice_step_1_state state.dim_row mat_of_cols_list_def by fastforce
  show "dim_col (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = dim_col v"
    using assms(1) alice_step_1_state state.is_column asm mat_of_cols_list_def by fastforce
  show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) $$ (i,j) = v $$ (i,j)"
  proof-
    fix i j assume "i < dim_row v" and "j < dim_col v"
    then have "i \<in> {0..<8} \<and> j = 0"
      using asm by (auto simp add: mat_of_cols_list_def)
    moreover have "dim_row |\<beta>\<^sub>0\<^sub>0\<rangle> = 4"
      using bell00_is_state state_def by simp
    moreover have "dim_col |\<beta>\<^sub>0\<^sub>0\<rangle> = 1"
      using bell00_is_state state_def by simp
    ultimately show "(\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) $$ (i, j) = v $$ (i,j)"
      using state_def assms asm by (auto simp add: bell00_def)
  qed
qed

lemma alice_step_2:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "(CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = mat_of_cols_list 8 [[\<alpha>/sqrt(2),0,0,\<alpha>/sqrt(2),0,\<beta>/sqrt(2),\<beta>/sqrt(2),0]]"
proof
  have f0:"(\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>) = mat_of_cols_list 8 [[\<alpha>/sqrt(2),0,0,\<alpha>/sqrt(2),\<beta>/sqrt(2),0,0,\<beta>/sqrt(2)]]"
    using assms alice_step_1 by simp
  define v where asm:"v = mat_of_cols_list 8 [[\<alpha>/sqrt(2),0,0,\<alpha>/sqrt(2),0,\<beta>/sqrt(2),\<beta>/sqrt(2),0]]"
  then show "dim_row ((CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) = dim_row v"
    using assms(1) alice_step_2_state state.dim_row mat_of_cols_list_def by fastforce
  show "dim_col ((CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) = dim_col v"
    using assms(1) alice_step_2_state state.is_column asm mat_of_cols_list_def by fastforce
  show "\<And>i j. i<dim_row v \<Longrightarrow> j<dim_col v \<Longrightarrow> ((CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) $$ (i,j) = v $$ (i,j)"
  proof-
    fix i j assume "i < dim_row v" and "j < dim_col v"
    then have "i \<in> {0..<8::nat} \<and> j = 0"
      using asm by (auto simp add: mat_of_cols_list_def)
    then have "(M1 * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) $$ (i,j) = v $$ (i,j)"
      by (auto simp add: f0 asm mat_of_cols_list_def times_mat_def scalar_prod_def)
    then show "((CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)) $$ (i,j) = v $$ (i,j)"
      using tensor_prod_of_cnot_id_1 by simp
  qed
qed

lemma alice_result:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "alice \<phi> = mat_of_cols_list 8 [[\<alpha>/2, \<beta>/2, \<beta>/2, \<alpha>/2, \<alpha>/2, -\<beta>/2, -\<beta>/2, \<alpha>/2]]"
proof
  define v where a0:"v = mat_of_cols_list 8 [[\<alpha>/2, \<beta>/2, \<beta>/2, \<alpha>/2, \<alpha>/2, -\<beta>/2, -\<beta>/2, \<alpha>/2]]"
  define w where a1:"w = (CNOT \<Otimes> Id 1) * (\<phi> \<Otimes> |\<beta>\<^sub>0\<^sub>0\<rangle>)"
  then have f0:"w = mat_of_cols_list 8 [[\<alpha>/sqrt(2), 0, 0, \<alpha>/sqrt(2), 0, \<beta>/sqrt(2), \<beta>/sqrt(2), 0]]"
    using assms alice_step_2 by simp
  show "dim_row (alice \<phi>) = dim_row v"
    using assms(1) alice_state state_def a0 by (simp add: mat_of_cols_list_def)
  show "dim_col (alice \<phi>) = dim_col v"
    using assms(1) alice_state state_def a0 by (simp add: mat_of_cols_list_def)
  show "\<And>i j. i < dim_row v \<Longrightarrow> j < dim_col v \<Longrightarrow> alice \<phi> $$ (i,j) = v $$ (i,j)"
  proof-
    fix i j assume "i < dim_row v" and "j < dim_col v"
    then have "i \<in> {0..<8} \<and> j = 0"
      using a0 by (auto simp add: Tensor.mat_of_cols_list_def)
    then have "(M2 * w) $$ (i,j) = v $$ (i,j)"
      by (auto simp add: f0 a0 mat_of_cols_list_def times_mat_def scalar_prod_def)
    then show "alice \<phi> $$ (i,j) = v $$ (i,j)"
      by (simp add: tensor_prod_of_h_id_2 alice_def a1)
  qed
qed

text \<open>
An application of function @{term "alice"} to a state @{term "\<phi>"} of a 1-qubit system results in the following cases.
\<close>

definition alice_meas:: "complex Matrix.mat \<Rightarrow> _list" where
"alice_meas \<phi> = [
  ((prob0 3 (alice \<phi>) 0) * (prob0 3 (post_meas0 3 (alice \<phi>) 0) 1), post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1)
, ((prob0 3 (alice \<phi>) 0) * (prob1 3 (post_meas0 3 (alice \<phi>) 0) 1), post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1)
, ((prob1 3 (alice \<phi>) 0) * (prob0 3 (post_meas1 3 (alice \<phi>) 0) 1), post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1)
, ((prob1 3 (alice \<phi>) 0) * (prob1 3 (post_meas1 3 (alice \<phi>) 0) 1), post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1)
]"

definition alice_pos:: "complex Matrix.mat \<Rightarrow> complex Matrix.mat \<Rightarrow> bool" where
"alice_pos \<phi> q \<equiv>  q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] \<or>
                  q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]]"

lemma phi_vec_length:
  assumes "state 1 \<phi>"
  shows "cmod(\<phi> $$ (0,0))^2 + cmod(\<phi> $$ (Suc 0,0))^2 = 1"
  using set_2 assms state_def Matrix.col_def cpx_vec_length_def by(auto simp add: atLeast0LessThan)

lemma select_index_3_subsets [simp]: 
  shows "{j::nat. select_index 3 0 j} = {4,5,6,7} \<and>
         {j::nat. j < 8 \<and> \<not> select_index 3 0 j} = {0,1,2,3} \<and>
         {j::nat. select_index 3 1 j} = {2,3,6,7} \<and>
         {j::nat. j < 8 \<and> \<not> select_index 3 1 j} = {0,1,4,5}"
proof-
  have "{j::nat. select_index 3 0 j} = {4,5,6,7}" by (auto simp add: select_index_def)
  moreover have "{j::nat. j < 8 \<and> \<not> select_index 3 0 j} = {0,1,2,3}" by(auto simp add: select_index_def)
  moreover have f1:"{j::nat. select_index 3 1 j} = {2,3,6,7}"
  proof
    show "{j. select_index 3 1 j} \<subseteq> {2,3,6,7}"
    proof
      fix j::nat assume "j \<in> {j. select_index 3 1 j}"
      then have "j \<in> {0..<8} \<and> j mod 4 \<in> {2,3}" by (auto simp add: select_index_def)
      then show "j \<in> {2,3,6,7}" by auto
    qed
    show "{2,3,6,7} \<subseteq> {j. select_index 3 1 j}" by (auto simp add: select_index_def)
  qed
  moreover have "{j::nat. j < 8 \<and> \<not> select_index 3 1 j} = {0,1,4,5}"
  proof-
    have "{j::nat. j < 8 \<and> j \<notin> {2,3,6,7}} = {0,1,4,5}"  by auto
    then show ?thesis using f1 by blast
  qed
  ultimately show ?thesis by simp
qed

lemma prob_index_0_alice:
  assumes "state 1 \<phi>"
  shows "prob0 3 (alice \<phi>) 0 = 1/2 \<and> prob1 3 (alice \<phi>) 0 = 1/2"
proof
  show "prob0 3 (alice \<phi>) 0 = 1/2"
    using alice_result assms prob0_def alice_state
    apply auto by (metis (no_types, hide_lams) One_nat_def phi_vec_length four_x_squared mult.commute 
nonzero_mult_div_cancel_right times_divide_eq_right zero_neq_numeral)
  then show"prob1 3 (alice \<phi>) 0 = 1/2"
    using prob_sum_is_one[of "3" "alice \<phi>" "0"] alice_state[of "\<phi>"] assms by linarith
qed

lemma post_meas0_index_0_alice:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "post_meas0 3 (alice \<phi>) 0 = 
mat_of_cols_list 8 [[\<alpha>/sqrt(2), \<beta>/sqrt(2), \<beta>/sqrt(2), \<alpha>/sqrt(2), 0, 0, 0, 0]]"
proof
  define v where asm:"v = mat_of_cols_list 8 [[\<alpha>/sqrt(2),\<beta>/sqrt(2),\<beta>/sqrt(2),\<alpha>/sqrt(2),0,0,0,0]]"
  then show "dim_row (post_meas0 3 (alice \<phi>) 0) = dim_row v"
    using mat_of_cols_list_def post_meas0_def assms(1) alice_state ket_vec_def by simp
  show "dim_col (post_meas0 3 (alice \<phi>) 0) = dim_col v"
    using mat_of_cols_list_def post_meas0_def assms(1) alice_state ket_vec_def asm by simp
  show "\<And>i j. i<dim_row v \<Longrightarrow> j<dim_col v \<Longrightarrow> post_meas0 3 (alice \<phi>) 0 $$ (i,j) = v $$ (i,j)"
  proof-
    fix i j assume "i < dim_row v" and "j < dim_col v"
    then have "i \<in> {0..<8} \<and> j = 0"
      using asm set_8_atLeast0 mat_of_cols_list_def by auto
    then show "post_meas0 3 (alice \<phi>) 0 $$ (i, j) = v $$ (i, j)"
      using post_meas0_def assms asm mat_of_cols_list_def ket_vec_def
      apply (auto simp add: prob_index_0_alice)
      using assms(1) alice_result select_index_def by auto
  qed
qed

lemma post_meas1_index_0_alice:
  assumes "state 1 \<phi>" and "\<alpha> = \<phi> $$ (0,0)" and "\<beta> = \<phi> $$ (1,0)"
  shows "post_meas1 3 (alice \<phi>) 0 = mat_of_cols_list 8 [[0,0,0,0,\<alpha>/sqrt(2),-\<beta>/sqrt(2),-\<beta>/sqrt(2),\<alpha>/sqrt(2)]]"
proof
  define v where asm:"v = mat_of_cols_list 8 [[0,0,0,0,\<alpha>/sqrt(2),-\<beta>/sqrt(2),-\<beta>/sqrt(2),\<alpha>/sqrt(2)]]"
  then show "dim_row (post_meas1 3 (alice \<phi>) 0) = dim_row v"
    using mat_of_cols_list_def post_meas1_def assms(1) alice_state ket_vec_def by simp
  show "dim_col (post_meas1 3 (alice \<phi>) 0) = dim_col v"
    using mat_of_cols_list_def post_meas1_def assms(1) alice_state ket_vec_def asm by simp
  show "\<And>i j. i<dim_row v \<Longrightarrow> j<dim_col v \<Longrightarrow> post_meas1 3 (alice \<phi>) 0 $$ (i,j) = v $$ (i,j)"
  proof-
    fix i j assume "i < dim_row v" and "j < dim_col v"
    then have "i \<in> {0..<8} \<and> j = 0"
      using asm set_8_atLeast0 mat_of_cols_list_def by auto
    then show "post_meas1 3 (alice \<phi>) 0 $$ (i,j) = v $$ (i,j)"
      using post_meas1_def assms asm mat_of_cols_list_def ket_vec_def
      apply (auto simp add: prob_index_0_alice)
      using assms(1) alice_result select_index_def by auto
  qed
qed

lemma post_meas0_index_0_alice_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 (post_meas0 3 (alice \<phi>) 0)"
  using assms by (simp add: prob_index_0_alice)

lemma post_meas1_index_0_alice_state [simp]:
  assumes "state 1 \<phi>"
  shows "state 3 (post_meas1 3 (alice \<phi>) 0)"
  using assms by (simp add: prob_index_0_alice)

lemma Alice_case [simp]:
  assumes "state 1 \<phi>" and "state 3 q" and "List.member (alice_meas \<phi>) (p, q)"
  shows "alice_pos \<phi> q"
proof-
  define \<alpha> \<beta> where a0:"\<alpha> = \<phi> $$ (0,0)" and a1:"\<beta> = \<phi> $$ (1,0)"
  have f0:"prob0 3 (Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[\<phi> $$ (0,0)/sqrt 2, \<phi> $$ (Suc 0,0)/sqrt 2, 
                    \<phi> $$ (Suc 0,0)/sqrt 2, \<phi> $$ (0,0)/sqrt 2,0,0,0,0]]!j!i)) (Suc 0) = 1/2"
    using post_meas0_index_0_alice prob0_def mat_of_cols_list_def post_meas0_index_0_alice_state 
assms(1) a0 a1 select_index_3_subsets by (auto simp add: norm_divide power_divide phi_vec_length)
  have f1:"prob1 3 (Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[\<phi> $$ (0,0)/sqrt 2, \<phi> $$ (Suc 0,0)/sqrt 2, 
                    \<phi> $$ (Suc 0,0)/sqrt 2, \<phi> $$ (0,0)/sqrt 2, 0, 0, 0, 0]] ! j ! i)) (Suc 0) = 1/2"
    using post_meas0_index_0_alice prob1_def mat_of_cols_list_def post_meas0_index_0_alice_state 
assms(1) a0 a1 select_index_3_subsets by(auto simp add: norm_divide power_divide phi_vec_length algebra_simps)
  have f2:"prob0 3 (Matrix.mat 8 (Suc 0) 
          (\<lambda>(i,j). [[0,0,0,0,\<phi> $$ (0,0)/complex_of_real (sqrt 2),-(\<phi> $$ (Suc 0,0)/complex_of_real (sqrt 2)), 
-(\<phi> $$ (Suc 0,0)/complex_of_real (sqrt 2)),\<phi> $$ (0,0)/complex_of_real (sqrt 2)]] ! j ! i)) (Suc 0) = 1/2"
    using post_meas1_index_0_alice prob0_def mat_of_cols_list_def post_meas1_index_0_alice_state 
      assms(1) a0 a1 select_index_3_subsets by(auto simp add: norm_divide power_divide phi_vec_length)
  have f3:"prob1 3 (Matrix.mat 8 (Suc 0) 
          (\<lambda>(i,j). [[0,0,0,0,\<phi> $$ (0,0)/complex_of_real (sqrt 2),-(\<phi> $$ (Suc 0,0)/complex_of_real (sqrt 2)), 
-(\<phi> $$ (Suc 0,0)/complex_of_real (sqrt 2)), \<phi> $$ (0,0)/complex_of_real (sqrt 2)]] ! j ! i)) (Suc 0) = 1/2"
    using post_meas1_index_0_alice prob1_def mat_of_cols_list_def post_meas1_index_0_alice_state 
assms(1) a0 a1 select_index_3_subsets by(auto simp add: norm_divide power_divide phi_vec_length algebra_simps)
  have "(p, q) = ((prob0 3 (alice \<phi>) 0) * (prob0 3 (post_meas0 3 (alice \<phi>) 0) 1), post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1) \<or>
        (p, q) = ((prob0 3 (alice \<phi>) 0) * (prob1 3 (post_meas0 3 (alice \<phi>) 0) 1), post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1) \<or>
        (p, q) = ((prob1 3 (alice \<phi>) 0) * (prob0 3 (post_meas1 3 (alice \<phi>) 0) 1), post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1) \<or>
        (p, q) = ((prob1 3 (alice \<phi>) 0) * (prob1 3 (post_meas1 3 (alice \<phi>) 0) 1), post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1)"
    using assms(3) alice_meas_def List.member_def by(smt list.distinct(1) list.exhaust list.inject member_rec(1) member_rec(2))
  then have "q = post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1 \<or> q = post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1 \<or>
             q = post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1 \<or> q = post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1"
    by auto
  moreover have "post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1 = mat_of_cols_list 8 [[\<alpha>,\<beta>,0,0,0,0,0,0]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]]"
    then show "dim_row (post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas0_def ket_vec_def by simp
    show "dim_col (post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas0_def ket_vec_def asm by simp
    show "\<And>i j. i<dim_row v \<Longrightarrow> j<dim_col v \<Longrightarrow> post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def by auto
      then show "post_meas0 3 (post_meas0 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
        using post_meas0_index_0_alice assms(1) a0 a1
        apply (auto)
        using post_meas0_def asm mat_of_cols_list_def ket_vec_def select_index_def
        by (auto simp add: f0 real_sqrt_divide)
    qed
  qed
  moreover have "post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1 = mat_of_cols_list 8 [[0,0,\<beta>,\<alpha>,0,0,0,0]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[0,0,\<beta>,\<alpha>,0,0,0,0]]"
    then show "dim_row (post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas1_def ket_vec_def asm by auto
    show "dim_col (post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas1_def ket_vec_def asm by auto
    show "\<And>i j. i<dim_row v \<Longrightarrow> j<dim_col v \<Longrightarrow> post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def by auto
      then show "post_meas1 3 (post_meas0 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
        using post_meas0_index_0_alice assms(1) a0 a1
        apply (auto)
        using post_meas1_def asm mat_of_cols_list_def ket_vec_def select_index_def
        by (auto simp add: f1 real_sqrt_divide)
    qed
  qed
  moreover have "post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1 = mat_of_cols_list 8 [[0,0,0,0,\<alpha>,-\<beta>,0,0]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>, -\<beta>, 0, 0]]"
    then show "dim_row (post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas0_def ket_vec_def by simp
    show "dim_col (post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas0_def ket_vec_def asm by simp
    show "\<And>i j. i<dim_row v \<Longrightarrow> j<dim_col v \<Longrightarrow> post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def by auto
      then show "post_meas0 3 (post_meas1 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
        using post_meas1_index_0_alice assms(1) a0 a1
        apply (auto)
        using post_meas0_def asm mat_of_cols_list_def ket_vec_def select_index_def
        by (auto simp add: f2 real_sqrt_divide)
    qed
  qed
  moreover have "post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1 = mat_of_cols_list 8 [[0,0,0,0,0,0,-\<beta>,\<alpha>]]"
  proof
    define v where asm:"v = mat_of_cols_list 8 [[0,0,0,0,0,0,-\<beta>,\<alpha>]]"
    then show "dim_row (post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1) = dim_row v"
      using mat_of_cols_list_def post_meas1_def ket_vec_def by simp
    show "dim_col (post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1) = dim_col v"
      using mat_of_cols_list_def post_meas1_def ket_vec_def asm by simp
    show "\<And>i j. i<dim_row v \<Longrightarrow> j<dim_col v \<Longrightarrow> post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
    proof-
      fix i j assume "i < dim_row v" and "j < dim_col v"
      then have "i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def by auto
      then show "post_meas1 3 (post_meas1 3 (alice \<phi>) 0) 1 $$ (i,j) = v $$ (i,j)"
        using post_meas1_index_0_alice assms(1) a0 a1
        apply (auto)
        using post_meas1_def asm mat_of_cols_list_def ket_vec_def select_index_def
        by (auto simp add: f3 real_sqrt_divide)
    qed
  qed
  ultimately show ?thesis using alice_pos_def a0 a1 by simp
qed


datatype bit = zero | one

definition alice_out:: "complex Matrix.mat => complex Matrix.mat => bit \<times> bit" where
"alice_out \<phi> q \<equiv> 
if q = mat_of_cols_list 8 [[\<phi> $$ (0,0), \<phi> $$ (1,0), 0, 0, 0, 0, 0, 0]] then (zero, zero) else
  if q = mat_of_cols_list 8 [[0, 0, \<phi> $$ (1,0), \<phi> $$ (0,0), 0, 0, 0, 0]] then (zero, one) else
    if q = mat_of_cols_list 8 [[0, 0, 0, 0, \<phi> $$ (0,0), - \<phi> $$ (1,0), 0, 0]] then (one, zero) else
      if q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, - \<phi> $$ (1,0), \<phi> $$ (0,0)]] then (one, one) else 
        undefined"

definition bob:: "complex Matrix.mat => bit \<times> bit \<Rightarrow> complex Matrix.mat" where
"bob q b \<equiv> 
if (fst b, snd b) = (zero, zero) then q else 
  if (fst b, snd b) = (zero, one) then (Id 2 \<Otimes> X) * q else
    if (fst b, snd b) = (one, zero) then (Id 2 \<Otimes> Z) * q else
      if (fst b, snd b) = (one, one) then (Id 2 \<Otimes> Z * X) * q else 
        undefined"

lemma alice_out_unique [simp]:
  assumes "state 1 \<phi>"
  shows "Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, \<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]]!j!i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[\<phi> $$ (0, 0), \<phi> $$ (Suc 0, 0), 0, 0, 0, 0, 0, 0]]!j!i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (Suc 0, 0), 0, 0]]!j!i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[\<phi> $$ (0, 0), \<phi> $$ (Suc 0, 0), 0, 0, 0, 0, 0, 0]]!j!i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0)]]!j!i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[\<phi> $$ (0, 0), \<phi> $$ (Suc 0, 0), 0, 0, 0, 0, 0, 0]]!j!i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (Suc 0, 0), 0, 0]]!j!i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, \<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]]!j!i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0)]]!j!i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, \<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0), 0, 0, 0, 0]]!j!i) \<and> 
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, 0, 0, 0, 0, -\<phi> $$ (Suc 0, 0), \<phi> $$ (0, 0)]]!j!i) \<noteq>
         Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0, 0, 0, 0, \<phi> $$ (0, 0), -\<phi> $$ (Suc 0, 0), 0, 0]]!j!i)"
proof-
  have f0:"\<phi> $$ (0,0) \<noteq> 0 \<or> \<phi> $$ (1,0) \<noteq> 0"
    using assms state_def Matrix.col_def cpx_vec_length_def set_2 by(auto simp add: atLeast0LessThan)
  define v1 v2 v3 v4 where d0:"v1 = Matrix.mat 8 1 (\<lambda>(i,j). [[\<phi> $$ (0,0),\<phi> $$ (1,0),0,0,0,0,0,0]]!j!i)"
                       and d1:"v2 = Matrix.mat 8 1 (\<lambda>(i,j). [[0,0,\<phi> $$ (1,0), \<phi> $$ (0,0),0,0,0,0]]!j!i)"
                       and d2:"v3 = Matrix.mat 8 1 (\<lambda>(i,j). [[0,0,0,0,\<phi> $$ (0,0),-\<phi> $$ (1,0),0,0]]!j!i)"
                       and d3:"v4 = Matrix.mat 8 1 (\<lambda>(i,j). [[0,0,0,0,0,0,-\<phi> $$ (1,0),\<phi> $$ (0,0)]]!j!i)"
  then have "(v1 $$ (0,0) \<noteq> v2 $$ (0,0) \<or> v1 $$ (1,0) \<noteq> v2 $$ (1,0)) \<and> 
             (v1 $$ (0,0) \<noteq> v3 $$ (0,0) \<or> v1 $$ (1,0) \<noteq> v3 $$ (1,0)) \<and>  
             (v1 $$ (0,0) \<noteq> v4 $$ (0,0) \<or> v1 $$ (1,0) \<noteq> v4 $$ (1,0)) \<and>  
             (v2 $$ (2,0) \<noteq> v3 $$ (2,0) \<or> v2 $$ (3,0) \<noteq> v3 $$ (3,0)) \<and>  
             (v2 $$ (2,0) \<noteq> v4 $$ (2,0) \<or> v2 $$ (3,0) \<noteq> v4 $$ (3,0)) \<and>  
             (v3 $$ (4,0) \<noteq> v4 $$ (4,0) \<or> v3 $$ (5,0) \<noteq> v4 $$ (5,0))" using f0 by auto
  then have "v1 \<noteq> v2 \<and> v1 \<noteq> v3 \<and> v1 \<noteq> v4 \<and> v2 \<noteq> v3 \<and> v2 \<noteq> v4 \<and> v3 \<noteq> v4" by auto
  thus ?thesis by (auto simp add: d0 d1 d2 d3)
qed

abbreviation M3:: "complex Matrix.mat" where 
"M3 \<equiv> mat_of_cols_list 8 [[0, 1, 0, 0, 0, 0, 0, 0],
                          [1, 0, 0, 0, 0, 0, 0, 0],
                          [0, 0, 0, 1, 0, 0, 0, 0],
                          [0, 0, 1, 0, 0, 0, 0, 0],
                          [0, 0, 0, 0, 0, 1, 0, 0],
                          [0, 0, 0, 0, 1, 0, 0, 0],
                          [0, 0, 0, 0, 0, 0, 0, 1],
                          [0, 0, 0, 0, 0, 0, 1, 0]]"

lemma tensor_prod_of_id_2_x:
  shows "(Id 2 \<Otimes> X) = M3"
proof
    have f0:"gate 3 (Id 2 \<Otimes> X)"
      using X_is_gate tensor_gate[of "2" "Id 2" "1" "X"] by simp
    then show "dim_row (Id 2 \<Otimes> X) = dim_row M3"
      using gate_def by (simp add: mat_of_cols_list_def)
    show "dim_col (Id 2 \<Otimes> X) = dim_col M3"
      using f0 gate_def by (simp add: mat_of_cols_list_def)
    show "\<And>i j. i < dim_row M3 \<Longrightarrow> j < dim_col M3 \<Longrightarrow> (Id 2 \<Otimes> X) $$ (i,j) = M3 $$ (i,j)"
    proof-
      fix i j assume "i < dim_row M3" and "j < dim_col M3"
      then have "i \<in> {0..<8} \<and> j \<in> {0..<8}" by (auto simp add: mat_of_cols_list_def)
      then show "(Id 2 \<Otimes> X) $$ (i,j) = M3 $$ (i,j)"
        using Id_def X_def index_tensor_mat[of "Id 2" "4" "4" "X" "2" "2" "i" "j"] gate_def X_is_gate 
id_is_gate Id_def by (auto simp add: mat_of_cols_list_def X_def)
    qed
qed

abbreviation M4:: "complex Matrix.mat" where 
"M4 \<equiv> mat_of_cols_list 8 [[0, -1, 0, 0, 0, 0, 0, 0],
                          [1, 0, 0, 0, 0, 0, 0, 0],
                          [0, 0, 0, -1, 0, 0, 0, 0],
                          [0, 0, 1, 0, 0, 0, 0, 0],
                          [0, 0, 0, 0, 0, -1, 0, 0],
                          [0, 0, 0, 0, 1, 0, 0, 0],
                          [0, 0, 0, 0, 0, 0, 0, -1],
                          [0, 0, 0, 0, 0, 0, 1, 0]]"

abbreviation ZX:: "complex Matrix.mat" where
"ZX \<equiv> mat_of_cols_list 2 [[0, -1], [1, 0]]"

lemma l_inv_of_ZX:
  shows "ZX\<^sup>\<dagger> * ZX = 1\<^sub>m 2"
proof
  show "dim_row (ZX\<^sup>\<dagger> * ZX) = dim_row (1\<^sub>m 2)" using dagger_def mat_of_cols_list_def by simp
  show "dim_col (ZX\<^sup>\<dagger> * ZX) = dim_col (1\<^sub>m 2)" using dagger_def mat_of_cols_list_def by simp
  show "\<And>i j. i < dim_row (1\<^sub>m 2) \<Longrightarrow> j < dim_col (1\<^sub>m 2) \<Longrightarrow> (ZX\<^sup>\<dagger> * ZX) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
  proof-
    fix i j assume "i < dim_row (1\<^sub>m 2)" and "j < dim_col (1\<^sub>m 2)"
    then have "i \<in> {0..<2} \<and> j \<in> {0..<2}" by auto
    then show "(ZX\<^sup>\<dagger> * ZX) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
      using mat_of_cols_list_def dagger_def by (auto simp add: set_2)
  qed
qed

lemma r_inv_of_ZX:
  shows "ZX * (ZX\<^sup>\<dagger>) = 1\<^sub>m 2"
proof
  show "dim_row (ZX * (ZX\<^sup>\<dagger>)) = dim_row (1\<^sub>m 2)" using dagger_def mat_of_cols_list_def by simp
  show "dim_col (ZX * (ZX\<^sup>\<dagger>)) = dim_col (1\<^sub>m 2)" using dagger_def mat_of_cols_list_def by simp
  show "\<And>i j. i < dim_row (1\<^sub>m 2) \<Longrightarrow> j < dim_col (1\<^sub>m 2) \<Longrightarrow> (ZX * (ZX\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
  proof-
    fix i j assume "i < dim_row (1\<^sub>m 2)" and "j < dim_col (1\<^sub>m 2)"
    then have "i \<in> {0..<2} \<and> j \<in> {0..<2}" by auto
    then show "(ZX * (ZX\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m 2 $$ (i, j)"
      using mat_of_cols_list_def dagger_def by (auto simp add: set_2)
  qed
qed

lemma ZX_is_gate [simp]:
  shows "gate 1 ZX"
proof
  show "dim_row ZX = 2 ^ 1" using mat_of_cols_list_def by simp
  show "square_mat ZX" using mat_of_cols_list_def by simp
  show "unitary ZX" using unitary_def l_inv_of_ZX r_inv_of_ZX mat_of_cols_list_def by auto
qed

lemma prod_of_ZX:
  shows "Z * X = ZX"
proof
  show "dim_row (Z * X) = dim_row ZX"
    using Z_is_gate mat_of_cols_list_def gate_def by auto
  show "dim_col (Z * X) = dim_col ZX"
    using X_is_gate mat_of_cols_list_def gate_def by auto
  show "\<And>i j. i < dim_row ZX \<Longrightarrow> j < dim_col ZX \<Longrightarrow> (Z * X) $$ (i, j) = ZX $$ (i, j)"
  proof-
    fix i j assume "i < dim_row ZX" and "j < dim_col ZX"
    then have "i \<in> {0..<2} \<and> j \<in> {0..<2}" by (auto simp add: mat_of_cols_list_def)
    then show "(Z * X) $$ (i, j) = ZX $$ (i, j)" by (auto simp add: set_2 Z_def X_def)
  qed
qed

lemma tensor_prod_of_id_2_y:
  shows "(Id 2 \<Otimes> Z * X) = M4"
proof
  have f0:"gate 3 (Id 2 \<Otimes> Z * X)"
    using prod_of_ZX ZX_is_gate tensor_gate[of "2" "Id 2" "1" "Z * X"] by simp
  then show "dim_row (Id 2 \<Otimes> Z * X) = dim_row M4"
      using gate_def by (simp add: mat_of_cols_list_def)
  show "dim_col (Id 2 \<Otimes> Z * X) = dim_col M4"
    using f0 gate_def by (simp add: mat_of_cols_list_def)
  show "\<And>i j. i < dim_row M4 \<Longrightarrow> j < dim_col M4 \<Longrightarrow> (Id 2 \<Otimes> Z * X) $$ (i,j) = M4 $$ (i,j)"
  proof-
    fix i j assume "i < dim_row M4" and "j < dim_col M4"
    then have "i \<in> {0..<8} \<and> j \<in> {0..<8}" by (auto simp add: mat_of_cols_list_def)
    then have "(Id 2 \<Otimes> ZX) $$ (i, j) = M4 $$ (i,j)"
      using Id_def mat_of_cols_list_def index_tensor_mat[of "Id 2" "4" "4" "ZX" "2" "2" "i" "j"] 
        gate_def ZX_is_gate id_is_gate
      by (auto simp add: mat_of_cols_list_def)
    then show "(Id 2 \<Otimes> Z * X) $$ (i, j) = M4 $$ (i,j)"
      using prod_of_ZX by simp
    qed
qed

abbreviation M5:: "complex Matrix.mat" where 
"M5 \<equiv> mat_of_cols_list 8 [[1, 0, 0, 0, 0, 0, 0, 0],
                          [0, -1, 0, 0, 0, 0, 0, 0],
                          [0, 0, 1, 0, 0, 0, 0, 0],
                          [0, 0, 0, -1, 0, 0, 0, 0],
                          [0, 0, 0, 0, 1, 0, 0, 0],
                          [0, 0, 0, 0, 0, -1, 0, 0],
                          [0, 0, 0, 0, 0, 0, 1, 0],
                          [0, 0, 0, 0, 0, 0, 0, -1]]"

lemma tensor_prod_of_id_2_z:
  shows "(Id 2 \<Otimes> Z) = M5"
proof
    have f0:"gate 3 (Id 2 \<Otimes> Z)"
      using Z_is_gate tensor_gate[of "2" "Id 2" "1" "Z"] by simp
    then show "dim_row (Id 2 \<Otimes> Z) = dim_row M5"
      using gate_def by (simp add:  mat_of_cols_list_def)
    show "dim_col (Id 2 \<Otimes> Z) = dim_col M5"
      using f0 gate_def by (simp add:  mat_of_cols_list_def)
    show "\<And>i j. i < dim_row M5 \<Longrightarrow> j < dim_col M5 \<Longrightarrow> (Id 2 \<Otimes> Z) $$ (i,j) = M5 $$ (i,j)"
    proof-
      fix i j assume "i < dim_row M5" and "j < dim_col M5"
      then have "i \<in> {0..<8} \<and> j \<in> {0..<8}" by (auto simp add: mat_of_cols_list_def)
      then show "(Id 2 \<Otimes> Z) $$ (i, j) = M5 $$ (i,j)"
        using Id_def Z_def index_tensor_mat[of "Id 2" "4" "4" "Z" "2" "2" "i" "j"] gate_def Z_is_gate 
id_is_gate Id_def by (auto simp add: mat_of_cols_list_def Z_def)
    qed
qed

lemma teleportation:
  assumes "state 1 \<phi>" and "state 3 q" and "List.member (alice_meas \<phi>) (p, q)"
  shows "\<exists>r. state 2 r \<and> bob q (alice_out \<phi> q) = r \<Otimes> \<phi>"
proof-
  define \<alpha> \<beta> where a0:"\<alpha> = \<phi> $$ (0,0)" and a1:"\<beta> = \<phi> $$ (1,0)"
  then have "q = mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]] \<or>
             q = mat_of_cols_list 8 [[0, 0, \<beta>, \<alpha>, 0, 0, 0, 0]] \<or>
             q = mat_of_cols_list 8 [[0, 0, 0, 0, \<alpha>, -\<beta>, 0, 0]] \<or>
             q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]]"
    using assms Alice_case alice_pos_def by simp
  moreover have "q = mat_of_cols_list 8 [[\<alpha>,\<beta>,0,0,0,0,0,0]] \<Longrightarrow> bob q (alice_out \<phi> q) = 
mat_of_cols_list 4 [[1, 0, 0, 0]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[\<alpha>, \<beta>, 0, 0, 0, 0, 0, 0]]"
    show "dim_row (bob q (alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm by simp
    show "dim_col (bob q (alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm by simp
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>) \<Longrightarrow>
           bob q (alice_out \<phi> q) $$ (i, j) = (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>) $$ (i,j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>)"
      then have "i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def assms state_def by auto
      then show "bob q (alice_out \<phi> q) $$ (i,j) = (Tensor.mat_of_cols_list 4 [[1,0,0,0]] \<Otimes> \<phi>) $$ (i,j)"
        using bob_def alice_out_def asm mat_of_cols_list_def a0 a1 assms state_def by auto
    qed
  qed
  moreover have "q = mat_of_cols_list 8 [[0,0,\<beta>,\<alpha>,0,0,0,0]] \<Longrightarrow> bob q (alice_out \<phi> q) = 
mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[0,0,\<beta>,\<alpha>,0,0,0,0]]"
    show "dim_row (bob q (alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm tensor_prod_of_id_2_x by simp
    show "dim_col (bob q (alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm by simp    
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>) \<Longrightarrow>
           bob q (alice_out \<phi> q) $$ (i,j) = (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>) $$ (i,j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>)"
      then have c1:"i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def assms(1) state_def by auto
      then have "(M3 * (Matrix.mat 8 1 (\<lambda>(i,j). [[0,0,\<phi> $$ (1,0),\<phi> $$ (0,0),0,0,0,0]]!j!i))) $$ (i,j) = 
(Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>) $$ (i,j)"
        using state_def assms(1) by(auto simp add:  a0 a1 mat_of_cols_list_def times_mat_def scalar_prod_def)
      then show "bob q (alice_out \<phi> q) $$ (i,j) = (Tensor.mat_of_cols_list 4 [[0,1,0,0]] \<Otimes> \<phi>) $$ (i,j)"
        using bob_def alice_out_def asm c1 a0 a1 mat_of_cols_list_def tensor_prod_of_id_2_x assms(1) by simp
    qed
  qed
  moreover have "q = mat_of_cols_list 8 [[0,0,0,0,\<alpha>,-\<beta>,0,0]] \<Longrightarrow> bob q (alice_out \<phi> q) = 
mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[0,0,0,0,\<alpha>,-\<beta>,0,0]]"
    show "dim_row (bob q (alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm tensor_prod_of_id_2_z by simp
    show "dim_col (bob q (alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm by simp      
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>) \<Longrightarrow>
           bob q (alice_out \<phi> q) $$ (i,j) = (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>) $$ (i,j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>)"
      then have c1:"i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def assms state_def by auto
      then have "(M5 * (Matrix.mat 8 (Suc 0) (\<lambda>(i,j). [[0,0,0,0,\<phi> $$ (0,0),-\<phi> $$ (Suc 0,0),0,0]]!j!i))) $$ (i,j) = 
(Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>) $$ (i,j)"
        using state_def assms(1) by(auto simp add: a0 a1 mat_of_cols_list_def times_mat_def scalar_prod_def)
      then show "bob q (alice_out \<phi> q) $$ (i,j) = (Tensor.mat_of_cols_list 4 [[0,0,1,0]] \<Otimes> \<phi>) $$ (i,j)"
        using bob_def alice_out_def asm c1 a0 a1 mat_of_cols_list_def tensor_prod_of_id_2_z assms(1) by simp
    qed
  qed
  moreover have "q = mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]] \<Longrightarrow> bob q (alice_out \<phi> q) = 
mat_of_cols_list 4 [[0, 0, 0, 1]] \<Otimes> \<phi>"
  proof
    assume asm:"q = Tensor.mat_of_cols_list 8 [[0, 0, 0, 0, 0, 0, -\<beta>, \<alpha>]]"
    show "dim_row (bob q (alice_out \<phi> q)) = dim_row (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm tensor_prod_of_id_2_y by simp
    show "dim_col (bob q (alice_out \<phi> q)) = dim_col (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>)"
      using mat_of_cols_list_def a0 a1 assms(1) state_def bob_def alice_out_def asm by simp  
    show "\<And>i j. i < dim_row (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>) \<Longrightarrow> 
                j < dim_col (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>) \<Longrightarrow>
           bob q (alice_out \<phi> q) $$ (i,j) = (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>) $$ (i,j)"
    proof-
      fix i j assume "i < dim_row (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>)" and
                     "j < dim_col (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>)"
      then have c1:"i \<in> {0..<8} \<and> j = 0"
        using asm mat_of_cols_list_def assms state_def by auto
      then have "(M4 * (Matrix.mat 8 (Suc 0) (\<lambda>(i, j). [[0,0,0,0,0,0,-\<phi> $$ (Suc 0,0),\<phi> $$ (0,0)]]!j!i))) $$ (i,j) = 
(Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>) $$ (i,j)"
        using state_def assms(1) by(auto simp add: a0 a1 mat_of_cols_list_def times_mat_def scalar_prod_def)
      then show "bob q (alice_out \<phi> q) $$ (i,j) = (Tensor.mat_of_cols_list 4 [[0,0,0,1]] \<Otimes> \<phi>) $$ (i,j)"
        using bob_def alice_out_def asm c1 a0 a1 mat_of_cols_list_def tensor_prod_of_id_2_y assms(1) by simp
    qed
  qed
  moreover have "state 2 (mat_of_cols_list 4 [[1, 0, 0, 0]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0 by simp
  moreover have "state 2 (mat_of_cols_list 4 [[0, 1, 0, 0]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0 by simp
  moreover have "state 2 (mat_of_cols_list 4 [[0, 0, 1, 0]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0 by simp
  moreover have "state 2 (mat_of_cols_list 4 [[0, 0, 0, 1]])"
    using state_def mat_of_cols_list_def cpx_vec_length_def lessThan_atLeast0 by simp
  ultimately show ?thesis by auto
qed

(* 
Biblio:

@inproceedings{Boender2015FormalizationOQ,
  title={Formalization of Quantum Protocols using Coq},
  author={Jaap Boender and Florian Kamm{\"u}ller and Rajagopal Nagarajan},
  booktitle={QPL},
  year={2015}
}
*)

end