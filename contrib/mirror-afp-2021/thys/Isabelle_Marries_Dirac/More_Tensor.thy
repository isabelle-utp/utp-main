(* 
Authors: 

  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk;
  Yijun He, University of Cambridge, yh403@cam.ac.uk 
*)

section \<open>Further Results on Tensor Products\<close>

theory More_Tensor
imports
  Quantum
  Tensor
  Jordan_Normal_Form.Matrix
  Basics
begin


lemma tensor_prod_2 [simp]: 
"mult.vec_vec_Tensor (*) [x1::complex,x2] [x3, x4] = [x1 * x3, x1 * x4, x2 * x3, x2 * x4]"
proof -
  have "Matrix_Tensor.mult (1::complex) (*)"
    by (simp add: Matrix_Tensor.mult_def)
  thus "mult.vec_vec_Tensor (*) [x1::complex,x2] [x3,x4] = [x1*x3,x1*x4,x2*x3,x2*x4]"
    using mult.vec_vec_Tensor_def[of "(1::complex)" "(*)"] mult.times_def[of "(1::complex)" "(*)"] by simp
qed

lemma list_vec [simp]: 
  assumes "v \<in> state_qbit 1"
  shows "list_of_vec v = [v $ 0, v $ 1]"
proof -
  have "Rep_vec v = (fst(Rep_vec v), snd(Rep_vec v))" by simp
  also have "\<dots> = (2, vec_index v)"
    by (metis (mono_tags, lifting) assms dim_vec.rep_eq mem_Collect_eq power_one_right state_qbit_def vec_index.rep_eq)
  moreover have "[0..<2::nat] = [0,1]"
    by(simp add: upt_rec) 
  ultimately show ?thesis
    by(simp add: list_of_vec_def)
qed

lemma vec_tensor_prod_2 [simp]:
  assumes "v \<in> state_qbit 1" and "w \<in> state_qbit 1"
  shows "v \<otimes> w = vec_of_list [v $ 0 * w $ 0, v $ 0 * w $ 1, v $ 1 * w $ 0, v $ 1 * w $ 1]"
proof -
  have "list_of_vec v = [v $ 0, v $ 1]"
    using assms by simp
  moreover have "list_of_vec w = [w $ 0, w $ 1]"
    using assms by simp
  ultimately show "v \<otimes> w = vec_of_list [v $ 0 * w $ 0, v $ 0 * w $ 1, v $ 1 * w $ 0, v $ 1 * w $ 1]"
    by(simp add: tensor_vec_def)
qed

lemma vec_dim_of_vec_of_list [simp]:
  assumes "length l = n"
  shows "dim_vec (vec_of_list l) = n"
  using assms vec_of_list_def by simp

lemma vec_tensor_prod_2_bis [simp]:
  assumes "v \<in> state_qbit 1" and "w \<in> state_qbit 1"
  shows "v \<otimes> w = Matrix.vec 4 (\<lambda>i. if i = 0 then v $ 0 * w $ 0 else 
                                      if i = 3 then v $ 1 * w $ 1 else
                                          if i = 1 then v $ 0 * w $ 1 else v $ 1 * w $ 0)"
proof
  define u where "u = Matrix.vec 4 (\<lambda>i. if i = 0 then v $ 0 * w $ 0 else 
                                          if i = 3 then v $ 1 * w $ 1 else
                                            if i = 1 then v $ 0 * w $ 1 else v $ 1 * w $ 0)"
  then show f2:"dim_vec (v \<otimes> w) = dim_vec u"
    using assms by simp
  show "\<And>i. i < dim_vec u \<Longrightarrow> (v \<otimes> w) $ i = u $ i"
    apply (auto simp: u_def)
    using assms apply auto[3]
    apply (simp add: numeral_3_eq_3)
    using u_def vec_of_list_index vec_tensor_prod_2 index_is_2 
    by (metis (no_types, lifting) One_nat_def assms nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
qed

lemma index_col_mat_of_cols_list [simp]:
  assumes "i < n" and "j < length l"
  shows "Matrix.col (mat_of_cols_list n l) j $ i = l ! j ! i"
  apply (auto simp: Matrix.col_def mat_of_cols_list_def)
  using assms less_le_trans by fastforce

lemma multTensor2 [simp]:
  assumes a1:"A = Matrix.mat 2 1 (\<lambda>(i,j). if i = 0 then a0 else a1)" and 
          a2:"B = Matrix.mat 2 1 (\<lambda>(i,j). if i = 0 then b0 else b1)"
  shows "mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list B) = [[a0*b0, a0*b1, a1*b0, a1*b1]]"
proof -
  have "mat_to_cols_list A = [[a0, a1]]"
    by (auto simp: a1 mat_to_cols_list_def) (simp add: numeral_2_eq_2)
  moreover have f2:"mat_to_cols_list B = [[b0, b1]]"
    by (auto simp: a2 mat_to_cols_list_def) (simp add: numeral_2_eq_2)
  ultimately have "mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list B) = 
                   mult.Tensor (*) [[a0,a1]] [[b0,b1]]" by simp
  thus ?thesis
    using mult.Tensor_def[of "(1::complex)" "(*)"] mult.times_def[of "(1::complex)" "(*)"]
    by (metis (mono_tags, lifting) append_self_conv list.simps(6) mult.Tensor.simps(2) mult.vec_mat_Tensor.simps(1) 
mult.vec_mat_Tensor.simps(2) plus_mult_cpx plus_mult_def tensor_prod_2)
qed

lemma multTensor2_bis [simp]:
  assumes a1:"dim_row A = 2" and a2:"dim_col A = 1" and a3:"dim_row B = 2" and a4:"dim_col B = 1"
  shows "mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list B) =  
[[A $$ (0,0) * B $$ (0,0), A $$ (0,0) *  B $$ (1,0), A $$ (1,0) * B $$ (0,0), A $$ (1,0) * B $$ (1,0)]]" 
proof -
  have "mat_to_cols_list A = [[A $$ (0,0), A $$ (1,0)]]"
    by (auto simp: a1 a2 mat_to_cols_list_def) (simp add: numeral_2_eq_2)
  moreover have f2:"mat_to_cols_list B = [[B $$ (0,0), B $$ (1,0)]]"
    by (auto simp: a3 a4 mat_to_cols_list_def) (simp add: numeral_2_eq_2)
  ultimately have "mult.Tensor (*) (mat_to_cols_list A) (mat_to_cols_list B) =
                   mult.Tensor (*) [[A $$ (0,0), A $$ (1,0)]] [[B $$ (0,0), B $$ (1,0)]]" by simp
  thus ?thesis
    using mult.Tensor_def[of "(1::complex)" "(*)"] mult.times_def[of "(1::complex)" "(*)"]
    by (smt append_self_conv list.simps(6) mult.Tensor.simps(2) mult.vec_mat_Tensor.simps(1) 
mult.vec_mat_Tensor.simps(2) plus_mult_cpx plus_mult_def tensor_prod_2)
qed

lemma mat_tensor_prod_2_prelim [simp]:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = mat_of_cols_list 4 
[[v $$ (0,0) * w $$ (0,0), v $$ (0,0) * w $$ (1,0), v $$ (1,0) * w $$ (0,0), v $$ (1,0) * w $$ (1,0)]]"
proof
  define u where "u = mat_of_cols_list 4 
[[v $$ (0,0) * w $$ (0,0), v $$ (0,0) * w $$ (1,0), v $$ (1,0) * w $$ (0,0), v $$ (1,0) * w $$ (1,0)]]"
  then show f1:"dim_row (v \<Otimes> w) = dim_row u"
    using assms state_def mat_of_cols_list_def tensor_mat_def by simp
  show f2:"dim_col (v \<Otimes> w) = dim_col u"
    using assms state_def mat_of_cols_list_def tensor_mat_def u_def by simp
  show "\<And>i j. i < dim_row u \<Longrightarrow> j < dim_col u \<Longrightarrow>  (v \<Otimes> w) $$ (i, j) = u $$ (i, j)"
      using u_def tensor_mat_def assms state_def by simp
qed

lemma mat_tensor_prod_2_col [simp]:
  assumes "state 1 v" and "state 1 w"
  shows "Matrix.col (v \<Otimes> w) 0 = Matrix.col v 0 \<otimes> Matrix.col w 0"
proof
  show f1:"dim_vec (Matrix.col (v \<Otimes> w) 0) = dim_vec (Matrix.col v 0 \<otimes> Matrix.col w 0)"
    using assms vec_tensor_prod_2_bis
    by (smt Tensor.mat_of_cols_list_def dim_col dim_row_mat(1) dim_vec mat_tensor_prod_2_prelim state.state_to_state_qbit)
next
  show "\<And>i. i<dim_vec (Matrix.col v 0 \<otimes> Matrix.col w 0) \<Longrightarrow> Matrix.col (v \<Otimes> w) 0 $ i = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ i"
  proof -
    have "dim_vec (Matrix.col v 0 \<otimes> Matrix.col w 0) = 4"
      by (metis (no_types, lifting) assms(1) assms(2) dim_vec state.state_to_state_qbit vec_tensor_prod_2_bis)
    moreover have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 0 = v $$ (0,0) * w $$ (0,0)"
      using assms vec_tensor_prod_2 state.state_to_state_qbit col_index_of_mat_col
      by (smt nth_Cons_0 power_one_right state_def vec_of_list_index zero_less_numeral)
    moreover have "\<dots> = Matrix.col (v \<Otimes> w) 0 $ 0"
      using assms by simp
    moreover have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 1 = v $$ (0,0) * w $$ (1,0)"
      using assms vec_tensor_prod_2 state.state_to_state_qbit col_index_of_mat_col 
      by (smt One_nat_def Suc_1 lessI nth_Cons_0 power_one_right state_def vec_index_vCons_Suc 
vec_of_list_Cons vec_of_list_index zero_less_numeral)
    moreover have "\<dots> = Matrix.col (v \<Otimes> w) 0 $ 1"
      using assms by simp
    moreover have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 2 = v $$ (1,0) * w $$ (0,0)"
      using assms vec_tensor_prod_2 state.state_to_state_qbit col_index_of_mat_col
      by (smt One_nat_def Suc_1 lessI nth_Cons_0 power_one_right state_def vec_index_vCons_Suc 
vec_of_list_Cons vec_of_list_index zero_less_numeral)
    moreover have "\<dots> = Matrix.col (v \<Otimes> w) 0 $ 2"
      using assms by simp
    moreover have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ 3 = v $$ (1,0) * w $$ (1,0)"
      using assms vec_tensor_prod_2 state.state_to_state_qbit col_index_of_mat_col numeral_3_eq_3
  by (smt One_nat_def Suc_1 lessI nth_Cons_0 power_one_right state_def vec_index_vCons_Suc 
vec_of_list_Cons vec_of_list_index zero_less_numeral)
    moreover have "\<dots> = Matrix.col (v \<Otimes> w) 0 $ 3"
      using assms by simp
    ultimately show "\<And>i. i<dim_vec (Matrix.col v 0 \<otimes> Matrix.col w 0) \<Longrightarrow> Matrix.col (v \<Otimes> w) 0 $ i = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ i"
      using index_sl_four by auto
  qed
qed

lemma mat_tensor_prod_2 [simp]:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = Matrix.mat 4 1 (\<lambda>(i,j). if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                            if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                              if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                                v $$ (1,0) * w $$ (0,0))"
proof
  define u where "u = Matrix.mat 4 1 (\<lambda>(i,j). if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                            if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                              if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                                v $$ (1,0) * w $$ (0,0))"
  then show "dim_row (v \<Otimes> w) = dim_row u"
    using assms tensor_mat_def state_def by(simp add: Tensor.mat_of_cols_list_def)
  also have "\<dots> = 4" by (simp add: u_def)
  show "dim_col (v \<Otimes> w) = dim_col u"
    using u_def assms tensor_mat_def state_def Tensor.mat_of_cols_list_def by simp
  moreover have "\<dots> = 1" by(simp add: u_def)
  ultimately show "\<And>i j. i < dim_row u \<Longrightarrow> j < dim_col u \<Longrightarrow> (v \<Otimes> w) $$ (i, j) = u $$ (i,j)"
  proof -
    fix i j::nat
    assume a1:"i < dim_row u" and a2:"j < dim_col u"
    then have "(v \<Otimes> w) $$ (i, j) = Matrix.col (v \<Otimes> w) 0 $ i"
      using Matrix.col_def u_def assms by simp
    then have f1:"(v \<Otimes> w) $$ (i, j) = (Matrix.col v 0 \<otimes> Matrix.col w 0) $ i"
      using assms mat_tensor_prod_2_col by simp
    have "(Matrix.col v 0 \<otimes> Matrix.col w 0) $ i = 
 Matrix.vec 4 (\<lambda>i. if i = 0 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 0 else 
                                      if i = 3 then Matrix.col v 0 $ 1 * Matrix.col w 0 $ 1 else
                                          if i = 1 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 1 else 
                                            Matrix.col v 0 $ 1 * Matrix.col w 0 $ 0) $ i"
      using vec_tensor_prod_2_bis assms state.state_to_state_qbit by presburger 
    thus "(v \<Otimes> w) $$ (i, j) = u $$ (i,j)"
      using u_def a1 a2 assms state_def by simp
  qed
qed
                         

lemma mat_tensor_prod_2_bis:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = |Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))\<rangle>"
  using assms ket_vec_def mat_tensor_prod_2 by(simp add: mat_eq_iff)

lemma eq_ket_vec:
  fixes u v:: "complex Matrix.vec"
  assumes "u = v"
  shows "|u\<rangle> = |v\<rangle>"
  using assms by simp

lemma mat_tensor_ket_vec:
  assumes "state 1 v" and "state 1 w"
  shows "v \<Otimes> w = |(Matrix.col v 0) \<otimes> (Matrix.col w 0)\<rangle>"
proof -
  have "v \<Otimes> w = |Matrix.col v 0\<rangle> \<Otimes> |Matrix.col w 0\<rangle>"
    using assms state_def by simp
  also have "\<dots> = 
|Matrix.vec 4 (\<lambda>i. if i = 0 then |Matrix.col v 0\<rangle> $$ (0,0) * |Matrix.col w 0\<rangle> $$ (0,0) else 
                                          if i = 3 then |Matrix.col v 0\<rangle> $$ (1,0) * |Matrix.col w 0\<rangle> $$ (1,0) else
                                            if i = 1 then |Matrix.col v 0\<rangle> $$ (0,0) * |Matrix.col w 0\<rangle> $$ (1,0) else 
                                              |Matrix.col v 0\<rangle> $$ (1,0) * |Matrix.col w 0\<rangle> $$ (0,0))\<rangle>"
    using assms mat_tensor_prod_2_bis state_col_ket_vec by simp
  also have "\<dots> = 
|Matrix.vec 4 (\<lambda>i. if i = 0 then v $$ (0,0) * w $$ (0,0) else 
                                          if i = 3 then v $$ (1,0) * w $$ (1,0) else
                                            if i = 1 then v $$ (0,0) * w $$ (1,0) else 
                                              v $$ (1,0) * w $$ (0,0))\<rangle>"
    using assms mat_tensor_prod_2_bis calculation by auto
  also have "\<dots> = 
|Matrix.vec 4 (\<lambda>i. if i = 0 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 0 else 
                                      if i = 3 then Matrix.col v 0 $ 1 * Matrix.col w 0 $ 1 else
                                          if i = 1 then Matrix.col v 0 $ 0 * Matrix.col w 0 $ 1 else 
                                            Matrix.col v 0 $ 1 * Matrix.col w 0 $ 0)\<rangle>"
    apply(rule eq_ket_vec)
    apply (rule eq_vecI)
    using col_index_of_mat_col assms state_def by auto
  finally show ?thesis
    using vec_tensor_prod_2_bis assms state.state_to_state_qbit by presburger
qed

text \<open>The property of being a state (resp. a gate) is preserved by tensor product.\<close>

lemma tensor_state2 [simp]:
  assumes "state 1 u" and "state 1 v"
  shows "state 2 (u \<Otimes> v)"
proof
  show "dim_col (u \<Otimes> v) = 1"
    using assms dim_col_tensor_mat state.is_column by presburger
  show "dim_row (u \<Otimes> v) = 2\<^sup>2" 
    using assms dim_row_tensor_mat state.dim_row
    by (metis (mono_tags, lifting) power2_eq_square power_one_right)
  show "\<parallel>Matrix.col (u \<Otimes> v) 0\<parallel> = 1"
  proof -
    define l where d0:"l = [u $$ (0,0) * v $$ (0,0), u $$ (0,0) * v $$ (1,0), u $$ (1,0) * v $$ (0,0), u $$ (1,0) * v $$ (1,0)]"
    then have f4:"length l = 4" by simp
    also have "u \<Otimes> v = mat_of_cols_list 4 
[[u $$ (0,0) * v $$ (0,0), u $$ (0,0) * v $$ (1,0), u $$ (1,0) * v $$ (0,0), u $$ (1,0) * v $$ (1,0)]]"
      using assms by simp
    then have "Matrix.col (u \<Otimes> v) 0 = vec_of_list [u $$ (0,0) * v $$ (0,0), u $$ (0,0) * v $$ (1,0), 
u $$ (1,0) * v $$ (0,0), u $$ (1,0) * v $$ (1,0)]"
      by (metis One_nat_def Suc_eq_plus1 add_Suc col_mat_of_cols_list list.size(3) list.size(4) 
nth_Cons_0 numeral_2_eq_2 numeral_Bit0 plus_1_eq_Suc vec_of_list_Cons zero_less_one_class.zero_less_one)    
    then have f5:"\<parallel>Matrix.col (u \<Otimes> v) 0\<parallel> = sqrt(\<Sum>i<4. (cmod (l ! i))\<^sup>2)"
      by (metis d0 f4 One_nat_def cpx_length_of_vec_of_list d0 vec_of_list_Cons)
    also have "\<dots> = sqrt ((cmod (u $$ (0,0) * v $$ (0,0)))\<^sup>2 + (cmod(u $$ (0,0) * v $$ (1,0)))\<^sup>2 + 
(cmod(u $$ (1,0) * v $$ (0,0)))\<^sup>2 + (cmod(u $$ (1,0) * v $$ (1,0)))\<^sup>2)"
    proof -
      have "(\<Sum>i<4. (cmod (l ! i))\<^sup>2) = (cmod (l ! 0))\<^sup>2 + (cmod (l ! 1))\<^sup>2 + (cmod (l ! 2))\<^sup>2 + 
(cmod (l ! 3))\<^sup>2"
        using sum_insert
        by (smt One_nat_def empty_iff finite.emptyI finite.insertI insertE lessThan_0 lessThan_Suc 
numeral_2_eq_2 numeral_3_eq_3 numeral_plus_one one_plus_numeral_commute plus_1_eq_Suc semiring_norm(2) 
semiring_norm(8) sum.empty) 
      also have "\<dots> = (cmod (u $$ (0,0) * v $$ (0,0)))\<^sup>2 + (cmod(u $$ (0,0) * v $$ (1,0)))\<^sup>2 + 
(cmod(u $$ (1,0) * v $$ (0,0)))\<^sup>2 + (cmod(u $$ (1,0) * v $$ (1,0)))\<^sup>2"
        using d0 by simp
      finally show ?thesis by(simp add: f5)
    qed
    moreover have "\<dots> = 
sqrt ((cmod (u $$ (0,0)))\<^sup>2 * (cmod (v $$ (0,0)))\<^sup>2 + (cmod(u $$ (0,0)))\<^sup>2 * (cmod (v $$ (1,0)))\<^sup>2 + 
(cmod(u $$ (1,0)))\<^sup>2 * (cmod (v $$ (0,0)))\<^sup>2 + (cmod(u $$ (1,0)))\<^sup>2 * (cmod(v $$ (1,0)))\<^sup>2)"
      by (simp add: norm_mult power_mult_distrib)
    moreover have "\<dots> = sqrt ((((cmod(u $$ (0,0)))\<^sup>2 + (cmod(u $$ (1,0)))\<^sup>2)) * 
(((cmod(v $$ (0,0)))\<^sup>2 + (cmod(v $$ (1,0)))\<^sup>2)))"
      by (simp add: distrib_left mult.commute)
    ultimately have f6:"\<parallel>Matrix.col (u \<Otimes> v) 0\<parallel>\<^sup>2 = (((cmod(u $$ (0,0)))\<^sup>2 + (cmod(u $$ (1,0)))\<^sup>2)) * 
(((cmod(v $$ (0,0)))\<^sup>2 + (cmod(v $$ (1,0)))\<^sup>2))"
      by (simp add: f4)
    also have f7:"\<dots> = (\<Sum>i< 2. (cmod (u $$ (i,0)))\<^sup>2) * (\<Sum>i<2. (cmod (v $$ (i,0)))\<^sup>2)"
      by (simp add: numeral_2_eq_2)
    also have f8:"\<dots> = (\<Sum>i< 2.(cmod (Matrix.col u 0 $ i))\<^sup>2) * (\<Sum>i<2.(cmod (Matrix.col v 0 $ i))\<^sup>2)"
      using assms index_col state_def by simp
    finally show ?thesis
    proof -
      have f1:"(\<Sum>i< 2.(cmod (Matrix.col u 0 $ i))\<^sup>2) = 1"
        using assms(1) state_def cpx_vec_length_def by auto
      have f2:"(\<Sum>i< 2.(cmod (Matrix.col v 0 $ i))\<^sup>2) = 1"
        using assms(2) state_def cpx_vec_length_def by auto
      thus ?thesis
        using f1 f8 f5 f6 f7
        by (simp add: \<open>sqrt (\<Sum>i<4. (cmod (l ! i))\<^sup>2) = sqrt ((cmod (u $$ (0, 0) * v $$ (0, 0)))\<^sup>2 + 
(cmod (u $$ (0, 0) * v $$ (1, 0)))\<^sup>2 + (cmod (u $$ (1, 0) * v $$ (0, 0)))\<^sup>2 + (cmod (u $$ (1, 0) * v $$ (1, 0)))\<^sup>2)\<close>)
    qed
  qed
qed

lemma sum_prod:
  fixes f::"nat \<Rightarrow> complex" and g::"nat \<Rightarrow> complex"
  shows "(\<Sum>i<a*b. f(i div b) * g(i mod b)) = (\<Sum>i<a. f(i)) * (\<Sum>j<b. g(j))"
proof (induction a)
  case 0
  then show ?case by simp
next
  case (Suc a)
  have "(\<Sum>i<(a+1)*b. f (i div b) * g (i mod b)) = (\<Sum>i<a*b. f (i div b) * g (i mod b)) + 
(\<Sum>i\<in>{a*b..<(a+1)*b}. f (i div b) * g (i mod b))"
    apply (auto simp: algebra_simps)
    by (smt add.commute mult_Suc sum.lessThan_Suc sum.nat_group)
  also have "\<dots> = (\<Sum>i<a. f(i)) * (\<Sum>j<b. g(j)) + (\<Sum>i\<in>{a*b..<(a+1)*b}. f (i div b) * g (i mod b))"
    by (simp add: Suc.IH)
  also have "\<dots> = (\<Sum>i<a. f(i)) * (\<Sum>j<b. g(j)) + (\<Sum>i\<in>{a*b..<(a+1)*b}. f (a) * g(i-a*b))" by simp
  also have "\<dots> = (\<Sum>i<a. f(i)) * (\<Sum>j<b. g(j)) + f(a) * (\<Sum>i\<in>{a*b..<(a+1)*b}. g(i-a*b))" 
    by(simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>i<a. f(i)) * (\<Sum>j<b. g(j)) + f(a) * (\<Sum>i\<in>{..<b}. g(i))"
    using sum_of_index_diff[of "g" "(a*b)" "b"] by (simp add: algebra_simps)
  ultimately show ?case  by (simp add: semiring_normalization_rules(1))
qed

lemma tensor_state [simp]:
  assumes "state m u" and "state n v"
  shows "state (m + n) (u \<Otimes> v)"
proof
  show c1:"dim_col (u \<Otimes> v) = 1"
    using assms dim_col_tensor_mat state.is_column by presburger
  show c2:"dim_row (u \<Otimes> v) = 2^(m + n)" 
    using assms dim_row_tensor_mat state.dim_row by (metis power_add)
  have "(\<Sum>i<2^(m + n). (cmod (u $$ (i div 2 ^ n, 0) * v $$ (i mod 2 ^ n, 0)))\<^sup>2) = 
(\<Sum>i<2^(m + n). (cmod (u $$ (i div 2 ^ n, 0)))\<^sup>2 * (cmod (v $$ (i mod 2 ^ n, 0)))\<^sup>2)"
    by (simp add: sqr_of_cmod_of_prod)
  also have "\<dots> = (\<Sum>i<2^m. (cmod (u $$ (i, 0)))\<^sup>2) * (\<Sum>i<2^n. (cmod (v $$ (i, 0)))\<^sup>2)"
  proof-
    have "\<dots> = (\<Sum>i<2^(m + n).complex_of_real((cmod (u $$ (i div 2^n,0)))\<^sup>2) * complex_of_real((cmod (v $$ (i mod 2^n,0)))\<^sup>2))"
      by simp
    moreover have "(\<Sum>i<2^m. (cmod (u $$ (i, 0)))\<^sup>2) = (\<Sum>i<2^m. complex_of_real ((cmod (u $$ (i,0)))\<^sup>2))" by simp
    moreover have "(\<Sum>i<2^n. (cmod (v $$ (i, 0)))\<^sup>2) = (\<Sum>i<2^n. complex_of_real ((cmod (v $$ (i, 0)))\<^sup>2))" by simp
    ultimately show ?thesis
      using sum_prod[of "\<lambda>i. (cmod (u $$ (i , 0)))\<^sup>2" "2^n" "\<lambda>i. (cmod (v $$ (i , 0)))\<^sup>2" "2^m"]
      by (smt of_real_eq_iff of_real_mult power_add)
  qed
  also have "\<dots> = 1"
  proof-
    have "(\<Sum>i<2^m. (cmod (u $$ (i, 0)))\<^sup>2) = 1"
      using assms(1) state_def cpx_vec_length_def by auto
    moreover have "(\<Sum>i<2^n. (cmod (v $$ (i, 0)))\<^sup>2) = 1"
      using assms(2) state_def cpx_vec_length_def by auto
    ultimately show ?thesis by simp
  qed
  ultimately show "\<parallel>Matrix.col (u \<Otimes> v) 0\<parallel> = 1"
    using c1 c2 assms state_def by (auto simp add: cpx_vec_length_def)
qed

lemma dim_row_of_tensor_gate:
  assumes "gate m G1" and "gate n G2"
  shows "dim_row (G1 \<Otimes> G2) = 2^(m+n)" 
  using assms dim_row_tensor_mat gate.dim_row by (simp add: power_add)

lemma tensor_gate_sqr_mat:
  assumes "gate m G1" and "gate n G2"
  shows "square_mat (G1 \<Otimes> G2)" 
  using assms gate.square_mat by simp

lemma dim_row_of_one_mat_less_pow:
  assumes "gate m G1" and "gate n G2" and "i < dim_row (1\<^sub>m(dim_col G1 * dim_col G2))"
  shows "i < 2^(m+n)" 
  using assms gate_def by (simp add: power_add)

lemma dim_col_of_one_mat_less_pow:
  assumes "gate m G1" and "gate n G2" and "j < dim_col (1\<^sub>m(dim_col G1 * dim_col G2))"
  shows "j < 2^(m+n)"
  using assms gate_def by (simp add: power_add)

lemma index_tensor_gate_unitary1:
  assumes "gate m G1" and "gate n G2" and "i < dim_row (1\<^sub>m(dim_col G1 * dim_col G2))" and 
"j < dim_col (1\<^sub>m(dim_col G1 * dim_col G2))"
  shows "((G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2)) $$ (i, j) = 1\<^sub>m(dim_col G1 * dim_col G2) $$ (i, j)"
proof-
  have "\<And>k. k<2^(m+n) \<Longrightarrow> cnj((G1 \<Otimes> G2) $$ (k,i)) = 
cnj(G1 $$ (k div 2^n, i div 2^n)) * cnj(G2 $$ (k mod 2^n, i mod 2^n))"
    using assms(1-3) by (simp add: gate_def power_add)
  moreover have "\<And>k. k<2^(m+n) \<Longrightarrow> (G1 \<Otimes> G2) $$ (k,j) = 
                                   G1 $$ (k div 2^n, j div 2^n) * G2 $$ (k mod 2^n, j mod 2^n)"
    using assms(1,2,4) by (simp add: gate_def power_add)
  ultimately have "\<And>k. k<2^(m+n) \<Longrightarrow> cnj((G1 \<Otimes> G2) $$ (k,i)) * ((G1 \<Otimes> G2) $$ (k,j)) = 
      cnj(G1 $$ (k div 2^n, i div 2^n)) * G1 $$ (k div 2^n, j div 2^n) * 
      cnj(G2 $$ (k mod 2^n, i mod 2^n)) * G2 $$ (k mod 2^n, j mod 2^n)" by simp
  then have "(\<Sum>k<2^(m+n). cnj((G1 \<Otimes> G2) $$ (k,i)) * ((G1 \<Otimes> G2) $$ (k,j))) = 
      (\<Sum>k<2^(m+n). cnj(G1 $$ (k div 2^n, i div 2^n)) * G1 $$ (k div 2^n, j div 2^n) * 
                    cnj(G2 $$ (k mod 2^n, i mod 2^n)) * G2 $$ (k mod 2^n, j mod 2^n))" by simp
  also have "\<dots> = 
             (\<Sum>k<2^m. cnj(G1 $$ (k, i div 2^n)) * G1 $$ (k, j div 2^n)) * 
             (\<Sum>k<2^n. cnj(G2 $$ (k, i mod 2^n)) * G2 $$ (k, j mod 2^n))"
    using sum_prod[of "\<lambda>x. cnj(G1 $$ (x, i div 2^n)) * G1 $$ (x, j div 2^n)" "2^n" 
"\<lambda>x. cnj(G2 $$ (x, i mod 2^n)) * G2 $$ (x, j mod 2^n)" "2^m"]
    by (metis (no_types, lifting) power_add semigroup_mult_class.mult.assoc sum.cong)
  also have "((G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2)) $$ (i, j) = (\<Sum>k<2^(m+n).cnj((G1 \<Otimes> G2) $$ (k,i)) * ((G1 \<Otimes> G2) $$ (k,j)))"
    using assms index_matrix_prod[of "i" "(G1 \<Otimes> G2)\<^sup>\<dagger>" "j" "(G1 \<Otimes> G2)"] dagger_def 
dim_row_of_tensor_gate tensor_gate_sqr_mat by simp
  ultimately have "((G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2)) $$ (i,j) = 
              (\<Sum>k1<2^m. cnj(G1 $$ (k1, i div 2^n)) * G1 $$ (k1, j div 2^n)) * 
              (\<Sum>k2<2^n. cnj(G2 $$ (k2, i mod 2^n)) * G2 $$ (k2, j mod 2^n))" by simp
  moreover have "(\<Sum>k<2^m. cnj(G1 $$ (k, i div 2^n))* G1 $$ (k, j div 2^n)) = (G1\<^sup>\<dagger> * G1) $$ (i div 2^n, j div 2^n)"
      using assms gate_def dagger_def index_matrix_prod[of "i div 2^n" "G1\<^sup>\<dagger>" "j div 2^n" "G1"]
      by (simp add: less_mult_imp_div_less power_add)
  moreover have "\<dots> = 1\<^sub>m(2^m) $$ (i div 2^n, j div 2^n)"
    using assms(1,2) gate_def unitary_def by simp
  moreover have "(\<Sum>k<2^n. cnj(G2 $$ (k, i mod 2^n))* G2 $$ (k, j mod 2^n)) = (G2\<^sup>\<dagger> * G2) $$ (i mod 2^n, j mod 2^n)"
    using assms(1,2) gate_def dagger_def index_matrix_prod[of "i mod 2^n" "G2\<^sup>\<dagger>" "j mod 2^n" "G2"] by simp
  moreover have "\<dots> = 1\<^sub>m(2^n) $$ (i mod 2^n, j mod 2^n)"
    using assms(1,2) gate_def unitary_def by simp
  ultimately have "((G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2)) $$ (i,j) = 1\<^sub>m (2^m) $$ (i div 2^n, j div 2^n) * 1\<^sub>m (2^n) $$ (i mod 2^n, j mod 2^n)"
    by simp
  thus ?thesis
    using assms assms(3,4) gate_def index_one_mat_div_mod[of "i" "m" "n" "j"] by(simp add: power_add)
qed

lemma tensor_gate_unitary1 [simp]:
  assumes "gate m G1" and "gate n G2"
  shows "(G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2) = 1\<^sub>m(dim_col G1 * dim_col G2)"
proof
  show "dim_row ((G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2)) = dim_row (1\<^sub>m(dim_col G1 * dim_col G2))" by simp
  show "dim_col ((G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2)) = dim_col (1\<^sub>m(dim_col G1 * dim_col G2))" by simp
  fix i j assume "i < dim_row (1\<^sub>m(dim_col G1 * dim_col G2))" and "j < dim_col (1\<^sub>m(dim_col G1 * dim_col G2))"
  thus "((G1 \<Otimes> G2)\<^sup>\<dagger> * (G1 \<Otimes> G2)) $$ (i, j) = 1\<^sub>m(dim_col G1 * dim_col G2) $$ (i, j)"
    using assms index_tensor_gate_unitary1 by simp
qed

lemma index_tensor_gate_unitary2 [simp]:
  assumes "gate m G1" and "gate n G2" and "i < dim_row (1\<^sub>m (dim_col G1 * dim_col G2))" and
"j < dim_col (1\<^sub>m (dim_col G1 * dim_col G2))"
  shows "((G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m(dim_col G1 * dim_col G2) $$ (i, j)"
proof-
  have "\<And>k. k<2^(m+n) \<Longrightarrow> (G1 \<Otimes> G2) $$ (i,k) = 
G1 $$ (i div 2^n, k div 2^n) * G2 $$ (i mod 2^n, k mod 2^n)"
    using assms(1-3) by (simp add: gate_def power_add)
  moreover have "\<And>k. k<2^(m+n) \<Longrightarrow> cnj((G1 \<Otimes> G2) $$ (j,k)) = 
cnj(G1 $$ (j div 2^n, k div 2^n)) * cnj(G2 $$ (j mod 2^n, k mod 2^n))"
    using assms(1,2,4) by (simp add: gate_def power_add)
  ultimately have "\<And>k. k\<in>{..<2^(m+n)} \<Longrightarrow> (G1 \<Otimes> G2) $$ (i,k) * cnj((G1 \<Otimes> G2) $$ (j,k)) = 
                         G1 $$ (i div 2^n, k div 2^n) * cnj(G1 $$ (j div 2^n, k div 2^n)) * 
                         G2 $$ (i mod 2^n, k mod 2^n) * cnj(G2 $$ (j mod 2^n, k mod 2^n))" by simp
  then have "(\<Sum>k<2^(m+n). (G1 \<Otimes> G2) $$ (i,k) * cnj((G1 \<Otimes> G2) $$ (j,k))) = 
      (\<Sum>k<2^(m+n). G1 $$ (i div 2^n, k div 2^n) * cnj(G1 $$ (j div 2^n, k div 2^n)) * 
      G2 $$ (i mod 2^n, k mod 2^n) * cnj(G2 $$ (j mod 2^n, k mod 2^n)))" by simp
  also have "\<dots> = 
             (\<Sum>k<2^m. G1 $$ (i div 2^n, k) * cnj(G1 $$ (j div 2^n, k))) * 
             (\<Sum>k<2^n. G2 $$ (i mod 2^n, k) * cnj(G2 $$ (j mod 2^n, k)))"
    using sum_prod[of "\<lambda>k. G1 $$ (i div 2^n, k) * cnj(G1 $$ (j div 2^n, k))" "2^n" 
                        "\<lambda>k. G2 $$ (i mod 2^n, k) * cnj(G2 $$ (j mod 2^n, k))" "2^m"]
    by (metis (no_types, lifting) power_add semigroup_mult_class.mult.assoc sum.cong)
  also have "((G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>)) $$ (i, j) = (\<Sum>k<2^(m+n). (G1 \<Otimes> G2) $$ (i,k) * cnj((G1 \<Otimes> G2) $$ (j,k)))"
    using assms index_matrix_prod[of "i" "(G1 \<Otimes> G2)" "j" "(G1 \<Otimes> G2)\<^sup>\<dagger>"] dagger_def
dim_row_of_tensor_gate tensor_gate_sqr_mat by simp
  ultimately have "((G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>)) $$ (i,j) = 
             (\<Sum>k<2^m. G1 $$ (i div 2^n, k) * cnj(G1 $$ (j div 2^n, k))) * 
             (\<Sum>k<2^n. G2 $$ (i mod 2^n, k) * cnj(G2 $$ (j mod 2^n, k)))" by simp
  moreover have "(\<Sum>k<2^m. G1 $$ (i div 2^n, k) * cnj(G1 $$ (j div 2^n, k))) = (G1 * (G1\<^sup>\<dagger>)) $$ (i div 2^n, j div 2^n)"
    using assms gate_def dagger_def index_matrix_prod[of "i div 2^n" "G1" "j div 2^n" "G1\<^sup>\<dagger>"]
    by (simp add: less_mult_imp_div_less power_add)
  moreover have "\<dots> = 1\<^sub>m(2^m) $$ (i div 2^n, j div 2^n)"
    using assms(1,2) gate_def unitary_def by simp
  moreover have "(\<Sum>k<2^n. G2 $$ (i mod 2^n, k) * cnj(G2 $$ (j mod 2^n, k))) = (G2 * (G2\<^sup>\<dagger>)) $$ (i mod 2^n, j mod 2^n)"
    using assms(1,2) gate_def dagger_def index_matrix_prod[of "i mod 2^n" "G2" "j mod 2^n" "G2\<^sup>\<dagger>"] by simp
  moreover have "\<dots> = 1\<^sub>m(2^n) $$ (i mod 2^n, j mod 2^n)"
    using assms(1,2) gate_def unitary_def by simp
  ultimately have "((G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>)) $$ (i,j) = 1\<^sub>m(2^m) $$ (i div 2^n, j div 2^n) * 1\<^sub>m(2^n) $$ (i mod 2^n, j mod 2^n)"
    by simp
  thus ?thesis
    using assms gate_def index_one_mat_div_mod[of "i" "m" "n" "j"] by(simp add: power_add)
qed

lemma tensor_gate_unitary2 [simp]:
  assumes "gate m G1" and "gate n G2"
  shows "(G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>) = 1\<^sub>m(dim_col G1 * dim_col G2)"
proof
  show "dim_row ((G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>)) = dim_row(1\<^sub>m (dim_col G1 * dim_col G2))"
    using assms gate_def by simp
  show "dim_col ((G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>)) = dim_col (1\<^sub>m(dim_col G1 * dim_col G2))"
    using assms gate_def by simp
  fix i j assume "i < dim_row (1\<^sub>m (dim_col G1 * dim_col G2))" and "j < dim_col (1\<^sub>m (dim_col G1 * dim_col G2))"
  thus "((G1 \<Otimes> G2) * ((G1 \<Otimes> G2)\<^sup>\<dagger>)) $$ (i, j) = 1\<^sub>m(dim_col G1 * dim_col G2) $$ (i, j)"
    using assms index_tensor_gate_unitary2 by simp
qed

lemma tensor_gate [simp]:
  assumes "gate m G1" and "gate n G2"
  shows "gate (m + n) (G1 \<Otimes> G2)" 
proof
  show "dim_row (G1 \<Otimes> G2) = 2^(m+n)"
    using assms dim_row_tensor_mat gate.dim_row by (simp add: power_add)
  show "square_mat (G1 \<Otimes> G2)"
    using assms gate.square_mat by simp
  thus "unitary (G1 \<Otimes> G2)"
    using assms unitary_def by simp
qed

end