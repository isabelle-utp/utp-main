(*
Authors: 

  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
*)

section \<open>The Deutsch Algorithm\<close>

theory Deutsch
imports
  More_Tensor
  Measurement
begin


text \<open>
Given a function $f:{0,1}\mapsto {0,1}$, Deutsch's algorithm decides if this function is constant
or balanced with a single $f(x)$ circuit to evaluate the function for multiple values of $x$ 
simultaneously. The algorithm makes use of quantum parallelism and quantum interference.
\<close>
                                   
text \<open>
A constant function with values in {0,1} returns either always 0 or always 1. 
A balanced function is 0 for half of the inputs and 1 for the other half. 
\<close>

locale deutsch =
  fixes f:: "nat \<Rightarrow> nat" 
  assumes dom: "f \<in> ({0,1} \<rightarrow>\<^sub>E {0,1})"

context deutsch
begin

definition is_swap:: bool where
"is_swap = (\<forall>x \<in> {0,1}. f x = 1 - x)"

lemma is_swap_values:
  assumes "is_swap"
  shows "f 0 = 1" and "f 1 = 0" 
  using assms is_swap_def by auto

lemma is_swap_sum_mod_2:
  assumes "is_swap"
  shows "(f 0 + f 1) mod 2 = 1"
  using assms is_swap_def by simp

definition const:: "nat \<Rightarrow> bool" where 
"const n = (\<forall>x \<in> {0,1}.(f x = n))"

definition is_const:: "bool" where 
"is_const \<equiv> const 0 \<or> const 1"

definition is_balanced:: "bool" where
"is_balanced \<equiv> (\<forall>x \<in> {0,1}.(f x = x)) \<or> is_swap"

lemma f_values: "(f 0 = 0 \<or> f 0 = 1) \<and> (f 1 = 0 \<or> f 1 = 1)" 
  using dom by auto
 
lemma f_cases:
  shows "is_const \<or> is_balanced"   
  using dom is_balanced_def const_def is_const_def is_swap_def f_values by auto

lemma const_0_sum_mod_2:
  assumes "const 0"
  shows "(f 0 + f 1) mod 2 = 0"
  using assms const_def by simp

lemma const_1_sum_mod_2:
  assumes "const 1"
  shows "(f 0 + f 1) mod 2 = 0"
  using assms const_def by simp

lemma is_const_sum_mod_2:
  assumes "is_const"
  shows "(f 0 + f 1) mod 2 = 0"
  using assms is_const_def const_0_sum_mod_2 const_1_sum_mod_2 by auto

lemma id_sum_mod_2:
  assumes "f = id"
  shows "(f 0 + f 1) mod 2 = 1"
  using assms by simp

lemma is_balanced_sum_mod_2:
  assumes "is_balanced"
  shows "(f 0 + f 1) mod 2 = 1"
  using assms is_balanced_def id_sum_mod_2 is_swap_sum_mod_2 by auto

lemma f_ge_0: "\<forall> x. (f x \<ge> 0)" by simp

end (* context deutsch *)

text \<open>The Deutsch's Transform @{text U\<^sub>f}.\<close>

definition (in deutsch) deutsch_transform:: "complex Matrix.mat" ("U\<^sub>f") where 
"U\<^sub>f \<equiv> mat_of_cols_list 4 [[1 - f(0), f(0), 0, 0],
                          [f(0), 1 - f(0), 0, 0],
                          [0, 0, 1 - f(1), f(1)],
                          [0, 0, f(1), 1 - f(1)]]"

lemma (in deutsch) deutsch_transform_dim [simp]: 
  shows "dim_row U\<^sub>f = 4" and "dim_col U\<^sub>f = 4" 
  by (auto simp add: deutsch_transform_def mat_of_cols_list_def)

lemma (in deutsch) deutsch_transform_coeff_is_zero [simp]: 
  shows "U\<^sub>f $$ (0,2) = 0" and "U\<^sub>f $$ (0,3) = 0"
    and "U\<^sub>f $$ (1,2) = 0" and "U\<^sub>f $$(1,3) = 0"
    and "U\<^sub>f $$ (2,0) = 0" and "U\<^sub>f $$(2,1) = 0"
    and "U\<^sub>f $$ (3,0) = 0" and "U\<^sub>f $$ (3,1) = 0"
  using deutsch_transform_def by auto

lemma (in deutsch) deutsch_transform_coeff [simp]: 
  shows "U\<^sub>f $$ (0,1) = f(0)" and "U\<^sub>f $$ (1,0) = f(0)"
    and "U\<^sub>f $$(2,3) = f(1)" and "U\<^sub>f $$ (3,2) = f(1)"
    and "U\<^sub>f $$ (0,0) = 1 - f(0)" and "U\<^sub>f $$(1,1) = 1 - f(0)"
    and "U\<^sub>f $$ (2,2) = 1 - f(1)" and "U\<^sub>f $$ (3,3) = 1 - f(1)"
  using deutsch_transform_def by auto

abbreviation (in deutsch) V\<^sub>f:: "complex Matrix.mat" where
"V\<^sub>f \<equiv> Matrix.mat 4 4 (\<lambda>(i,j). 
                if i=0 \<and> j=0 then 1 - f(0) else
                  (if i=0 \<and> j=1 then f(0) else
                    (if i=1 \<and> j=0 then f(0) else
                      (if i=1 \<and> j=1 then 1 - f(0) else
                        (if i=2 \<and> j=2 then 1 - f(1) else
                          (if i=2 \<and> j=3 then f(1) else
                            (if i=3 \<and> j=2 then f(1) else
                              (if i=3 \<and> j=3 then 1 - f(1) else 0))))))))"

lemma (in deutsch) deutsch_transform_alt_rep_coeff_is_zero [simp]:
  shows "V\<^sub>f $$ (0,2) = 0" and "V\<^sub>f $$ (0,3) = 0"
    and "V\<^sub>f $$ (1,2) = 0" and "V\<^sub>f $$(1,3) = 0"
    and "V\<^sub>f $$ (2,0) = 0" and "V\<^sub>f $$(2,1) = 0"
    and "V\<^sub>f $$ (3,0) = 0" and "V\<^sub>f $$ (3,1) = 0"
  by auto

lemma (in deutsch) deutsch_transform_alt_rep_coeff [simp]:
  shows "V\<^sub>f $$ (0,1) = f(0)" and "V\<^sub>f $$ (1,0) = f(0)"
    and "V\<^sub>f $$(2,3) = f(1)" and "V\<^sub>f $$ (3,2) = f(1)"
    and "V\<^sub>f $$ (0,0) = 1 - f(0)" and "V\<^sub>f $$(1,1) = 1 - f(0)"
    and "V\<^sub>f $$ (2,2) = 1 - f(1)" and "V\<^sub>f $$ (3,3) = 1 - f(1)"
  by auto

lemma (in deutsch) deutsch_transform_alt_rep:
  shows "U\<^sub>f = V\<^sub>f"
proof
  show c0:"dim_row U\<^sub>f = dim_row V\<^sub>f" by simp
  show c1:"dim_col U\<^sub>f = dim_col V\<^sub>f" by simp
  fix i j:: nat
  assume "i < dim_row V\<^sub>f" and "j < dim_col V\<^sub>f"
  then have "i < 4" and "j < 4" by auto
  thus "U\<^sub>f $$ (i,j) = V\<^sub>f $$ (i,j)"
    by (smt deutsch_transform_alt_rep_coeff deutsch_transform_alt_rep_coeff_is_zero deutsch_transform_coeff
 deutsch_transform_coeff_is_zero set_4_disj)
qed

text \<open>@{text U\<^sub>f} is a gate.\<close>

lemma (in deutsch) transpose_of_deutsch_transform:
  shows "(U\<^sub>f)\<^sup>t = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>t) = dim_row U\<^sub>f" by simp
  show "dim_col (U\<^sub>f\<^sup>t) = dim_col U\<^sub>f" by simp
  fix i j:: nat
  assume "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
  thus "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)"
    by (auto simp add: transpose_mat_def)
      (metis deutsch_transform_coeff(1-4) deutsch_transform_coeff_is_zero set_4_disj)
qed

lemma (in deutsch) adjoint_of_deutsch_transform: 
  shows "(U\<^sub>f)\<^sup>\<dagger> = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>\<dagger>) = dim_row U\<^sub>f" by simp
  show "dim_col (U\<^sub>f\<^sup>\<dagger>) = dim_col U\<^sub>f" by simp
  fix i j:: nat
  assume "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f"
  thus "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)"
    by (auto simp add: dagger_def)
      (metis complex_cnj_of_nat complex_cnj_zero deutsch_transform_coeff 
        deutsch_transform_coeff_is_zero set_4_disj)
qed

lemma (in deutsch) deutsch_transform_is_gate:
  shows "gate 2 U\<^sub>f"
proof
  show "dim_row U\<^sub>f = 2\<^sup>2" by simp
  show "square_mat U\<^sub>f" by simp
  show "unitary U\<^sub>f"
  proof-
    have "U\<^sub>f * U\<^sub>f = 1\<^sub>m (dim_col U\<^sub>f)"
    proof
      show "dim_row (U\<^sub>f * U\<^sub>f) = dim_row (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      show "dim_col (U\<^sub>f * U\<^sub>f) = dim_col (1\<^sub>m (dim_col U\<^sub>f))" by simp
    next
      fix i j:: nat
      assume "i < dim_row (1\<^sub>m (dim_col U\<^sub>f))" and "j < dim_col (1\<^sub>m (dim_col U\<^sub>f))"
      then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i, j)"
        apply (auto simp add: deutsch_transform_alt_rep one_mat_def times_mat_def)
         apply (auto simp: scalar_prod_def) 
        using f_values by auto
    qed
    thus ?thesis by (simp add: adjoint_of_deutsch_transform unitary_def)
  qed
qed

text \<open>
Two qubits are prepared. 
The first one in the state $|0\rangle$, the second one in the state $|1\rangle$.
\<close>

abbreviation zero where "zero \<equiv> unit_vec 2 0"
abbreviation one where "one \<equiv> unit_vec 2 1" 

lemma ket_zero_is_state: 
  shows "state 1 |zero\<rangle>"
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_one_is_state:
  shows "state 1 |one\<rangle>" 
  by (simp add: state_def ket_vec_def cpx_vec_length_def numerals(2))

lemma ket_zero_to_mat_of_cols_list [simp]: "|zero\<rangle> = mat_of_cols_list 2 [[1, 0]]"
  by (auto simp add: ket_vec_def mat_of_cols_list_def)

lemma ket_one_to_mat_of_cols_list [simp]: "|one\<rangle> = mat_of_cols_list 2 [[0, 1]]"
  apply (auto simp add: ket_vec_def unit_vec_def mat_of_cols_list_def)
  using less_2_cases by fastforce

text \<open>
Applying the Hadamard gate to the state $|0\rangle$ results in the new state 
@{term "\<psi>\<^sub>0\<^sub>0"} = $\dfrac {(|0\rangle + |1\rangle)} {\sqrt 2 }$
\<close>

abbreviation \<psi>\<^sub>0\<^sub>0:: "complex Matrix.mat" where
"\<psi>\<^sub>0\<^sub>0 \<equiv> mat_of_cols_list 2 [[1/sqrt(2), 1/sqrt(2)]]"

lemma H_on_ket_zero: 
  shows "(H * |zero\<rangle>) = \<psi>\<^sub>0\<^sub>0"
proof 
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>0\<^sub>0" and "j < dim_col \<psi>\<^sub>0\<^sub>0"
  then have "i \<in> {0,1} \<and> j = 0" by (simp add: mat_of_cols_list_def less_2_cases)
  then show "(H * |zero\<rangle>) $$ (i,j) = \<psi>\<^sub>0\<^sub>0 $$ (i,j)"
    by (auto simp add: mat_of_cols_list_def times_mat_def scalar_prod_def H_def)
next
  show "dim_row (H * |zero\<rangle>) = dim_row \<psi>\<^sub>0\<^sub>0"  by (simp add: H_def mat_of_cols_list_def)
  show "dim_col (H * |zero\<rangle>) = dim_col \<psi>\<^sub>0\<^sub>0" by (simp add: H_def mat_of_cols_list_def)
qed

lemma H_on_ket_zero_is_state: 
  shows "state 1 (H * |zero\<rangle>)"
proof
  show "gate 1 H" 
    using H_is_gate by simp
  show "state 1 |zero\<rangle>" 
    using ket_zero_is_state by simp
qed

text \<open>
Applying the Hadamard gate to the state $|0\rangle$ results in the new state 
@{text \<psi>\<^sub>0\<^sub>1} = $\dfrac {(|0\rangle - |1\rangle)} {\sqrt 2}$.
\<close>

abbreviation \<psi>\<^sub>0\<^sub>1:: "complex Matrix.mat" where
"\<psi>\<^sub>0\<^sub>1 \<equiv> mat_of_cols_list 2 [[1/sqrt(2), -1/sqrt(2)]]"

lemma H_on_ket_one: 
  shows "(H * |one\<rangle>) = \<psi>\<^sub>0\<^sub>1"
proof 
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>0\<^sub>1" and "j < dim_col \<psi>\<^sub>0\<^sub>1"
  then have "i \<in> {0,1} \<and> j = 0" by (simp add: mat_of_cols_list_def less_2_cases)
  then show "(H * |one\<rangle>) $$ (i,j) = \<psi>\<^sub>0\<^sub>1 $$ (i,j)"
    by (auto simp add: mat_of_cols_list_def times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |one\<rangle>) = dim_row \<psi>\<^sub>0\<^sub>1" by (simp add: H_def mat_of_cols_list_def)
  show "dim_col (H * |one\<rangle>) = dim_col \<psi>\<^sub>0\<^sub>1" by (simp add: H_def mat_of_cols_list_def ket_vec_def)
qed

lemma H_on_ket_one_is_state: 
  shows "state 1 (H * |one\<rangle>)"
  using H_is_gate ket_one_is_state by simp

text\<open>
Then, the state @{text \<psi>\<^sub>1} = $\dfrac {(|00\rangle - |01\rangle + |10\rangle - |11\rangle)} {2} $
is obtained by taking the tensor product of the states 
@{text \<psi>\<^sub>0\<^sub>0} = $\dfrac {(|0\rangle + |1\rangle)} {\sqrt 2} $  and  
@{text \<psi>\<^sub>0\<^sub>1} = $\dfrac {(|0\rangle - |1\rangle)} {\sqrt 2} $.
\<close>

abbreviation \<psi>\<^sub>1:: "complex Matrix.mat" where
"\<psi>\<^sub>1 \<equiv> mat_of_cols_list 4 [[1/2, -1/2, 1/2, -1/2]]"

lemma \<psi>\<^sub>0_to_\<psi>\<^sub>1: 
  shows "(\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1) = \<psi>\<^sub>1"
proof 
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>1" and "j < dim_col \<psi>\<^sub>1"
  then have "i \<in> {0,1,2,3}" and "j = 0" using mat_of_cols_list_def by auto  
  moreover have "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
    by (metis mult_2_right numeral_Bit0 of_real_mult of_real_numeral real_sqrt_four real_sqrt_mult)
  ultimately show "(\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1) $$ (i,j) = \<psi>\<^sub>1 $$ (i,j)" using mat_of_cols_list_def by auto
next 
  show "dim_row (\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1) = dim_row \<psi>\<^sub>1" by (simp add: mat_of_cols_list_def)
  show "dim_col (\<psi>\<^sub>0\<^sub>0 \<Otimes> \<psi>\<^sub>0\<^sub>1) = dim_col \<psi>\<^sub>1" by (simp add: mat_of_cols_list_def)
qed

lemma \<psi>\<^sub>1_is_state: 
  shows "state 2 \<psi>\<^sub>1"
proof 
  show  "dim_col \<psi>\<^sub>1 = 1" 
    by (simp add: Tensor.mat_of_cols_list_def)
  show "dim_row \<psi>\<^sub>1 = 2\<^sup>2" 
    by (simp add: Tensor.mat_of_cols_list_def)
  show "\<parallel>Matrix.col \<psi>\<^sub>1 0\<parallel> = 1"
    using H_on_ket_one_is_state H_on_ket_zero_is_state state.is_normal tensor_state2 \<psi>\<^sub>0_to_\<psi>\<^sub>1
    H_on_ket_one H_on_ket_zero by force
qed

text \<open>
Next, the gate @{text U\<^sub>f} is applied to the state 
@{text \<psi>\<^sub>1} = $\dfrac {(|00\rangle - |01\rangle + |10\rangle - |11\rangle)} {2}$ and 
@{text \<psi>\<^sub>2}= $\dfrac {(|0f(0)\oplus 0\rangle - |0 f(0) \oplus 1\rangle + |1 f(1)\oplus 0\rangle - |1f(1)\oplus 1\rangle)} {2}$ 
is obtained. This simplifies to 
@{text \<psi>\<^sub>2}= $\dfrac {(|0f(0)\rangle - |0 \overline{f(0)} \rangle + |1 f(1)\rangle - |1\overline{f(1)}\rangle)} {2}$ 
\<close>

abbreviation (in deutsch) \<psi>\<^sub>2:: "complex Matrix.mat" where
"\<psi>\<^sub>2 \<equiv>  mat_of_cols_list 4 [[(1 - f(0))/2 - f(0)/2,
                            f(0)/2 - (1 - f(0))/2,
                            (1 - f(1))/2 - f(1)/2,
                            f(1)/2 - (1- f(1))/2]]"

lemma (in deutsch) \<psi>\<^sub>1_to_\<psi>\<^sub>2: 
  shows "U\<^sub>f * \<psi>\<^sub>1 = \<psi>\<^sub>2"
proof 
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>2 " and "j < dim_col \<psi>\<^sub>2"
  then have asm:"i \<in> {0,1,2,3} \<and> j = 0 " by (auto simp add: mat_of_cols_list_def)
  then have "i < dim_row U\<^sub>f \<and> j < dim_col \<psi>\<^sub>1" 
    using deutsch_transform_def mat_of_cols_list_def by auto
  then have "(U\<^sub>f * \<psi>\<^sub>1) $$ (i, j) 
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>\<^sub>1}. (Matrix.row U\<^sub>f i) $ k * (Matrix.col \<psi>\<^sub>1 j) $ k)"
    apply (auto simp add: times_mat_def scalar_prod_def).
  thus "(U\<^sub>f * \<psi>\<^sub>1) $$ (i, j) = \<psi>\<^sub>2 $$ (i, j)"
    using  mat_of_cols_list_def deutsch_transform_def asm by auto
next
  show "dim_row (U\<^sub>f * \<psi>\<^sub>1) = dim_row \<psi>\<^sub>2" by (simp add: mat_of_cols_list_def)
  show "dim_col (U\<^sub>f * \<psi>\<^sub>1) = dim_col \<psi>\<^sub>2" by (simp add: mat_of_cols_list_def)
qed

lemma (in deutsch) \<psi>\<^sub>2_is_state:
  shows "state 2 \<psi>\<^sub>2" 
proof
  show  "dim_col \<psi>\<^sub>2 = 1" 
    by (simp add: Tensor.mat_of_cols_list_def)
  show "dim_row \<psi>\<^sub>2 = 2\<^sup>2" 
    by (simp add: Tensor.mat_of_cols_list_def)
  show "\<parallel>Matrix.col \<psi>\<^sub>2 0\<parallel> = 1"
    using gate_on_state_is_state \<psi>\<^sub>1_is_state deutsch_transform_is_gate \<psi>\<^sub>1_to_\<psi>\<^sub>2 state_def
    by (metis (no_types, lifting))
qed

lemma H_tensor_Id_1: 
  defines d:"v \<equiv>  mat_of_cols_list 4 [[1/sqrt(2), 0, 1/sqrt(2), 0],
                                  [0, 1/sqrt(2), 0, 1/sqrt(2)],
                                  [1/sqrt(2), 0, -1/sqrt(2), 0],
                                  [0, 1/sqrt(2), 0, -1/sqrt(2)]]"
  shows "(H \<Otimes> Id 1) = v"
proof
  show "dim_col (H \<Otimes> Id 1) = dim_col v"  
    by (simp add: d H_def Id_def mat_of_cols_list_def)
  show "dim_row (H \<Otimes> Id 1) = dim_row v"
    by (simp add: d H_def Id_def mat_of_cols_list_def)
  fix i j:: nat assume "i < dim_row v" and "j < dim_col v"
  then have "i \<in> {0..<4} \<and> j \<in> {0..<4}" 
    by (auto simp add: d mat_of_cols_list_def)
  thus "(H \<Otimes> Id 1) $$ (i, j) = v $$ (i, j)"
    by (auto simp add: d Id_def H_def mat_of_cols_list_def)
qed

lemma H_tensor_Id_1_is_gate: 
  shows "gate 2 (H \<Otimes> Id 1)"
proof 
  show "dim_row (H \<Otimes> Quantum.Id 1) = 2\<^sup>2" 
    using H_tensor_Id_1 by (simp add: mat_of_cols_list_def)
  show "square_mat (H \<Otimes> Quantum.Id 1)" 
    using H_is_gate id_is_gate tensor_gate_sqr_mat by blast
  show "unitary (H \<Otimes> Quantum.Id 1)" 
    using H_is_gate gate_def id_is_gate tensor_gate by blast
qed

text \<open>
Applying the Hadamard gate to the first qubit of @{text \<psi>\<^sub>2} results in @{text \<psi>\<^sub>3} = 
$\pm |f(0)\oplus f(1)\rangle \left[ \dfrac {(|0\rangle - |1\rangle)} {\sqrt 2}\right]$ 
\<close>

abbreviation (in deutsch) \<psi>\<^sub>3:: "complex Matrix.mat" where
"\<psi>\<^sub>3 \<equiv> mat_of_cols_list 4 
[[(1-f(0))/(2*sqrt(2)) - f(0)/(2*sqrt(2)) + (1-f(1))/(2*sqrt(2)) - f(1)/(2*sqrt(2)),
  f(0)/(2*sqrt(2)) - (1-f(0))/(2*sqrt(2)) + (f(1)/(2*sqrt(2)) - (1-f(1))/(2*sqrt(2))),
  (1-f(0))/(2*sqrt(2)) - f(0)/(2*sqrt(2)) - (1-f(1))/(2*sqrt(2)) + f(1)/(2*sqrt(2)),
  f(0)/(2*sqrt(2)) - (1-f(0))/(2*sqrt(2)) - f(1)/(2*sqrt(2)) + (1-f(1))/(2*sqrt(2))]]"

lemma (in deutsch) \<psi>\<^sub>2_to_\<psi>\<^sub>3: 
 shows "(H \<Otimes> Id 1) * \<psi>\<^sub>2 = \<psi>\<^sub>3" 
proof
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>3" and "j < dim_col \<psi>\<^sub>3"
  then have a0:"i \<in> {0,1,2,3} \<and> j = 0" by (auto simp add: mat_of_cols_list_def)
  then have "i < dim_row (H \<Otimes> Id 1) \<and> j < dim_col \<psi>\<^sub>2"
    using mat_of_cols_list_def H_tensor_Id_1 by auto
  then have "((H \<Otimes> Id 1)*\<psi>\<^sub>2) $$ (i,j)
        = (\<Sum> k \<in> {0 ..< dim_vec \<psi>\<^sub>2}. (Matrix.row (H \<Otimes> Id 1) i) $ k * (Matrix.col \<psi>\<^sub>2 j) $ k)"
    by (auto simp: times_mat_def scalar_prod_def)
  thus "((H \<Otimes> Id 1) * \<psi>\<^sub>2) $$ (i, j) = \<psi>\<^sub>3 $$ (i, j)"
    using  mat_of_cols_list_def H_tensor_Id_1 a0 f_ge_0 
    by (auto simp: diff_divide_distrib)
next
  show "dim_row ((H \<Otimes> Id 1) * \<psi>\<^sub>2) = dim_row \<psi>\<^sub>3"
    using H_tensor_Id_1 mat_of_cols_list_def by simp
  show "dim_col ((H \<Otimes> Id 1) * \<psi>\<^sub>2) = dim_col \<psi>\<^sub>3"    
    using H_tensor_Id_1 mat_of_cols_list_def by simp
qed

lemma (in deutsch) \<psi>\<^sub>3_is_state: 
  shows "state 2 \<psi>\<^sub>3"
proof-
  have "gate 2 (H \<Otimes> Id 1)" 
    using H_tensor_Id_1_is_gate by simp
  thus "state 2 \<psi>\<^sub>3" 
    using \<psi>\<^sub>2_is_state \<psi>\<^sub>2_to_\<psi>\<^sub>3 by (metis gate_on_state_is_state)
qed

text \<open>
Finally, all steps are put together. The result depends on the function f. If f is constant
the first qubit of $\pm |f(0)\oplus f(1)\rangle \left[ \dfrac {(|0\rangle - |1\rangle)} {\sqrt 2}\right]$
is 0, if it is is\_balanced it is 1. 
The algorithm only uses one evaluation of f(x) and will always succeed. 
\<close>

definition (in deutsch) deutsch_algo:: "complex Matrix.mat" where 
"deutsch_algo \<equiv> (H \<Otimes> Id 1) * (U\<^sub>f * ((H * |zero\<rangle>) \<Otimes> (H * |one\<rangle>)))"

lemma (in deutsch) deutsch_algo_result [simp]: 
  shows "deutsch_algo = \<psi>\<^sub>3" 
  using deutsch_algo_def H_on_ket_zero H_on_ket_one \<psi>\<^sub>0_to_\<psi>\<^sub>1 \<psi>\<^sub>1_to_\<psi>\<^sub>2 \<psi>\<^sub>2_to_\<psi>\<^sub>3 by simp

lemma (in deutsch) deutsch_algo_result_is_state: 
  shows "state 2 deutsch_algo" 
  using \<psi>\<^sub>3_is_state by simp


text \<open>
If the function is constant then the measurement of the first qubit should result in the state 
$|0\rangle$ with probability 1. 
\<close>

lemma (in deutsch) prob0_deutsch_algo_const:
  assumes "is_const" 
  shows "prob0 2 deutsch_algo 0 = 1" 
proof -
  have "{k| k::nat. (k < 4) \<and> \<not> select_index 2 0 k} = {0,1}"
    using select_index_def by auto
  then have "prob0 2 deutsch_algo 0 = (\<Sum>j\<in>{0,1}. (cmod(deutsch_algo $$ (j,0)))\<^sup>2)"
    using deutsch_algo_result_is_state prob0_def by simp
  thus "prob0 2 deutsch_algo 0 = 1" 
    using assms is_const_def const_def by auto
qed

lemma (in deutsch) prob1_deutsch_algo_const: 
  assumes "is_const" 
  shows "prob1 2 deutsch_algo 0 = 0" 
  using assms prob0_deutsch_algo_const prob_sum_is_one[of "2" "deutsch_algo" "0"] 
deutsch_algo_result_is_state by simp

text \<open>
If the function is balanced the measurement of the first qubit should result in the state $|1\rangle$ 
with probability 1. 
\<close>

lemma (in deutsch) prob0_deutsch_algo_balanced:  
  assumes "is_balanced" 
  shows "prob0 2 deutsch_algo 0 = 0" 
proof-
  have "{k| k::nat. (k < 4) \<and> \<not> select_index 2 0 k} = {0,1}"
    using select_index_def by auto
  then have "prob0 2 deutsch_algo 0 = (\<Sum>j \<in> {0,1}. (cmod(deutsch_algo $$ (j,0)))\<^sup>2)"
    using deutsch_algo_result_is_state prob0_def by simp
  thus "prob0 2 deutsch_algo 0 = 0" 
    using is_swap_values assms is_balanced_def by auto
qed

lemma (in deutsch) prob1_deutsch_algo_balanced:
  assumes "is_balanced" 
  shows "prob1 2 deutsch_algo 0 = 1" 
using assms prob0_deutsch_algo_balanced prob_sum_is_one[of "2" "deutsch_algo" "0"] 
deutsch_algo_result_is_state by simp
 
text \<open>Eventually, the measurement of the first qubit results in $f(0)\oplus f(1)$. \<close>

definition (in deutsch) deutsch_algo_eval:: "real" where 
"deutsch_algo_eval \<equiv> prob1 2 deutsch_algo 0"

lemma (in deutsch) sum_mod_2_cases:
  shows "(f 0 + f 1) mod 2 = 0 \<longrightarrow> is_const" 
  and "(f 0 + f 1) mod 2 = 1 \<longrightarrow> is_balanced"
  using f_cases is_balanced_sum_mod_2 is_const_sum_mod_2 by auto 

lemma (in deutsch) deutsch_algo_eval_is_sum_mod_2:
  shows "deutsch_algo_eval = (f 0 + f 1) mod 2"
  using deutsch_algo_eval_def f_cases is_const_sum_mod_2 is_balanced_sum_mod_2 
prob1_deutsch_algo_const prob1_deutsch_algo_balanced by auto

text \<open>
If the algorithm returns 0 then one concludes that the input function is constant and
if it returns 1 then the function is balanced.
\<close>

theorem (in deutsch) deutsch_algo_is_correct:
  shows "deutsch_algo_eval = 0 \<longrightarrow> is_const" and "deutsch_algo_eval = 1 \<longrightarrow> is_balanced"
  using deutsch_algo_eval_is_sum_mod_2 sum_mod_2_cases by auto

end