(*
Authors: 
  Hanna Lachnitt, TU Wien, lachnitt@student.tuwien.ac.at
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
*) 

section \<open>The Deutsch-Jozsa Algorithm\<close>

theory Deutsch_Jozsa
imports
  Deutsch
  More_Tensor
  Binary_Nat
begin


text \<open>
Given a function $f:{0,1}^n \mapsto {0,1}$, the Deutsch-Jozsa algorithm decides if this function is 
constant or balanced with a single $f(x)$ circuit to evaluate the function for multiple values of $x$ 
simultaneously. The algorithm makes use of quantum parallelism and quantum interference.

A constant function with values in {0,1} returns either always 0 or always 1. 
A balanced function is 0 for half of the inputs and 1 for the other half. 
\<close>

locale bob_fun =
  fixes f:: "nat \<Rightarrow> nat" and n:: "nat"
  assumes dom: "f \<in> ({(i::nat). i < 2^n} \<rightarrow>\<^sub>E {0,1})"
  assumes dim: "n \<ge> 1"

context bob_fun
begin

definition const:: "nat \<Rightarrow> bool" where 
"const c = (\<forall>x\<in>{i::nat. i<2^n}. f x = c)"

definition is_const:: bool where 
"is_const \<equiv> const 0 \<or> const 1"

definition is_balanced:: bool where
"is_balanced \<equiv> \<exists>A B ::nat set. A \<subseteq> {i::nat. i < 2^n} \<and> B \<subseteq> {i::nat. i < 2^n}
                   \<and> card A = 2^(n-1) \<and> card B = 2^(n-1)  
                   \<and> (\<forall>x\<in>A. f x = 0)  \<and> (\<forall>x\<in>B. f x = 1)"

lemma is_balanced_inter: 
  fixes A B:: "nat set"
  assumes "\<forall>x \<in> A. f x = 0" and "\<forall>x \<in> B. f x = 1" 
  shows "A \<inter> B = {}" 
  using assms by auto

lemma is_balanced_union:
  fixes A B:: "nat set"
  assumes "A \<subseteq> {i::nat. i < 2^n}" and "B \<subseteq> {i::nat. i < 2^n}" 
      and "card A = 2^(n-1)" and "card B = 2^(n-1)" 
      and "A \<inter> B = {}"
  shows "A \<union> B = {i::nat. i < 2^n}"
proof-
  have "finite A" and "finite B" 
    by (simp add: assms(3) card_ge_0_finite)
      (simp add: assms(4) card_ge_0_finite)
  then have "card(A \<union> B) = 2 * 2^(n-1)" 
    using assms(3-5) by (simp add: card_Un_disjoint)
  then have "card(A \<union> B) = 2^n"
    by (metis Nat.nat.simps(3) One_nat_def dim le_0_eq power_eq_if)
  moreover have "\<dots> = card({i::nat. i < 2^n})" by simp
  moreover have "A \<union> B \<subseteq> {i::nat. i < 2^n}" 
    using assms(1,2) by simp
  moreover have "finite ({i::nat. i < 2^n})" by simp
  ultimately show ?thesis 
    using card_subset_eq[of "{i::nat. i < 2^n}" "A \<union> B"] by simp
qed

lemma f_ge_0: "\<forall>x. f x \<ge> 0" by simp

lemma f_dom_not_zero: 
  shows "f \<in> ({i::nat. n \<ge> 1 \<and> i < 2^n} \<rightarrow>\<^sub>E {0,1})" 
  using dim dom by simp

lemma f_values: "\<forall>x \<in> {(i::nat). i < 2^n} . f x = 0 \<or> f x = 1" 
  using dom by auto

end (* bob_fun *)

text \<open>The input function has to be constant or balanced.\<close>

locale jozsa = bob_fun +
  assumes const_or_balanced: "is_const \<or> is_balanced "

text \<open>
Introduce two customised rules: disjunctions with four disjuncts and induction starting from one 
instead of zero.
\<close>

(* To deal with Uf it is often necessary to do a case distinction with four different cases.*)
lemma disj_four_cases:
  assumes "A \<or> B \<or> C \<or> D" and "A \<Longrightarrow> P" and "B \<Longrightarrow> P" and "C \<Longrightarrow> P" and "D \<Longrightarrow> P"
  shows "P" 
  using assms by auto

text \<open>The unitary transform @{term U\<^sub>f}.\<close>

definition (in jozsa) jozsa_transform:: "complex Matrix.mat" ("U\<^sub>f") where 
"U\<^sub>f \<equiv> Matrix.mat (2^(n+1)) (2^(n+1)) (\<lambda>(i,j). 
  if i = j then (1-f(i div 2)) else 
    if i = j + 1 \<and> odd i then f(i div 2) else
      if i = j - 1 \<and> even i \<and> j\<ge>1 then f(i div 2) else 0)"

lemma (in jozsa) jozsa_transform_dim [simp]:
  shows "dim_row U\<^sub>f = 2^(n+1)" and "dim_col U\<^sub>f = 2^(n+1)" 
  by (auto simp add: jozsa_transform_def)

lemma (in jozsa) jozsa_transform_coeff_is_zero [simp]:
  assumes "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f"
  shows "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1)) \<longrightarrow> U\<^sub>f $$ (i,j) = 0"
  using jozsa_transform_def assms by auto

lemma (in jozsa) jozsa_transform_coeff [simp]: 
  assumes "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f"
  shows "i = j \<longrightarrow> U\<^sub>f $$ (i,j) = 1 - f (i div 2)"
  and "i = j + 1 \<and> odd i \<longrightarrow> U\<^sub>f $$ (i,j) = f (i div 2)"
  and "j \<ge> 1 \<and> i = j - 1 \<and> even i \<longrightarrow> U\<^sub>f $$ (i,j) = f (i div 2)" 
  using jozsa_transform_def assms by auto

lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_even:
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A" and "even i" and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i,k) * A $$ (k,j)) =(\<Sum>k\<in>{i,i+1}. U\<^sub>f $$ (i,k) * A $$ (k,j))"
proof-
  have "(\<Sum>k \<in> {0..< 2^(n+1)}. U\<^sub>f $$ (i,k) * A $$ (k,j)) = 
             (\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i,k) * A $$ (k,j)) +
             (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i,k) * A $$ (k,j)) +
             (\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i,k) * A $$ (k,j))" 
  proof- 
    have "{0..< 2^(n+1)} = {0..<i} \<union> {i..< 2^(n+1)} 
          \<and> {i..< 2^(n+1)} = {i,i+1} \<union> {(i+2)..<2^(n+1)}" using assms(1-3) by auto
    moreover have "{0..<i} \<inter> {i,i+1} = {} 
                  \<and> {i,i+1} \<inter> {(i+2)..< 2^(n+1)} = {} 
                  \<and> {0..<i} \<inter> {(i+2)..< 2^(n+1)} = {}" using assms by simp
    ultimately show ?thesis
      using sum.union_disjoint
      by (metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))
  qed
  moreover have "(\<Sum>k \<in> {0..<i}. U\<^sub>f $$ (i,k) * A $$ (k,j)) = 0" 
  proof-
    have "k \<in> {0..<i} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k 
      using assms by auto
    then have "k \<in> {0..<i} \<longrightarrow> U\<^sub>f $$ (i,k) = 0" for k
      using assms(1) by auto
    then show ?thesis by simp
  qed
  moreover have "(\<Sum>k \<in> {(i+2)..< 2^(n+1)}. U\<^sub>f $$ (i,k) * A $$ (k,j)) = 0" 
  proof- 
    have "k\<in>{(i+2)..< 2^(n+1)} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k by auto
    then have "k \<in> {(i+2)..< 2^(n+1)}\<longrightarrow> U\<^sub>f $$ (i,k) = 0" for k
      using assms(1) by auto
    then show ?thesis by simp
  qed
  moreover have  "dim_row A = 2^(n+1)" using assms(4) by simp
  ultimately show "?thesis" by(metis (no_types, lifting) add.left_neutral add.right_neutral)
qed

lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_even: 
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A" and "even i" and "dim_col U\<^sub>f = dim_row A"
  shows "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i,k) * A $$ (k,j))"
proof-
  have "(U\<^sub>f * A) $$ (i,j) = (\<Sum> k\<in>{0..< dim_row A}. (U\<^sub>f $$ (i,k)) * (A $$ (k,j)))"
    using assms(1,2,4) index_matrix_prod by (simp add: atLeast0LessThan)
  then show ?thesis
    using assms U\<^sub>f_mult_without_empty_summands_sum_even by simp
qed

lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_sum_odd:
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A" and "odd i" and "dim_col U\<^sub>f = dim_row A"
  shows "(\<Sum>k\<in>{0..< dim_row A}. U\<^sub>f $$ (i,k) * A $$ (k,j)) =(\<Sum>k\<in>{i-1,i}. U\<^sub>f $$ (i,k) * A $$ (k,j))"
proof-
  have "(\<Sum>k\<in>{0..< 2^(n+1)}. U\<^sub>f $$ (i,k) * A $$ (k,j)) = 
             (\<Sum>k \<in> {0..<i-1}. U\<^sub>f $$ (i,k) * A $$ (k,j)) +
             (\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i,k) * A $$ (k,j)) +
             (\<Sum>k \<in> {i+1..< 2^(n+1)}. U\<^sub>f $$ (i,k) * A $$ (k,j))" 
  proof- 
    have "{0..< 2^(n+1)} = {0..<i-1} \<union> {i-1..< 2^(n+1)} 
          \<and> {i-1..< 2^(n+1)} = {i-1,i} \<union> {i+1..<2^(n+1)}" using assms(1-3) by auto
    moreover have "{0..<i-1} \<inter> {i-1,i} = {} 
                  \<and> {i-1,i} \<inter> {i+1..< 2^(n+1)} = {} 
                  \<and> {0..<i-1} \<inter> {i+1..< 2^(n+1)} = {}" using assms by simp
    ultimately show ?thesis
      using sum.union_disjoint 
      by(metis (no_types, lifting) finite_Un finite_atLeastLessThan is_num_normalize(1) ivl_disj_int_two(3))
  qed
  moreover have "(\<Sum>k \<in> {0..<i-1}. U\<^sub>f $$ (i,k) * A $$ (k,j)) = 0"
  proof-
    have "k \<in> {0..<i-1} \<longrightarrow> (i\<noteq>k \<and> \<not>(i=k+1 \<and> odd i) \<and> \<not> (i=k-1 \<and> even i \<and> k\<ge>1))" for k by auto
    then have "k \<in> {0..<i-1} \<longrightarrow> U\<^sub>f $$ (i,k) = 0" for k
      using assms(1) by auto
    then show ?thesis by simp
  qed
  moreover have "(\<Sum>k \<in> {i+1..< 2^(n+1)}. U\<^sub>f $$ (i,k) * A $$ (k,j)) = 0" 
    using assms(3) by auto 
  moreover have  "dim_row A = 2^(n+1)" using assms(4) by simp
  ultimately show "?thesis" by(metis (no_types, lifting) add.left_neutral add.right_neutral)
qed

lemma (in jozsa) U\<^sub>f_mult_without_empty_summands_odd: 
  fixes i j A
  assumes "i < dim_row U\<^sub>f" and "j < dim_col A" and "odd i" and "dim_col U\<^sub>f = dim_row A"
  shows "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i,k) * A $$ (k,j)) "
proof-
  have "(U\<^sub>f * A) $$ (i,j) = (\<Sum>k \<in> {0 ..< dim_row A}. (U\<^sub>f $$ (i,k)) * (A $$ (k,j)))"
    using assms(1,2,4) index_matrix_prod by (simp add: atLeast0LessThan)
  then show "?thesis" 
    using assms U\<^sub>f_mult_without_empty_summands_sum_odd by auto
qed

text \<open>@{term U\<^sub>f} is a gate.\<close>

lemma (in jozsa) transpose_of_jozsa_transform:
  shows "(U\<^sub>f)\<^sup>t = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>t) = dim_row U\<^sub>f" by simp
next
  show "dim_col (U\<^sub>f\<^sup>t) = dim_col U\<^sub>f" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row U\<^sub>f" and a1: "j < dim_col U\<^sub>f"
  then show "U\<^sub>f\<^sup>t $$ (i, j) = U\<^sub>f $$ (i, j)" 
  proof (induct rule: disj_four_cases)
    show "i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))" 
      by linarith
  next
    assume "i = j"
    then show "U\<^sub>f\<^sup>t $$ (i,j) = U\<^sub>f $$ (i,j)" using a0 by simp
  next
    assume "(i=j+1 \<and> odd i)"
    then show "U\<^sub>f\<^sup>t $$ (i,j) = U\<^sub>f $$ (i,j)" using transpose_mat_def a0 a1 by auto
  next
    assume a2:"(i=j-1 \<and> even i \<and> j\<ge>1)"
    then have "U\<^sub>f $$ (i,j) = f (i div 2)" 
      using a0 a1 jozsa_transform_coeff by auto
    moreover have "U\<^sub>f $$ (j,i) = f (i div 2)" 
      using a0 a1 a2 jozsa_transform_coeff
      by (metis add_diff_assoc2 diff_add_inverse2 even_plus_one_iff even_succ_div_two jozsa_transform_dim)
    ultimately show "?thesis"
      using transpose_mat_def a0 a1 by simp
  next 
    assume a2:"(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    then have "(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))" 
      by (metis le_imp_diff_is_add diff_add_inverse even_plus_one_iff le_add1)
    then have "U\<^sub>f $$ (j,i) = 0" 
      using jozsa_transform_coeff_is_zero a0 a1 by auto
    moreover have "U\<^sub>f $$ (i,j) = 0" 
      using jozsa_transform_coeff_is_zero a0 a1 a2 by auto
    ultimately show "U\<^sub>f\<^sup>t $$ (i,j) = U\<^sub>f $$ (i,j)"
      using transpose_mat_def a0 a1 by simp
  qed 
qed

lemma (in jozsa) adjoint_of_jozsa_transform: 
  shows "(U\<^sub>f)\<^sup>\<dagger> = U\<^sub>f"
proof
  show "dim_row (U\<^sub>f\<^sup>\<dagger>) = dim_row U\<^sub>f" by simp
next
  show "dim_col (U\<^sub>f\<^sup>\<dagger>) = dim_col U\<^sub>f" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row U\<^sub>f" and a1: "j < dim_col U\<^sub>f"
  then show "U\<^sub>f\<^sup>\<dagger> $$ (i,j) = U\<^sub>f $$ (i,j)"
  proof (induct rule: disj_four_cases)
  show "i=j \<or> (i=j+1 \<and> odd i) \<or> (i=j-1 \<and> even i \<and> j\<ge>1) \<or> (i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    by linarith
  next
    assume "i=j"
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i,j) = U\<^sub>f $$ (i,j)" using a0 dagger_def by simp
  next
    assume "(i=j+1 \<and> odd i)"
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i,j) = U\<^sub>f $$ (i,j)" using a0 dagger_def by auto
  next
    assume a2:"(i=j-1 \<and> even i \<and> j\<ge>1)"
    then have "U\<^sub>f $$ (i,j) = f (i div 2)" 
      using a0 a1 jozsa_transform_coeff by auto
    moreover have "U\<^sub>f\<^sup>\<dagger>  $$ (j,i) = f (i div 2)" 
      using a1 a2 jozsa_transform_coeff dagger_def by auto
    ultimately show "U\<^sub>f\<^sup>\<dagger> $$ (i,j) = U\<^sub>f $$ (i,j)"
      by(metis a0 a1 cnj_transpose_is_dagger dim_row_of_dagger index_transpose_mat dagger_of_transpose_is_cnj transpose_of_jozsa_transform)
  next 
    assume a2: "(i\<noteq>j \<and> \<not>(i=j+1 \<and> odd i) \<and> \<not> (i=j-1 \<and> even i \<and> j\<ge>1))"
    then have f0:"(i\<noteq>j \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))" 
      by (metis le_imp_diff_is_add diff_add_inverse even_plus_one_iff le_add1)
    then have "U\<^sub>f $$ (j,i) = 0" and "cnj 0 = 0"
      using jozsa_transform_coeff_is_zero a0 a1 a2 by auto
    then have "U\<^sub>f\<^sup>\<dagger> $$ (i,j) = 0" 
      using a0 a1 dagger_def by simp
    then show "U\<^sub>f\<^sup>\<dagger> $$ (i, j) = U\<^sub>f $$ (i, j)" 
      using a0 a1 a2 jozsa_transform_coeff_is_zero by auto
  qed 
qed

lemma (in jozsa) jozsa_transform_is_unitary_index_even:
  fixes i j:: nat
  assumes "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f" and "even i"
  shows "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)"
proof-
  have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i,k) * U\<^sub>f $$ (k,j)) " 
    using U\<^sub>f_mult_without_empty_summands_even[of i j U\<^sub>f ] assms by simp
  moreover have "U\<^sub>f $$ (i,i) * U\<^sub>f $$ (i,j) = (1-f(i div 2)) * U\<^sub>f $$ (i,j)"
    using assms(1,3) by simp
  moreover have f0: "U\<^sub>f $$ (i,i+1) * U\<^sub>f $$ (i+1,j) = f(i div 2) * U\<^sub>f $$ (i+1,j)"
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right assms(1) assms(3) diff_add_inverse2 
even_add even_mult_iff jozsa_transform_coeff(3) jozsa_transform_dim le_add2 le_eq_less_or_eq odd_one 
one_add_one power.simps(2))
  ultimately have f1: "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2)) * U\<^sub>f $$ (i,j) +  f(i div 2) * U\<^sub>f $$ (i+1,j)" by auto
  thus ?thesis
  proof (induct rule: disj_four_cases)
    show "j=i \<or> (j=i+1 \<and> odd j) \<or> (j=i-1 \<and> even j \<and> i\<ge>1) \<or> (j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
      by linarith
  next
    assume a0:"j=i"
    then have "U\<^sub>f $$ (i,j) = (1-f(i div 2))" 
      using assms(1,2) a0 by simp
    moreover have "U\<^sub>f $$ (i+1,j) = f(i div 2)"
      using assms(1,3) a0 by auto
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2)) * (1-f(i div 2)) +  f(i div 2) * f(i div 2)" 
      using f1 by simp
    moreover have "(1-f(i div 2)) * (1-f(i div 2)) + f(i div 2) * f(i div 2) = 1" 
      using f_values assms(1)
      by (metis (no_types, lifting) Nat.minus_nat.diff_0 diff_add_0 diff_add_inverse jozsa_transform_dim(1) 
          less_power_add_imp_div_less mem_Collect_eq mult_eq_if one_power2 power2_eq_square power_one_right) 
    ultimately show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)"  by(metis assms(2) a0 index_one_mat(1) of_nat_1)
  next
    assume a0: "(j=i+1 \<and> odd j)"
    then have "U\<^sub>f $$ (i,j) = f(i div 2)" 
      using assms(1,2) a0 by simp
    moreover have "U\<^sub>f $$ (i+1,j) = (1-f(i div 2))"
      using assms(2,3) a0 by simp
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2)) * f(i div 2) + f(i div 2) * (1-f(i div 2))"
      using f0 f1 assms by simp
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" 
      using assms(1,2) a0 by auto
  next
    assume "(j=i-1 \<and> even j \<and> i\<ge>1)"
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" 
      using assms(3) dvd_diffD1 odd_one by blast
  next 
    assume a0:"(j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
    then have "U\<^sub>f $$ (i,j) = 0" 
      using assms(1,2) by(metis index_transpose_mat(1) jozsa_transform_coeff_is_zero jozsa_transform_dim transpose_of_jozsa_transform)
    moreover have "U\<^sub>f $$ (i+1,j) = 0" 
      using assms a0 by auto
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2)) * 0 +  f(i div 2) * 0" 
      by (simp add: f1)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" 
      using a0 assms(1,2) by(metis add.left_neutral index_one_mat(1) jozsa_transform_dim mult_0_right of_nat_0)
  qed
qed

lemma (in jozsa) jozsa_transform_is_unitary_index_odd:
  fixes i j:: nat
  assumes "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f" and "odd i"
  shows "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)"
proof-
  have f0: "i \<ge> 1"  
    using linorder_not_less assms(3) by auto
  have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i,k) * U\<^sub>f $$ (k,j)) " 
    using U\<^sub>f_mult_without_empty_summands_odd[of i j U\<^sub>f ] assms by simp
  moreover have "(\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i,k) * U\<^sub>f $$ (k,j)) 
                 = U\<^sub>f $$ (i,i-1) * U\<^sub>f $$ (i-1,j) +  U\<^sub>f $$ (i,i) * U\<^sub>f $$ (i,j)"
    using f0 by simp
  moreover have "U\<^sub>f $$ (i,i) * U\<^sub>f $$ (i,j) = (1-f(i div 2)) * U\<^sub>f $$ (i,j)" 
    using assms(1,2) by simp
  moreover have f1: "U\<^sub>f $$ (i,i-1) * U\<^sub>f $$ (i-1,j) = f(i div 2) * U\<^sub>f $$ (i-1,j)" 
    using assms(1) assms(3) by simp
  ultimately have f2: "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * U\<^sub>f $$ (i-1,j) + (1-f(i div 2)) * U\<^sub>f $$ (i,j)" by simp
  then show "?thesis"
  proof (induct rule: disj_four_cases)
    show "j=i \<or> (j=i+1 \<and> odd j) \<or> (j=i-1 \<and> even j \<and> i\<ge>1) \<or> (j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1))"
      by linarith
  next
    assume a0:"j=i"
    then have "U\<^sub>f $$ (i,j) = (1-f(i div 2))"
      using assms(1,2) by simp
    moreover have "U\<^sub>f $$ (i-1,j) = f(i div 2)"
      using a0 assms
      by (metis index_transpose_mat(1) jozsa_transform_coeff(2) less_imp_diff_less odd_two_times_div_two_nat 
          odd_two_times_div_two_succ transpose_of_jozsa_transform)
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * f(i div 2) + (1-f(i div 2)) * (1-f(i div 2))"
      using f2 by simp
    moreover have "f(i div 2) * f(i div 2) + (1-f(i div 2)) * (1-f(i div 2)) = 1" 
      using f_values assms(1)
      by (metis (no_types, lifting) Nat.minus_nat.diff_0 diff_add_0 diff_add_inverse jozsa_transform_dim(1) 
          less_power_add_imp_div_less mem_Collect_eq mult_eq_if one_power2 power2_eq_square power_one_right) 
    ultimately show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" by(metis assms(2) a0 index_one_mat(1) of_nat_1)
  next
    assume a0:"(j=i+1 \<and> odd j)"
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" 
      using assms(3) dvd_diffD1 odd_one even_plus_one_iff by blast
  next
    assume a0:"(j=i-1 \<and> even j \<and> i\<ge>1)"
    then have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = f(i div 2) * (1-f(i div 2)) + (1-f(i div 2)) * f(i div 2)" 
      using f0 f1 f2 assms
      by (metis jozsa_transform_coeff(1) Groups.ab_semigroup_mult_class.mult.commute even_succ_div_two f2 
          jozsa_transform_dim odd_two_times_div_two_nat odd_two_times_div_two_succ of_nat_add of_nat_mult)
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" 
      using assms(1) a0 by auto
  next 
    assume a0:"j\<noteq>i \<and> \<not>(j=i+1 \<and> odd j) \<and> \<not> (j=i-1 \<and> even j \<and> i\<ge>1)"
    then have "U\<^sub>f $$ (i,j) = 0" 
      by (metis assms(1,2) index_transpose_mat(1) jozsa_transform_coeff_is_zero jozsa_transform_dim transpose_of_jozsa_transform)
    moreover have "U\<^sub>f $$ (i-1,j) = 0" 
      using assms a0 f0 
      by auto (smt One_nat_def Suc_n_not_le_n add_diff_inverse_nat assms(1) assms(2) diff_Suc_less even_add 
jozsa_transform_coeff_is_zero jozsa_axioms less_imp_le less_le_trans less_one odd_one)
    ultimately have "(U\<^sub>f * U\<^sub>f) $$ (i,j) = (1-f(i div 2)) * 0 +  f(i div 2) * 0" 
      using f2 by simp
    then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" 
      using a0 assms by (metis add.left_neutral index_one_mat(1) jozsa_transform_dim mult_0_right of_nat_0)
  qed
qed

lemma (in jozsa) jozsa_transform_is_gate:
  shows "gate (n+1) U\<^sub>f"
proof
  show "dim_row U\<^sub>f = 2^(n+1)" by simp
next
  show "square_mat U\<^sub>f" by simp
next
  show "unitary U\<^sub>f"
  proof-
    have "U\<^sub>f * U\<^sub>f = 1\<^sub>m (dim_col U\<^sub>f)"
    proof
      show "dim_row (U\<^sub>f * U\<^sub>f) = dim_row (1\<^sub>m (dim_col U\<^sub>f))" by simp
      show "dim_col (U\<^sub>f * U\<^sub>f) = dim_col (1\<^sub>m (dim_col U\<^sub>f))" by simp
      fix i j:: nat
      assume "i < dim_row (1\<^sub>m (dim_col U\<^sub>f))" and "j < dim_col (1\<^sub>m (dim_col U\<^sub>f))"
      then have "i < dim_row U\<^sub>f" and "j < dim_col U\<^sub>f" by auto
      then show "(U\<^sub>f * U\<^sub>f) $$ (i,j) = 1\<^sub>m (dim_col U\<^sub>f) $$ (i,j)" 
        using jozsa_transform_is_unitary_index_odd jozsa_transform_is_unitary_index_even by blast
    qed
    thus ?thesis by (simp add: adjoint_of_jozsa_transform unitary_def)
  qed
qed

text \<open>N-fold application of the tensor product\<close>

fun iter_tensor:: "complex Matrix.mat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat" ("_ \<otimes>\<^bsup>_\<^esup>" 75)  where
  "A \<otimes>\<^bsup>(Suc 0)\<^esup> = A"  
| "A \<otimes>\<^bsup>(Suc k)\<^esup> = A \<Otimes> (A \<otimes>\<^bsup>k\<^esup>)"

lemma one_tensor_is_id [simp]:
  fixes A
  shows "A \<otimes>\<^bsup>1\<^esup> = A"
  using one_mat_def by simp

lemma iter_tensor_suc: 
  fixes n
  assumes "n \<ge> 1"
  shows " A \<otimes>\<^bsup>(Suc n)\<^esup> = A \<Otimes> (A \<otimes>\<^bsup>n\<^esup>)" 
  using assms by (metis Deutsch_Jozsa.iter_tensor.simps(2) One_nat_def Suc_le_D)

lemma dim_row_of_iter_tensor [simp]:
  fixes A n
  assumes "n \<ge> 1"
  shows "dim_row(A \<otimes>\<^bsup>n\<^esup>) = (dim_row A)^n"
  using assms
proof (rule nat_induct_at_least)
  show "dim_row (A \<otimes>\<^bsup>1\<^esup>) = (dim_row A)^1"
    using one_tensor_is_id by simp
  fix n:: nat
  assume "n \<ge> 1" and "dim_row (A \<otimes>\<^bsup>n\<^esup>) = (dim_row A)^n"
  then show "dim_row (A \<otimes>\<^bsup>Suc n\<^esup>) = (dim_row A)^Suc n"
    using iter_tensor_suc assms dim_row_tensor_mat by simp
qed

lemma dim_col_of_iter_tensor [simp]:
  fixes A n
  assumes "n \<ge> 1"
  shows "dim_col(A \<otimes>\<^bsup>n\<^esup>) = (dim_col A)^n"
  using assms
proof (rule nat_induct_at_least)
  show "dim_col (A \<otimes>\<^bsup>1\<^esup>) = (dim_col A)^1"
    using one_tensor_is_id by simp
  fix n:: nat
  assume "n \<ge> 1" and "dim_col (A \<otimes>\<^bsup>n\<^esup>) = (dim_col A)^n"
  then show "dim_col (A \<otimes>\<^bsup>Suc n\<^esup>) = (dim_col A)^Suc n"
    using iter_tensor_suc assms dim_col_tensor_mat by simp
qed

lemma iter_tensor_values:
  fixes A n i j
  assumes "n \<ge> 1" and "i < dim_row (A \<Otimes> (A \<otimes>\<^bsup>n\<^esup>))" and "j < dim_col (A \<Otimes> (A \<otimes>\<^bsup>n\<^esup>))"
  shows "(A \<otimes>\<^bsup>(Suc n)\<^esup>) $$ (i,j) = (A \<Otimes> (A \<otimes>\<^bsup>n\<^esup>)) $$ (i,j)"
  using assms by (metis One_nat_def le_0_eq not0_implies_Suc iter_tensor.simps(2))

lemma iter_tensor_mult_distr:
  assumes "n \<ge> 1" and "dim_col A = dim_row B" and "dim_col A > 0" and "dim_col B > 0"
  shows "(A \<otimes>\<^bsup>(Suc n)\<^esup>) * (B \<otimes>\<^bsup>(Suc n)\<^esup>) = (A * B) \<Otimes> ((A \<otimes>\<^bsup>n\<^esup>) * (B \<otimes>\<^bsup>n\<^esup>))" 
proof-
  have "(A \<otimes>\<^bsup>(Suc n)\<^esup>) * (B \<otimes>\<^bsup>(Suc n)\<^esup>) = (A \<Otimes> (A \<otimes>\<^bsup>n\<^esup>)) * (B \<Otimes> (B \<otimes>\<^bsup>n\<^esup>))" 
    using Suc_le_D assms(1) by fastforce
  then show "?thesis" 
    using mult_distr_tensor[of "A" "B" "(iter_tensor A n)" "(iter_tensor B n)"] assms by simp
qed

lemma index_tensor_mat_with_vec2_row_cond:
  fixes A B:: "complex Matrix.mat" and i:: "nat" 
  assumes "i < 2 * (dim_row B)" and "i \<ge> dim_row B" and "dim_col B > 0"
and "dim_row A = 2" and "dim_col A = 1"
  shows "(A \<Otimes> B) $$ (i,0) = (A $$ (1,0)) * (B $$ (i-dim_row B,0))"
proof-
  have "(A \<Otimes> B) $$ (i,0) = A $$ (i div (dim_row B),0) * B $$ (i mod (dim_row B),0)"
    using assms index_tensor_mat[of A "dim_row A" "dim_col A" B "dim_row B" "dim_col B" i 0] by simp
  moreover have "i div (dim_row B) = 1" 
    using assms(1,2,4) by simp
  then have "i mod (dim_row B) = i - (dim_row B)" 
    by (simp add: modulo_nat_def)
  ultimately show "(A \<Otimes> B) $$ (i,0) = (A $$ (1,0)) * (B $$ (i-dim_row B,0))" 
    by (simp add: \<open>i div dim_row B = 1\<close>)
qed

lemma iter_tensor_of_gate_is_gate:
  fixes A:: "complex Matrix.mat" and n m:: "nat" 
  assumes "gate m A" and "n \<ge> 1" 
  shows "gate (m*n) (A \<otimes>\<^bsup>n\<^esup>)"
  using assms(2)
proof(rule nat_induct_at_least)
  show "gate (m * 1) (A \<otimes>\<^bsup>1\<^esup>)" using assms(1) by simp
  fix n:: nat
  assume "n \<ge> 1" and IH:"gate (m * n) (A \<otimes>\<^bsup>n\<^esup>)"
  then have "A \<otimes>\<^bsup>(Suc n)\<^esup> = A \<Otimes> (A \<otimes>\<^bsup>n\<^esup>)" 
    by (simp add: iter_tensor_suc)
  moreover have "gate (m*n + m) (A \<otimes>\<^bsup>(Suc n)\<^esup>)"  
    using tensor_gate assms(1) by (simp add: IH add.commute calculation(1))
  then show "gate (m*(Suc n)) (A \<otimes>\<^bsup>(Suc n)\<^esup>)"
    by (simp add: add.commute)
qed

lemma iter_tensor_of_state_is_state:
  fixes A:: "complex Matrix.mat" and n m:: "nat" 
  assumes "state m A" and "n\<ge>1" 
  shows "state (m*n) (A \<otimes>\<^bsup>n\<^esup>)"
  using assms(2)
proof(rule nat_induct_at_least)
  show "state (m * 1) (A \<otimes>\<^bsup>1\<^esup>)"
    using one_tensor_is_id assms(1) by simp
  fix n:: nat
  assume "n \<ge> 1" and IH:"state (m * n) (A \<otimes>\<^bsup>n\<^esup>)"
  then have "A \<otimes>\<^bsup>(Suc n)\<^esup> = A \<Otimes> (A \<otimes>\<^bsup>n\<^esup>)" 
    by (simp add: iter_tensor_suc)
  moreover have "state (m*n + m) (A \<otimes>\<^bsup>(Suc n)\<^esup>)"  
    using tensor_gate assms(1) by (simp add: IH add.commute calculation)
  then show "state (m*(Suc n)) (A \<otimes>\<^bsup>(Suc n)\<^esup>)" 
    by (simp add: add.commute)
qed

text \<open>
We prepare n+1 qubits. The first n qubits in the state $|0\rangle$, the last one in the state 
$|1\rangle$.
\<close>

abbreviation \<psi>\<^sub>1\<^sub>0:: "nat \<Rightarrow> complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>0 n \<equiv> Matrix.mat (2^n) 1 (\<lambda>(i,j). 1/(sqrt 2)^n)" 

lemma \<psi>\<^sub>1\<^sub>0_values:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1\<^sub>0 n)" and "j < dim_col (\<psi>\<^sub>1\<^sub>0 n)" 
  shows "(\<psi>\<^sub>1\<^sub>0 n) $$ (i,j) = 1/(sqrt 2)^n" 
  using assms case_prod_conv by simp

text \<open>$H^{\otimes n}$ is applied to $|0\rangle^{\otimes n}$.\<close>

lemma H_on_ket_zero: 
  shows "(H * |zero\<rangle>) = \<psi>\<^sub>1\<^sub>0 1"
proof 
  fix i j:: nat
  assume "i < dim_row (\<psi>\<^sub>1\<^sub>0 1)" and "j < dim_col (\<psi>\<^sub>1\<^sub>0 1)"
  then have f1: "i \<in> {0,1} \<and> j = 0" by (simp add: less_2_cases)
  then show "(H * |zero\<rangle>) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 1) $$ (i,j)"
    by (auto simp add: times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |zero\<rangle>) = dim_row (\<psi>\<^sub>1\<^sub>0 1)"  by (simp add: H_def)
  show "dim_col (H * |zero\<rangle>) = dim_col (\<psi>\<^sub>1\<^sub>0 1)" using H_def  
    by (simp add: ket_vec_def)
qed

lemma \<psi>\<^sub>1\<^sub>0_tensor: 
  assumes "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n) = (\<psi>\<^sub>1\<^sub>0 (Suc n))"
proof
  have "dim_row (\<psi>\<^sub>1\<^sub>0 1) * dim_row (\<psi>\<^sub>1\<^sub>0 n) = 2^(Suc n)" by simp 
  then show "dim_row ((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) = dim_row (\<psi>\<^sub>1\<^sub>0 (Suc n))" by simp
  have "dim_col (\<psi>\<^sub>1\<^sub>0 1) * dim_col (\<psi>\<^sub>1\<^sub>0 n) = 1" by simp
  then show "dim_col ((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) = dim_col (\<psi>\<^sub>1\<^sub>0 (Suc n))" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row (\<psi>\<^sub>1\<^sub>0 (Suc n))" and a1: "j < dim_col (\<psi>\<^sub>1\<^sub>0 (Suc n))"
  then have f0: "j = 0" and f1: "i < 2^(Suc n)" by auto
  then have f2:"(\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j) = 1/(sqrt 2)^(Suc n)" 
    using \<psi>\<^sub>1\<^sub>0_values[of "i" "(Suc n)" "j"] a0 a1 by simp
  show "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
  proof (rule disjE) (*case distinction*)
    show "i < dim_row (\<psi>\<^sub>1\<^sub>0 n) \<or> i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n)" by linarith
  next (* case i < dim_row (\<psi>\<^sub>1\<^sub>0 n) *)
    assume a2: "i < dim_row (\<psi>\<^sub>1\<^sub>0 n)"
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 1) $$ (0,0) * (\<psi>\<^sub>1\<^sub>0 n) $$ (i,0)"
      using index_tensor_mat f0 assms by simp
    also have "... = 1/sqrt(2) * 1/(sqrt(2)^n)"
      using \<psi>\<^sub>1\<^sub>0_values a2 assms by simp
    finally show "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
      using f2 divide_divide_eq_left power_Suc by simp
  next (* case i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n) *)
    assume "i \<ge> dim_row (\<psi>\<^sub>1\<^sub>0 n)"
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,0) = ((\<psi>\<^sub>1\<^sub>0 1) $$ (1, 0)) * ((\<psi>\<^sub>1\<^sub>0 n) $$ ( i -dim_row (\<psi>\<^sub>1\<^sub>0 n),0))"
      using index_tensor_mat_with_vec2_row_cond[of i "(\<psi>\<^sub>1\<^sub>0 1)" "(\<psi>\<^sub>1\<^sub>0 n)" ] a0 a1 f0
      by (metis dim_col_mat(1) dim_row_mat(1) index_tensor_mat_with_vec2_row_cond power_Suc power_one_right)  
    then have "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,0) = 1/sqrt(2) * 1/(sqrt 2)^n"
      using \<psi>\<^sub>1\<^sub>0_values[of "i -dim_row (\<psi>\<^sub>1\<^sub>0 n)" "n" "j"] a0 a1 by simp
    then show  "((\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)) $$ (i,j) = (\<psi>\<^sub>1\<^sub>0 (Suc n)) $$ (i,j)" 
      using f0 f1 divide_divide_eq_left power_Suc by simp
  qed
qed

lemma \<psi>\<^sub>1\<^sub>0_tensor_is_state:
  assumes "n \<ge> 1"
  shows "state n ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>)"  
  using iter_tensor_of_state_is_state ket_zero_is_state assms by fastforce

lemma iter_tensor_of_H_is_gate:
  assumes "n \<ge> 1"
  shows "gate n (H \<otimes>\<^bsup>n\<^esup>)" 
  using iter_tensor_of_gate_is_gate H_is_gate assms by fastforce

lemma iter_tensor_of_H_on_zero_tensor: 
  assumes "n \<ge> 1"
  shows "(H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>) = \<psi>\<^sub>1\<^sub>0 n"
  using assms
proof(rule nat_induct_at_least)
  show "(H \<otimes>\<^bsup>1\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>1\<^esup>) = \<psi>\<^sub>1\<^sub>0 1"
    using H_on_ket_zero by simp
next
  fix n:: nat
  assume a0: "n \<ge> 1" and IH: "(H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>) = \<psi>\<^sub>1\<^sub>0 n"
  then have "(H \<otimes>\<^bsup>(Suc n)\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>(Suc n)\<^esup>) = (H * |zero\<rangle>) \<Otimes> ((H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>))" 
    using iter_tensor_mult_distr[of "n" "H" "|zero\<rangle>"] a0 ket_vec_def H_def by(simp add: H_def) 
  also have  "... = (H * |zero\<rangle>) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)" using IH by simp 
  also have "... = (\<psi>\<^sub>1\<^sub>0 1) \<Otimes> (\<psi>\<^sub>1\<^sub>0 n)" using H_on_ket_zero by simp
  also have "... = (\<psi>\<^sub>1\<^sub>0 (Suc n))" using \<psi>\<^sub>1\<^sub>0_tensor a0 by simp
  finally show "(H \<otimes>\<^bsup>(Suc n)\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>(Suc n)\<^esup>) = (\<psi>\<^sub>1\<^sub>0 (Suc n))" by simp
qed

lemma \<psi>\<^sub>1\<^sub>0_is_state:
  assumes "n \<ge> 1"
  shows "state n (\<psi>\<^sub>1\<^sub>0 n)"
  using iter_tensor_of_H_is_gate \<psi>\<^sub>1\<^sub>0_tensor_is_state assms gate_on_state_is_state iter_tensor_of_H_on_zero_tensor assms by metis

abbreviation \<psi>\<^sub>1\<^sub>1:: "complex Matrix.mat" where
"\<psi>\<^sub>1\<^sub>1 \<equiv> Matrix.mat 2 1 (\<lambda>(i,j). if i=0 then 1/sqrt(2) else -1/sqrt(2))"

lemma H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1: 
  shows "(H * |one\<rangle>) = \<psi>\<^sub>1\<^sub>1"
proof 
  fix i j:: nat
  assume "i < dim_row \<psi>\<^sub>1\<^sub>1" and "j < dim_col \<psi>\<^sub>1\<^sub>1"
  then have "i \<in> {0,1} \<and> j = 0" by (simp add: less_2_cases)
  then show "(H * |one\<rangle>) $$ (i,j) = \<psi>\<^sub>1\<^sub>1 $$ (i,j)"
    by (auto simp add: times_mat_def scalar_prod_def H_def ket_vec_def)
next
  show "dim_row (H * |one\<rangle>) = dim_row \<psi>\<^sub>1\<^sub>1" by (simp add: H_def)
next 
  show "dim_col (H * |one\<rangle>) = dim_col \<psi>\<^sub>1\<^sub>1" by (simp add: H_def ket_vec_def)
qed

abbreviation \<psi>\<^sub>1:: "nat \<Rightarrow> complex Matrix.mat" where
"\<psi>\<^sub>1 n \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if even i then 1/(sqrt 2)^(n+1) else -1/(sqrt 2)^(n+1))"

lemma \<psi>\<^sub>1_values_even[simp]:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1 n)" and "j < dim_col (\<psi>\<^sub>1 n)" and "even i"
  shows "(\<psi>\<^sub>1 n) $$ (i,j) = 1/(sqrt 2)^(n+1)" 
  using assms case_prod_conv by simp

lemma \<psi>\<^sub>1_values_odd [simp]:
  fixes i j n
  assumes "i < dim_row (\<psi>\<^sub>1 n)" and "j < dim_col (\<psi>\<^sub>1 n)" and "odd i"
  shows "(\<psi>\<^sub>1 n) $$ (i,j) = -1/(sqrt 2)^(n+1)" 
  using assms case_prod_conv by simp

lemma "\<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1":
  assumes "n \<ge> 1"
  shows "(\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1 = \<psi>\<^sub>1 n" 
proof 
 show "dim_col ((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) = dim_col (\<psi>\<^sub>1 n)" by simp
next
  show "dim_row ((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) = dim_row (\<psi>\<^sub>1 n)" by simp
next
  fix i j:: nat
  assume a0: "i < dim_row (\<psi>\<^sub>1 n)" and a1: "j < dim_col (\<psi>\<^sub>1 n)"
  then have "i < 2^(n+1)" and "j = 0" by auto 
  then have f0: "((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) $$ (i,j) = 1/(sqrt 2)^n * \<psi>\<^sub>1\<^sub>1 $$ (i mod 2, j)" 
    using \<psi>\<^sub>1\<^sub>0_values[of "i div 2" n "j div 1"] a0 a1 by simp
  show "((\<psi>\<^sub>1\<^sub>0 n) \<Otimes> \<psi>\<^sub>1\<^sub>1) $$ (i,j) = (\<psi>\<^sub>1 n) $$ (i,j)" 
    using f0 \<psi>\<^sub>1_values_even \<psi>\<^sub>1_values_odd a0 a1 by auto 
qed

lemma \<psi>\<^sub>1_is_state:
  assumes "n \<ge> 1"
  shows "state (n+1) (\<psi>\<^sub>1 n)" 
  using assms \<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1 \<psi>\<^sub>1\<^sub>0_is_state H_on_ket_one_is_state H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 tensor_state by metis

abbreviation (in jozsa) \<psi>\<^sub>2:: "complex Matrix.mat" where
"\<psi>\<^sub>2 \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). if even i then (-1)^f(i div 2)/(sqrt 2)^(n+1) 
                                        else (-1)^(f(i div 2)+1)/(sqrt 2)^(n+1))"

lemma (in jozsa) \<psi>\<^sub>2_values_even [simp]:
  fixes i j 
  assumes "i < dim_row \<psi>\<^sub>2 " and "j < dim_col \<psi>\<^sub>2" and "even i"
  shows "\<psi>\<^sub>2 $$ (i,j) = (-1)^f(i div 2)/(sqrt 2)^(n+1)" 
  using assms case_prod_conv by simp

lemma (in jozsa) \<psi>\<^sub>2_values_odd [simp]:
  fixes i j 
  assumes "i < dim_row \<psi>\<^sub>2" and "j < dim_col \<psi>\<^sub>2" and "odd i"
  shows "\<psi>\<^sub>2 $$ (i,j) = (-1)^(f(i div 2)+1)/(sqrt 2)^(n+1)" 
  using assms case_prod_conv by simp

lemma (in jozsa) \<psi>\<^sub>2_values_odd_hidden [simp]:
  assumes "2*k+1 < dim_row \<psi>\<^sub>2" and "j < dim_col \<psi>\<^sub>2" 
  shows "\<psi>\<^sub>2 $$ (2*k+1,j) = ((-1)^(f((2*k+1) div 2)+1))/(sqrt 2)^(n+1)" 
  using assms by simp

lemma (in jozsa) snd_rep_of_\<psi>\<^sub>2:
  assumes "i < dim_row \<psi>\<^sub>2"
  shows "((1-f(i div 2)) + -f(i div 2)) * 1/(sqrt 2)^(n+1) = (-1)^f(i div 2)/(sqrt 2)^(n+1)"
    and "(-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt 2)^(n+1) = (-1)^(f(i div 2)+1)/(sqrt 2)^(n+1)"
proof- 
  have "i div 2 \<in> {i. i < 2 ^ n}" 
    using assms by auto
  then have "real (Suc 0 - f (i div 2)) - real (f (i div 2)) = (- 1) ^ f (i div 2)" 
    using assms f_values by auto
  thus "((1-f(i div 2)) + -f(i div 2)) * 1/(sqrt 2)^(n+1) = (-1)^f(i div 2)/(sqrt 2)^(n+1)" by auto
next
  have "i div 2 \<in> {i. i < 2^n}" 
    using assms by simp
  then have "(real (f (i div 2)) - real (Suc 0 - f (i div 2))) / (sqrt 2 ^ (n+1)) =
           - ((- 1) ^ f (i div 2) / (sqrt 2 ^ (n+1)))" 
   using assms f_values by fastforce
  then show "(-(1-f(i div 2))+(f(i div 2)))* 1/(sqrt 2)^(n+1) = (-1)^(f(i div 2)+1)/(sqrt 2)^(n+1)" by simp
qed

lemma (in jozsa) jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2:
  shows "U\<^sub>f * (\<psi>\<^sub>1 n) = \<psi>\<^sub>2" 
proof 
  show "dim_row (U\<^sub>f * (\<psi>\<^sub>1 n)) = dim_row \<psi>\<^sub>2" by simp
next
  show "dim_col (U\<^sub>f * (\<psi>\<^sub>1 n)) = dim_col \<psi>\<^sub>2" by simp
next
  fix i j ::nat
  assume a0: "i < dim_row \<psi>\<^sub>2" and a1: "j < dim_col \<psi>\<^sub>2"
  then have f0:"i \<in> {0..2^(n+1)} \<and> j=0" by simp
  then have f1: "i < dim_row U\<^sub>f \<and> j < dim_col U\<^sub>f " using a0 by simp
  have f2: "i < dim_row (\<psi>\<^sub>1 n) \<and> j < dim_col (\<psi>\<^sub>1 n)" using a0 a1 by simp
  show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)"
  proof (rule disjE)
    show "even i \<or> odd i" by auto
  next
    assume a2: "even i"
    then have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (\<Sum>k \<in> {i,i+1}. U\<^sub>f $$ (i,k) * (\<psi>\<^sub>1 n) $$ (k,j))"
      using f1 f2 U\<^sub>f_mult_without_empty_summands_even[of i j "(\<psi>\<^sub>1 n)"] by simp 
    moreover have "U\<^sub>f $$ (i,i) * (\<psi>\<^sub>1 n) $$ (i,j) = (1-f(i div 2))* 1/(sqrt 2)^(n+1)" 
      using f0 f1 a2 by simp
    moreover have "U\<^sub>f $$ (i,i+1) * (\<psi>\<^sub>1 n) $$ (i+1,j) = (-f(i div 2))* 1/(sqrt 2)^(n+1)" 
      using f0 f1 a2 by auto
    ultimately have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (1-f(i div 2))* 1/(sqrt 2)^(n+1) + (-f(i div 2))* 1/(sqrt 2)^(n+1)" by simp
    also have "... = ((1-f(i div 2))+-f(i div 2)) * 1/(sqrt 2)^(n+1)" 
      using add_divide_distrib 
      by (metis (no_types, hide_lams) mult.right_neutral of_int_add of_int_of_nat_eq)
    also have "... = \<psi>\<^sub>2 $$ (i,j)" 
      using a0 a1 a2 snd_rep_of_\<psi>\<^sub>2 by simp
    finally show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)" by simp
  next 
    assume a2: "odd i"
    then have f6: "i\<ge>1"  
    using linorder_not_less by auto
    have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i,k) * (\<psi>\<^sub>1 n) $$ (k,j))"
      using f1 f2 a2 U\<^sub>f_mult_without_empty_summands_odd[of i j "(\<psi>\<^sub>1 n)"]  
      by (metis dim_row_mat(1) jozsa_transform_dim(2)) 
    moreover have "(\<Sum>k \<in> {i-1,i}. U\<^sub>f $$ (i,k) * (\<psi>\<^sub>1 n) $$ (k,j)) 
                 = U\<^sub>f $$ (i,i-1) * (\<psi>\<^sub>1 n) $$ (i-1,j) +  U\<^sub>f $$ (i,i) * (\<psi>\<^sub>1 n) $$ (i,j)" 
      using a2 f6 by simp
    moreover have  "U\<^sub>f $$ (i,i) * (\<psi>\<^sub>1 n) $$ (i,j) = (1-f(i div 2))* -1/(sqrt 2)^(n+1)" 
      using f1 f2 a2 by simp
    moreover have "U\<^sub>f $$ (i,i-1) * (\<psi>\<^sub>1 n) $$ (i-1,j) = f(i div 2)* 1/(sqrt 2)^(n+1)" 
      using a0 a1 a2 by simp
    ultimately have "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = (1-f(i div 2))* -1/(sqrt 2)^(n+1) +(f(i div 2))* 1/(sqrt 2)^(n+1)" 
      using of_real_add by simp
    also have "... = (-(1-f(i div 2)) + (f(i div 2))) * 1/(sqrt 2)^(n+1)" 
      by (metis (no_types, hide_lams) mult.right_neutral add_divide_distrib mult_minus1_right 
          of_int_add of_int_of_nat_eq)
    also have "... = (-1)^(f(i div 2)+1)/(sqrt 2)^(n+1)" 
       using a0 a1 a2 snd_rep_of_\<psi>\<^sub>2 by simp
   finally show "(U\<^sub>f * (\<psi>\<^sub>1 n)) $$ (i,j) = \<psi>\<^sub>2 $$ (i,j)" 
      using a0 a1 a2 by simp
  qed
qed

lemma (in jozsa) \<psi>\<^sub>2_is_state:
  shows "state (n+1) \<psi>\<^sub>2" 
  using jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2 jozsa_transform_is_gate \<psi>\<^sub>1_is_state dim gate_on_state_is_state by fastforce

text \<open>@{text "H^\<^sub>\<otimes> n"} is the result of taking the nth tensor product of H\<close>

abbreviation iter_tensor_of_H_rep:: "nat \<Rightarrow> complex Matrix.mat" ("H^\<^sub>\<otimes> _") where
"iter_tensor_of_H_rep n \<equiv> Matrix.mat (2^n) (2^n) (\<lambda>(i,j).(-1)^(i \<cdot>\<^bsub>n\<^esub> j)/(sqrt 2)^n)"

lemma tensor_of_H_values [simp]:
  fixes n i j:: nat
  assumes "i < dim_row (H^\<^sub>\<otimes> n)" and "j < dim_col (H^\<^sub>\<otimes> n)"
  shows "(H^\<^sub>\<otimes> n) $$ (i,j) = (-1)^(i \<cdot>\<^bsub>n\<^esub> j)/(sqrt 2)^n"
  using assms by simp

lemma dim_row_of_iter_tensor_of_H [simp]:
  assumes "n \<ge> 1"
  shows "1 < dim_row (H^\<^sub>\<otimes> n)" 
  using assms by(metis One_nat_def Suc_1 dim_row_mat(1) le_trans lessI linorder_not_less one_less_power)

lemma iter_tensor_of_H_fst_pos:
  fixes n i j:: nat
  assumes "i < 2^n \<or> j < 2^n" and "i < 2^(n+1) \<and> j < 2^(n+1)"
  shows "(H^\<^sub>\<otimes> (Suc n)) $$ (i,j) = 1/sqrt(2) * ((H^\<^sub>\<otimes> n) $$ (i mod 2^n, j mod 2^n))"
proof-
  have "(H^\<^sub>\<otimes> (Suc n)) $$ (i,j) = (-1)^(bip i (Suc n) j)/(sqrt 2)^(Suc n)"
    using assms by simp
  moreover have "bip i (Suc n) j = bip (i mod 2^n) n (j mod 2^n)" 
    using bitwise_inner_prod_fst_el_0 assms(1) by simp 
  ultimately show ?thesis 
    using bitwise_inner_prod_def by simp
qed

lemma iter_tensor_of_H_fst_neg:
  fixes n i j:: nat
  assumes "i \<ge> 2^n \<and> j \<ge> 2^n" and "i < 2^(n+1) \<and> j < 2^(n+1)"
  shows "(H^\<^sub>\<otimes> (Suc n)) $$ (i,j) = -1/sqrt(2) * (H^\<^sub>\<otimes> n) $$ (i mod 2^n, j mod 2^n)"
proof-
  have "(H^\<^sub>\<otimes> (Suc n)) $$ (i,j) = (-1)^(bip i (n+1) j)/(sqrt 2)^(n+1)" 
    using assms(2) by simp
  moreover have "bip i (n+1) j = 1 + bip (i mod 2^n) n (j mod 2^n)" 
    using bitwise_inner_prod_fst_el_is_1 assms by simp
  ultimately show ?thesis by simp
qed 

lemma H_tensor_iter_tensor_of_H:   
  fixes n:: nat
  shows  "(H \<Otimes> H^\<^sub>\<otimes> n) = H^\<^sub>\<otimes> (Suc n)" 
proof
  fix i j:: nat
  assume a0: "i < dim_row (H^\<^sub>\<otimes> (Suc n))" and a1: "j < dim_col (H^\<^sub>\<otimes> (Suc n))"
  then have f0: "i \<in> {0..<2^(n+1)} \<and> j \<in> {0..<2^(n+1)}" by simp
  then have f1: "(H \<Otimes> H^\<^sub>\<otimes> n) $$ (i,j) = H $$ (i div (dim_row (H^\<^sub>\<otimes> n)),j div (dim_col (H^\<^sub>\<otimes> n))) 
                                       * (H^\<^sub>\<otimes> n) $$ (i mod (dim_row (H^\<^sub>\<otimes> n)),j mod (dim_col (H^\<^sub>\<otimes> n)))"
    by (simp add: H_without_scalar_prod)
  show "(H \<Otimes> H^\<^sub>\<otimes> n) $$ (i,j) = (H^\<^sub>\<otimes> (Suc n)) $$ (i,j)"
  proof (rule disjE) 
    show "(i < 2^n \<or> j < 2^n) \<or> \<not>(i < 2^n \<or> j < 2^n)" by auto
  next
    assume a2: "(i < 2^n \<or> j < 2^n)"
    then have "(H^\<^sub>\<otimes> (Suc n)) $$ (i,j) = 1/sqrt(2) * ((H^\<^sub>\<otimes> n) $$ (i mod 2^n, j mod 2^n))" 
      using a0 a1 f0 iter_tensor_of_H_fst_pos by (metis (mono_tags, lifting) atLeastLessThan_iff)
    moreover have "H $$ (i div (dim_row (H^\<^sub>\<otimes> n)),j div (dim_col (H^\<^sub>\<otimes> n))) = 1/sqrt 2"
      using a0 a1 f0 H_without_scalar_prod H_values a2
      by (metis (no_types, lifting) dim_col_mat(1) dim_row_mat(1) div_less le_eq_less_or_eq 
          le_numeral_extra(2) less_power_add_imp_div_less plus_1_eq_Suc power_one_right) 
    ultimately show "(H \<Otimes> H^\<^sub>\<otimes> n) $$ (i,j) = (H^\<^sub>\<otimes> (Suc n)) $$ (i,j)" 
      using f1 by simp
  next 
    assume a2: "\<not>(i < 2^n \<or> j < 2^n)"
    then have "i \<ge> 2^n \<and> j \<ge> 2^n" by simp
    then have f2:"(H^\<^sub>\<otimes> (Suc n)) $$ (i,j) = -1/sqrt(2) * ((H^\<^sub>\<otimes> n) $$ (i mod 2^n, j mod 2^n))" 
      using a0 a1 f0 iter_tensor_of_H_fst_neg by simp
    have "i div (dim_row (H^\<^sub>\<otimes> n)) =1" and "j div (dim_row (H^\<^sub>\<otimes> n)) = 1"  
      using a2 a0 a1 by auto
    then have "H $$ (i div (dim_row (H^\<^sub>\<otimes> n)),j div (dim_col (H^\<^sub>\<otimes> n))) = -1/sqrt 2"
      using a0 a1 f0 H_values_right_bottom[of "i div (dim_row (H^\<^sub>\<otimes> n))" "j div (dim_col (H^\<^sub>\<otimes> n))"] a2 
      by fastforce
    then show "(H \<Otimes> H^\<^sub>\<otimes> n) $$ (i,j) = (H^\<^sub>\<otimes> (Suc n)) $$ (i,j)" 
      using f1 f2 by simp
  qed
next
  show "dim_row (H \<Otimes> H^\<^sub>\<otimes> n) = dim_row (H^\<^sub>\<otimes> (Suc n))" 
    by (simp add: H_without_scalar_prod) 
next
  show "dim_col (H \<Otimes> H^\<^sub>\<otimes> n) = dim_col (H^\<^sub>\<otimes> (Suc n))" 
    by (simp add: H_without_scalar_prod) 
qed

text \<open>
We prove that @{term "H^\<^sub>\<otimes> n"} is indeed the matrix representation of @{term "H \<otimes>\<^bsup>n\<^esup>"}, the iterated 
tensor product of the Hadamard gate H.
\<close>

lemma one_tensor_of_H_is_H:
  shows "(H^\<^sub>\<otimes> 1) = H"
proof(rule eq_matI)
  show "dim_row (H^\<^sub>\<otimes> 1) = dim_row H"
    by (simp add: H_without_scalar_prod)
  show "dim_col (H^\<^sub>\<otimes> 1) = dim_col H"
    by (simp add: H_without_scalar_prod)
next
  fix i j:: nat
  assume a0:"i < dim_row H" and a1:"j < dim_col H"
  then show "(H^\<^sub>\<otimes> 1) $$ (i,j) = H $$ (i,j)"
  proof-
    have "(H^\<^sub>\<otimes> 1) $$ (0, 0) = 1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
    moreover have "(H^\<^sub>\<otimes> 1) $$ (0,1) = 1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
    moreover have "(H^\<^sub>\<otimes> 1) $$ (1,0) = 1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
    moreover have "(H^\<^sub>\<otimes> 1) $$ (1,1) = -1/sqrt(2)" 
       using bitwise_inner_prod_def bin_rep_def by simp 
     ultimately show "(H^\<^sub>\<otimes> 1) $$ (i,j) = H $$ (i,j)" 
       using a0 a1 H_values H_values_right_bottom
       by (metis (no_types, lifting) H_without_scalar_prod One_nat_def dim_col_mat(1) dim_row_mat(1) 
divide_minus_left less_2_cases)
  qed
qed

lemma iter_tensor_of_H_rep_is_correct:
  fixes n:: nat
  assumes "n \<ge> 1"
  shows "(H \<otimes>\<^bsup>n\<^esup>) = H^\<^sub>\<otimes> n"
  using assms
proof(rule nat_induct_at_least)
  show "(H \<otimes>\<^bsup>1\<^esup>) = H^\<^sub>\<otimes> 1" 
    using one_tensor_is_id one_tensor_of_H_is_H by simp
next
  fix n:: nat
  assume a0:"n \<ge> 1" and IH:"(H \<otimes>\<^bsup>n\<^esup>) = H^\<^sub>\<otimes> n"
  then have "(H \<otimes>\<^bsup>(Suc n)\<^esup>) = H \<Otimes> (H \<otimes>\<^bsup>n\<^esup>)" 
    using iter_tensor_suc Nat.Suc_eq_plus1 by metis
  also have "... = H \<Otimes> (H^\<^sub>\<otimes> n)" 
    using IH by simp
  also have "... = H^\<^sub>\<otimes> (Suc n)" 
    using a0 H_tensor_iter_tensor_of_H by simp
  finally show "(H \<otimes>\<^bsup>(Suc n)\<^esup>) = H^\<^sub>\<otimes> (Suc n)" 
    by simp
qed

text \<open>@{text "HId^\<^sub>\<otimes> 1"} is the result of taking the tensor product of the nth tensor of H and Id 1 \<close>

abbreviation tensor_of_H_tensor_Id:: "nat \<Rightarrow> complex Matrix.mat" ("HId^\<^sub>\<otimes> _") where
"tensor_of_H_tensor_Id n \<equiv> Matrix.mat (2^(n+1)) (2^(n+1)) (\<lambda>(i,j).
  if (i mod 2 = j mod 2) then (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2))/(sqrt 2)^n else 0)"

lemma mod_2_is_both_even_or_odd:
  "((even i \<and> even j) \<or> (odd i \<and> odd j)) \<longleftrightarrow> (i mod 2 = j mod 2)" 
  by (metis even_iff_mod_2_eq_zero odd_iff_mod_2_eq_one)
  
lemma HId_values [simp]:
  assumes "n \<ge> 1" and "i < dim_row (HId^\<^sub>\<otimes> n)" and "j < dim_col (HId^\<^sub>\<otimes> n)"
  shows "even i \<and> even j \<longrightarrow> (HId^\<^sub>\<otimes> n) $$ (i,j) = (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2))/(sqrt 2)^n"
and "odd i \<and> odd j \<longrightarrow> (HId^\<^sub>\<otimes> n) $$ (i,j) = (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2))/(sqrt 2)^n"
and "(i mod 2 = j mod 2) \<longrightarrow> (HId^\<^sub>\<otimes> n) $$ (i,j) = (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> (j div 2))/(sqrt 2)^n"
and "\<not>(i mod 2 = j mod 2) \<longrightarrow> (HId^\<^sub>\<otimes> n) $$ (i,j) = 0"
  using assms mod_2_is_both_even_or_odd by auto

lemma iter_tensor_of_H_tensor_Id_is_HId:
  shows "(H^\<^sub>\<otimes> n) \<Otimes> Id 1 = HId^\<^sub>\<otimes> n"
proof
  show "dim_row ((H^\<^sub>\<otimes> n) \<Otimes> Id 1) = dim_row (HId^\<^sub>\<otimes> n)" 
    by (simp add: Quantum.Id_def)
  show "dim_col ((H^\<^sub>\<otimes> n) \<Otimes> Id 1) = dim_col (HId^\<^sub>\<otimes> n)" 
    by (simp add: Quantum.Id_def)
next
  fix i j:: nat
  assume a0: "i < dim_row (HId^\<^sub>\<otimes> n)" and a1: "j < dim_col (HId^\<^sub>\<otimes> n)"
  then have f0: "i < (2^(n+1)) \<and> j < (2^(n+1))" by simp
  then have "i < dim_row (H^\<^sub>\<otimes> n) * dim_row (Id 1) \<and> j < dim_col (H^\<^sub>\<otimes> n) * dim_col (Id 1)"   
    using Id_def by simp
  moreover have "dim_col (H^\<^sub>\<otimes> n) \<ge> 0 \<and> dim_col (Id 1) \<ge> 0"  
    using Id_def by simp
  ultimately have f1: "((H^\<^sub>\<otimes> n) \<Otimes> (Id 1)) $$ (i,j) 
    = (H^\<^sub>\<otimes> n) $$ (i div (dim_row (Id 1)),j div (dim_col (Id 1))) * 
      (Id 1) $$ (i mod (dim_row (Id 1)),j mod (dim_col (Id 1)))"
    by (simp add: Quantum.Id_def)
  show "((H^\<^sub>\<otimes> n)\<Otimes>Id 1) $$ (i,j) = (HId^\<^sub>\<otimes> n) $$ (i,j)" 
  proof (rule disjE)
    show "(i mod 2 = j mod 2) \<or> \<not> (i mod 2 = j mod 2)" by simp
  next
    assume a2:"(i mod 2 = j mod 2)"
    then have "(Id 1) $$ (i mod (dim_row (Id 1)),j mod (dim_col (Id 1))) = 1" 
      by (simp add: Quantum.Id_def)
    moreover have "(H^\<^sub>\<otimes> n) $$ (i div (dim_row (Id 1)), j div (dim_col (Id 1))) 
                    = (-1)^((i div (dim_row (Id 1))) \<cdot>\<^bsub>n\<^esub> (j div (dim_col (Id 1))))/(sqrt 2)^n" 
      using tensor_of_H_values Id_def f0 less_mult_imp_div_less by simp
    ultimately show "((H^\<^sub>\<otimes> n) \<Otimes> Id 1) $$ (i,j) = (HId^\<^sub>\<otimes> n) $$ (i,j)" 
      using a2 f0 f1 Id_def by simp
  next
    assume a2: "\<not>(i mod 2 = j mod 2)" 
    then have "(Id 1) $$ (i mod (dim_row (Id 1)),j mod (dim_col (Id 1))) = 0" 
      by (simp add: Quantum.Id_def)
    then show "((H^\<^sub>\<otimes> n) \<Otimes> Id 1) $$ (i,j) = (HId^\<^sub>\<otimes> n) $$ (i,j)" 
      using a2 f0 f1 by simp
  qed
qed

lemma HId_is_gate:
  assumes "n \<ge> 1"
  shows "gate (n+1) (HId^\<^sub>\<otimes> n)" 
proof- 
  have "(HId^\<^sub>\<otimes> n) = (H^\<^sub>\<otimes> n) \<Otimes> Id 1" 
    using iter_tensor_of_H_tensor_Id_is_HId by simp
  moreover have "gate 1 (Id 1)" 
    using id_is_gate by simp
  moreover have "gate n (H^\<^sub>\<otimes> n)"
    using H_is_gate iter_tensor_of_gate_is_gate[of 1 H n] assms by(simp add: iter_tensor_of_H_rep_is_correct)
  ultimately show "gate (n+1) (HId^\<^sub>\<otimes> n)" 
    using tensor_gate by presburger
qed

text \<open>State @{term "\<psi>\<^sub>3"} is obtained by the multiplication of @{term "HId^\<^sub>\<otimes> n"} and @{term "\<psi>\<^sub>2"}\<close>

abbreviation (in jozsa) \<psi>\<^sub>3:: "complex Matrix.mat" where
"\<psi>\<^sub>3 \<equiv> Matrix.mat (2^(n+1)) 1 (\<lambda>(i,j). 
if even i 
  then (\<Sum>k<2^n. (-1)^(f(k) + ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/((sqrt 2)^n * (sqrt 2)^(n+1))) 
    else  (\<Sum>k<2^n. (-1)^(f(k)+ 1 + ((i div 2) \<cdot>\<^bsub>n\<^esub> k)) /((sqrt 2)^n * (sqrt 2)^(n+1))))"

lemma (in jozsa) \<psi>\<^sub>3_values:
  assumes "i < dim_row \<psi>\<^sub>3"
  shows "odd i \<longrightarrow> \<psi>\<^sub>3 $$ (i,0) = (\<Sum>k<2^n. (-1)^(f(k) + 1 + ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/((sqrt 2)^n * (sqrt 2)^(n+1)))"
  using assms by simp

lemma (in jozsa) \<psi>\<^sub>3_dim [simp]:
  shows "1 < dim_row \<psi>\<^sub>3"
  using dim_row_mat(1) nat_neq_iff by fastforce

lemma sum_every_odd_summand_is_zero:
  fixes n:: nat 
  assumes "n \<ge> 1"
  shows "\<forall>f::(nat \<Rightarrow> complex).(\<forall>i. i<2^(n+1) \<and> odd i \<longrightarrow> f i = 0) \<longrightarrow> 
            (\<Sum>k\<in>{0..<2^(n+1)}. f k) = (\<Sum>k\<in>{0..<2^n}. f (2*k))"
  using assms
proof(rule nat_induct_at_least)
  show "\<forall>f::(nat \<Rightarrow> complex).(\<forall>i. i<2^(1+1) \<and> odd i \<longrightarrow> f i = 0) \<longrightarrow>
            (\<Sum>k\<in>{0..<2^(1+1)}. f k) = (\<Sum>k \<in> {0..<2^1}. f (2*k))"
  proof(rule allI,rule impI)
    fix f:: "(nat \<Rightarrow> complex)"
    assume asm: "(\<forall>i. i<2^(1+1) \<and> odd i \<longrightarrow> f i = 0)" 
    moreover have "(\<Sum>k\<in>{0..<4}. f k) = f 0 + f 1 + f 2 + f 3" 
      by (simp add: add.commute add.left_commute)
    moreover have "f 1 = 0" 
      using asm by simp 
    moreover have "f 3 = 0" 
      using asm by simp 
    moreover have "(\<Sum>k\<in>{0..<2^1}. f (2*k)) = f 0 + f 2" 
      using add.commute add.left_commute by simp
    ultimately show "(\<Sum>k\<in>{0..<2^(1+1)}. f k) = (\<Sum>k\<in>{0..<2^1}. f (2*k))" 
      by simp
  qed
next
  fix n:: nat
  assume "n \<ge> 1"
  and IH: "\<forall>f::(nat \<Rightarrow>complex).(\<forall>i. i<2^(n+1) \<and> odd i \<longrightarrow> f i = 0) \<longrightarrow>
(\<Sum>k\<in>{0..<2^(n+1)}. f k) = (\<Sum>k\<in>{0..<2^n}. f (2*k))" 
  show "\<forall>f::(nat \<Rightarrow>complex).(\<forall>i. i<2^(Suc n +1) \<and> odd i \<longrightarrow> f i = 0) \<longrightarrow>
(\<Sum>k\<in>{0..<2^(Suc n +1)}. f k) = (\<Sum>k\<in>{0..< 2^(Suc n)}. f (2*k))" 
  proof (rule allI,rule impI)
    fix f::"nat \<Rightarrow> complex"
    assume asm: "(\<forall>i. i<2^(Suc n +1) \<and> odd i \<longrightarrow> f i = 0)"
    have f0: "(\<Sum>k\<in>{0..<2^(n+1)}. f k) = (\<Sum>k\<in>{0..<2^n}. f (2*k))" 
      using asm IH by simp
    have f1: "(\<Sum>k\<in>{0..<2^(n+1)}. (\<lambda>x. f (x+2^(n+1))) k) = (\<Sum>k\<in>{0..< 2^n}. (\<lambda>x. f (x+2^(n+1))) (2*k))" 
      using asm IH by simp
    have "(\<Sum>k\<in>{0..<2^(n+2)}. f k) = (\<Sum>k\<in>{0..<2^(n+1)}. f k) + (\<Sum>k\<in>{2^(n+1)..<2^(n+2)}. f k)"
      by (simp add: sum.atLeastLessThan_concat)
    also have "... = (\<Sum>k\<in>{0..<2^n}. f (2*k)) + (\<Sum>k\<in>{2^(n+1)..<2^(n+2)}. f k)"  
      using f0 by simp
    also have "... = (\<Sum>k\<in>{0..<2^n}. f (2*k)) + (\<Sum>k\<in>{0..<2^(n+1)}. f (k+2^(n+1)))"  
      using sum.shift_bounds_nat_ivl[of "f" "0" "2^(n+1)" "2^(n+1)"] by simp
    also have "... = (\<Sum>k\<in>{0..<2^n}. f (2*k)) + (\<Sum>k\<in>{0..< 2^n}. (\<lambda>x. f (x+2^(n+1))) (2*k))"
      using f1 by simp
    also have "... = (\<Sum>k\<in>{0..<2^n}. f (2*k)) + (\<Sum>k\<in>{2^n..< 2^(n+1)}. f (2 *k))"
      using sum.shift_bounds_nat_ivl[of "\<lambda>x. (f::nat\<Rightarrow>complex) (2*(x-2^n)+2^(n+1))" "0" "2^n" "2^n"] 
      by (simp add: mult_2)
    also have "... = (\<Sum>k \<in> {0..<2^(n+1)}. f (2*k))" 
      by (metis Suc_eq_plus1 lessI less_imp_le_nat one_le_numeral power_increasing sum.atLeastLessThan_concat zero_le)
    finally show "(\<Sum>k\<in>{0..<2^((Suc n)+1)}. f k) = (\<Sum>k\<in>{0..< 2^(Suc n)}. f (2*k))"
      by (metis Suc_eq_plus1 add_2_eq_Suc')
  qed
qed

lemma sum_every_even_summand_is_zero:
  fixes n:: nat 
  assumes "n \<ge> 1"
  shows "\<forall>f::(nat \<Rightarrow> complex).(\<forall>i. i<2^(n+1) \<and> even i \<longrightarrow> f i = 0) \<longrightarrow> 
            (\<Sum>k\<in>{0..<2^(n+1)}. f k) = (\<Sum>k\<in>{0..< 2^n}. f (2*k+1))"
  using assms
proof(rule nat_induct_at_least)
  show "\<forall>f::(nat \<Rightarrow> complex).(\<forall>i. i<2^(1+1) \<and> even i \<longrightarrow> f i = 0) \<longrightarrow> 
            (\<Sum>k\<in>{0..<2^(1+1)}. f k) = (\<Sum>k\<in>{0..< 2^1}. f (2*k+1))"
  proof(rule allI,rule impI)
    fix f:: "nat \<Rightarrow>complex"
    assume asm: "(\<forall>i. i<2^(1+1) \<and> even i \<longrightarrow> f i = 0)" 
    moreover have "(\<Sum>k\<in>{0..<4}. f k) = f 0 + f 1 + f 2 + f 3" 
      by (simp add: add.commute add.left_commute)
    moreover have "f 0 = 0" using asm by simp 
    moreover have "f 2 = 0" using asm by simp 
    moreover have "(\<Sum>k \<in> {0..< 2^1}. f (2*k+1)) = f 1 + f 3" 
      using add.commute add.left_commute by simp
    ultimately show "(\<Sum>k\<in>{0..<2^(1+1)}. f k) = (\<Sum>k\<in>{0..< 2^1}. f (2*k+1))" by simp
  qed
next
  fix n:: nat
  assume "n \<ge> 1"
  and IH: "\<forall>f::(nat \<Rightarrow>complex).(\<forall>i. i<2^(n+1) \<and> even i \<longrightarrow> f i = 0) \<longrightarrow>
(\<Sum>k\<in>{0..<2^(n+1)}. f k) = (\<Sum>k\<in>{0..< 2^n}. f (2*k+1))" 
  show "\<forall>f::(nat \<Rightarrow>complex).(\<forall>i. i<2^((Suc n)+1) \<and> even i \<longrightarrow> f i = 0) \<longrightarrow>
(\<Sum>k\<in>{0..<2^((Suc n)+1)}. f k) = (\<Sum>k\<in>{0..< 2^(Suc n)}. f (2*k+1))" 
  proof (rule allI,rule impI)
    fix f::"nat \<Rightarrow>complex"
    assume asm: "(\<forall>i. i<2^((Suc n)+1) \<and> even i \<longrightarrow> f i = 0)"
    have f0: "(\<Sum>k \<in>{0..<2^(n+1)}. f k) = (\<Sum>k \<in> {0..< 2^n}. f (2*k+1))" 
      using asm IH by simp
    have f1: "(\<Sum>k\<in>{0..<2^(n+1)}. (\<lambda>x. f (x+2^(n+1))) k) 
              = (\<Sum>k\<in>{0..< 2^n}. (\<lambda>x. f (x+2^(n+1))) (2*k+1))" 
      using asm IH by simp
    have "(\<Sum>k\<in>{0..<2^(n+2)}. f k) 
               = (\<Sum>k\<in>{0..<2^(n+1)}. f k) + (\<Sum>k\<in>{2^(n+1)..<2^(n+2)}. f k)"
      by (simp add: sum.atLeastLessThan_concat)
    also have "... = (\<Sum>k\<in>{0..< 2^n}. f (2*k+1)) + (\<Sum>k\<in>{2^(n+1)..<2^(n+2)}. f k)"  
      using f0 by simp
    also have "... = (\<Sum>k\<in>{0..< 2^n}. f (2*k+1)) + (\<Sum>k\<in>{0..<2^(n+1)}. f (k+(2^(n+1))))"  
      using sum.shift_bounds_nat_ivl[of "f" "0" "2^(n+1)" "2^(n+1)"] by simp
    also have "... = (\<Sum>k\<in>{0..< 2^n}. f (2*k+1)) + (\<Sum>k\<in>{0..< 2^n}. (\<lambda>x. f (x+2^(n+1))) (2*k+1))"
      using f1 by simp
    also have "... = (\<Sum>k\<in>{0..< 2^n}. f (2*k+1)) + (\<Sum>k\<in>{2^n..< 2^(n+1)}. f (2 *k+1))"
      using sum.shift_bounds_nat_ivl[of "\<lambda>x. (f::nat\<Rightarrow>complex) (2*(x-2^n)+1+2^(n+1))" "0" "2^n" "2^n"] 
      by (simp add: mult_2)
    also have "... = (\<Sum>k\<in>{0..< 2^(n+1)}. f (2*k+1))" 
      by (metis Suc_eq_plus1 lessI less_imp_le_nat one_le_numeral power_increasing sum.atLeastLessThan_concat zero_le)
    finally show "(\<Sum>k\<in>{0..<2^((Suc n)+1)}. f k) = (\<Sum>k\<in>{0..< 2^(Suc n)}. f (2*k+1))"
      by (metis Suc_eq_plus1 add_2_eq_Suc')
  qed
qed

lemma (in jozsa) iter_tensor_of_H_times_\<psi>\<^sub>2_is_\<psi>\<^sub>3:
  shows "((H^\<^sub>\<otimes> n) \<Otimes> Id 1) * \<psi>\<^sub>2 = \<psi>\<^sub>3"
proof
  fix i j
  assume a0:"i < dim_row \<psi>\<^sub>3" and a1:"j < dim_col \<psi>\<^sub>3" 
  then have f0: "i < (2^(n+1)) \<and> j = 0" by simp
  have f1: "((HId^\<^sub>\<otimes> n)* \<psi>\<^sub>2) $$ (i,j) = (\<Sum>k<(2^(n+1)). ((HId^\<^sub>\<otimes> n) $$ (i,k)) * (\<psi>\<^sub>2 $$ (k,j)))" 
    using a1 f0 by (simp add: atLeast0LessThan)
  show "(((H^\<^sub>\<otimes> n) \<Otimes> Id 1) * \<psi>\<^sub>2) $$ (i,j) = \<psi>\<^sub>3 $$ (i,j)"
  proof(rule disjE)
    show "even i \<or> odd i" by simp
  next
    assume a2: "even i"
    have "(\<not>(i mod 2 = k mod 2) \<and> k<dim_col (HId^\<^sub>\<otimes> n)) \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,k)) * (\<psi>\<^sub>2 $$ (k,j)) = 0" for k 
      using f0 by simp
    then have "k<(2^(n+1)) \<and> odd k \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,k)) * (\<psi>\<^sub>2 $$ (k,j)) = 0" for k 
      using a2 mod_2_is_both_even_or_odd f0 by (metis (no_types, lifting) dim_col_mat(1))
    then have "(\<Sum>k\<in>{(0::nat)..<(2^(n+1))}. ((HId^\<^sub>\<otimes> n) $$ (i,k)) * (\<psi>\<^sub>2 $$ (k,j)))
             = (\<Sum>k\<in>{(0::nat)..< (2^n)}. ((HId^\<^sub>\<otimes> n) $$ (i,2*k)) * (\<psi>\<^sub>2 $$ (2*k,j)))" 
      using sum_every_odd_summand_is_zero dim by simp
    moreover have "(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k)) * (\<psi>\<^sub>2 $$ (2*k,j))) 
                 = (\<Sum>k<2^n.(-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> k)/(sqrt(2)^n) *((-1)^f(k))/(sqrt(2)^(n+1)))" 
    proof-
        have "(even k \<and> k<dim_row \<psi>\<^sub>2) \<longrightarrow> (\<psi>\<^sub>2 $$ (k,j)) = ((-1)^f(k div 2))/(sqrt(2)^(n+1))" for k 
          using a0 a1 by simp
      then have "(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k)) * (\<psi>\<^sub>2 $$ (2*k,j))) 
               = (\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k)) *((-1)^f((2*k) div 2))/(sqrt(2)^(n+1)))" 
        by simp
      moreover have "(even k \<and> k<dim_col (HId^\<^sub>\<otimes> n))
                 \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,k)) = (-1)^ ((i div 2) \<cdot>\<^bsub>n\<^esub> (k div 2))/(sqrt(2)^n)" for k
        using a2 a0 a1 by simp
      ultimately have "(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k)) * (\<psi>\<^sub>2 $$ (2*k,j))) 
                     = (\<Sum>k<2^n. (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub>  ((2*k) div 2))/(sqrt(2)^n) * 
                                   ((-1)^f((2*k) div 2))/(sqrt(2)^(n+1)))" 
      by simp
      then show "(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k)) * (\<psi>\<^sub>2 $$ (2*k,j))) 
               = (\<Sum>k<2^n. (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub>  k)/(sqrt(2)^n) *((-1)^f(k))/(sqrt(2)^(n+1)))" 
        by simp
    qed
    ultimately have "((HId^\<^sub>\<otimes> n)* \<psi>\<^sub>2) $$ (i,j) = (\<Sum>k<2^n. (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> k)/(sqrt(2)^n) 
                                                        * ((-1)^f(k))/(sqrt(2)^(n+1)))" 
      using f1 by (metis atLeast0LessThan) 
    also have "... =  (\<Sum>k<2^n. (-1)^(f(k)+((i div 2) \<cdot>\<^bsub>n\<^esub> k))/((sqrt(2)^n)*(sqrt(2)^(n+1))))" 
      by (simp add: power_add mult.commute)
    finally have "((HId^\<^sub>\<otimes> n)* \<psi>\<^sub>2) $$ (i,j) = (\<Sum>k<2^n. (-1)^(f(k)+((i div 2) \<cdot>\<^bsub>n\<^esub> k))/((sqrt(2)^n)*(sqrt(2)^(n+1))))" 
       by simp
    moreover have "\<psi>\<^sub>3 $$ (i,j) = (\<Sum>k<2^n. (-1)^(f(k) + ((i div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n * sqrt(2)^(n+1)))" 
      using a0 a1 a2 by simp
    ultimately show "(((H^\<^sub>\<otimes> n) \<Otimes> Id 1)* \<psi>\<^sub>2) $$ (i,j) = \<psi>\<^sub>3 $$ (i,j)" 
      using iter_tensor_of_H_tensor_Id_is_HId dim by simp
  next
    assume a2: "odd i"
    have "(\<not>(i mod 2 = k mod 2) \<and> k<dim_col (HId^\<^sub>\<otimes> n)) \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,k)) * (\<psi>\<^sub>2 $$ (k,j)) = 0" for k 
      using f0 by simp
    then have "k<(2^(n+1)) \<and> even k \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,k)) * (\<psi>\<^sub>2 $$ (k,j)) = 0" for k 
      using a2 mod_2_is_both_even_or_odd f0 by (metis (no_types, lifting) dim_col_mat(1))
    then have "(\<Sum>k\<in>{0..<2^(n+1)}. ((HId^\<^sub>\<otimes> n) $$ (i,k)) * (\<psi>\<^sub>2 $$ (k,j)))
             = (\<Sum>k\<in>{0..<2^n}. ((HId^\<^sub>\<otimes> n) $$ (i,2*k+1)) * (\<psi>\<^sub>2 $$ (2*k+1,j)))" 
      using sum_every_even_summand_is_zero dim by simp
    moreover have "(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k+1)) * (\<psi>\<^sub>2 $$ (2*k+1,j))) 
                 = (\<Sum> k<2^n. (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> k)/(sqrt(2)^n) * ((-1)^(f(k)+1))/(sqrt(2)^(n+1)))" 
    proof-
      have "(odd k \<and> k<dim_row \<psi>\<^sub>2) \<longrightarrow> (\<psi>\<^sub>2 $$ (k,j)) = ((-1)^(f(k div 2)+1))/(sqrt(2)^(n+1))" for k 
        using a0 a1 a2 by simp
      then have f2:"(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k+1)) * (\<psi>\<^sub>2 $$ (2*k+1,j))) 
                  = (\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k+1)) * ((-1)^(f((2*k+1) div 2)+1))/(sqrt(2)^(n+1)))" 
        by simp
      have "i < dim_row (HId^\<^sub>\<otimes> n)" 
        using f0 a2 mod_2_is_both_even_or_odd by simp
      then have "((i mod 2 = k mod 2) \<and> k<dim_col (HId^\<^sub>\<otimes> n))
                 \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,k)) = (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> (k div 2))/(sqrt(2)^n) " for k
        using a2 a0 a1 f0 dim HId_values by simp
      moreover have "odd k \<longrightarrow> (i mod 2 = k mod 2)" for k 
        using a2 mod_2_is_both_even_or_odd by auto
      ultimately have "(odd k \<and> k<dim_col (HId^\<^sub>\<otimes> n))
                 \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,k)) = (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> (k div 2))/(sqrt(2)^n)" for k
        by simp
      then have "k<2^n \<longrightarrow> ((HId^\<^sub>\<otimes> n) $$ (i,2*k+1)) = (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> ((2*k+1) div 2))/(sqrt(2)^n) " for k
        by simp
      then have "(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k+1)) * (\<psi>\<^sub>2 $$ (2*k+1,j))) 
               = (\<Sum>k<2^n. (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> ((2*k+1) div 2))/(sqrt(2)^n) 
                             * ((-1)^(f((2*k+1) div 2)+1))/(sqrt(2)^(n+1)))" 
        using f2 by simp
      then show "(\<Sum>k<2^n. ((HId^\<^sub>\<otimes> n) $$ (i,2*k+1)) * (\<psi>\<^sub>2 $$ (2*k+1,j))) 
               = (\<Sum>k<2^n. (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> k)/(sqrt(2)^n) *((-1)^(f(k)+1))/(sqrt(2)^(n+1)))" 
        by simp
    qed
    ultimately have "((HId^\<^sub>\<otimes> n)* \<psi>\<^sub>2) $$ (i,j) = (\<Sum>k<2^n. (-1)^((i div 2) \<cdot>\<^bsub>n\<^esub> k)/(sqrt(2)^n) 
                * ((-1)^(f(k)+1))/(sqrt(2)^(n+1)))" 
      using f1 by (metis atLeast0LessThan) 
    also have "... = (\<Sum>k<2^n. (-1)^(f(k)+1+((i div 2) \<cdot>\<^bsub>n\<^esub> k))/((sqrt(2)^n)*(sqrt(2)^(n+1))))"
      by (simp add: mult.commute power_add)
    finally have "((HId^\<^sub>\<otimes> n)* \<psi>\<^sub>2) $$ (i,j) 
                = (\<Sum>k< 2^n. (-1)^(f(k)+1+((i div 2) \<cdot>\<^bsub>n\<^esub> k))/((sqrt(2)^n)*(sqrt(2)^(n+1))))" 
      by simp
    then show "(((H^\<^sub>\<otimes> n) \<Otimes> Id 1)* \<psi>\<^sub>2) $$ (i,j) = \<psi>\<^sub>3 $$ (i,j)" 
      using iter_tensor_of_H_tensor_Id_is_HId dim a2 a0 a1 by simp
  qed
next
  show "dim_row (((H^\<^sub>\<otimes> n) \<Otimes> Id 1) * \<psi>\<^sub>2) = dim_row \<psi>\<^sub>3"  
    using iter_tensor_of_H_tensor_Id_is_HId dim by simp
next
  show "dim_col (((H^\<^sub>\<otimes> n) \<Otimes> Id 1)* \<psi>\<^sub>2) = dim_col \<psi>\<^sub>3" 
    using iter_tensor_of_H_tensor_Id_is_HId dim by simp
qed

lemma (in jozsa) \<psi>\<^sub>3_is_state:
  shows "state (n+1) \<psi>\<^sub>3"
proof-
  have "((H^\<^sub>\<otimes> n) \<Otimes> Id 1) * \<psi>\<^sub>2 = \<psi>\<^sub>3" 
    using iter_tensor_of_H_times_\<psi>\<^sub>2_is_\<psi>\<^sub>3 by simp
  moreover have "gate (n+1) ((H^\<^sub>\<otimes> n) \<Otimes> Id 1)" 
    using iter_tensor_of_H_tensor_Id_is_HId HId_is_gate dim by simp
  moreover have "state (n+1) \<psi>\<^sub>2" 
    using \<psi>\<^sub>2_is_state by simp
  ultimately show "state (n+1) \<psi>\<^sub>3"
    using gate_on_state_is_state dim by (metis (no_types, lifting))
qed

text \<open>
Finally, all steps are put together. The result depends on the function f. If f is constant
the first n qubits are 0, if f is balanced there is at least one qubit in state 1 among the 
first n qubits. 
The algorithm only uses one evaluation of f(x) and will always succeed. 
\<close>

definition (in jozsa) jozsa_algo:: "complex Matrix.mat" where 
"jozsa_algo \<equiv> ((H \<otimes>\<^bsup>n\<^esup>) \<Otimes> Id 1) * (U\<^sub>f * (((H \<otimes>\<^bsup>n\<^esup>) * ( |zero\<rangle> \<otimes>\<^bsup>n\<^esup>)) \<Otimes> (H * |one\<rangle>)))"

lemma (in jozsa) jozsa_algo_result [simp]: 
  shows "jozsa_algo = \<psi>\<^sub>3" 
  using jozsa_algo_def H_on_ket_one_is_\<psi>\<^sub>1\<^sub>1 iter_tensor_of_H_on_zero_tensor \<psi>\<^sub>1\<^sub>0_tensor_\<psi>\<^sub>1\<^sub>1_is_\<psi>\<^sub>1
  jozsa_transform_times_\<psi>\<^sub>1_is_\<psi>\<^sub>2 iter_tensor_of_H_times_\<psi>\<^sub>2_is_\<psi>\<^sub>3 dim iter_tensor_of_H_rep_is_correct 
  by simp

lemma (in jozsa) jozsa_algo_result_is_state: 
  shows "state (n+1) jozsa_algo" 
  using \<psi>\<^sub>3_is_state by simp

lemma (in jozsa) prob0_fst_qubits_of_jozsa_algo: 
  shows "(prob0_fst_qubits n jozsa_algo) = (\<Sum>j\<in>{0,1}. (cmod(jozsa_algo $$ (j,0)))\<^sup>2)"
  using prob0_fst_qubits_eq by simp

text \<open>General lemmata required to compute probabilities.\<close>

lemma aux_comp_with_sqrt2:
  shows "(sqrt 2)^n * (sqrt 2)^n = 2^n"
  by (smt power_mult_distrib real_sqrt_mult_self)

lemma aux_comp_with_sqrt2_bis [simp]:
  shows "2^n/(sqrt(2)^n * sqrt(2)^(n+1)) = 1/sqrt 2"
  using aux_comp_with_sqrt2 by (simp add: mult.left_commute)

lemma aux_ineq_with_card: 
  fixes g:: "nat \<Rightarrow> nat" and A:: "nat set"
  assumes "finite A" 
  shows "(\<Sum>k\<in>A. (-1)^(g k)) \<le> card A" and "(\<Sum>k\<in>A. (-1)^(g k)) \<ge> -card A" 
   apply (smt assms neg_one_even_power neg_one_odd_power card_eq_sum of_nat_1 of_nat_sum sum_mono)
   apply (smt assms neg_one_even_power neg_one_odd_power card_eq_sum of_nat_1 of_nat_sum sum_mono sum_negf).

lemma aux_comp_with_cmod:
  fixes g:: "nat \<Rightarrow> nat"
  assumes "(\<forall>x<2^n. g x = 0) \<or> (\<forall>x<2^n. g x = 1)"
  shows "(cmod (\<Sum>k<2^n. (-1)^(g k)))\<^sup>2  = 2^(2*n)"
proof(rule disjE)
  show "(\<forall>x<2^n. g x = 0) \<or> (\<forall>x<2^n. g x = 1)" 
    using assms by simp
next
  assume "\<forall>x<2^n. g x = 0"
  then have "(cmod (\<Sum>k<2^n. (-1)^(g k)))\<^sup>2 = (2^n)\<^sup>2" 
    by (simp add: norm_power)
  then show "?thesis" 
    by (simp add: power_even_eq)
next 
  assume "\<forall>x<2^n. g x = 1" 
  then have "(cmod (\<Sum>k<2^n. (-1)^(g k)))\<^sup>2 = (2^n)\<^sup>2" 
    by (simp add: norm_power)
  then show "?thesis" 
    by (simp add: power_even_eq)
qed

lemma cmod_less:
  fixes a n:: int
  assumes "a < n" and "a > -n"
  shows "cmod a < n" 
  using assms by simp

lemma square_less:
  fixes a n:: real
  assumes "a < n" and "a > -n" 
  shows "a\<^sup>2 < n\<^sup>2"
  using assms by (smt power2_eq_iff power2_minus power_less_imp_less_base)

lemma cmod_square_real [simp]:
  fixes n:: real
  shows "(cmod n)\<^sup>2 = n\<^sup>2" 
  by simp

lemma aux_comp_sum_divide_cmod:
  fixes n:: nat and g:: "nat \<Rightarrow> int" and a:: real
  shows "(cmod(complex_of_real(\<Sum>k<n. g k / a)))\<^sup>2 = (cmod (\<Sum>k<n. g k) / a)\<^sup>2"
  by (metis cmod_square_real of_int_sum of_real_of_int_eq power_divide sum_divide_distrib)


text \<open>
The function is constant if and only if the first n qubits are 0. So, if the function is constant, 
then the probability of measuring 0 for the first n qubits is 1.
\<close>

lemma (in jozsa) prob0_jozsa_algo_of_const_0:
  assumes "const 0"
  shows "prob0_fst_qubits n jozsa_algo = 1"
proof-
  have "prob0_fst_qubits n jozsa_algo = (\<Sum>j\<in>{0,1}. (cmod(jozsa_algo $$ (j,0)))\<^sup>2)"
    using prob0_fst_qubits_of_jozsa_algo by simp
  moreover have "(cmod(jozsa_algo $$ (0,0)))\<^sup>2 = 1/2"
  proof-
    have "k<2^n \<longrightarrow> ((0 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k::nat 
      using bitwise_inner_prod_with_zero by simp 
    then have "(cmod(jozsa_algo $$ (0,0)))\<^sup>2 = (cmod(\<Sum>k::nat<2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      using jozsa_algo_result const_def assms by simp
    also have "... = (cmod((2::nat)^n/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"  by simp
    also have "... = (cmod(1/(sqrt(2))))\<^sup>2" 
      using aux_comp_with_sqrt2_bis by simp
    also have "... = 1/2" 
      by (simp add: norm_divide power2_eq_square)
    finally show "?thesis" by simp
  qed
  moreover have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 = 1/2"
  proof-
    have "k<2^n \<longrightarrow> ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k:: nat
      using bitwise_inner_prod_with_zero by simp
    then have "k<2^n \<longrightarrow> f k + 1 + ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 1" for k::nat 
      using const_def assms by simp
    moreover have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 
    = (cmod (\<Sum>k::nat<2^n. (-1)^(f k + 1 + ((1 div 2) \<cdot>\<^bsub>n\<^esub> k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using \<psi>\<^sub>3_dim by simp
    ultimately have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 = (cmod(\<Sum>k::nat<2^n. -1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      by (smt lessThan_iff power_one_right sum.cong)
    also have "... = (cmod(-1/(sqrt(2))))\<^sup>2" 
      using aux_comp_with_sqrt2_bis by simp
    also have "... = 1/2" 
      by (simp add: norm_divide power2_eq_square)
    finally show "?thesis" by simp
  qed
  ultimately have "prob0_fst_qubits n jozsa_algo = 1/2 + 1/2" by simp
  then show  "?thesis" by simp
qed

lemma (in jozsa) prob0_jozsa_algo_of_const_1:
  assumes "const 1"
  shows "prob0_fst_qubits n jozsa_algo = 1"
proof-
  have "prob0_fst_qubits n jozsa_algo = (\<Sum>j\<in>{0,1}. (cmod(jozsa_algo $$ (j,0)))\<^sup>2)"
    using prob0_fst_qubits_of_jozsa_algo by simp
  moreover have "(cmod(jozsa_algo $$ (0,0)))\<^sup>2 = 1/2"
  proof-
     have "k<2^n \<longrightarrow> ((0 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k::nat
      using bitwise_inner_prod_with_zero by simp 
    then have "(cmod(jozsa_algo $$ (0,0)))\<^sup>2 = (cmod(\<Sum>k::nat<2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      using jozsa_algo_result const_def assms by simp
    also have "... = (cmod((-1)/(sqrt(2))))\<^sup>2 " 
      using aux_comp_with_sqrt2_bis by simp
    also have "... = 1/2" 
      by (simp add: norm_divide power2_eq_square)
    finally show "?thesis" by simp
  qed
  moreover have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 = 1/2"
  proof-
    have "k<2^n \<longrightarrow> ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k::nat
      using bitwise_inner_prod_with_zero by simp
    then have "(\<Sum>k::nat<2^n. (-1)^(f k +1 + ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1)))
             = (\<Sum>k::nat<2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1)))"
      using const_def assms by simp
    moreover have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 
    = (cmod (\<Sum>k::nat<2^n. (-1)^(f k + 1 + ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using  \<psi>\<^sub>3_dim by simp
    ultimately have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 = (cmod(\<Sum>k::nat<2^n. 1/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" by simp
    also have "... = (cmod(1/(sqrt(2))))\<^sup>2 " 
      using aux_comp_with_sqrt2_bis by simp
    also have "... = 1/2" 
      by (simp add: norm_divide power2_eq_square)
    finally show "?thesis" by simp
  qed
  ultimately have "prob0_fst_qubits n jozsa_algo = 1/2 + 1/2" by simp
  then show  "?thesis" by simp
qed

text \<open>If the probability of measuring 0 for the first n qubits is 1, then the function is constant.\<close>

lemma (in jozsa) max_value_of_not_const_less:
  assumes "\<not> const 0" and "\<not> const 1"
  shows "(cmod (\<Sum>k::nat<2^n. (-(1::nat))^(f k)))\<^sup>2 < (2::nat)^(2*n)"
proof-
  have "cmod (\<Sum>k::nat<2^n. (-(1::nat))^(f k)) < 2^n"
  proof-
    have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k)) < 2^n"
    proof-
      obtain x where f0:"x < 2^n" and f1:"f x = 1"
        using assms(1) const_def f_values by auto
      then have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k)) < (\<Sum>k\<in>{i| i:: nat. i < 2^n}-{x}. (-(1::nat))^(f k))"
      proof-
        have "(-(1::nat))^ f x = -1" using f1 by simp
        moreover have "x\<in>{i| i::nat. i<2^n}" using f0 by simp
        moreover have "finite {i| i::nat. i<2^n}" by simp
        moreover have "(\<Sum>k\<in>{i| i::nat. i<2^n}. (-(1::nat))^(f k)) < 
(\<Sum>k\<in>{i| i:: nat. i<2^n}-{x}. (-(1::nat))^(f k))"
          using calculation(1,2,3) sum_diff1 by (simp add: sum_diff1)
        ultimately show ?thesis by (metis Collect_cong Collect_mem_eq lessThan_iff)
      qed
      moreover have "\<dots> \<le> int (2^n - 1)"
        using aux_ineq_with_card(1)[of "{i| i:: nat. i<2^n}-{x}"] f0 by simp
      ultimately show ?thesis
        by (meson diff_le_self less_le_trans of_nat_le_numeral_power_cancel_iff)
   qed
   moreover have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k)) > - (2^n)"
   proof-
      obtain x where f0:"x < 2^n" and f1:"f x = 0"
        using assms(2) const_def f_values by auto
      then have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k)) > (\<Sum>k\<in>{i| i:: nat. i < 2^n}-{x}. (-(1::nat))^(f k))"
      proof-
        have "(-(1::nat))^ f x = 1" using f1 by simp
        moreover have "x\<in>{i| i::nat. i<2^n}" using f0 by simp
        moreover have "finite {i| i::nat. i<2^n}" by simp
        moreover have "(\<Sum>k\<in>{i| i::nat. i<2^n}. (-(1::nat))^(f k)) > 
(\<Sum>k\<in>{i| i:: nat. i<2^n}-{x}. (-(1::nat))^(f k))"
          using calculation(1,2,3) sum_diff1 by (simp add: sum_diff1)
        ultimately show ?thesis by (metis Collect_cong Collect_mem_eq lessThan_iff)
      qed
      moreover have "- int (2^n - 1) \<le> (\<Sum>k\<in>{i| i:: nat. i < 2^n}-{x}. (-(1::nat))^(f k))"
        using aux_ineq_with_card(2)[of "{i| i:: nat. i<2^n}-{x}"] f0 by simp
      ultimately show ?thesis
        by (smt diff_le_self of_nat_1 of_nat_add of_nat_power_le_of_nat_cancel_iff one_add_one)
   qed
   ultimately show ?thesis
     using cmod_less of_int_of_nat_eq of_nat_numeral of_nat_power by (metis (no_types, lifting))
  qed
  then have "(cmod (\<Sum>k::nat<2^n. (-(1::nat))^(f k)))\<^sup>2 < (2^n)\<^sup>2"
    using square_less norm_ge_zero by smt
  thus ?thesis
    by (simp add: power_even_eq)
qed

lemma (in jozsa) max_value_of_not_const_less_bis:
  assumes "\<not> const 0" and "\<not> const 1"
  shows "(cmod (\<Sum>k::nat<2^n. (-(1::nat))^(f k + 1)))\<^sup>2 < (2::nat)^(2*n)"
proof-
  have "cmod (\<Sum>k::nat<2^n. (-(1::nat))^(f k + 1)) < 2^n"
  proof-
    have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k + 1)) < 2^n"
    proof-
      obtain x where f0:"x < 2^n" and f1:"f x = 0"
        using assms(2) const_def f_values by auto
      then have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k + 1)) < (\<Sum>k\<in>{i| i:: nat. i < 2^n}-{x}. (-(1::nat))^(f k + 1))"
      proof-
        have "(-(1::nat))^ (f x + 1) = -1" using f1 by simp
        moreover have "x\<in>{i| i::nat. i<2^n}" using f0 by simp
        moreover have "finite {i| i::nat. i<2^n}" by simp
        moreover have "(\<Sum>k\<in>{i| i::nat. i<2^n}. (-(1::nat))^(f k + 1)) < 
(\<Sum>k\<in>{i| i:: nat. i<2^n}-{x}. (-(1::nat))^(f k + 1))"
          using calculation(1,2,3) sum_diff1 by (simp add: sum_diff1)
        ultimately show ?thesis by (metis Collect_cong Collect_mem_eq lessThan_iff)
      qed
      moreover have "\<dots> \<le> int (2^n - 1)"
        using aux_ineq_with_card(1)[of "{i| i:: nat. i<2^n}-{x}" "\<lambda>k. f k + 1"] f0 by simp
      ultimately show ?thesis
        by (meson diff_le_self less_le_trans of_nat_le_numeral_power_cancel_iff)
   qed
   moreover have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k + 1)) > - (2^n)"
   proof-
      obtain x where f0:"x < 2^n" and f1:"f x = 1"
        using assms(1) const_def f_values by auto
      then have "(\<Sum>k::nat<2^n. (-(1::nat))^(f k + 1)) > (\<Sum>k\<in>{i| i:: nat. i < 2^n}-{x}. (-(1::nat))^(f k + 1))"
      proof-
        have "(-(1::nat))^ (f x + 1) = 1" using f1 by simp
        moreover have "x\<in>{i| i::nat. i<2^n}" using f0 by simp
        moreover have "finite {i| i::nat. i<2^n}" by simp
        moreover have "(\<Sum>k\<in>{i| i::nat. i<2^n}. (-(1::nat))^(f k + 1)) > 
(\<Sum>k\<in>{i| i:: nat. i<2^n}-{x}. (-(1::nat))^(f k + 1))"
          using calculation(1,2,3) sum_diff1 by (simp add: sum_diff1)
        ultimately show ?thesis by (metis Collect_cong Collect_mem_eq lessThan_iff)
      qed
      moreover have "- int (2^n - 1) \<le> (\<Sum>k\<in>{i| i:: nat. i < 2^n}-{x}. (-(1::nat))^(f k + 1))"
        using aux_ineq_with_card(2)[of "{i| i:: nat. i<2^n}-{x}" "\<lambda>k. f k + 1"] f0 by simp
      ultimately show ?thesis
        by (smt diff_le_self of_nat_1 of_nat_add of_nat_power_le_of_nat_cancel_iff one_add_one)
   qed
   ultimately show ?thesis
     using cmod_less of_int_of_nat_eq of_nat_numeral of_nat_power by (metis (no_types, lifting))
  qed
  then have "(cmod (\<Sum>k::nat<2^n. (-(1::nat))^(f k + 1)))\<^sup>2 < (2^n)\<^sup>2"
    using square_less norm_ge_zero by smt
  thus ?thesis
    by (simp add: power_even_eq)
qed

lemma (in jozsa) f_const_has_max_value: 
  assumes "const 0 \<or> const 1"
  shows "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k)))\<^sup>2 = (2::nat)^(2*n)" 
  and "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k + 1)))\<^sup>2 = (2::nat)^(2*n)" 
  using aux_comp_with_cmod[of n "\<lambda>k. f k"] aux_comp_with_cmod[of n "\<lambda>k. f k + 1"] const_def assms by auto

lemma (in jozsa) prob0_fst_qubits_leq:
  shows "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k)))\<^sup>2 \<le> (2::nat)^(2*n)" 
    and "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k + 1)))\<^sup>2 \<le> (2::nat)^(2*n)"  
proof-
  show "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k)))\<^sup>2 \<le> (2::nat)^(2*n)" 
  proof(rule disjE)
    show "(const 0 \<or> const 1) \<or> (\<not> const 0 \<and> \<not> const 1)" by auto
  next
    assume "const 0 \<or> const 1" 
    then show "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k)))\<^sup>2 \<le> (2::nat)^(2*n)" 
      using f_const_has_max_value by simp
  next
    assume "\<not> const 0 \<and> \<not> const 1"
    then show "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k)))\<^sup>2 \<le> (2::nat)^(2*n)" 
      using max_value_of_not_const_less by simp
  qed
next
  show "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k + 1)))\<^sup>2 \<le> (2::nat)^(2*n)" 
  proof(rule disjE)
    show "(const 0 \<or> const 1) \<or> (\<not> const 0 \<and> \<not> const 1)" by auto
  next
    assume "const 0 \<or> const 1" 
    then show "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k + 1)))\<^sup>2 \<le> (2::nat)^(2*n)" 
      using f_const_has_max_value by simp
  next
    assume "\<not> const 0 \<and> \<not> const 1"
    then show "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k + 1)))\<^sup>2 \<le> (2::nat)^(2*n)" 
      using max_value_of_not_const_less_bis by simp
  qed
qed

lemma (in jozsa) prob0_jozsa_algo_1_is_const:
  assumes "prob0_fst_qubits n jozsa_algo = 1"
  shows "const 0 \<or> const 1"
proof-
  have f0: "(\<Sum>j\<in>{0,1}. (cmod(jozsa_algo $$ (j,0)))\<^sup>2) = 1"
    using prob0_fst_qubits_of_jozsa_algo assms by simp
  have "k < 2^n\<longrightarrow>((0 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k::nat
    using bitwise_inner_prod_with_zero by simp 
  then have f1: "(cmod(jozsa_algo $$ (0,0)))\<^sup>2 = (cmod(\<Sum>k<(2::nat)^n. (-1)^(f k)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
    by simp
  have "k < 2^n\<longrightarrow>((1 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k::nat
    using bitwise_inner_prod_with_zero by simp
  moreover have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 
               = (cmod (\<Sum>k<(2::nat)^n. (-1)^(f k+ 1 + ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using \<psi>\<^sub>3_dim by simp
  ultimately have f2: "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 
                     = (cmod (\<Sum>k<(2::nat)^n. (-1)^(f k + 1)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" by simp   
  have f3: "1 = (cmod(\<Sum>k::nat<(2::nat)^n.(-1)^(f k)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2
        + (cmod (\<Sum>k::nat<(2::nat)^n. (-1)^(f k + 1)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
    using f0 f1 f2 by simp 
  also have "... = ((cmod (\<Sum>k::nat<(2::nat)^n. (-1)^(f k)) ) /(sqrt(2)^n * sqrt(2)^(n+1)))\<^sup>2
                 + ((cmod(\<Sum>k::nat<(2::nat)^n. (-1)^(f k + 1))) /(sqrt(2)^n * sqrt(2)^(n+1)))\<^sup>2"
    using aux_comp_sum_divide_cmod[of "\<lambda>k. (-1)^(f k)" "(sqrt(2)^n * sqrt(2)^(n+1))" "(2::nat)^n"] 
          aux_comp_sum_divide_cmod[of "\<lambda>k. (-1)^(f k + 1)" "(sqrt(2)^n * sqrt(2)^(n+1))" "(2::nat)^n"] 
    by simp
  also have "... = ((cmod (\<Sum>k::nat<(2::nat)^n. (-1)^(f k))))\<^sup>2 /((sqrt(2)^n * sqrt(2)^(n+1)))\<^sup>2
                 + ((cmod(\<Sum>k::nat<(2::nat)^n. (-1)^(f k +1))))\<^sup>2 /((sqrt(2)^n * sqrt(2)^(n+1)))\<^sup>2"
    by (simp add: power_divide)
  also have "... = ((cmod (\<Sum>k::nat<(2::nat)^n. (-1)^(f k)) ) )\<^sup>2/(2^(2*n+1))
                 + ((cmod(\<Sum>k::nat<(2::nat)^n. (-1)^(f k + 1))))\<^sup>2 /(2^(2*n+1))"
    by (smt left_add_twice power2_eq_square power_add power_mult_distrib real_sqrt_pow2)
  also have "... = (((cmod (\<Sum>k::nat<(2::nat)^n. (-1)^(f k))))\<^sup>2 
                 + ((cmod(\<Sum>k::nat<(2::nat)^n. (-1)^(f k + 1))))\<^sup>2)/(2^(2*n+1)) "
    by (simp add: add_divide_distrib)
  finally have "((2::nat)^(2*n+1)) = (((cmod (\<Sum>k::nat<(2::nat)^n. (-1)^(f k))))\<^sup>2 
                 + ((cmod(\<Sum>k::nat<(2::nat)^n. (-1)^(f k + 1))))\<^sup>2)" by simp
  moreover have "((2::nat)^(2*n+1)) = 2^(2*n) + 2^(2*n)" by auto
  moreover have "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k)))\<^sup>2 \<le> 2^(2*n)" 
    using prob0_fst_qubits_leq by simp 
  moreover have "(cmod (\<Sum>k<(2::nat)^n. (-1)^(f k + 1)))\<^sup>2 \<le> 2^(2*n)" 
    using prob0_fst_qubits_leq by simp 
  ultimately have "2^(2*n) = ((cmod (\<Sum>k::nat<(2::nat)^n. (-1)^(f k))))\<^sup>2" by simp
  then show ?thesis
    using  max_value_of_not_const_less by auto
qed

text \<open>
The function is balanced if and only if at least one qubit among the first n qubits is not zero.
So, if the function is balanced then the probability of measuring 0 for the first n qubits is 0.
\<close>

lemma sum_union_disjoint_finite_set:
  fixes C::"nat set" and g::"nat \<Rightarrow> int"
  assumes "finite C"
  shows "\<forall>A B. A \<inter> B = {} \<and> A \<union> B = C \<longrightarrow> (\<Sum>k\<in>C. g k) = (\<Sum>k\<in>A. g k) + (\<Sum>k\<in>B. g k)" 
  using assms sum.union_disjoint by auto

lemma (in jozsa) balanced_pos_and_neg_terms_cancel_out1:
  assumes "is_balanced" 
  shows "(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k)) = 0"
proof-
  have "\<And>A B. A \<subseteq> {i::nat. i < (2::nat)^n} \<and> B \<subseteq> {i::nat. i < (2::nat)^n}
             \<and> card A = ((2::nat)^(n-1)) \<and> card B = ((2::nat)^(n-1))  
             \<and> (\<forall>(x::nat) \<in> A. f x = (0::nat))  \<and> (\<forall>(x::nat) \<in> B. f x = 1)
        \<longrightarrow> (\<Sum>k<(2::nat)^n. (-(1::nat))^(f k)) = 0"
  proof
    fix A B::"nat set"
    assume asm: "A \<subseteq> {i::nat. i < (2::nat)^n} \<and> B \<subseteq> {i::nat. i < (2::nat)^n}
             \<and> card A = ((2::nat)^(n-1)) \<and> card B = ((2::nat)^(n-1))  
             \<and> (\<forall>(x::nat) \<in> A. f x = (0::nat))  \<and> (\<forall>(x::nat) \<in> B. f x = 1)" 
    then have " A \<inter> B = {}" and "{0..<(2::nat)^n} = A \<union> B" 
      using is_balanced_union is_balanced_inter by auto
    then have "(\<Sum>k\<in>{0..<(2::nat)^n}. (-(1::nat))^(f k)) =
               (\<Sum>k\<in>A. (-(1::nat))^(f k)) 
             + (\<Sum>k\<in>B. (-(1::nat))^(f k))" 
      by (metis finite_atLeastLessThan sum_union_disjoint_finite_set)
    moreover have "(\<Sum>k\<in>A. (-1)^(f k)) = ((2::nat)^(n-1))"
      using asm by simp
    moreover have "(\<Sum>k\<in>B. (-1)^(f k)) = -((2::nat)^(n-1))" 
      using asm by simp
    ultimately have "(\<Sum>k\<in> {0..<(2::nat)^n}. (-(1::nat))^(f k)) = 0" by simp
    then show "(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k)) = 0"
      by (simp add: lessThan_atLeast0)
  qed
  then show ?thesis 
    using assms is_balanced_def by auto
qed

lemma (in jozsa) balanced_pos_and_neg_terms_cancel_out2:
  assumes "is_balanced" 
  shows "(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k + 1)) = 0"
proof-
  have "\<And>A B. A \<subseteq> {i::nat. i < (2::nat)^n} \<and> B \<subseteq> {i::nat. i < (2::nat)^n}
             \<and> card A = ((2::nat)^(n-1)) \<and> card B = ((2::nat)^(n-1))  
             \<and> (\<forall>(x::nat)\<in>A. f x = (0::nat))  \<and> (\<forall>(x::nat)\<in>B. f x = 1)
        \<longrightarrow> (\<Sum>k<(2::nat)^n. (-(1::nat))^(f k + 1)) = 0"
  proof
    fix A B::"nat set"
    assume asm: "A \<subseteq> {i::nat. i < (2::nat)^n} \<and> B \<subseteq> {i::nat. i < (2::nat)^n}
             \<and> card A = ((2::nat)^(n-1)) \<and> card B = ((2::nat)^(n-1))  
             \<and> (\<forall>(x::nat) \<in> A. f x = (0::nat))  \<and> (\<forall>(x::nat) \<in> B. f x = 1)" 
    have "A \<inter> B = {}" and "{0..<(2::nat)^n} = A \<union> B" 
      using is_balanced_union is_balanced_inter asm by auto
    then have "(\<Sum>k\<in>{0..<(2::nat)^n}. (-(1::nat))^(f k + 1)) =
               (\<Sum>k\<in>A. (-(1::nat))^(f k + 1)) 
             + (\<Sum>k\<in>B. (-(1::nat))^(f k + 1))" 
      by (metis finite_atLeastLessThan sum_union_disjoint_finite_set)
    moreover have "(\<Sum>k\<in>A. (-1)^(f k + 1)) = -((2::nat)^(n-1))" 
      using asm by simp
    moreover have "(\<Sum>k\<in>B. (-1)^(f k + 1)) = ((2::nat)^(n-1))" 
      using asm by simp
    ultimately have "(\<Sum>k\<in>{0..<(2::nat)^n}. (-(1::nat))^(f k + 1)) = 0 " by simp
    then show "(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k + 1)) = 0"
      by (simp add: lessThan_atLeast0)
  qed
  then show "(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k + 1)) = 0" 
    using assms is_balanced_def by auto
qed

lemma (in jozsa) prob0_jozsa_algo_of_balanced:
assumes "is_balanced"
  shows "prob0_fst_qubits n jozsa_algo = 0"
proof-
  have "prob0_fst_qubits n jozsa_algo = (\<Sum>j\<in>{0,1}. (cmod(jozsa_algo $$ (j,0)))\<^sup>2)"
    using prob0_fst_qubits_of_jozsa_algo by simp
  moreover have "(cmod(jozsa_algo $$ (0,0)))\<^sup>2 = 0"
  proof-
     have "k < 2^n\<longrightarrow>((1 div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k::nat
      using bitwise_inner_prod_with_zero by simp
    then have "(cmod(jozsa_algo $$ (0,0)))\<^sup>2 = (cmod(\<Sum> k < (2::nat)^n. (-1)^(f k)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      using \<psi>\<^sub>3_values by simp
    also have "... = (cmod(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k))/(sqrt(2)^n * sqrt(2)^(n+1)))\<^sup>2" 
      using aux_comp_sum_divide_cmod[of "\<lambda>k.(-(1::nat))^(f k)" "(sqrt(2)^n * sqrt(2)^(n+1))" "2^n"] 
      by simp
    also have "... = (cmod ((0::int)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      using balanced_pos_and_neg_terms_cancel_out1 assms by (simp add: bob_fun_axioms)
    also have "... = 0" by simp
    finally show ?thesis by simp
  qed
  moreover have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 = 0" 
  proof-
     have "k < 2^n \<longrightarrow> (((1::nat) div 2) \<cdot>\<^bsub>n\<^esub>  k) = 0" for k::nat
       using bitwise_inner_prod_with_zero by auto
     moreover have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 
     = (cmod (\<Sum>k<(2::nat)^n. (-(1::nat))^(f k + (1::nat) + ((1 div 2) \<cdot>\<^bsub>n\<^esub>  k))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2"
      using \<psi>\<^sub>3_dim by simp
    ultimately have "(cmod(jozsa_algo $$ (1,0)))\<^sup>2 
    = (cmod(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k + (1::nat))/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
       by simp
    also have "... = (cmod(\<Sum>k<(2::nat)^n. (-(1::nat))^(f k + 1))/(sqrt(2)^n * sqrt(2)^(n+1)))\<^sup>2" 
      using aux_comp_sum_divide_cmod[of "\<lambda>k.(-(1::nat))^(f k + 1)" "(sqrt(2)^n * sqrt(2)^(n+1))" "2^n"] 
      by simp
    also have "... = (cmod ((0::int)/(sqrt(2)^n * sqrt(2)^(n+1))))\<^sup>2" 
      using balanced_pos_and_neg_terms_cancel_out2 assms by (simp add: bob_fun_axioms)
    also have "... = 0" by simp
    finally show ?thesis by simp
  qed
  ultimately have "prob0_fst_qubits n jozsa_algo = 0 + 0" by simp
  then show  ?thesis by simp
qed

text \<open>If the probability that the first n qubits are 0 is 0, then the function is balanced.\<close>

lemma (in jozsa) balanced_prob0_jozsa_algo:
  assumes "prob0_fst_qubits n jozsa_algo = 0"
  shows "is_balanced"
proof-
  have "is_const \<or> is_balanced" 
    using const_or_balanced by simp
  moreover have "is_const \<longrightarrow> \<not> prob0_fst_qubits n jozsa_algo = 0"
    using is_const_def prob0_jozsa_algo_of_const_0 prob0_jozsa_algo_of_const_1 by simp
  ultimately show ?thesis 
    using assms by simp
qed

text \<open>We prove the correctness of the algorithm.\<close>

definition (in jozsa) jozsa_algo_eval:: "real" where
"jozsa_algo_eval \<equiv> prob0_fst_qubits n jozsa_algo"

theorem (in jozsa) jozsa_algo_is_correct:
  shows "jozsa_algo_eval = 1 \<longleftrightarrow> is_const" 
    and "jozsa_algo_eval = 0 \<longleftrightarrow> is_balanced" 
  using prob0_jozsa_algo_of_const_1 prob0_jozsa_algo_of_const_0 jozsa_algo_eval_def
prob0_jozsa_algo_1_is_const is_const_def balanced_prob0_jozsa_algo prob0_jozsa_algo_of_balanced 
  by auto

end