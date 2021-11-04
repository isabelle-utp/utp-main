(* 
Author: 
  Anthony Bordg, University of Cambridge, apdb3@cam.ac.uk
  Yijun He, University of Cambridge, yh403@cam.ac.uk
*)

section \<open>Measurement\<close>

theory Measurement
imports
  Quantum
begin


text \<open>
Given an element v  such that @{text "state n v"}, its components @{text "v $ i"} (when v is seen as 
a vector, v being a matrix column) for @{text "0 \<le> i < n"} have to be understood as the coefficients 
of the representation of v in the basis given by the unit vectors of dimension $2^n$, unless stated otherwise. 
Such a vector v is a state for a quantum system of n qubits.
In the literature on quantum computing, for $n = 1$, i.e. for a quantum system of 1 qubit, the elements
of the so-called computational basis are denoted $|0\rangle$,$|1\rangle$, and these last elements might be understood
for instance as $(1,0)$,$(0,1)$, i.e. as the zeroth and the first elements of a given basis ; for $n = 2$, 
i.e. for a quantum system of 2 qubits, the elements of the computational basis are denoted $|00\rangle$,
$|01\rangle$, $|10\rangle$,$|11\rangle$, and they might be understood for instance as $(1,0,0,0)$,
$(0,1,0,0)$, $(0,0,1,0)$, $(0,0,0,1)$; and so on for higher values of $n$. 
The idea behind these standard notations is that the labels on the vectors of the 
computational basis are the binary expressions of the natural numbers indexing the elements
in a given ordered basis interpreting the computational basis in a specific context, another point of
view is that the order of the basis corresponds to the lexicographic order for the labels. 
Those labels also represent the possible outcomes of a measurement of the $n$ qubits of the system, 
while the squared modules of the corresponding coefficients represent the probabilities for those 
outcomes. The fact that the vector v has to be normalized expresses precisely the fact that the squared 
modules of the coefficients represent some probabilities and hence their sum should be $1$.
Note that in the case of a system with multiple qubits, i.e. $n \geq 2$, one can model the simultaneous 
measurement of multiple qubits by sequential measurements of single qubits. Indeed, this last process
leads to the same probabilities for the various possible outcomes.
Given a system with n-qubits and i the index of one qubit among the $n$ qubits of the system, where
$0 \leq i \leq n-1$ (i.e. we start the indexing from $0$), we want to find the indices of the states of the
computational basis whose labels have a $1$ at the ith spot (counting from $0$). For instance, 
if $n=3$ and $i=2$ then $1$,$3$,$5$,$7$ are the indices of the elements of the computational basis 
with a $1$ at the 2nd spot, namely $|001\rangle$,$|011\rangle$,$|101\rangle$,$|111\rangle$. To achieve that we define the 
predicate @{term "select_index"} below.
\<close>

definition select_index ::"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"select_index n i j \<equiv> (i\<le>n-1) \<and> (j\<le>2^n - 1) \<and> (j mod 2^(n-i) \<ge> 2^(n-1-i))"

lemma select_index_union:
  "{k| k::nat. select_index n i k} \<union> {k| k::nat. (k<2^n) \<and> \<not> select_index n i k} = {0..<2^n::nat}"
proof
  have "{k |k. select_index n i k} \<subseteq> {0..<2 ^ n}"
  proof
    fix x::nat assume "x \<in> {k |k. select_index n i k}"
    then show "x \<in> {0..<2^n}" 
      using select_index_def
      by (metis (no_types, lifting) atLeastLessThan_iff diff_diff_cancel diff_is_0_eq' diff_le_mono2 
le_less_linear le_numeral_extra(2) mem_Collect_eq one_le_numeral one_le_power select_index_def zero_order(1))
  qed
  moreover have "{k |k. k<2 ^ n \<and> \<not> select_index n i k} \<subseteq> {0..<2 ^ n}" by auto
  ultimately show "{k |k. select_index n i k} \<union> {k |k. k<2 ^ n \<and> \<not> select_index n i k} \<subseteq> {0..<2 ^ n}" by simp
next
  show "{0..<2 ^ n} \<subseteq> {k |k. select_index n i k} \<union> {k |k. k<2 ^ n \<and> \<not> select_index n i k}" by auto
qed

lemma select_index_inter:
  "{k| k::nat. select_index n i k} \<inter> {k| k::nat. (k<2^n) \<and> \<not> select_index n i k} = {}" by auto

lemma outcomes_sum [simp]:
  fixes f :: "nat \<Rightarrow> real"
  shows
  "(\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
   (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) = 
   (\<Sum>j\<in>{0..<2^n::nat}. (f j))"
proof -
  have "{k| k::nat. select_index n i k} \<subseteq> {0..<2^n::nat}"
    using select_index_union by blast
  then have "finite {k| k::nat. select_index n i k}"
    using rev_finite_subset by blast
  moreover have "{k| k::nat. (k<2^n) \<and> \<not> select_index n i k} \<subseteq> {0..<2^n::nat}"
    using select_index_union by blast
  then have "finite {k| k::nat. (k<2^n) \<and> \<not> select_index n i k}"
    using rev_finite_subset by blast
  ultimately have "(\<Sum>j\<in>{k| k::nat. select_index n i k}\<union>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
           (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) -
           (\<Sum>j\<in>{k| k::nat. select_index n i k}\<inter>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j))"
    using sum_Un by blast
  then have "(\<Sum>j\<in>{0..<2^n::nat}. (f j)) = 
                (\<Sum>j\<in>{k| k::nat. select_index n i k}. (f j)) + 
                (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (f j)) -
                (\<Sum>j\<in>{}. (f j))"
    using select_index_union select_index_inter by simp
  thus ?thesis by simp
qed

text \<open>
Given a state v of a n-qbit system, we compute the probability that a measure 
of qubit i has the outcome 1.
\<close>

definition prob1 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> real" where
"prob1 n v i \<equiv> \<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2"

definition prob0 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> real" where
"prob0 n v i \<equiv> \<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2"

lemma
  shows prob1_geq_zero:"prob1 n v i \<ge> 0" and prob0_geq_zero:"prob0 n v i \<ge> 0" 
proof -
  have "(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (0::real))"
    by (simp add: sum_nonneg)
  then have "(\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 0" by simp
  thus "prob1 n v i \<ge> 0"
    using prob1_def by simp
next
  have "(\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 
           (\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (0::real))"
    by (simp add: sum_nonneg)
  then have "(\<Sum>j\<in>{k| k::nat. (k < 2 ^ n) \<and> \<not> select_index n i k}. (cmod(v $$ (j,0)))\<^sup>2) \<ge> 0" by simp
  thus "prob0 n v i \<ge> 0"
    using prob0_def by simp
qed

lemma prob_sum_is_one [simp]:
  assumes "state n v"
  shows "prob1 n v i + prob0 n v i = 1"
proof-
  have "prob1 n v i + prob0 n v i = (\<Sum>j\<in>{0..<2^n::nat}. (cmod(v $$ (j,0)))\<^sup>2)"
    using prob1_def prob0_def outcomes_sum by simp
  also have "\<dots> = \<parallel>col v 0\<parallel>\<^sup>2"
    using cpx_vec_length_def assms state_def atLeast0LessThan by fastforce
  finally show ?thesis 
    using assms state_def by simp
qed

lemma
  assumes "state n v"
  shows prob1_leq_one:"prob1 n v i \<le> 1" and prob0_leq_one:"prob0 n v i \<le> 1"
   apply(metis assms le_add_same_cancel1 prob0_geq_zero prob_sum_is_one)
  apply(metis assms le_add_same_cancel2 prob1_geq_zero prob_sum_is_one)
  done

lemma prob0_is_prob: 
  assumes "state n v"
  shows "prob0 n v i \<ge> 0 \<and> prob0 n v i \<le> 1"
  by (simp add: assms prob0_geq_zero prob0_leq_one)

lemma prob1_is_prob: 
  assumes "state n v"
  shows "prob1 n v i \<ge> 0 \<and> prob1 n v i \<le> 1"
  by (simp add: assms prob1_geq_zero prob1_leq_one)

text \<open>Below we give the new state of a n-qubits system after a measurement of the ith qubit gave 0.\<close>

definition post_meas0 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> complex mat" where
"post_meas0 n v i \<equiv> 
  of_real(1/sqrt(prob0 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<rangle>"
 
text \<open>
Note that a division by 0 never occurs. Indeed, if @{text "sqrt(prob0 n v i)"} would be 0 then 
@{text "prob0 n v i"} would be 0 and it would mean that the measurement of the ith qubit gave 1.
\<close>

lemma post_meas0_is_state [simp]:
  assumes "state n v" and "prob0 n v i \<noteq> 0"
  shows "state n (post_meas0 n v i)" 
proof -
  have "(\<Sum>j\<in>{0..<2^n::nat}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) +
           (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    using outcomes_sum[of "\<lambda>j. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2" n i] by simp
  moreover have "(\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod (if \<not> select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           prob0 n v i"
    by(simp add: prob0_def)
  ultimately have "\<parallel>vec (2 ^ n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<parallel> = sqrt(prob0 n v i)"
    using lessThan_atLeast0 by (simp add: cpx_vec_length_def)
  moreover have "\<parallel>col (complex_of_real (1/sqrt (prob0 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel> = 
           (1/sqrt (prob0 n v i)) * \<parallel>vec (2^n) (\<lambda>j. if \<not> select_index n i j then v $$ (j,0) else 0)\<parallel>"
    using prob0_geq_zero smult_vec_length_bis by(metis (no_types, lifting) real_sqrt_ge_0_iff zero_le_divide_1_iff)
  ultimately show ?thesis
    using state_def post_meas0_def by (simp add: ket_vec_def post_meas0_def assms(2))
qed

text \<open>Below we give the new state of a n-qubits system after a measurement of the ith qubit gave 1.\<close>

definition post_meas1 ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> complex mat" where
"post_meas1 n v i \<equiv> 
  of_real(1/sqrt(prob1 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>"
 
text \<open>
Note that a division by 0 never occurs. Indeed, if @{text "sqrt(prob1 n v i)"} would be 0 then 
@{text "prob1 n v i"} would be 0 and it would mean that the measurement of the ith qubit gave 0.
\<close> 

lemma post_meas_1_is_state [simp]:
  assumes "state n v" and "prob1 n v i \<noteq> 0"
  shows "state n (post_meas1 n v i)"
proof -
  have "(\<Sum>j\<in>{0..<2^n::nat}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) = 
           (\<Sum>j\<in>{k| k::nat. select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2) +
           (\<Sum>j\<in>{k| k::nat. (k<2^n) \<and> \<not> select_index n i k}. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2)"
    using outcomes_sum[of "\<lambda>j. (cmod (if select_index n i j then v $$ (j,0) else 0))\<^sup>2" n i] by simp
  then have "\<parallel>vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<parallel> = sqrt(prob1 n v i)"
    using lessThan_atLeast0 by (simp add: cpx_vec_length_def prob1_def)
  moreover have "\<parallel>col(complex_of_real (1/sqrt (prob1 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel> = 
           (1/sqrt(prob1 n v i)) * \<parallel>vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<parallel>"
    using prob1_geq_zero smult_vec_length_bis
    by (metis (no_types, lifting) real_sqrt_ge_0_iff zero_le_divide_1_iff)
  ultimately have "\<parallel>col(complex_of_real (1/sqrt (prob1 n v i)) \<cdot>\<^sub>m |vec (2^n) (\<lambda>j. if select_index n i j then v $$ (j,0) else 0)\<rangle>) 0\<parallel>
= (1/sqrt(prob1 n v i)) * sqrt(prob1 n v i)" by simp
  thus ?thesis
    using state_def post_meas1_def by (simp add: ket_vec_def post_meas1_def assms(2))
qed

text \<open>
The measurement operator below takes a number of qubits n, a state v of a n-qubits system, a number
i corresponding to the index (starting from 0) of one qubit among the n-qubits, and it computes a list 
whose first (resp. second) element is the pair made of the probability that the outcome of the measurement
of the ith qubit is 0 (resp. 1) and the corresponding post-measurement state of the system.
Of course, note that i should be strictly less than n and v should be a state of dimension n, i.e. 
state n v should hold".
\<close>

definition meas ::"nat \<Rightarrow> complex mat \<Rightarrow> nat \<Rightarrow> _list" where
"meas n v i \<equiv> [(prob0 n v i, post_meas0 n v i), (prob1 n v i, post_meas1 n v i)]"

text \<open>
We want to determine the probability that the first n qubits of an n+1 qubit system are 0. 
For this we need to find the indices of the states of the computational basis whose labels do 
not have a 1 at spot $i=0,...,n$.
\<close>

definition prob0_fst_qubits:: "nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where
"prob0_fst_qubits n v \<equiv> 
\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (\<forall>i\<in>{0..<n}. \<not> select_index (n+1) i k)}. (cmod(v $$ (j,0)))\<^sup>2"

lemma select_index_div_2:
  fixes n i j::"nat"
  assumes "i < 2^(n+1)" and "j<n"
  shows "select_index n j (i div 2) = select_index (n+1) j i"
proof-
  have "2^(n-Suc j) \<le> i div 2 mod 2^(n-j) \<Longrightarrow> 2^(n-j) \<le> i mod 2^(n+1-j)"
  proof-
    define a::nat where a0:"a = i div 2 mod 2^(n-j)"
    assume "2^(n-Suc j) \<le> a"
    then have "2*a + i mod 2 \<ge> 2^(n-(Suc j)+1)" by simp
    then have f0:"2*a + i mod 2 \<ge> 2^(n-j)"
      by (metis Suc_diff_Suc Suc_eq_plus1 assms(2))
    have "a < 2^(n-j)" using a0 by simp
    then have "2*a + i mod 2 < 2*2^(n-j)" by linarith
    then have "2*a + i mod 2 < 2^(n-j+1)" by simp
    then have f1:"2*a + i mod 2 < 2^(n+1-j)"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    have "i = 2*(a + 2^(n-j)*(i div 2 div 2^(n-j))) + i mod 2" using a0 by simp
    then have "i = 2*a + i mod 2 + 2^(n-j+1)*(i div 2 div 2^(n-j))" by simp
    then have "i = 2*a + i mod 2 + 2^(n+1-j)*(i div 2 div 2^(n-j))"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    then have "i mod 2^(n+1-j) = 2*a + i mod 2"
      using f1 by (metis mod_if mod_mult_self2)
    then show "2^(n-j) \<le> i mod 2^(n+1-j)"
      using f0 by simp
  qed
  moreover have "2^(n-j) \<le> i mod 2^(n+1-j) \<Longrightarrow> 2^(n-Suc j) \<le> i div 2 mod 2^(n-j)"
  proof-
    define a::nat where a0:"a = i div 2 mod 2^(n-j)"
    assume a1:"2^(n-j) \<le> i mod 2^(n+1-j)"
    have f0:"2^(n-j) = 2^(n-Suc j+1)"
      by (metis Suc_diff_Suc Suc_eq_plus1 assms(2))
    have "a < 2^(n-j)" using a0 by simp
    then have "2*a + i mod 2 < 2*2^(n-j)" by linarith
    then have "2*a + i mod 2 < 2^(n-j+1)" by simp
    then have f1:"2*a + i mod 2 < 2^(n+1-j)"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    have "i = 2*(a + 2^(n-j)*(i div 2 div 2^(n-j))) + i mod 2" using a0 by simp
    then have "i = 2*a + i mod 2 + 2^(n-j+1)*(i div 2 div 2^(n-j))" by simp
    then have "i = 2*a + i mod 2 + 2^(n+1-j)*(i div 2 div 2^(n-j))"
      by (metis Nat.add_diff_assoc2 Suc_leD Suc_leI assms(2))
    then have "i mod 2^(n+1-j) = 2*a + i mod 2"
      using f1 by (metis mod_if mod_mult_self2)
    then have "2*a + i mod 2 \<ge> 2^(n-j)"
      using a1 by simp
    then have "(2*a + i mod 2) div 2 \<ge> (2^(n-j)) div 2"
      using div_le_mono by blast
    then show "2^(n-Suc j) \<le> a" by (simp add: f0)
  qed
  ultimately show ?thesis
    using select_index_def assms by auto
qed

lemma select_index_suc_even:
  fixes n k i:: nat
  assumes "k < 2^n" and "select_index n i k"
  shows "select_index (Suc n) i (2*k)"
proof-
  have "select_index n i k = select_index n i (2*k div 2)" by simp
  moreover have "\<dots> = select_index (Suc n) i (2*k)"
  proof-
    have "i < n" using assms(2) select_index_def
      by (metis (no_types, hide_lams) Suc_eq_plus1 assms(1) calculation diff_diff_left diff_le_self 
diff_self_eq_0 div_by_1 le_0_eq le_eq_less_or_eq less_imp_diff_less mod_div_trivial mult.left_neutral mult_eq_0_iff mult_le_mono1 not_less plus_1_eq_Suc power_0 semiring_normalization_rules(7))
    thus ?thesis
      using select_index_div_2 assms(1) select_index_def by(metis Suc_1 Suc_eq_plus1 Suc_mult_less_cancel1 power_Suc)
  qed
  ultimately show "select_index (Suc n) i (2*k)" 
    using assms(2) by simp
qed

lemma select_index_suc_odd:
  fixes n k i:: nat
  assumes "k \<le> 2^n -1" and "select_index n i k"
  shows "select_index (Suc n) i (2*k+1)"
proof-
  have "((2*k+1) mod 2^(Suc n - i) \<ge> 2^(n - i)) =  
(((2*k+1) div 2) mod 2^(n - i) \<ge> 2^(n-1-i))"
  proof-
    have "2*k+1 < 2^(n + 1)" 
      using assms(1)
      by (smt Suc_1 Suc_eq_plus1 Suc_le_lessD Suc_le_mono add_Suc_right distrib_left_numeral le_add_diff_inverse mult_le_mono2 nat_mult_1_right one_le_numeral one_le_power plus_1_eq_Suc power_add power_one_right)
    moreover have "i < n" 
      using assms(2) select_index_def
      by (metis (no_types, hide_lams) add_cancel_left_left add_diff_inverse_nat diff_le_self div_by_1 le_antisym less_le_trans less_one mod_div_trivial not_le power_0)
    ultimately show ?thesis
      using select_index_div_2[of "2*k+1" "n" i] select_index_def
      by (metis Nat.le_diff_conv2 Suc_eq_plus1 Suc_leI assms(2) diff_Suc_1 less_imp_le less_power_add_imp_div_less one_le_numeral one_le_power power_one_right)
  qed
  moreover have "\<dots> = (k mod 2^(n - i) \<ge> 2^(n-1-i))" by simp
  ultimately show ?thesis
  proof-
    have "i \<le> Suc n -1" using assms(2) select_index_def by auto
    moreover have "2*k+1 \<le> 2^(Suc n)-1" 
      using assms(1) by (smt Suc_diff_1 Suc_eq_plus1 add_diff_cancel_right' diff_Suc_diff_eq2 diff_diff_left diff_is_0_eq diff_mult_distrib2 le_add2 mult_2 mult_Suc_right plus_1_eq_Suc pos2 power_Suc zero_less_power)
    ultimately show ?thesis
      using select_index_def
      by (metis \<open>(2 ^ (n - 1 - i) \<le> (2 * k + 1) div 2 mod 2 ^ (n - i)) = (2 ^ (n - 1 - i) \<le> k mod 2 ^ (n - i))\<close> \<open>(2 ^ (n - i) \<le> (2 * k + 1) mod 2 ^ (Suc n - i)) = (2 ^ (n - 1 - i) \<le> (2 * k + 1) div 2 mod 2 ^ (n - i))\<close> assms(2) diff_Suc_1)
  qed
qed

lemma aux_range:
  fixes k:: nat
  assumes "k < 2^(Suc n + 1)" and "k \<ge> 2"
  shows "k = 2 \<or> k = 3 \<or> (\<exists>l. l\<ge>2 \<and> l\<le>2^(n+1)-1 \<and> (k = 2*l \<or> k = 2*l + 1))"
proof(rule disjCI)
  assume "\<not> (k = 3 \<or> (\<exists>l\<ge>2. l \<le> 2^(n + 1) - 1 \<and> (k = 2 * l \<or> k = 2 * l + 1)))"
  have "k > 3 \<longrightarrow> (\<exists>l\<ge>2. l \<le> 2^(n + 1) - 1 \<and> (k = 2 * l \<or> k = 2 * l + 1))"
  proof
    assume asm:"k > 3"
    have "even k \<or> odd k" by simp
    then obtain l where "k = 2*l \<or> k = 2*l+1" by (meson evenE oddE)
    moreover have "l \<ge> 2" 
      using asm calculation by linarith
    moreover have "l \<le> 2^(n+1) - 1" 
      using assms(1) by (metis Suc_diff_1 Suc_eq_plus1 calculation(1) dvd_triv_left even_Suc_div_two less_Suc_eq_le less_power_add_imp_div_less nonzero_mult_div_cancel_left pos2 power_one_right zero_less_power zero_neq_numeral)
    ultimately show "\<exists>l\<ge>2. l \<le> 2^(n + 1) - 1 \<and> (k = 2 * l \<or> k = 2 * l + 1)" by auto
  qed
  then have "k \<le> 2"
    using \<open>\<not> (k = 3 \<or> (\<exists>l\<ge>2. l \<le> 2 ^ (n + 1) - 1 \<and> (k = 2 * l \<or> k = 2 * l + 1)))\<close> less_Suc_eq_le by auto
  thus "k = 2"
    using assms(2) by simp
qed

lemma select_index_with_1:
  fixes n:: nat
  assumes "n \<ge> 1"
  shows "\<forall>k. k < 2^(n+1) \<longrightarrow> k \<ge> 2 \<longrightarrow> (\<exists>i<n. select_index (n+1) i k)"
  using assms
proof(rule nat_induct_at_least)
  show "\<forall>k< 2^(1+1). 2 \<le> k \<longrightarrow> (\<exists>i<1. select_index (1+1) i k)"
  proof-
    have "select_index 2 0 2 = True" 
      using select_index_def by simp
    moreover have "select_index 2 0 3"
      using select_index_def by simp
    ultimately show ?thesis
      by (metis Suc_leI add_Suc_shift le_eq_less_or_eq mult_2 not_less one_add_one one_plus_numeral 
plus_1_eq_Suc power.simps(2) power_one_right semiring_norm(3) zero_less_one_class.zero_less_one)
  qed
next
  show "\<And>n. 1 \<le> n \<Longrightarrow>
         \<forall>k < 2^(n+1). 2 \<le> k \<longrightarrow> (\<exists>i<n. select_index (n+1) i k) \<Longrightarrow>
         \<forall>k < 2^(Suc n + 1). 2 \<le> k \<longrightarrow> (\<exists>i<Suc n. select_index (Suc n +1) i k)"
  proof-
    fix n:: nat
    assume asm:"n \<ge> 1" and IH:"\<forall>k < 2^(n+1). 2 \<le> k \<longrightarrow> (\<exists>i<n. select_index (n+1) i k)"
    have "select_index (Suc n + 1) n 2"
    proof-
      have "select_index (Suc n) n 1" 
        using select_index_def by(smt Suc_1 Suc_diff_Suc Suc_lessI add_diff_cancel_right' diff_Suc_1 
diff_commute diff_zero le_eq_less_or_eq less_Suc_eq_le nat.simps(3) nat_power_eq_Suc_0_iff 
one_mod_two_eq_one plus_1_eq_Suc power_one_right zero_less_power)
      thus ?thesis 
        using select_index_suc_even by (metis Suc_eq_plus1 less_numeral_extra(4) mult_2 not_less_less_Suc_eq one_add_one one_less_power zero_less_Suc)
    qed
    moreover have "select_index (Suc n + 1) n 3"
    proof-
      have "select_index (Suc n) n 1"
        using select_index_def by(smt Suc_1 Suc_diff_Suc Suc_lessI add_diff_cancel_right' diff_Suc_1 
diff_commute diff_zero le_eq_less_or_eq less_Suc_eq_le nat.simps(3) nat_power_eq_Suc_0_iff 
one_mod_two_eq_one plus_1_eq_Suc power_one_right zero_less_power)
      thus ?thesis 
        using select_index_suc_odd by (metis One_nat_def Suc_eq_plus1 mult_2 numeral_3_eq_3 select_index_def)
    qed
    moreover have "\<exists>i<Suc n. select_index (Suc n +1) i (2*k)" if "k \<ge> 2" and "k \<le> 2^(n + 1)-1" for k:: nat
    proof-
      obtain i where "i<n" and "select_index (n+1) i k" 
        using IH by(metis One_nat_def Suc_diff_Suc \<open>2 \<le> k\<close> \<open>k \<le> 2 ^ (n + 1) - 1\<close> diff_zero le_imp_less_Suc pos2 zero_less_power)
      then have "select_index (Suc n +1) i (2*k)"
        using select_index_suc_even
        by (metis One_nat_def Suc_diff_Suc add.commute diff_zero le_imp_less_Suc plus_1_eq_Suc pos2 that(2) zero_less_power)
      thus ?thesis
        using \<open>i < n\<close> less_SucI by blast
    qed
    moreover have "\<exists>i<Suc n. select_index (Suc n +1) i (2*k +1)" if "k \<ge> 2" and "k \<le> 2^(n + 1)-1" for k:: nat
    proof-
      obtain i where "i<n" and "select_index (n+1) i k" 
        using IH by(metis One_nat_def Suc_diff_Suc \<open>2 \<le> k\<close> \<open>k \<le> 2 ^ (n + 1) - 1\<close> diff_zero le_imp_less_Suc pos2 zero_less_power)
      then have "select_index (Suc n +1) i (2*k+1)"
        using select_index_suc_odd that(2) by simp
      thus ?thesis
        using \<open>i < n\<close> less_SucI by blast
    qed
    ultimately show "\<forall>k< 2^(Suc n + 1). 2 \<le> k \<longrightarrow> (\<exists>i<Suc n. select_index (Suc n +1) i k)"
      using aux_range by (metis lessI)
  qed
qed

lemma prob0_fst_qubits_index:
  fixes n:: nat and v:: "complex Matrix.mat"
  shows "{k| k::nat. (k<2^(n+1)) \<and> (\<forall>i\<in>{0..<n}. \<not> select_index (n+1) i k)} = {0,1}"
proof(induct n)
  case 0
  show "{k |k. k < 2^(0+1) \<and> (\<forall>i\<in>{0..<0}. \<not> select_index (0+1) i k)} = {0,1}" by auto
next
  case (Suc n)
  show "\<And>n. {k |k. k < 2^(n+1) \<and> (\<forall>i\<in>{0..<n}. \<not> select_index (n+1) i k)} = {0,1} \<Longrightarrow>
         {k |k. k < 2^(Suc n + 1) \<and> (\<forall>i\<in>{0..<Suc n}. \<not> select_index (Suc n + 1) i k)} =
         {0, 1}"
  proof-
    fix n
    assume IH: "{k |k. k < 2^(n+1) \<and> (\<forall>i\<in>{0..<n}. \<not> select_index (n+1) i k)} = {0,1}"
    then have "{0,1} \<subseteq> {k |k. k < 2^(Suc n + 1) \<and> (\<forall>i\<in>{0..<Suc n}. \<not> select_index (Suc n + 1) i k)}"
    proof-
      have "k < 2^(n+1) \<longrightarrow> k < 2^(Suc n + 1)" for k::nat by simp
      moreover have "(\<forall>i\<in>{0..<n}. \<not> select_index (n+1) i 0) \<and> (\<forall>i\<in>{0..<n}. \<not> select_index (n+1) i 1)"
        using IH by auto
      then have "(\<forall>i\<in>{0..<n}. \<not> select_index (Suc n +1) i 0) \<and> (\<forall>i\<in>{0..<n}. \<not> select_index (Suc n +1) i 1)"
        using select_index_suc_odd[of 0 "n+1"] Suc_eq_plus1
        by (smt One_nat_def Suc_1 add_Suc_shift add_diff_cancel_right' atLeastLessThan_iff diff_diff_cancel 
le_eq_less_or_eq less_Suc_eq linorder_not_le mod_less nat_power_eq_Suc_0_iff select_index_def zero_less_power)
      moreover have "select_index (Suc n + 1) n 0 = False" using select_index_def by simp
      moreover have "select_index (Suc n + 1) n 1 = False" using select_index_def by simp
      ultimately show ?thesis
        by (smt One_nat_def Suc_1 Suc_eq_plus1 Suc_lessI atLeast0_lessThan_Suc empty_iff insertE 
mem_Collect_eq nat.simps(1) nat_power_eq_Suc_0_iff pos2 subsetI zero_less_power)
    qed
    moreover have "{k |k. k < 2^(Suc n + 1) \<and> (\<forall>i\<in>{0..<Suc n}. \<not> select_index (Suc n + 1) i k)} \<subseteq> {0,1}"
    proof-
      have "\<forall>k<2^(Suc n +1). k \<ge> 2 \<longrightarrow> (\<exists>i<Suc n. \<not> select_index (Suc n +1) i k = False)"
        using select_index_with_1[of "Suc n"] by (metis Suc_eq_plus1 add.commute le_add1)
      thus ?thesis by auto
    qed
    ultimately show "{k |k. k<2^(Suc n + 1) \<and> (\<forall>i\<in>{0..<Suc n}. \<not> select_index (Suc n +1) i k)} = {0,1}" by auto
  qed
qed

lemma prob0_fst_qubits_eq:
  fixes n:: nat
  shows "prob0_fst_qubits n v = (cmod(v $$ (0,0)))\<^sup>2 + (cmod(v $$ (1,0)))\<^sup>2"
proof-
  have "prob0_fst_qubits n v = (\<Sum>j\<in>{k| k::nat. (k<2^(n+1)) \<and> (\<forall>i\<in>{0..<n}. \<not> select_index (n+1) i k)}. (cmod(v $$ (j,0)))\<^sup>2)"
    using prob0_fst_qubits_def by simp
  moreover have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(v $$ (j,0)))\<^sup>2)"
    using prob0_fst_qubits_index by simp
  finally show ?thesis by simp
qed

(* Below in iter_post_meas0, the first argument n corresponds to the number of qubits of the system
, and the second argument m corresponds to the number of qubits that have been measured. *)
primrec iter_post_meas0:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> complex Matrix.mat" where
  "iter_post_meas0 n 0 v = v"
| "iter_post_meas0 n (Suc m) v = post_meas0 n (iter_post_meas0 n m v) m"

(* iter_prob0 outputs the probability that successive measurements of the first m qubits
(out of n qubits in the system) give m zeros. *)
definition iter_prob0:: "nat \<Rightarrow> nat \<Rightarrow> complex Matrix.mat \<Rightarrow> real" where 
  "iter_prob0 n m v = (\<Prod>i<m. prob0 n (iter_post_meas0 n i v) i)"

(* To do:
lemma iter_prob0_eq:
  fixes n:: nat and v:: "complex Matrix.mat"
  assumes "n \<ge> 1"
  shows "iter_prob0 (Suc n) n v = prob0_fst_qubits n v"
*)

subsection \<open>Measurements with Bell States\<close>

text \<open>
A Bell state is a remarkable state. Indeed, if one makes one measure, either of the first or the second 
qubit, then one gets either $0$ with probability $1/2$ or $1$ with probability $1/2$. Moreover, in the case of 
two successive measurements of the first and second qubit, the outcomes are correlated. 
Indeed, in the case of @{text "|\<beta>\<^sub>0\<^sub>0\<rangle>"} or @{text "|\<beta>\<^sub>1\<^sub>0\<rangle>"} (resp. @{text "|\<beta>\<^sub>0\<^sub>1\<rangle>"} or @{text "|\<beta>\<^sub>1\<^sub>1\<rangle>"}) if 
one measures the second qubit after a measurement of the first qubit (or the other way around) then 
one gets the same outcomes (resp. opposite outcomes), i.e. for instance the probability of measuring 
$0$ for the second qubit after a measure with outcome $0$ for the first qubit is $1$ (resp. $0$).
\<close>

lemma prob0_bell_fst [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob0 2 v 0 = 1/2" 
proof -
  have set_0 [simp]:"{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k} = {0,1}"
    using select_index_def by auto
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell00_def ket_vec_def)
      finally show  ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell01_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell10_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob0 2 v 0 = 1/2"
    proof -
      have "prob0 2 v 0 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 0 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,1}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell11_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma prob_1_bell_fst [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob1 2 v 0 = 1/2" 
proof -
  have set_0 [simp]:"{k| k::nat. select_index 2 0 k} = {2,3}"
    using select_index_def by auto
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell00_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell01_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell10_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 0 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob1 2 v 0 = 1/2"
    proof -
      have "prob1 2 v 0 = (\<Sum>j\<in>{k| k::nat. select_index 2 0 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{2,3}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell11_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma prob0_bell_snd [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob0 2 v 1 = 1/2" 
proof -
  have set_0 [simp]:"{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k} = {0,2}"
    by (auto simp: select_index_def)
      (metis Suc_le_mono add_Suc add_Suc_right le_numeral_extra(3) less_antisym mod_Suc_eq mod_less 
        neq0_conv not_mod2_eq_Suc_0_eq_0 numeral_2_eq_2 numeral_Bit0 one_add_one one_mod_two_eq_one one_neq_zero) 
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell00_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell01_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell10_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob0 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob0 2 v 1 = 1/2"
    proof -
      have "prob0 2 v 1 = (\<Sum>j\<in>{k| k::nat. (k<4) \<and> \<not> select_index 2 1 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob0_def asm)
      also have "\<dots> = (\<Sum>j\<in>{0,2}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell11_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma prob_1_bell_snd [simp]:
  assumes "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<or> v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
  shows "prob1 2 v 1 = 1/2" 
proof -
  have set_0:"{k| k::nat. select_index 2 1 k} = {1,3}"
    by (auto simp: select_index_def)
      (metis Suc_le_lessD le_SucE le_less mod2_gr_0 mod_less mod_self numeral_2_eq_2 numeral_3_eq_3)
  have "v = |\<beta>\<^sub>0\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>0\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell00 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell00_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>0\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>0\<^sub>1\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell01 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell01_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>0\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>0\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell10 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(1/sqrt(2)))\<^sup>2 + (cmod(0))\<^sup>2"
        by (auto simp: bell10_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  moreover have "v = |\<beta>\<^sub>1\<^sub>1\<rangle> \<Longrightarrow> prob1 2 v 1 = 1/2"
  proof -
    fix v assume asm:"v = |\<beta>\<^sub>1\<^sub>1\<rangle>"
    show "prob1 2 v 1 = 1/2"
    proof -
      have "prob1 2 v 1 = (\<Sum>j\<in>{k| k::nat. select_index 2 1 k}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        by (auto simp: prob1_def asm)
      also have "\<dots> = (\<Sum>j\<in>{1,3}. (cmod(bell11 $$ (j,0)))\<^sup>2)"
        using set_0 by simp
      also have "\<dots> = (cmod(0))\<^sup>2 + (cmod(1/sqrt(2)))\<^sup>2"
        by (auto simp: bell11_def ket_vec_def)
      finally show ?thesis by(simp add: cmod_def power_divide)
    qed
  qed
  ultimately show ?thesis using assms by auto
qed

lemma post_meas0_bell00_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 = |unit_vec 4 0\<rangle>"
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide) 
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell00_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 = |unit_vec 4 0\<rangle>"
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell01_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 = |unit_vec 4 1\<rangle>"
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell01_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 = |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 2\<rangle>" and "j < dim_col |unit_vec 4 2\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 2\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 2\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 2\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 2\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 2\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell10_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 = |unit_vec 4 0\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell10_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 = |unit_vec 4 0\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 0\<rangle>" and "j < dim_col |unit_vec 4 0\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 0\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 0\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 0\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 0\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 0\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 0\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell11_fst [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 = |unit_vec 4 1\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"  
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas0_bell11_snd [simp]:
  "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 = - |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 2\<rangle>)" and "j < dim_col (- |unit_vec 4 2\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (0,0) = (- |unit_vec 4 2\<rangle>) $$ (0,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (1,0) = (- |unit_vec 4 2\<rangle>) $$ (1,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (2,0) = (- |unit_vec 4 2\<rangle>) $$ (2,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide del:One_nat_def)
  moreover have "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (3,0) = (- |unit_vec 4 2\<rangle>) $$ (3,0)"
    by(simp add: post_meas0_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (i,j) = (- |unit_vec 4 2\<rangle>) $$ (i,j)" by auto
next
  show "dim_row (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_row (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas0_def ket_vec_def)
  show "dim_col (post_meas0 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_col (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas0_def ket_vec_def)
qed

lemma post_meas1_bell00_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 = |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 3\<rangle>" and "j < dim_col |unit_vec 4 3\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"  
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (0,0) = |unit_vec 4 3\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (1,0) = |unit_vec 4 3\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (2,0) = |unit_vec 4 3\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (3,0) = |unit_vec 4 3\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0 $$ (i,j) = |unit_vec 4 3\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_row |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 0) = dim_col |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell00_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 = |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 3\<rangle>" and "j < dim_col |unit_vec 4 3\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (0,0) = |unit_vec 4 3\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (1,0) = |unit_vec 4 3\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (2,0) = |unit_vec 4 3\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (3,0) = |unit_vec 4 3\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell00_def ket_vec_def real_sqrt_divide del: One_nat_def)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1 $$ (i,j) = |unit_vec 4 3\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_row |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>0\<rangle> 1) = dim_col |unit_vec 4 3\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell01_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 = |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 2\<rangle>" and "j < dim_col |unit_vec 4 2\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (0,0) = |unit_vec 4 2\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (1,0) = |unit_vec 4 2\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (2,0) = |unit_vec 4 2\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (3,0) = |unit_vec 4 2\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0 $$ (i,j) = |unit_vec 4 2\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_row |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 0) = dim_col |unit_vec 4 2\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell01_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 = |unit_vec 4 1\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide del: One_nat_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell01_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>0\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell10_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 = - |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 3\<rangle>)" and "j < dim_col (- |unit_vec 4 3\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (0,0) = (- |unit_vec 4 3\<rangle>) $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (1,0) = (- |unit_vec 4 3\<rangle>) $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (2,0) = (- |unit_vec 4 3\<rangle>) $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (3,0) = (- |unit_vec 4 3\<rangle>) $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0 $$ (i,j) = (- |unit_vec 4 3\<rangle>) $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_row (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 0) = dim_col (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell10_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 = - |unit_vec 4 3\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 3\<rangle>)" and "j < dim_col (- |unit_vec 4 3\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (0,0) = (- |unit_vec 4 3\<rangle>) $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (1,0) = (- |unit_vec 4 3\<rangle>) $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (2,0) = (- |unit_vec 4 3\<rangle>) $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (3,0) = (- |unit_vec 4 3\<rangle>) $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell10_def ket_vec_def real_sqrt_divide del: One_nat_def)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1 $$ (i,j) = (- |unit_vec 4 3\<rangle>) $$ (i,j)" by auto    
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_row (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>0\<rangle> 1) = dim_col (- |unit_vec 4 3\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell11_fst [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 = - |unit_vec 4 2\<rangle>" 
proof
  fix i j::nat assume "i < dim_row (- |unit_vec 4 2\<rangle>)" and "j < dim_col (- |unit_vec 4 2\<rangle>)"
  then have "i \<in> {0,1,2,3}" and "j = 0" 
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (0,0) = (- |unit_vec 4 2\<rangle>) $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (1,0) = (- |unit_vec 4 2\<rangle>) $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (2,0) = (- |unit_vec 4 2\<rangle>) $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (3,0) = (- |unit_vec 4 2\<rangle>) $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0 $$ (i,j) = (- |unit_vec 4 2\<rangle>) $$ (i,j)" by auto    
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_row (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 0) = dim_col (- |unit_vec 4 2\<rangle>)"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

lemma post_meas1_bell11_snd [simp]:
  "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 = |unit_vec 4 1\<rangle>" 
proof
  fix i j::nat assume "i < dim_row |unit_vec 4 1\<rangle>" and "j < dim_col |unit_vec 4 1\<rangle>"
  then have "i \<in> {0,1,2,3}" and "j = 0"  
    by(auto simp add: ket_vec_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (0,0) = |unit_vec 4 1\<rangle> $$ (0,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (1,0) = |unit_vec 4 1\<rangle> $$ (1,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide del: One_nat_def)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (2,0) = |unit_vec 4 1\<rangle> $$ (2,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  moreover have "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (3,0) = |unit_vec 4 1\<rangle> $$ (3,0)"
    by(simp add: post_meas1_def unit_vec_def select_index_def bell11_def ket_vec_def real_sqrt_divide)
  ultimately show "post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1 $$ (i,j) = |unit_vec 4 1\<rangle> $$ (i,j)" by auto
next
  show "dim_row (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_row |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
  show "dim_col (post_meas1 2 |\<beta>\<^sub>1\<^sub>1\<rangle> 1) = dim_col |unit_vec 4 1\<rangle>"
    by(auto simp add: post_meas1_def ket_vec_def)
qed

end