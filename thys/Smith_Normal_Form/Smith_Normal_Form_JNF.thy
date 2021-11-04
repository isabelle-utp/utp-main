(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Definition of Smith normal form in JNF\<close>

theory Smith_Normal_Form_JNF
  imports
    SNF_Missing_Lemmas
begin

text \<open>Now, we define diagonal matrices and Smith normal form in JNF\<close>

definition "isDiagonal_mat A = (\<forall>i j. i \<noteq> j \<and> i < dim_row A \<and> j < dim_col A \<longrightarrow> A$$(i,j) = 0)"

definition "Smith_normal_form_mat A = 
  (
    (\<forall>a. a + 1 < min (dim_row A) (dim_col A) \<longrightarrow> A $$ (a,a) dvd A $$ (a+1,a+1))
    \<and> isDiagonal_mat A    
  )"

lemma SNF_first_divides:
  assumes SNF_A: "Smith_normal_form_mat A" and "(A::('a::comm_ring_1) mat) \<in> carrier_mat n m"
  and i: "i < min (dim_row A) (dim_col A)"
shows "A $$ (0,0) dvd A $$ (i,i)"
  using i
proof (induct i)
  case 0
  then show ?case by auto
next
  case (Suc i)
  show ?case 
    by (metis (full_types) Smith_normal_form_mat_def Suc.hyps Suc.prems 
        Suc_eq_plus1 Suc_lessD SNF_A dvd_trans)
qed

lemma Smith_normal_form_mat_intro:
  assumes "(\<forall>a. a + 1 < min (dim_row A) (dim_col A) \<longrightarrow> A $$ (a,a) dvd A $$ (a+1,a+1))"
    and "isDiagonal_mat A" 
  shows "Smith_normal_form_mat A"
  unfolding Smith_normal_form_mat_def using assms by auto

lemma Smith_normal_form_mat_m0[simp]:
  assumes A: "A\<in>carrier_mat m 0"
  shows "Smith_normal_form_mat A"
  using A unfolding Smith_normal_form_mat_def isDiagonal_mat_def by auto

lemma Smith_normal_form_mat_0m[simp]:
  assumes A: "A\<in>carrier_mat 0 m"
  shows "Smith_normal_form_mat A"
  using A unfolding Smith_normal_form_mat_def isDiagonal_mat_def by auto

lemma S00_dvd_all_A:
  assumes A: "(A::'a::comm_ring_1 mat) \<in> carrier_mat m n"
  and P: "P \<in> carrier_mat m m"
  and Q: "Q \<in> carrier_mat n n"
  and inv_P: "invertible_mat P"
  and inv_Q: "invertible_mat Q"
  and S_PAQ: "S = P*A*Q"
  and SNF_S: "Smith_normal_form_mat S"
  and i: "i<m" and j: "j<n"
shows "S$$(0,0) dvd A $$ (i,j)"
proof -
  have S00: "(\<forall>i j. i<m \<and> j<n \<longrightarrow> S$$(0,0) dvd S$$(i,j))"
    using SNF_S unfolding Smith_normal_form_mat_def isDiagonal_mat_def
    by (smt P Q SNF_first_divides A S_PAQ SNF_S carrier_matD 
        dvd_0_right min_less_iff_conj mult_carrier_mat)
    obtain P' where PP': "inverts_mat P P'" and P'P: "inverts_mat P' P"
      using inv_P unfolding invertible_mat_def by auto
    obtain Q' where QQ': "inverts_mat Q Q'" and Q'Q: "inverts_mat Q' Q"
      using inv_Q unfolding invertible_mat_def by auto
    have A_P'SQ': "P'*S*Q' = A"
    proof -
      have "P'*S*Q' = P'*(P*A*Q)*Q'" unfolding S_PAQ by auto
      also have "... = (P'*P)*A*(Q*Q')"
        by (smt A PP' Q Q'Q P assoc_mult_mat carrier_mat_triv index_mult_mat(2) index_mult_mat(3) 
            index_one_mat(3) inverts_mat_def right_mult_one_mat)
      also have "... = A"
        by (metis A P'P QQ' A Q P carrier_matD(1) index_mult_mat(3) index_one_mat(3) inverts_mat_def
            left_mult_one_mat right_mult_one_mat)
      finally show ?thesis .
    qed
    have "(\<forall>i j. i<m \<and> j<n \<longrightarrow> S$$(0,0) dvd (P'*S*Q')$$(i,j))"
    proof (rule dvd_elements_mult_matrix_left_right[OF _ _ _ S00])
      show "S \<in> carrier_mat m n" using P A Q S_PAQ by auto
      show "P' \<in> carrier_mat m m"
        by (metis (mono_tags, lifting) A_P'SQ' PP' P A carrier_matD carrier_matI index_mult_mat(2) 
            index_mult_mat(3) inverts_mat_def one_carrier_mat)
      show "Q' \<in> carrier_mat n n"
        by (metis (mono_tags, lifting) A_P'SQ' Q'Q Q A carrier_matD(2) carrier_matI 
            index_mult_mat(3) inverts_mat_def one_carrier_mat)
    qed
    thus ?thesis using A_P'SQ' i j by auto
qed


lemma SNF_first_divides_all:
  assumes SNF_A: "Smith_normal_form_mat A" and A: "(A::('a::comm_ring_1) mat) \<in> carrier_mat m n"
  and i: "i < m" and j: "j<n"
shows "A $$ (0,0) dvd A $$ (i,j)"
proof (cases "i=j")
  case True
  then show ?thesis using assms SNF_first_divides by (metis carrier_matD min_less_iff_conj)
next
  case False
  hence "A$$(i,j) = 0" using SNF_A i j A unfolding Smith_normal_form_mat_def isDiagonal_mat_def by auto
  then show ?thesis by auto
qed

(*This can also be obtained from HOL Analysis via local type definitions*)
lemma SNF_divides_diagonal:
  fixes A::"'a::comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n m" 
    and SNF_A: "Smith_normal_form_mat A"
    and j: "j < min n m"
    and ij: "i\<le>j"
  shows "A$$(i,i) dvd A$$(j,j)" 
  using ij j
proof (induct j)
  case 0
  then show ?case by auto
next
  case (Suc j)
  show ?case
  proof (cases "i\<le>j")
    case True
    have "A $$ (i, i) dvd A $$ (j, j)" using Suc.hyps Suc.prems True by simp
    also have "... dvd A $$ (Suc j, Suc j)" 
      using SNF_A Suc.prems A 
      unfolding Smith_normal_form_mat_def by auto
    finally show ?thesis by auto 
  next
    case False
    hence "i=Suc j" using Suc.prems by auto
    then show ?thesis by auto
  qed
qed

lemma Smith_zero_imp_zero:
  fixes A::"'a::comm_ring_1 mat"
  assumes  A: "A \<in> carrier_mat m n"
    and SNF: "Smith_normal_form_mat A"
    and Aii: "A$$(i,i) = 0" 
    and j: "j<min m n" 
    and ij: "i\<le>j"
  shows "A$$(j,j) = 0"
proof -
  have "A$$(i,i) dvd A$$(j,j)" by (rule SNF_divides_diagonal[OF A SNF j ij])
  thus ?thesis using Aii by auto
qed

lemma SNF_preserved_multiples_identity:
  assumes S: "S \<in> carrier_mat m n" and SNF: "Smith_normal_form_mat (S::'a::comm_ring_1 mat)"
  shows "Smith_normal_form_mat (S*(k \<cdot>\<^sub>m 1\<^sub>m n))"
proof (rule Smith_normal_form_mat_intro)
  have rw: "S*(k \<cdot>\<^sub>m 1\<^sub>m n) = Matrix.mat m n (\<lambda>(i, j). S $$ (i, j) * k)"
    unfolding mat_diag_smult[symmetric] by (rule mat_diag_mult_right[OF S])
  show "isDiagonal_mat (S * (k \<cdot>\<^sub>m 1\<^sub>m n))" 
    using SNF S unfolding Smith_normal_form_mat_def isDiagonal_mat_def rw
    by auto
  show "\<forall>a. a + 1 < min (dim_row (S * (k \<cdot>\<^sub>m 1\<^sub>m n))) (dim_col (S * (k \<cdot>\<^sub>m 1\<^sub>m n))) \<longrightarrow>
        (S * (k \<cdot>\<^sub>m 1\<^sub>m n)) $$ (a, a) dvd (S * (k \<cdot>\<^sub>m 1\<^sub>m n)) $$ (a + 1, a + 1)"
    using SNF S unfolding Smith_normal_form_mat_def isDiagonal_mat_def rw
    by (auto simp add: mult_dvd_mono)
qed

end
