(*
    Author:      Jose Divasón
    Email:       jose.divason@unirioja.es
*)

section \<open>The Cauchy--Binet formula in HOL Analysis\<close>

theory Cauchy_Binet_HOL_Analysis
  imports
    Cauchy_Binet
    Perron_Frobenius.HMA_Connect
begin

subsection \<open>Definition of submatrices in HOL Analysis\<close>

definition submatrix_hma :: "'a^'nc^'nr\<Rightarrow>nat set\<Rightarrow>nat set\<Rightarrow>('a^'nc2^'nr2)"
  where "submatrix_hma A I J = (\<chi> a b. A $h (from_nat (pick I (to_nat a))) $h (from_nat (pick J (to_nat b))))"

context includes lifting_syntax
begin

context
  fixes I::"nat set" and J::"nat set"
  assumes I: "card {i. i < CARD('nr::finite) \<and> i \<in> I} = CARD('nr2::finite)"
  assumes J: "card {i. i < CARD('nc::finite) \<and> i \<in> J} = CARD('nc2::finite)"
begin

lemma HMA_submatrix[transfer_rule]: "(HMA_M ===> HMA_M) (\<lambda>A. submatrix A I J)
  ((\<lambda>A. submatrix_hma A I J):: 'a^ 'nc ^ 'nr \<Rightarrow> 'a ^ 'nc2 ^ 'nr2)"
proof (intro rel_funI, goal_cases)
  case (1 A B)
  note relAB[transfer_rule] = this
  show ?case unfolding  HMA_M_def
  proof (rule eq_matI, auto)
    show "dim_row (submatrix A I J) = CARD('nr2)"
      unfolding submatrix_def
      using I dim_row_transfer_rule relAB by force
    show "dim_col (submatrix A I J) = CARD('nc2)"
      unfolding submatrix_def
      using J dim_col_transfer_rule relAB by force
    let ?B="(submatrix_hma B I J)::'a ^ 'nc2 ^ 'nr2"
    fix i j assume i: "i < CARD('nr2)" and
           j: "j < CARD('nc2)"
    have i2: "i < card {i. i < dim_row A \<and> i \<in> I}"
      using I dim_row_transfer_rule i relAB by fastforce
    have j2: "j < card {j. j < dim_col A \<and> j \<in> J}"
      using J dim_col_transfer_rule j relAB by fastforce
    let ?i = "(from_nat (pick I i))::'nr"
    let ?j = "(from_nat (pick J j))::'nc"
    let ?i' = "Bij_Nat.to_nat ((Bij_Nat.from_nat i)::'nr2)"
    let ?j' = "Bij_Nat.to_nat ((Bij_Nat.from_nat j)::'nc2)"
    have i': "?i' = i" by (rule to_nat_from_nat_id[OF i])
    have j': "?j' = j" by (rule to_nat_from_nat_id[OF j])
    let ?f = "(\<lambda>(i, j).
         B $h Bij_Nat.from_nat (pick I (Bij_Nat.to_nat ((Bij_Nat.from_nat i)::'nr2))) $h
         Bij_Nat.from_nat (pick J (Bij_Nat.to_nat ((Bij_Nat.from_nat j)::'nc2))))"
    have [transfer_rule]: "HMA_I (pick I i) ?i"
      by (simp add: Bij_Nat.to_nat_from_nat_id I i pick_le HMA_I_def)
    have [transfer_rule]: "HMA_I (pick J j) ?j"
      by (simp add: Bij_Nat.to_nat_from_nat_id J j pick_le HMA_I_def)
    have "submatrix A I J $$ (i, j) = A $$ (pick I i, pick J j)" by (rule submatrix_index[OF i2 j2])
    also have "... = index_hma B ?i ?j" by (transfer, simp)
    also have "... =  B $h Bij_Nat.from_nat (pick I (Bij_Nat.to_nat ((Bij_Nat.from_nat i)::'nr2))) $h
         Bij_Nat.from_nat (pick J (Bij_Nat.to_nat ((Bij_Nat.from_nat j)::'nc2)))"
      unfolding i' j' index_hma_def by auto
    also have "... = ?f (i,j)" by auto
    also have "... = Matrix.mat CARD('nr2) CARD('nc2) ?f $$ (i, j)"
      by (rule index_mat[symmetric, OF i j])
    also have "... = from_hma\<^sub>m ?B $$ (i, j)"
      unfolding from_hma\<^sub>m_def submatrix_hma_def by auto
    finally show "submatrix A I J $$ (i, j) = from_hma\<^sub>m ?B $$ (i, j)" .
  qed
qed

end
end


subsection \<open>Transferring the proof from JNF to HOL Analysis\<close>

lemma Cauchy_Binet_HOL_Analysis:
  fixes A::"'a::comm_ring_1^'m^'n" and B::"'a^'n^'m"
  shows "Determinants.det (A**B) = (\<Sum>I\<in>{I. I\<subseteq>{0..<ncols A} \<and> card I=nrows A}.
         Determinants.det ((submatrix_hma A UNIV I)::'a^'n^'n) *
         Determinants.det ((submatrix_hma B I UNIV)::'a^'n^'n))"
proof -
  let ?A = "(from_hma\<^sub>m A)"
  let ?B = "(from_hma\<^sub>m B)"
  have relA[transfer_rule]: "HMA_M ?A A" unfolding HMA_M_def by simp
  have relB[transfer_rule]: "HMA_M ?B B" unfolding HMA_M_def by simp
  have "(\<Sum>I\<in>{I. I\<subseteq>{0..<ncols A} \<and> card I = nrows A}.
         Determinants.det ((submatrix_hma A UNIV I)::'a^'n^'n) *
         Determinants.det ((submatrix_hma B I UNIV)::'a^'n^'n)) =
          (\<Sum>I\<in>{I. I\<subseteq>{0..<ncols A} \<and> card I=nrows A}. det (submatrix ?A UNIV I)
        * det (submatrix ?B I UNIV))"
  proof (rule sum.cong)
    fix I assume I: "I \<in>{I. I\<subseteq>{0..<ncols A} \<and> card I=nrows A}"
    let ?sub_A= "((submatrix_hma A UNIV I)::'a^'n^'n)"
    let ?sub_B= "((submatrix_hma B I UNIV)::'a^'n^'n)"
    have c1: "card {i. i < CARD('n) \<and> i \<in> UNIV} = CARD('n)" using I by auto
    have c2: "card {i. i < CARD('m) \<and> i \<in> I} = CARD('n)"
    proof -
      have "I = {i. i < CARD('m) \<and> i \<in> I}" using I unfolding nrows_def ncols_def by auto
      thus ?thesis using I nrows_def by auto
    qed
    have [transfer_rule]: "HMA_M (submatrix ?A UNIV I) ?sub_A"
      using HMA_submatrix[OF c1 c2] relA unfolding rel_fun_def by auto
    have [transfer_rule]: "HMA_M (submatrix ?B I UNIV) ?sub_B"
      using HMA_submatrix[OF c2 c1] relB unfolding rel_fun_def by auto
    show "Determinants.det ?sub_A * Determinants.det ?sub_B
      = det (submatrix ?A UNIV I) * det (submatrix ?B I UNIV)" by (transfer', auto)
  qed (auto)
  also have "... = det (?A*?B)"
    by (rule Cauchy_Binet[symmetric], unfold nrows_def ncols_def, auto)
  also have "... = Determinants.det (A**B)" by (transfer', auto)
  finally show ?thesis ..
qed

end