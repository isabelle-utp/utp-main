(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Executable Smith normal form algorithm over Euclidean domains\<close>

theory SNF_Algorithm_Euclidean_Domain
  imports
    Diagonal_To_Smith
    Echelon_Form.Examples_Echelon_Form_Abstract

    Elementary_Divisor_Rings 
    Diagonal_To_Smith_JNF

    Mod_Type_Connect
    Show.Show_Instances
    Jordan_Normal_Form.Show_Matrix
    Show.Show_Poly    
begin

text \<open>This provides an executable implementation of the verified general algorithm, provinding
executable operations over a Euclidean domain.\<close>

lemma zero_less_one_type2: "(0::2) < 1"
proof -
  have "Mod_Type.from_nat 0 = (0::2)" by (simp add: from_nat_0)
  moreover have "Mod_Type.from_nat 1 = (1::2)" using from_nat_1 by blast
  moreover have "(Mod_Type.from_nat 0::2) < Mod_Type.from_nat 1" by (rule from_nat_mono, auto)
  ultimately show ?thesis by simp
qed

subsection \<open>Previous code equations\<close>
(*Firstly, code equations for Mod_Type_Connect.to_hma\<^sub>m*)

definition "to_hma\<^sub>m_row A i
  = (vec_lambda (\<lambda>j. A $$ (Mod_Type.to_nat i, Mod_Type.to_nat j)))"

lemma bezout_matrix_row_code [code abstract]:
  "vec_nth (to_hma\<^sub>m_row A i) = 
      (\<lambda>j. A $$ (Mod_Type.to_nat i, Mod_Type.to_nat j))"
  unfolding to_hma\<^sub>m_row_def by auto 

lemma [code abstract]: "vec_nth (Mod_Type_Connect.to_hma\<^sub>m A) = to_hma\<^sub>m_row A"
  unfolding Mod_Type_Connect.to_hma\<^sub>m_def  unfolding to_hma\<^sub>m_row_def[abs_def]
  by auto


subsection \<open>An executable algorithm to transform $2 \times 2$ matrices into its Smith normal form
in HOL Analysis\<close>
(*

There are several alternatives to obtain an algorithm to transform a 2x2 matrix (over 
a euclidean domain) into its Smith normal form. One of them is diagonalize + diagonal to Smith.

To take advantage of existing results in HOL Analysis (HA), we proceed as follows:

  1) We implement an algorithm to diagonalize a matrix in HA, taking advantage of the existing 
     bezout matrix
  2) Then, we transform the diagonal matrix to its Smith normal form using the diagonal_to_Smith
     algorithm in HA, already proved.
  3) We define an algorithm in JNF based on the one in HA, which is possible since the types 
     are known. Then, transfer the results to JNF.
*)

subclass (in euclidean_ring_gcd) bezout_ring_div
proof qed

(*value[code] "let (P,S,Q) = (diagonal_to_Smith_PQ ((list_of_list_to_matrix [[4,0],[0,10]])::int^2^2) euclid_ext2)
  in (matrix_to_list_of_list P,matrix_to_list_of_list S,matrix_to_list_of_list Q)"*)

context
  fixes bezout::"('a::euclidean_ring_gcd \<Rightarrow> 'a \<Rightarrow> ('a\<times>'a\<times>'a\<times>'a\<times>'a))"
  assumes ib: "is_bezout_ext bezout"
begin

lemma normalize_bezout_gcd: 
  assumes b: "(p,q,u,v,d) = bezout a b"
  shows "normalize d = gcd a b"
proof -
  let ?gcd = "(\<lambda>a b. case bezout a b of (x, xa,u,v, gcd') \<Rightarrow> gcd')"
  have is_gcd: "is_gcd ?gcd" by (simp add: ib is_gcd_is_bezout_ext)
  have "(?gcd a b) = d" using b by (metis case_prod_conv)
  moreover have "normalize (?gcd a b) = normalize (gcd a b)"
  proof (rule associatedI)
    show "(?gcd a b) dvd (gcd a b)" using is_gcd is_gcd_def by fastforce
    show "(gcd a b) dvd (?gcd a b)" by (metis (no_types) gcd_dvd1 gcd_dvd2 is_gcd is_gcd_def)
  qed
  ultimately show ?thesis by auto
qed

end


lemma bezout_matrix_works_transpose1:
  assumes ib: "is_bezout_ext bezout"
  and a_not_b: "a \<noteq> b"
shows "(A**transpose (bezout_matrix (transpose A) a b i bezout)) $ i $ a 
    = snd (snd (snd (snd (bezout (A $ i $ a) (A $ i $ b)))))"
proof -
  have "(A**transpose (bezout_matrix (transpose A) a b i bezout)) $h i $h a 
    = transpose (A**transpose (bezout_matrix (transpose A) a b i bezout)) $h a $h i"
    by (simp add: transpose_code transpose_row_code)
  also have "... = ((bezout_matrix (transpose A) a b i bezout) ** (transpose A)) $h a $h i"
    by (simp add: matrix_transpose_mul)
  also have "... = snd (snd (snd (snd (bezout ((transpose A) $ a $ i) ((transpose A) $ b $ i)))))"
    by (rule bezout_matrix_works1[OF ib a_not_b])
  also have "... = snd (snd (snd (snd (bezout (A $ i $ a) (A $ i $ b)))))"
    by (simp add: transpose_code transpose_row_code)
  finally show ?thesis .
qed

lemma invertible_bezout_matrix_transpose:
 fixes A::"'a::{bezout_ring_div}^'cols::{finite,wellorder}^'rows"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b"
  and aj: "A $h i $h a \<noteq> 0"
shows "invertible (transpose (bezout_matrix (transpose A) a b i bezout))"
proof -
  have "Determinants.det (bezout_matrix (transpose A) a b i bezout) = 1"
    by (rule det_bezout_matrix[OF ib a_less_b], insert aj, auto simp add: transpose_def)
  hence "Determinants.det (transpose (bezout_matrix (transpose A) a b i bezout)) = 1" by simp
  thus ?thesis by (simp add: invertible_iff_is_unit)
qed


(*I will have to ensure that a is not zero before starting the algorithm (moving the pivot)*)
function diagonalize_2x2_aux :: "(('a::euclidean_ring_gcd^2^2) \<times> ('a^2^2)\<times>('a^2^2)) \<Rightarrow> 
                                  (('a^2^2) \<times>('a^2^2)\<times>('a^2^2))"
  where "diagonalize_2x2_aux (P,A,Q)  =
(
  let 
      a = A $h 0 $h 0;
      b = A $h 0 $h 1;
      c = A $h 1 $h 0;
      d = A $h 1 $h 1 in
      if a\<noteq> 0 \<and> \<not> a dvd b then let bezout_mat = transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2) in
       diagonalize_2x2_aux (P, A**bezout_mat,Q**bezout_mat) else
        if  a \<noteq> 0 \<and> \<not> a dvd c then let bezout_mat = bezout_matrix A 0 1 0 euclid_ext2
      in diagonalize_2x2_aux (bezout_mat**P,bezout_mat**A,Q) else \<comment> \<open>We can divide an get zeros\<close>
      let Q' = column_add (Finite_Cartesian_Product.mat 1) 1 0 (- (b div a));
          P' = row_add (Finite_Cartesian_Product.mat 1) 1 0 (- (c div a)) in
        (P'**P,P'**A**Q',Q**Q')
)" by auto

(*The algorithm terminates since the euclidean size of the A $h 0 $h 0 element gets reduced.*)
termination 
proof-
  have ib: "is_bezout_ext euclid_ext2" by (simp add: is_bezout_ext_euclid_ext2)
  have "euclidean_size ((bezout_matrix A 0 1 0 euclid_ext2 ** A) $h 0 $h 0) < euclidean_size (A $h 0 $h 0)"
    if a_not_dvd_c: "\<not> A $h 0 $h 0 dvd A $h 1 $h 0" and a_not0: "A $h 0 $h 0 \<noteq> 0" for A::"'a^2^2"
  proof-
    let ?a = "(A $h 0 $h 0)" let ?c = "(A $h 1 $h 0)"
    obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 ?a ?c" by (metis prod_cases5)
    have "(bezout_matrix A 0 1 0 euclid_ext2 ** A) $h 0 $h 0 = d"      
      by (metis bezout_matrix_works1 ib one_neq_zero pquvd prod.sel(2))
    hence "normalize ((bezout_matrix A 0 1 0 euclid_ext2 ** A) $h 0 $h 0) = normalize d" by auto
    also have "... = gcd ?a ?c" by (rule normalize_bezout_gcd[OF ib pquvd])
    finally have "euclidean_size ((bezout_matrix A 0 1 0 euclid_ext2 ** A) $h 0 $h 0) 
      = euclidean_size (gcd ?a ?c)" by (metis euclidean_size_normalize)
    also have "... < euclidean_size ?a" by (rule euclidean_size_gcd_less1[OF a_not0 a_not_dvd_c])
    finally show ?thesis .
  qed
  moreover have "euclidean_size ((A ** transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2)) $h 0 $h 0)
      < euclidean_size (A $h 0 $h 0)"
    if a_not_dvd_b: "\<not> A $h 0 $h 0 dvd A $h 0 $h 1" and a_not0: "A $h 0 $h 0 \<noteq> 0" for A::"'a^2^2"
  proof-
    let ?a = "(A $h 0 $h 0)" let ?b = "(A $h 0 $h 1)"
    obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 ?a ?b" by (metis prod_cases5)
    have "(A ** transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2)) $h 0 $h 0 = d"
      by (metis bezout_matrix_works_transpose1 ib pquvd prod.sel(2) zero_neq_one)
    hence "normalize ((A ** transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2)) $h 0 $h 0) = normalize d" by auto
    also have "... = gcd ?a ?b" by (rule normalize_bezout_gcd[OF ib pquvd])
    finally have "euclidean_size ((A ** transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2)) $h 0 $h 0)
      = euclidean_size (gcd ?a ?b)" by (metis euclidean_size_normalize)
    also have "... < euclidean_size ?a" by (rule euclidean_size_gcd_less1[OF a_not0 a_not_dvd_b])
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by (relation "Wellfounded.measure (\<lambda>(P,A,Q). euclidean_size (A $h 0 $h 0))", auto)
qed


lemma diagonalize_2x2_aux_works:
  assumes  "A = P ** A_input ** Q"
    and "invertible P" and "invertible Q"
    and "(P',D,Q') = diagonalize_2x2_aux (P,A,Q)"
    and "A $h 0 $h 0 \<noteq> 0"
  shows "D = P' ** A_input ** Q' \<and> invertible P' \<and> invertible Q' \<and> isDiagonal D"
  using assms
proof (induct "(P,A,Q)" arbitrary: P A Q rule: diagonalize_2x2_aux.induct)
  case (1 P A Q)
  let ?a = "A $h 0 $h 0"
  let ?b = "A $h 0 $h 1"
  let ?c = "A $h 1 $h 0"
  let ?d = "A $h 1 $h 1"
  have a_not_0: "?a \<noteq> 0" using "1.prems" by blast
  have ib: "is_bezout_ext euclid_ext2" by (simp add: is_bezout_ext_euclid_ext2)
  have one_not_zero: "1 \<noteq> (0::2)" by auto
  show ?case 
  proof (cases "\<not> ?a dvd ?b")
    case True
    let ?bezout_mat_right = "transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2)"
    have "(P', D, Q') = diagonalize_2x2_aux (P, A, Q)" using "1.prems" by blast 
    also have "... = diagonalize_2x2_aux (P, A** ?bezout_mat_right, Q ** ?bezout_mat_right)"
      using True a_not_0 by (auto simp add: Let_def)
    finally have eq: "(P',D,Q') = ..." .
    show ?thesis
    proof (rule "1.hyps"(1)[OF  _ _ _ _ _ _ _ _ _ eq])
      have "invertible ?bezout_mat_right" 
        by (rule invertible_bezout_matrix_transpose[OF ib zero_less_one_type2 a_not_0])
      thus "invertible (Q ** ?bezout_mat_right)"
        using "1.prems" invertible_mult by blast
      show "A ** ?bezout_mat_right = P ** A_input ** (Q ** ?bezout_mat_right)"
        by (simp add: "1.prems" matrix_mul_assoc)    
      show "(A ** ?bezout_mat_right) $h 0 $h 0 \<noteq> 0"
        by (metis (no_types, lifting) a_not_0 bezout_matrix_works_transpose1 bezout_matrix_not_zero  
           bezout_matrix_works1 is_bezout_ext_euclid_ext2 one_neq_zero transpose_code transpose_row_code)
    qed (insert True a_not_0  "1.prems", blast+)
  next
    case False note a_dvd_b = False
    show ?thesis
    proof (cases "\<not> ?a dvd ?c")
      case True
      let ?bezout_mat = "(bezout_matrix A 0 1 0 euclid_ext2)"
      have "(P', D, Q') = diagonalize_2x2_aux (P, A, Q)" using "1.prems" by blast 
      also have "... = diagonalize_2x2_aux (?bezout_mat**P, ?bezout_mat ** A, Q)"
      using True a_dvd_b a_not_0 by (auto simp add: Let_def)
      finally have eq: "(P',D,Q') = ..." .
      show ?thesis 
      proof (rule "1.hyps"(2)[OF _ _ _ _ _ _ _ _ _ _ eq])
        have "invertible ?bezout_mat" 
        by (rule invertible_bezout_matrix[OF ib zero_less_one_type2 a_not_0])
        thus "invertible (?bezout_mat ** P)"
          using "1.prems" invertible_mult by blast
        show "?bezout_mat ** A = (?bezout_mat ** P) ** A_input ** Q"
          by (simp add: "1.prems" matrix_mul_assoc)
        show "(?bezout_mat ** A) $h 0 $h 0 \<noteq> 0"
          by (simp add: a_not_0 bezout_matrix_not_zero is_bezout_ext_euclid_ext2)
      qed (insert True a_not_0 a_dvd_b "1.prems", blast+)
    next
      case False
      hence a_dvd_c: "?a dvd ?c" by simp
      let ?Q' = "column_add (Finite_Cartesian_Product.mat 1) 1 0 (- (?b div ?a))::'a^2^2"
      let ?P' = "(row_add (Finite_Cartesian_Product.mat 1) 1 0 (- (?c div ?a)))::'a^2^2"
      have eq: "(P', D, Q') =  (?P'**P,?P'**A**?Q',Q**?Q')" 
        using "1.prems" a_dvd_b a_dvd_c a_not_0 by (auto simp add: Let_def)
      have d: "isDiagonal (?P'**A**?Q')"
      proof -
        {
        fix a b::2 assume a_not_b: "a \<noteq> b"
        have "(?P' ** A ** ?Q') $h a $h b = 0"
        proof (cases "(a,b) = (0,1)")
          case True
          hence a0: "a = 0" and b1: "b = 1" by auto
          have "(?P' ** A ** ?Q') $h a $h b = (?P' ** (A ** ?Q')) $h a $h b" 
            by (simp add: matrix_mul_assoc)
          also have "... = (A**?Q') $h a $h b" unfolding row_add_mat_1
            by (smt True a_not_b prod.sel(2) row_add_def vec_lambda_beta)
          also have "... = 0" unfolding column_add_mat_1 a0 b1
            by (smt Groups.mult_ac(2) a_dvd_b ab_group_add_class.ab_left_minus add_0_left
                add_diff_cancel_left' add_uminus_conv_diff column_add_code_nth column_add_row_def
                comm_semiring_class.distrib dvd_div_mult_self vec_lambda_beta)
          finally show ?thesis .
        next
          case False
          hence a1: "a = 1" and b0: "b = 0"
            by (metis (no_types, hide_lams) False a_not_b exhaust_2 zero_neq_one)+
          have "(?P' ** A ** ?Q') $h a $h b = (?P' ** A) $h a $h b" 
            unfolding a1 b0 column_add_mat_1
            by (simp add: column_add_code_nth column_add_row_def)
          also have "... = 0" unfolding row_add_mat_1 a1 b0
            by (simp add: a_dvd_c row_add_def)
          finally show ?thesis .
        qed}
      thus ?thesis unfolding isDiagonal_def by auto
      qed
      have inv_P': "invertible ?P'" by (rule invertible_row_add[OF one_not_zero])
      have inv_Q': "invertible ?Q'" by (rule invertible_column_add[OF one_not_zero])
      have "invertible (?P'**P)" using "1.prems"(2) inv_P' invertible_mult by blast
      moreover have "invertible (Q**?Q')" using "1.prems"(3) inv_Q' invertible_mult by blast
      moreover have "D = P' ** A_input ** Q'"
        by (metis (no_types, lifting) "1.prems"(1) Pair_inject eq matrix_mul_assoc)
      ultimately show ?thesis using eq d by auto
    qed    
  qed
qed


definition "diagonalize_2x2 A = 
  (if A $h 0 $h 0 = 0 then 
        if A $h 0 $h 1 \<noteq> 0 then 
            let A' = interchange_columns A 0 1;
                Q' = interchange_columns (Finite_Cartesian_Product.mat 1) 0 1 in
            diagonalize_2x2_aux (Finite_Cartesian_Product.mat 1, A', Q')
        else 
            if A $h 1 $h 0 \<noteq> 0 then
                  let A' = interchange_rows A 0 1;
                      P' = interchange_rows (Finite_Cartesian_Product.mat 1) 0 1 in
                   diagonalize_2x2_aux (P', A', Finite_Cartesian_Product.mat 1)
            else (Finite_Cartesian_Product.mat 1,A,Finite_Cartesian_Product.mat 1)
   else diagonalize_2x2_aux (Finite_Cartesian_Product.mat 1,A,Finite_Cartesian_Product.mat 1)
)"


lemma diagonalize_2x2_works:
  assumes PDQ: "(P,D,Q) = diagonalize_2x2 A"
  shows "D = P ** A ** Q \<and> invertible P \<and> invertible Q \<and> isDiagonal D"
proof -
  let ?a = "A $h 0 $h 0"
  let ?b = "A $h 0 $h 1"
  let ?c = "A $h 1 $h 0"
  let ?d = "A $h 1 $h 1"
  show ?thesis
  proof (cases "?a = 0")
    case False
    hence eq: "(P,D,Q) = diagonalize_2x2_aux (Finite_Cartesian_Product.mat 1,A,Finite_Cartesian_Product.mat 1)"
      using PDQ unfolding diagonalize_2x2_def by auto 
    show ?thesis 
      by (rule diagonalize_2x2_aux_works[OF _ _ _ eq False], auto simp add: invertible_mat_1)
  next
    case True note a0 = True
    show ?thesis
    proof (cases "?b \<noteq> 0")
      case True
      let ?A' = "interchange_columns A 0 1"
      let ?Q' = "(interchange_columns (Finite_Cartesian_Product.mat 1) 0 1)::'a^2^2"
      have eq: "(P,D,Q) = diagonalize_2x2_aux (Finite_Cartesian_Product.mat 1, ?A', ?Q')"
        using PDQ a0 True unfolding diagonalize_2x2_def by (auto simp add: Let_def)
      show ?thesis 
      proof (rule diagonalize_2x2_aux_works[OF _ _ _ eq _])
        show "?A' $h 0 $h 0 \<noteq> 0"
          by (simp add: True interchange_columns_code interchange_columns_code_nth)
        show "invertible ?Q'" by (simp add: invertible_interchange_columns)
        show "?A' = Finite_Cartesian_Product.mat 1 ** A ** ?Q'"
          by (simp add: interchange_columns_mat_1)
      qed (auto simp add: invertible_mat_1)
    next
      case False note b0 = False
      show ?thesis
      proof (cases "?c \<noteq> 0")
        case True
        let ?A' = "interchange_rows A 0 1"
        let ?P' = "(interchange_rows (Finite_Cartesian_Product.mat 1) 0 1)::'a^2^2"
        have eq: "(P,D,Q) = diagonalize_2x2_aux (?P', ?A',Finite_Cartesian_Product.mat 1)"
          using PDQ a0 b0 True unfolding diagonalize_2x2_def by (auto simp add: Let_def)
        show ?thesis 
        proof (rule diagonalize_2x2_aux_works[OF _ _ _ eq _])
          show "?A' $h 0 $h 0 \<noteq> 0"
            by (simp add: True interchange_columns_code interchange_columns_code_nth)
          show "invertible ?P'" by (simp add: invertible_interchange_rows)
          show "?A' = ?P' ** A ** Finite_Cartesian_Product.mat 1"
            by (simp add: interchange_rows_mat_1)
        qed (auto simp add: invertible_mat_1)
      next
        case False
        have eq: "(P,D,Q) = (Finite_Cartesian_Product.mat 1, A,Finite_Cartesian_Product.mat 1)"
          using PDQ a0 b0 True False unfolding diagonalize_2x2_def by (auto simp add: Let_def)
        have "isDiagonal A" unfolding isDiagonal_def using a0 b0 True False
          by (metis (full_types) exhaust_2 one_neq_zero) 
        thus ?thesis using invertible_mat_1 eq by auto
      qed  
    qed
  qed
qed
  

definition "diagonalize_2x2_JNF (A::'a::euclidean_ring_gcd mat) 
  = (let (P,D,Q) = diagonalize_2x2 (Mod_Type_Connect.to_hma\<^sub>m A::'a^2^2) in 
  (Mod_Type_Connect.from_hma\<^sub>m P,Mod_Type_Connect.from_hma\<^sub>m D,Mod_Type_Connect.from_hma\<^sub>m Q))"


(*Obtained via transfer rules*)
lemma diagonalize_2x2_JNF_works:
  assumes A: "A \<in> carrier_mat 2 2"
  and PDQ: "(P,D,Q) = diagonalize_2x2_JNF A"
  shows "D = P * A * Q \<and> invertible_mat P \<and> invertible_mat Q \<and> isDiagonal_mat D \<and> P\<in>carrier_mat 2 2
  \<and> Q \<in> carrier_mat 2 2 \<and> D \<in> carrier_mat 2 2"
proof -
  let ?A = "(Mod_Type_Connect.to_hma\<^sub>m A::'a^2^2)"
  have A[transfer_rule]: "Mod_Type_Connect.HMA_M A ?A" 
    using A unfolding Mod_Type_Connect.HMA_M_def by auto
  obtain P_HMA D_HMA Q_HMA where PDQ_HMA: "(P_HMA,D_HMA,Q_HMA) = diagonalize_2x2 ?A" 
    by (metis prod_cases3)
(*  have "HMA_M3 (diagonalize_2x2_JNF A) (diagonalize_2x2 ?A)"
    using HMA_diagonalize_2x2 A rel_funE by fastforce*)  
  have P: "P = Mod_Type_Connect.from_hma\<^sub>m P_HMA" and Q: "Q = Mod_Type_Connect.from_hma\<^sub>m Q_HMA" 
    and D: "D = Mod_Type_Connect.from_hma\<^sub>m D_HMA" 
    using PDQ_HMA PDQ unfolding diagonalize_2x2_JNF_def 
    by (metis prod.simps(1) split_conv)+ 
  have [transfer_rule]: "Mod_Type_Connect.HMA_M P P_HMA" 
    unfolding Mod_Type_Connect.HMA_M_def using P by auto
  have [transfer_rule]: "Mod_Type_Connect.HMA_M Q Q_HMA" 
    unfolding Mod_Type_Connect.HMA_M_def using Q by auto
  have [transfer_rule]: "Mod_Type_Connect.HMA_M D D_HMA" 
    unfolding Mod_Type_Connect.HMA_M_def using D by auto
  have r: "D_HMA = P_HMA ** ?A ** Q_HMA \<and> invertible P_HMA \<and> invertible Q_HMA \<and> isDiagonal D_HMA"
    by (rule diagonalize_2x2_works[OF PDQ_HMA])
  have "D = P * A * Q \<and> invertible_mat P \<and> invertible_mat Q \<and> isDiagonal_mat D" 
    using r by (transfer, rule)
  thus ?thesis using P Q D by auto 
qed



(*The full algorithm in HOL Analysis*)
definition "Smith_2x2_eucl A = (
  let (P,D,Q) = diagonalize_2x2 A;
      (P',S,Q') = diagonal_to_Smith_PQ D euclid_ext2
  in (P' ** P, S, Q ** Q'))"

lemma Smith_2x2_eucl_works:
  assumes PBQ: "(P,S,Q) = Smith_2x2_eucl A"
  shows "S = P ** A ** Q \<and> invertible P \<and> invertible Q \<and> Smith_normal_form S"   
proof -
  have ib: "is_bezout_ext euclid_ext2" by (simp add: is_bezout_ext_euclid_ext2)
  obtain P1 D Q1 where P1DQ1: "(P1,D,Q1) = diagonalize_2x2 A" by (metis prod_cases3)
  obtain P2 S' Q2 where P2SQ2:"(P2,S',Q2) = diagonal_to_Smith_PQ D euclid_ext2" 
    by (metis prod_cases3)
  have P: "P = P2 ** P1" and S: "S = S'" and Q: "Q = Q1 ** Q2"
    by (metis (mono_tags, lifting) PBQ Pair_inject Smith_2x2_eucl_def P1DQ1 P2SQ2 old.prod.case)+
  have 1: "D = P1 ** A ** Q1 \<and> invertible P1 \<and> invertible Q1 \<and> isDiagonal D" 
    by (rule diagonalize_2x2_works[OF P1DQ1])
  have 2: "S' = P2 ** D ** Q2 \<and> invertible P2 \<and> invertible Q2 \<and> Smith_normal_form S'"
    by (rule diagonal_to_Smith_PQ'[OF _ ib P2SQ2], insert 1, auto)
  show ?thesis using 1 2 P S Q by (simp add: 2 invertible_mult matrix_mul_assoc)
qed


subsection \<open>An executable algorithm to transform $2 \times 2$ matrices into its Smith normal form
in JNF\<close>
(*The full algorithm in JNF*)
definition "Smith_2x2_JNF_eucl A = (
  let (P,D,Q) = diagonalize_2x2_JNF A;
      (P',S,Q') = diagonal_to_Smith_PQ_JNF D euclid_ext2
  in (P' * P, S, Q * Q'))"

lemma Smith_2x2_JNF_eucl_works:
  assumes A: "A \<in> carrier_mat 2 2"
    and PBQ: "(P,S,Q) = Smith_2x2_JNF_eucl A"
  shows "is_SNF A (P,S,Q)"
proof -
  have ib: "is_bezout_ext euclid_ext2" by (simp add: is_bezout_ext_euclid_ext2)
  obtain P1 D Q1 where P1DQ1: "(P1,D,Q1) = diagonalize_2x2_JNF A" by (metis prod_cases3)
  obtain P2 S' Q2 where P2SQ2: "(P2,S',Q2) = diagonal_to_Smith_PQ_JNF D euclid_ext2" 
    by (metis prod_cases3)
  have P: "P = P2 * P1" and S: "S = S'" and Q: "Q = Q1 * Q2"
    by (metis (mono_tags, lifting) PBQ Pair_inject Smith_2x2_JNF_eucl_def P1DQ1 P2SQ2 old.prod.case)+             
  have 1: "D = P1 * A * Q1 \<and> invertible_mat P1 \<and> invertible_mat Q1 \<and> isDiagonal_mat D
    \<and> P1 \<in> carrier_mat 2 2 \<and> Q1 \<in> carrier_mat 2 2 \<and> D \<in> carrier_mat 2 2"
    by (rule diagonalize_2x2_JNF_works[OF A P1DQ1])
  have 2: "S' = P2 * D * Q2 \<and> invertible_mat P2 \<and> invertible_mat Q2 \<and> Smith_normal_form_mat S' 
        \<and> P2 \<in> carrier_mat 2 2 \<and> S' \<in> carrier_mat 2 2 \<and> Q2 \<in> carrier_mat 2 2"
    by (rule diagonal_to_Smith_PQ_JNF[OF _ ib _ P2SQ2], insert 1, auto)
  show ?thesis
  proof (rule is_SNF_intro)
    have dim_Q: "Q \<in> carrier_mat 2 2" using Q 1 2 by auto
    have P1AQ1: "(P1*A*Q1) \<in> carrier_mat 2 2" using 1 2 A by auto
    have rw1: "(P1 * A * Q1) * Q2 = (P1 * A * (Q1 * Q2))" 
      by (meson "1" "2" A assoc_mult_mat mult_carrier_mat)
    have rw2: "(P1 * A * Q) = P1 * (A * Q)" by (rule assoc_mult_mat[OF _ A dim_Q], insert 1, auto)
    show "invertible_mat Q" using 1 2 Q invertible_mult_JNF by blast
    show "invertible_mat P" using 1 2 P invertible_mult_JNF by blast
    have "P2 * D * Q2 = P2 * (P1 * A * Q1) * Q2" using 1 2 by auto   
    also have "... = P2 * ((P1 * A * Q1) * Q2)" using 1 2 by auto
    also have "... = P2 * (P1 * A * (Q1 * Q2))" unfolding rw1 by simp
    also have "... = P2 * (P1 * A * Q)" using Q by auto
    also have "... = P2 * (P1 * (A * Q))" unfolding rw2 by simp
    also have "... = P2 * P1 * (A * Q)" by (rule assoc_mult_mat[symmetric], insert 1 2 A Q, auto)
    also have "... = P*(A*Q)" unfolding P by simp
    also have "... = P*A*Q" by (rule assoc_mult_mat[symmetric], insert 1 2 A Q P, auto)
    finally show "S = P * A * Q" using 1 2 S by auto
  qed (insert 1 2 P Q A S, auto)
qed

subsection \<open>An executable algorithm to transform $1 \times 2$ matrices into its Smith normal form\<close>

(*Let's move to prove the case 1x2*)

(*This is not executable since type 1 is not mod_type*)
definition "Smith_1x2_eucl (A::'a::euclidean_ring_gcd^2^1) = (
  if A $h 0 $h 0 = 0 \<and> A $h 0 $h 1 \<noteq> 0 then 
    let Q = interchange_columns (Finite_Cartesian_Product.mat 1) 0 1;
        A' = interchange_columns A 0 1 in (A',Q)
  else
    if A $h 0 $h 0 \<noteq> 0 \<and> A $h 0 $h 1 \<noteq> 0 then
      let bezout_matrix_right = transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2)
      in (A ** bezout_matrix_right, bezout_matrix_right)
    else (A, Finite_Cartesian_Product.mat 1)
  )"


lemma Smith_1x2_eucl_works:
  assumes SQ: "(S,Q) = Smith_1x2_eucl A"
  shows "S = A ** Q \<and> invertible Q \<and> S $h 0 $h 1 = 0"
proof (cases "A $h 0 $h 0 = 0 \<and> A $h 0 $h 1 \<noteq> 0")
  case True
  have Q: "Q = interchange_columns (Finite_Cartesian_Product.mat 1) 0 1"
    and S: "S = interchange_columns A 0 1" 
    using SQ True unfolding Smith_1x2_eucl_def by (auto simp add: Let_def)
  have "S $h 0 $h 1 = 0" by (simp add: S True interchange_columns_code interchange_columns_code_nth)
  moreover have "invertible Q" using Q invertible_interchange_columns by blast
  moreover have "S = A ** Q" by (simp add: Q S interchange_columns_mat_1)
  ultimately show ?thesis by simp
next
  case False note A00_A01 = False
  show ?thesis
  proof (cases "A $h 0 $h 0 \<noteq> 0 \<and> A $h 0 $h 1 \<noteq> 0")
    case True
    have ib: "is_bezout_ext euclid_ext2" by (simp add: is_bezout_ext_euclid_ext2)
    let ?bezout_matrix_right = "transpose (bezout_matrix (transpose A) 0 1 0 euclid_ext2)"
    have Q: "Q = ?bezout_matrix_right" and S: "S = A**?bezout_matrix_right" 
      using SQ True A00_A01 unfolding Smith_1x2_eucl_def by (auto simp add: Let_def)
    have "invertible Q" unfolding Q
      by (rule invertible_bezout_matrix_transpose[OF ib zero_less_one_type2], insert True, auto)
    moreover have "S $h 0 $h 1 = 0"
      by (smt Finite_Cartesian_Product.transpose_transpose S True bezout_matrix_works2 ib 
          matrix_transpose_mul rel_simps(92) transpose_code transpose_row_code)
    moreover have "S = A**Q" unfolding S Q by simp
    ultimately show ?thesis by simp
  next
    case False
    have Q: "Q = (Finite_Cartesian_Product.mat 1)" and S: "S = A" 
      using SQ False A00_A01 unfolding Smith_1x2_eucl_def by (auto simp add: Let_def)
    show ?thesis using False A00_A01 S Q invertible_mat_1 by auto
  qed
qed


(*Bezout_matrix in JNF*)
definition bezout_matrix_JNF :: "'a::comm_ring_1 mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat 
    \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)) \<Rightarrow> 'a mat"
  where 
  "bezout_matrix_JNF A a b j bezout = Matrix.mat (dim_row A) (dim_row A) (\<lambda>(x,y). 
      (let 
        (p, q, u, v, d) = bezout (A $$ (a, j)) (A $$ (b, j)) 
       in
         if x = a \<and> y = a then p else
         if x = a \<and> y = b then q else
         if x = b \<and> y = a then u else
         if x = b \<and> y = b then v else
         if x = y then 1 else 0))"


definition "Smith_1x2_eucl_JNF (A::'a::euclidean_ring_gcd mat) = (
  if A $$ (0, 0) = 0 \<and> A $$ (0, 1) \<noteq> 0 then 
    let Q = swaprows_mat 2 0 1;
        A' = swapcols 0 1 A 
     in (A',Q)
  else
    if A $$ (0, 0) \<noteq> 0 \<and> A $$ (0, 1) \<noteq> 0 then
      let bezout_matrix_right = transpose_mat (bezout_matrix_JNF (transpose_mat A) 0 1 0 euclid_ext2)
      in (A * bezout_matrix_right, bezout_matrix_right)
    else (A, 1\<^sub>m 2)
  )"


lemma Smith_1x2_eucl_JNF_works:
  assumes A: "A \<in> carrier_mat 1 2"
  and SQ: "(S,Q) = Smith_1x2_eucl_JNF A"
shows "is_SNF A (1\<^sub>m 1, (Smith_1x2_eucl_JNF A))"
proof -
  have i: "0<dim_row A" and j: "1<dim_col A" using A by auto
  have ib: "is_bezout_ext euclid_ext2" by (simp add: is_bezout_ext_euclid_ext2)
  show ?thesis
  proof (cases "A $$ (0, 0) = 0 \<and> A $$ (0, 1) \<noteq> 0")
    case True
    have Q: "Q = swaprows_mat 2 0 1"
      and S: "S = swapcols 0 1 A"
      using SQ True unfolding Smith_1x2_eucl_JNF_def by (auto simp add: Let_def)
    have S01: "S $$ (0,1) = 0" unfolding S using index_mat_swapcols j i True by simp
    have dim_S: "S \<in> carrier_mat 1 2" using S A by auto
    moreover have dim_Q: "Q \<in> carrier_mat 2 2" using S Q by auto
    moreover have "invertible_mat Q" (*TODO: better a lemma for invertible swaprows_mat, etc*)
    proof -
      have "Determinant.det (swaprows_mat 2 0 1) = -1" by (rule det_swaprows_mat, auto)
      also have "... dvd 1" by simp
      finally show ?thesis using Q dim_Q invertible_iff_is_unit_JNF by blast
    qed
    moreover have "S = A * Q" unfolding S Q using A by (simp add: swapcols_mat)
    moreover have "Smith_normal_form_mat S" unfolding Smith_normal_form_mat_def isDiagonal_mat_def
      using S01 dim_S less_2_cases by fastforce
    ultimately show ?thesis using SQ S Q A unfolding is_SNF_def by auto
  next
    case False note A00_A01 = False
    show ?thesis
    proof (cases "A $$ (0,0) \<noteq> 0 \<and> A $$ (0,1) \<noteq> 0")
      case True
      have ib: "is_bezout_ext euclid_ext2" by (simp add: is_bezout_ext_euclid_ext2)
      let ?BM = "(bezout_matrix_JNF A\<^sup>T 0 1 0 euclid_ext2)\<^sup>T"
      have Q: "Q = ?BM" and S: "S = A*?BM" 
        using SQ True A00_A01 unfolding Smith_1x2_eucl_JNF_def by (auto simp add: Let_def)
      let ?a = "A $$ (0, 0)" let ?b = "A $$ (0, Suc 0)"
      obtain p q u v d where pquvd: "(p,q,u,v,d) = euclid_ext2 ?a ?b" by (metis prod_cases5)
      have d: "p*?a + q*?b = d" and u: "u = - ?b div d" and v: "v = ?a div d" 
        using pquvd unfolding euclid_ext2_def using bezout_coefficients_fst_snd by blast+   
      have da: "d dvd ?a" and db: "d dvd ?b" and gcd_ab: "d = gcd ?a ?b" 
        by (metis euclid_ext2_def gcd_dvd1 gcd_dvd2 pquvd prod.sel(2))+
      have dim_S: "S \<in> carrier_mat 1 2" using S A by (simp add: bezout_matrix_JNF_def)
      moreover have dim_Q: "Q \<in> carrier_mat 2 2" using A Q by (simp add: bezout_matrix_JNF_def)
      have "invertible_mat Q" 
      proof -
        have "Determinant.det ?BM = ?BM $$ (0, 0) * ?BM $$ (1, 1) - ?BM $$ (0, 1) * ?BM $$ (1, 0)"
          by (rule det_2, insert A, auto simp add: bezout_matrix_JNF_def)
        also have "... = p * v - u*q" 
          by (insert i j pquvd, auto simp add: bezout_matrix_JNF_def, metis split_conv)
        also have "... = (p * ?a) div d - (q * (-?b)) div d" unfolding v u
          by (simp add: da db div_mult_swap mult.commute)
        also have "... = (p * ?a + q * ?b) div d"
          by (metis (no_types, lifting) da db diff_minus_eq_add div_diff dvd_minus_iff dvd_trans 
              dvd_triv_right more_arith_simps(8))
        also have "... = 1 " unfolding d using True da by fastforce
        finally show ?thesis unfolding Q 
          by (metis (full_types) Determinant.det_def Q carrier_matI invertible_iff_is_unit_JNF 
              not_is_unit_0 one_dvd)
      qed
      moreover have S_AQ: "S = A*Q" unfolding S Q by simp
      moreover have S01: "S $$ (0,1) = 0"
      proof -
        have Q01: "Q $$ (0, 1) = u"
        proof -
          have "?BM $$ (0,1) = (bezout_matrix_JNF A\<^sup>T 0 1 0 euclid_ext2) $$ (1, 0)"
            using Q dim_Q by auto
          also have "... =  (\<lambda>(x::nat, y::nat).
          let (p, q, u, v, d) = euclid_ext2 (A\<^sup>T $$ (0, 0)) (A\<^sup>T $$ (1, 0)) in if x = 0 \<and> y = 0 then p
            else if x = 0 \<and> y = 1 then q else if x = 1 \<and> y = 0 then u else if x = 1 \<and> y = 1 then v
            else if x = y then 1 else 0) (1, 0)"
            unfolding bezout_matrix_JNF_def by (rule index_mat(1), insert A, auto)
          also have "... = u" using pquvd unfolding split_beta Let_def
            by (auto, metis A One_nat_def carrier_matD(2) fst_conv i index_transpose_mat(1) 
                j rel_simps(51) snd_conv)   
          finally show ?thesis unfolding Q by auto
        qed
        have Q11: "Q $$ (1, 1) = v"
        proof -
          have "?BM $$ (1,1) = (bezout_matrix_JNF A\<^sup>T 0 1 0 euclid_ext2) $$ (1, 1)"
            using Q dim_Q by auto
          also have "... =  (\<lambda>(x::nat, y::nat).
          let (p, q, u, v, d) = euclid_ext2 (A\<^sup>T $$ (0, 0)) (A\<^sup>T $$ (1, 0)) in if x = 0 \<and> y = 0 then p
            else if x = 0 \<and> y = 1 then q else if x = 1 \<and> y = 0 then u else if x = 1 \<and> y = 1 then v
            else if x = y then 1 else 0) (1, 1)"
            unfolding bezout_matrix_JNF_def by (rule index_mat(1), insert A, auto)
          also have "... = v" using pquvd unfolding split_beta Let_def
            by (auto, metis A One_nat_def carrier_matD(2) fst_conv i index_transpose_mat(1) 
                j rel_simps(51) snd_conv)   
          finally show ?thesis unfolding Q by auto
        qed      
        have "S $$ (0,1) = Matrix.row A 0 \<bullet> col Q 1" using index_mult_mat Q S dim_S i by auto        
        also have "... = (\<Sum>i = 0..<2. Matrix.row A 0 $v i * Q $$ (i, 1))"
          unfolding scalar_prod_def using dim_S dim_Q by auto
        also have "... = (\<Sum>i \<in> {0,1}. Matrix.row A 0 $v i * Q $$ (i, 1))" by (rule sum.cong, auto)
        also have "... = Matrix.row A 0 $v 0 * Q $$ (0, 1) + Matrix.row A 0 $v 1 * Q $$ (1, 1)" 
          using sum_two_elements by auto
        also have "... =  ?a*u + ?b * v" unfolding Q01 Q11 using i index_row(1) j A by auto          
        also have "... = 0" unfolding u v
          by (smt Groups.mult_ac(2) Groups.mult_ac(3) add.right_inverse add_uminus_conv_diff da db 
              diff_minus_eq_add dvd_div_mult_self dvd_neg_div minus_mult_left)
        finally show ?thesis .
      qed
      moreover have "Smith_normal_form_mat S" 
        using less_2_cases S01 dim_S unfolding Smith_normal_form_mat_def isDiagonal_mat_def
        by fastforce
      ultimately show ?thesis using S Q A SQ unfolding is_SNF_def bezout_matrix_JNF_def by force
    next
      case False
      have Q: "Q = 1\<^sub>m 2" and S: "S = A" 
        using SQ False A00_A01 unfolding Smith_1x2_eucl_JNF_def by (auto simp add: Let_def)
      have "is_SNF A (1\<^sub>m 1, A, 1\<^sub>m 2)"
        by (rule is_SNF_intro, insert A False A00_A01 S Q A less_2_cases, 
          unfold Smith_normal_form_mat_def isDiagonal_mat_def, fastforce+)
      thus ?thesis using SQ S Q by auto
    qed
  qed
qed

subsection \<open>The final executable algorithm to transform any matrix into its Smith normal form\<close>

global_interpretation Smith_ED: Smith_Impl Smith_1x2_eucl_JNF Smith_2x2_JNF_eucl "(div)"
  defines Smith_ED_1xn_aux = Smith_ED.Smith_1xn_aux
    and Smith_ED_nx1 = Smith_ED.Smith_nx1
  and Smith_ED_1xn = Smith_ED.Smith_1xn
  and Smith_ED_2xn = Smith_ED.Smith_2xn
  and Smith_ED_nx2 = Smith_ED.Smith_nx2
  and Smith_ED_mxn = Smith_ED.Smith_mxn
proof 
  show "\<forall>(A::'a mat)\<in>carrier_mat 1 2. is_SNF A (1\<^sub>m 1, Smith_1x2_eucl_JNF A)"
    using Smith_1x2_eucl_JNF_works prod.collapse by blast
  show "\<forall>A\<in>carrier_mat 2 2. is_SNF A (Smith_2x2_JNF_eucl A)"
    by (simp add: Smith_2x2_JNF_eucl_def Smith_2x2_JNF_eucl_works split_beta)
  show "is_div_op ((div)::'a\<Rightarrow>'a\<Rightarrow>'a::euclidean_ring_gcd)"
    by (unfold is_div_op_def, simp)
qed


(*
value[code] "let (P,S,Q) = diagonalize_2x2 ((list_of_list_to_matrix [[32,128],[24,20]])::int^2^2)
  in (matrix_to_list_of_list P,matrix_to_list_of_list S,matrix_to_list_of_list Q)"
value [code]  "show (diagonalize_2x2_JNF (mat_of_rows_list 2 [[1,2::int],[3,4]]))"
*)


(*
value [code]  "show (Smith_ED_mxn (mat_of_rows_list 2 [[1,2::int],[3,4]]))"

value [code]  "show (Smith_ED_mxn (mat_of_rows_list 2 
  [
    [[:2,4,1:]::rat poly, [:3,2,0,2:]],
    [[:0,2:]  , [:3,2:]]
  ]
))"
*)


end