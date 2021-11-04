section \<open>Generalization of the statement about the uniqueness of the Hermite normal form\<close>

theory Uniqueness_Hermite
imports Hermite.Hermite
begin

(*This file presents a generalized version of the theorem Hermite_unique when applied to integer
matrices. More concretely, instead of assuming invertibility over Z of the input matrix A, we now 
assume invertibility over Q. Only some changes to adapt the original proof are required.*)

instance int :: bezout_ring_div
proof qed

lemma map_matrix_rat_of_int_mult:
  shows "map_matrix rat_of_int (A**B) = (map_matrix rat_of_int A)**(map_matrix rat_of_int B)" 
  unfolding map_matrix_def matrix_matrix_mult_def by auto

lemma det_map_matrix:
  fixes A :: "int^'n::mod_type^'n::mod_type"
  shows "det (map_matrix rat_of_int A) = rat_of_int (det A)" 
  unfolding map_matrix_def unfolding Determinants.det_def by auto

lemma inv_Z_imp_inv_Q:
  fixes A :: "int^'n::mod_type^'n::mod_type"
  assumes inv_A: "invertible A"
  shows "invertible (map_matrix rat_of_int A)"
proof -
  have "is_unit (det A)" using inv_A invertible_iff_is_unit by blast
  hence "is_unit (det (map_matrix rat_of_int A))"
    by (simp add: det_map_matrix dvd_if_abs_eq)
  thus ?thesis using invertible_iff_is_unit by blast
qed

lemma upper_triangular_Z_eq_Q:
  "upper_triangular (map_matrix rat_of_int A) = upper_triangular A" 
  unfolding upper_triangular_def by auto

lemma invertible_and_upper_diagonal_not0:
  fixes H :: "int^'n::mod_type^'n::mod_type"
  assumes inv_H: "invertible (map_matrix rat_of_int H)" and up_H: "upper_triangular H"
  shows "H $ i $ i \<noteq> 0"
proof -
  let ?RAT_H = "(map_matrix rat_of_int H)"
  have up_RAT_H: "upper_triangular ?RAT_H"
    using up_H unfolding upper_triangular_def by auto
  have "is_unit (det ?RAT_H)" using inv_H using invertible_iff_is_unit by blast
  hence "?RAT_H $ i $ i \<noteq> 0" using inv_H up_RAT_H is_unit_diagonal
    by (metis not_is_unit_0)
  thus ?thesis by auto
qed

lemma diagonal_least_nonzero:
  fixes H :: "int^'n::mod_type^'n::mod_type"
  assumes H: "Hermite associates residues H"
  and inv_H: "invertible (map_matrix rat_of_int H)" and up_H: "upper_triangular H"
  shows "(LEAST n. H $ i $ n \<noteq> 0) = i"
proof (rule Least_equality)
  show "H $ i $ i \<noteq> 0" by (rule invertible_and_upper_diagonal_not0[OF inv_H up_H])
  fix y
  assume Hiy: "H $ i $ y \<noteq> 0"
  show "i \<le> y" 
    using up_H unfolding upper_triangular_def
    by (metis (poly_guards_query) Hiy not_less)
qed

lemma diagonal_in_associates:
  fixes H :: "int^'n::mod_type^'n::mod_type"
  assumes H: "Hermite associates residues H"
  and inv_H: "invertible (map_matrix rat_of_int H)" and up_H: "upper_triangular H"
  shows "H $ i $ i \<in> associates"
proof -
  have "H $ i $ i \<noteq> 0" by (rule invertible_and_upper_diagonal_not0[OF inv_H up_H])
  hence "\<not> is_zero_row i H" unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
  thus ?thesis using H unfolding Hermite_def unfolding diagonal_least_nonzero[OF H inv_H up_H] 
    by auto
qed

lemma above_diagonal_in_residues:
  fixes H :: "int^'n::mod_type^'n::mod_type"
  assumes H: "Hermite associates residues H"
  and inv_H: "invertible (map_matrix rat_of_int H)" and up_H: "upper_triangular H"
  and j_i: "j<i"
  shows "H $ j $ (LEAST n. H $ i $ n \<noteq> 0) \<in> residues (H $ i $ (LEAST n. H $ i $ n \<noteq> 0))" 
proof -
  have "H $ i $ i \<noteq> 0" by (rule invertible_and_upper_diagonal_not0[OF inv_H up_H])
  hence "\<not> is_zero_row i H" unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto
  thus ?thesis using H j_i unfolding Hermite_def unfolding diagonal_least_nonzero[OF H inv_H up_H] 
    by auto
qed


lemma Hermite_unique_generalized:
  fixes K::"int^'n::mod_type^'n::mod_type"
  assumes A_PH: "A = P ** H" 
  and A_QK: "A = Q ** K"
  and inv_A: "invertible (map_matrix rat_of_int A)" (*The original statement assumes "invertible A", 
                                                      that is, invertibility over integers, which is
                                                      more restrictive.*)
  and inv_P: "invertible P"
  and inv_Q: "invertible Q"
  and H: "Hermite associates residues H"
  and K: "Hermite associates residues K"
  shows "H = K"
proof -
  let ?RAT = "map_matrix rat_of_int"
  have cs_residues: "Complete_set_residues residues" using H unfolding Hermite_def by simp
  have inv_H: "invertible (?RAT H)"
  proof -
    have "?RAT A = ?RAT P ** ?RAT H" using A_PH map_matrix_rat_of_int_mult by blast
    thus ?thesis
      by (metis inv_A invertible_left_inverse matrix_inv(1) matrix_mul_assoc)
  qed
  have inv_K: "invertible (?RAT K)"
  proof -
   have "?RAT A = ?RAT Q ** ?RAT K" using A_QK map_matrix_rat_of_int_mult by blast
    thus ?thesis
      by (metis inv_A invertible_left_inverse matrix_inv(1) matrix_mul_assoc)
  qed
  define U where "U = (matrix_inv P)**Q"
  have inv_U: "invertible U" 
    by (metis U_def inv_P inv_Q invertible_def invertible_mult matrix_inv_left matrix_inv_right)
  have H_UK: "H = U ** K" using A_PH A_QK inv_P 
    by (metis U_def matrix_inv_left matrix_mul_assoc matrix_mul_lid)
  have "Determinants.det K *k U = H ** adjugate K"
    unfolding H_UK matrix_mul_assoc[symmetric] mult_adjugate_det matrix_mul_mat ..
  have upper_triangular_H: "upper_triangular H"
    by (metis H Hermite_def echelon_form_imp_upper_triagular)
  have upper_triangular_K: "upper_triangular K" 
    by (metis K Hermite_def echelon_form_imp_upper_triagular)
  have upper_triangular_U: "upper_triangular U" 
  proof -
    have U_H_K: "?RAT U = (?RAT H) ** (matrix_inv (?RAT K))"
      by (metis H_UK inv_K map_matrix_rat_of_int_mult matrix_inv(2) matrix_mul_assoc matrix_mul_rid)
    have up_inv_RAT_K: "upper_triangular (matrix_inv (?RAT K))" using upper_triangular_inverse
      by (simp add: upper_triangular_inverse inv_K upper_triangular_K upper_triangular_Z_eq_Q)
    have "upper_triangular (?RAT U)" unfolding U_H_K 
      by (rule upper_triangular_mult[OF _ up_inv_RAT_K], 
          auto simp add: upper_triangular_H upper_triangular_Z_eq_Q)
    thus ?thesis using upper_triangular_Z_eq_Q by auto
  qed
  have unit_det_U: "is_unit (det U)" by (metis inv_U invertible_iff_is_unit)
  have is_unit_diagonal_U: "(\<forall>i. is_unit (U $ i $ i))"
    by (rule is_unit_diagonal[OF upper_triangular_U unit_det_U])
  have Uii_1: "(\<forall>i. (U $ i $ i) = 1)" and Hii_Kii: "(\<forall>i. (H $ i $ i) = (K $ i $ i))"
  proof (auto)
    fix i
    have Hii: "H $ i $ i \<in> associates" 
      by (rule diagonal_in_associates[OF H inv_H upper_triangular_H])
    have Kii: "K $ i $ i \<in> associates"
      by (rule diagonal_in_associates[OF K inv_K upper_triangular_K])
    have ass_Hii_Kii: "normalize (H $ i $ i) = normalize (K $ i $ i)"
      by (metis H_UK is_unit_diagonal_U normalize_mult_unit_left upper_triangular_K upper_triangular_U upper_triangular_mult_diagonal)
    show Hii_eq_Kii: "H $ i $ i = K $ i $ i"
      by (metis Hermite_def Hii K Kii ass_Hii_Kii in_Ass_not_associated)
    have "H $ i $ i = U $ i $ i * K $ i $ i" 
      by (metis H_UK upper_triangular_K upper_triangular_U upper_triangular_mult_diagonal)
    thus "U $ i $ i = 1" unfolding Hii_eq_Kii mult_cancel_right1
      using inv_K invertible_and_upper_diagonal_not0 upper_triangular_K by blast 
  qed
  have zero_above: "\<forall>j s. j\<ge>1 \<and> j < ncols A - to_nat s \<longrightarrow> U $ s $ (s + from_nat j) = 0"
  proof (clarify)
    fix j s assume  "1 \<le> j" and "j < ncols A - (to_nat (s::'n))"
    thus "U $ s $ (s + from_nat j) = 0"
    proof (induct j rule: less_induct)
      fix p 
      assume induct_step: "(\<And>y. y < p \<Longrightarrow> 1 \<le> y \<Longrightarrow> y < ncols A - to_nat s \<Longrightarrow> U $ s $ (s + from_nat y) = 0)"
        and p1: "1 \<le> p" and p2: "p < ncols A - to_nat s"
      have s_less: "s < s + from_nat p" using p1 p2 unfolding ncols_def
        by (metis One_nat_def add.commute add_diff_cancel_right' add_lessD1 add_to_nat_def 
          from_nat_to_nat_id less_diff_conv neq_iff not_le
          to_nat_from_nat_id to_nat_le zero_less_Suc)
      show "U $ s $ (s + from_nat p) = 0"
      proof -
        have UNIV_rw: "UNIV = insert s (UNIV-{s})" by auto
        have UNIV_s_rw: "UNIV-{s} = insert (s + from_nat p) ((UNIV-{s}) - {s + from_nat p})" 
          using p1 p2 s_less unfolding ncols_def by (auto simp: algebra_simps)
        have sum_rw: "(\<Sum>k\<in>UNIV-{s}. U $ s $ k * K $ k $ (s + from_nat p)) 
          = U $ s $ (s + from_nat p) * K $ (s + from_nat p) $ (s + from_nat p) 
          + (\<Sum>k\<in>(UNIV-{s})-{s + from_nat p}. U $ s $ k * K $ k $ (s + from_nat p))"
          using UNIV_s_rw sum.insert by (metis (erased, lifting) Diff_iff finite singletonI)
        have sum_0: "(\<Sum>k\<in>(UNIV-{s})-{s + from_nat p}. U $ s $ k * K $ k $ (s + from_nat p)) = 0"
        proof (rule sum.neutral, rule)
          fix x assume x: "x \<in> UNIV - {s} - {s + from_nat p}"
          show "U $ s $ x * K $ x $ (s + from_nat p) = 0" 
          proof (cases "x<s")
            case True
            thus ?thesis using upper_triangular_U unfolding upper_triangular_def
              by auto
          next
            case False
            hence x_g_s: "x>s" using x by (metis Diff_iff neq_iff singletonI)
            show ?thesis 
            proof (cases "x<s+from_nat p")
              case True
              define a where "a = to_nat x - to_nat s"
              from x_g_s have "to_nat s < to_nat x" by (rule to_nat_mono)
              hence xa: "x=s+(from_nat a)" unfolding a_def add_to_nat_def
                by (simp add: less_imp_diff_less to_nat_less_card algebra_simps to_nat_from_nat_id)
              have "U $ s $ x =0" 
              proof (unfold xa, rule induct_step)
                show a_p: "a<p" unfolding a_def using p2 unfolding ncols_def 
                proof -
                  have "x < from_nat (to_nat s + to_nat (from_nat p::'n))"
                    by (metis (no_types) True add_to_nat_def)
                  hence "to_nat x - to_nat s < to_nat (from_nat p::'n)"
                    by (simp add: add.commute less_diff_conv2 less_imp_le to_nat_le x_g_s)
                  thus "to_nat x - to_nat s < p"
                    by (metis (no_types) from_nat_eq_imp_eq from_nat_to_nat_id le_less_trans 
                        less_imp_le not_le to_nat_less_card)
                qed                    
                show "1 \<le> a" 
                  by (auto simp add: a_def p1 p2) (metis Suc_leI to_nat_mono x_g_s zero_less_diff)
                show "a < ncols A - to_nat s" using a_p p2 by auto
              qed
              thus ?thesis by simp
            next
              case False
              hence "x>s+from_nat p" using x_g_s x by auto
              thus ?thesis using upper_triangular_K unfolding upper_triangular_def
                by auto
            qed
          qed 
        qed
        have "H $ s $ (s + from_nat p) = (\<Sum>k\<in>UNIV. U $ s $ k * K $ k $ (s + from_nat p))"
          unfolding H_UK matrix_matrix_mult_def by auto
        also have "... = (\<Sum>k\<in>insert s (UNIV-{s}). U $ s $ k * K $ k $ (s + from_nat p))"
          using UNIV_rw by simp
        also have "... = U $ s $ s * K $ s $ (s + from_nat p) 
          + (\<Sum>k\<in>UNIV-{s}. U $ s $ k * K $ k $ (s + from_nat p))"
          by (rule sum.insert, simp_all)
        also have "... = U $ s $ s * K $ s $ (s + from_nat p) 
          + U $ s $ (s + from_nat p) * K $ (s + from_nat p) $ (s + from_nat p)"
          unfolding sum_rw sum_0 by simp
        finally have H_s_sp: "H $ s $ (s + from_nat p) 
          = U $ s $ (s + from_nat p) * K $ (s + from_nat p) $ (s + from_nat p) + K $ s $ (s + from_nat p)"
          using Uii_1 by auto
        hence cong_HK: "cong (H $ s $ (s + from_nat p)) (K $ s $ (s + from_nat p)) (K $ (s+from_nat p) $ (s + from_nat p))"
          unfolding cong_def by auto
        have H_s_sp_residues: "(H $ s $ (s + from_nat p)) \<in> residues (K $ (s+from_nat p) $ (s + from_nat p))" 
          using above_diagonal_in_residues[OF H inv_H upper_triangular_H s_less]
          unfolding diagonal_least_nonzero[OF H inv_H upper_triangular_H]
          by (metis Hii_Kii)
        have K_s_sp_residues: "(K $ s $ (s + from_nat p)) \<in> residues (K $ (s+from_nat p) $ (s + from_nat p))"
          using above_diagonal_in_residues[OF K inv_K upper_triangular_K s_less]
          unfolding diagonal_least_nonzero[OF K inv_K upper_triangular_K] .
        have Hs_sp_Ks_sp: "(H $ s $ (s + from_nat p)) = (K $ s $ (s + from_nat p))"             
          using cong_HK in_Res_not_congruent[OF cs_residues H_s_sp_residues K_s_sp_residues]
          by fast
        have "K $ (s + from_nat p) $ (s + from_nat p) \<noteq> 0"
          using inv_K invertible_and_upper_diagonal_not0 upper_triangular_K by blast
        thus ?thesis unfolding from_nat_1 using H_s_sp unfolding Hs_sp_Ks_sp by auto
      qed 
    qed 
  qed
  have "U = mat 1" 
  proof (unfold mat_def vec_eq_iff, auto)
    fix ia show "U $ ia $ ia = 1" using Uii_1 by simp
    fix i assume i_ia: "i \<noteq> ia"
    show "U $ i $ ia = 0"
    proof (cases "ia<i")
      case True
      thus ?thesis using upper_triangular_U unfolding upper_triangular_def by auto
    next
      case False
      hence i_less_ia: "i<ia" using i_ia by auto
      define a where "a = to_nat ia - to_nat i"
      have ia_eq: "ia = i + from_nat a" unfolding a_def
        by (metis i_less_ia a_def add_to_nat_def dual_order.strict_iff_order from_nat_to_nat_id 
            le_add_diff_inverse less_imp_diff_less to_nat_from_nat_id to_nat_less_card to_nat_mono)
      have "1 \<le> a" unfolding a_def
        by (metis diff_is_0_eq i_less_ia less_one not_less to_nat_mono)
      moreover have "a < ncols A - to_nat i"
        unfolding a_def ncols_def
        by (metis False diff_less_mono not_less to_nat_less_card to_nat_mono')
      ultimately show ?thesis using zero_above unfolding ia_eq by blast
    qed
  qed
  thus ?thesis using H_UK matrix_mul_lid by fast
qed

end