(*
    Author:      Jose Divasón
    Email:       jose.divason@unirioja.es
*)

section \<open>The Cauchy--Binet formula\<close>

theory Cauchy_Binet
  imports
  Diagonal_To_Smith
  SNF_Missing_Lemmas
begin

subsection \<open>Previous missing results about @{text "pick"} and @{text "insert"}\<close>

lemma pick_insert:
  assumes a_notin_I: "a \<notin> I" and i2: "i < card I"
    and a_def: "pick (insert a I) a' = a" (*Alternative: index (insort a (sorted_list_of_set I)) a = a'*)
    and ia': "i < a'" (*Case 1*)
    and a'_card: "a' < card I + 1"
  shows "pick (insert a I) i = pick I i"
proof -
  have finI: "finite I"
    using i2
    using card.infinite by force
  have "pick (insert a I) i = sorted_list_of_set (insert a I) ! i"
  proof (rule sorted_list_of_set_eq_pick[symmetric])
    have "finite (insert a I)"
      using card.infinite i2 by force
    thus "i < length (sorted_list_of_set (insert a I))"
      by (metis a_notin_I card_insert_disjoint distinct_card finite_insert
          i2 less_Suc_eq sorted_list_of_set(1) sorted_list_of_set(3))
  qed
  also have "... = insort a (sorted_list_of_set I) ! i"
    using sorted_list_of_set.insert
    by (metis a_notin_I card.infinite i2 not_less0)
  also have "... = (sorted_list_of_set I) ! i"
  proof (rule insort_nth[OF])
     show "sorted (sorted_list_of_set I)" by auto
     show "a \<notin> set (sorted_list_of_set I)" using a_notin_I
       by (metis card.infinite i2 not_less_zero set_sorted_list_of_set)
     have "index (sorted_list_of_set (insert a I)) a = a'"
       using pick_index a_def
       using a'_card a_notin_I finI by auto
     hence "index (insort a (sorted_list_of_set I)) a = a'"
       by (simp add: a_notin_I finI)
     thus "i < index (insort a (sorted_list_of_set I)) a" using ia' by auto
     show "sorted_list_of_set I \<noteq> []" using finI i2 by fastforce
   qed
  also have "... = pick I i"
  proof (rule sorted_list_of_set_eq_pick)
    have "finite I" using card.infinite i2 by fastforce
    thus "i < length (sorted_list_of_set I)"
      by (metis distinct_card distinct_sorted_list_of_set i2 set_sorted_list_of_set)
  qed
  finally show ?thesis .
qed


lemma pick_insert2:
  assumes a_notin_I: "a \<notin> I" and i2: "i < card I"
    and a_def: "pick (insert a I) a' = a" (*Alternative: index (sorted_list_of_set (insert a I)) a = a'*)
    and ia': "i \<ge> a'" (*Case 2*)
    and a'_card: "a' < card I + 1"
  shows "pick (insert a I) i < pick I i"
proof (cases "i = 0")
  case True
  then show ?thesis
    by (auto, metis (mono_tags, lifting) DL_Missing_Sublist.pick.simps(1) Least_le a_def a_notin_I
        dual_order.order_iff_strict i2 ia' insertCI le_zero_eq not_less_Least pick_in_set_le)
next
  case False
  hence i0: "i = Suc (i - 1)" using a'_card ia' by auto
  have finI: "finite I"
    using i2 card.infinite by force
  have index_a'1: "index (sorted_list_of_set (insert a I)) a = a'"
    using pick_index
    using a'_card a_def a_notin_I finI by auto
  hence index_a': "index (insort a (sorted_list_of_set I)) a = a'"
    by (simp add: a_notin_I finI)
  have i1_length: "i - 1 < length (sorted_list_of_set I)" using i2
    by (metis distinct_card distinct_sorted_list_of_set finI
        less_imp_diff_less set_sorted_list_of_set)
  have 1: "pick (insert a I) i = sorted_list_of_set (insert a I) ! i"
  proof (rule sorted_list_of_set_eq_pick[symmetric])
    have "finite (insert a I)"
      using card.infinite i2 by force
    thus "i < length (sorted_list_of_set (insert a I))"
      by (metis a_notin_I card_insert_disjoint distinct_card finite_insert
          i2 less_Suc_eq sorted_list_of_set(1) sorted_list_of_set(3))
  qed
  also have 2: "... = insort a (sorted_list_of_set I) ! i"
    using sorted_list_of_set.insert
    by (metis a_notin_I card.infinite i2 not_less0)
  also have "... = insort a (sorted_list_of_set I) ! Suc (i-1)" using i0 by auto
  also have "... < pick I i"
  proof (cases "i = a'")
    case True
    have "(sorted_list_of_set I) ! i > a"
      by (smt "1" Suc_less_eq True a_def a_notin_I distinct_card distinct_sorted_list_of_set finI i2
          ia' index_a' insort_nth2 length_insort lessI list.size(3) nat_less_le not_less_zero
          pick_in_set_le set_sorted_list_of_set sorted_list_of_set(2) sorted_list_of_set.insert
          sorted_list_of_set_eq_pick sorted_sorted_wrt sorted_wrt_nth_less)
    moreover have "a = insort a (sorted_list_of_set I) ! i" using True 1 2 a_def by auto
    ultimately show ?thesis using 1 2
      by (metis distinct_card finI i0 i2 set_sorted_list_of_set
          sorted_list_of_set(3) sorted_list_of_set_eq_pick)
  next
    case False
    have "insort a (sorted_list_of_set I) ! Suc (i-1) = (sorted_list_of_set I) ! (i-1)"
      by (rule insort_nth2, insert i1_length False ia' index_a', auto simp add: a_notin_I finI)
    also have "... = pick I (i-1)"
      by (rule sorted_list_of_set_eq_pick[OF i1_length])
    also have "... < pick I i" using i0 i2 pick_mono_le by auto
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma pick_insert3:
  assumes a_notin_I: "a \<notin> I" and i2: "i < card I"
    and a_def: "pick (insert a I) a' = a" (*Alternative: index (sorted_list_of_set (insert a I)) a = a'.*)
    and ia': "i \<ge> a'" (*Case 2*)
    and a'_card: "a' < card I + 1"
  shows "pick (insert a I) (Suc i) = pick I i"
proof (cases "i = 0")
  case True
  have a_LEAST: "a < (LEAST aa. aa\<in>I)"
    using True a_def a_notin_I i2 ia' pick_insert2 by fastforce
  have Least_rw: "(LEAST aa. aa = a \<or> aa \<in> I) = a"
    by (rule Least_equality, insert a_notin_I, auto,
        metis a_LEAST le_less_trans nat_le_linear not_less_Least)
  let ?P = "\<lambda>aa. (aa = a \<or> aa \<in> I) \<and> (LEAST aa. aa = a \<or> aa \<in> I) < aa"
  let ?Q = "\<lambda>aa. aa \<in> I"
  have "?P = ?Q" unfolding Least_rw fun_eq_iff
    by (auto, metis a_LEAST le_less_trans not_le not_less_Least)
  thus ?thesis using True by auto
next
  case False
  have finI: "finite I"
    using i2 card.infinite by force
  have index_a'1: "index (sorted_list_of_set (insert a I)) a = a'"
    using pick_index
    using a'_card a_def a_notin_I finI by auto
  hence index_a': "index (insort a (sorted_list_of_set I)) a = a'"
    by (simp add: a_notin_I finI)
  have i1_length: "i < length (sorted_list_of_set I)" using i2
    by (metis distinct_card distinct_sorted_list_of_set finI set_sorted_list_of_set)
  have 1: "pick (insert a I) (Suc i) = sorted_list_of_set (insert a I) ! (Suc i)"
  proof (rule sorted_list_of_set_eq_pick[symmetric])
    have "finite (insert a I)"
      using card.infinite i2 by force
    thus "Suc i < length (sorted_list_of_set (insert a I))"
      by (metis Suc_mono a_notin_I card_insert_disjoint distinct_card distinct_sorted_list_of_set
          finI i2 set_sorted_list_of_set)
  qed
  also have 2: "... = insort a (sorted_list_of_set I) ! Suc i"
    using sorted_list_of_set.insert
    by (metis a_notin_I card.infinite i2 not_less0)
  also have "... = pick I i"
  proof (cases "i = a'")
    case True
    show ?thesis
      by (metis True a_notin_I finI i1_length index_a' insort_nth2 le_refl list.size(3) not_less0
          set_sorted_list_of_set sorted_list_of_set(2) sorted_list_of_set_eq_pick)
  next
    case False
    have "insort a (sorted_list_of_set I) ! Suc i = (sorted_list_of_set I) ! i"
      by (rule insort_nth2, insert i1_length False ia' index_a', auto simp add: a_notin_I finI)
    also have "... = pick I i"
      by (rule sorted_list_of_set_eq_pick[OF i1_length])
    finally show ?thesis .
  qed
  finally show ?thesis .
qed


lemma pick_insert_index:
  assumes Ik: "card I = k"
  and a_notin_I: "a \<notin> I"
  and ik: "i < k"
  and a_def: "pick (insert a I) a' = a"
  and a'k: "a' < card I + 1"
shows "pick (insert a I) (insert_index a' i) = pick I i"
proof (cases "i<a'")
  case True
  have "pick (insert a I) i = pick I i"
    by (rule pick_insert[OF a_notin_I _ a_def _ a'k], auto simp add: Ik ik True)
  thus ?thesis using True unfolding insert_index_def by auto
next
  case False note i_ge_a' = False
  have fin_aI: "finite (insert a I)"
    using Ik finite_insert ik by fastforce
  let ?P = "\<lambda>aa. (aa = a \<or> aa \<in> I) \<and> pick (insert a I) i < aa"
  let ?Q = "\<lambda>aa. aa \<in> I \<and> pick (insert a I) i < aa"
  have "?P = ?Q" using a_notin_I unfolding fun_eq_iff
    by (auto, metis False Ik a_def card.infinite card_insert_disjoint ik less_SucI
        linorder_neqE_nat not_less_zero order.asym pick_mono_le)
  hence "Least ?P = Least ?Q" by simp
  also have "... = pick I i"
  proof (rule Least_equality, rule conjI)
    show "pick I i \<in> I"
      by (simp add: Ik ik pick_in_set_le)
    show "pick (insert a I) i < pick I i"
      by (rule pick_insert2[OF a_notin_I _ a_def _ a'k], insert False, auto simp add: Ik ik)
    fix y assume y: "y \<in> I \<and> pick (insert a I) i < y"
    let ?xs = "sorted_list_of_set (insert a I)"
    have "y \<in> set ?xs" using y by (metis fin_aI insertI2 set_sorted_list_of_set y)
    from this obtain j where xs_j_y: "?xs ! j = y" and j: "j < length ?xs"
      using in_set_conv_nth by metis
    have ij: "i<j"
      by (metis (no_types, lifting) Ik a_notin_I card.infinite card_insert_disjoint ik j less_SucI
          linorder_neqE_nat not_less_zero order.asym pick_mono_le sorted_list_of_set_eq_pick xs_j_y y)
    have "pick I i = pick (insert a I) (Suc i)"
      by (rule pick_insert3[symmetric, OF a_notin_I _ a_def _ a'k], insert False Ik ik, auto)
    also have "... \<le> pick (insert a I) j"
      by (metis Ik Suc_lessI card.infinite distinct_card distinct_sorted_list_of_set eq_iff
          finite_insert ij ik j less_imp_le_nat not_less_zero pick_mono_le set_sorted_list_of_set)
    also have "... = ?xs ! j" by (rule sorted_list_of_set_eq_pick[symmetric, OF j])
    also have "... = y" by (rule xs_j_y)
    finally show "pick I i \<le> y" .
  qed
  finally show ?thesis unfolding insert_index_def using False by auto
qed


subsection\<open>Start of the proof\<close>

definition "strict_from_inj n f = (\<lambda>i. if i\<in>{0..<n} then (sorted_list_of_set (f`{0..<n})) ! i else i)"

lemma strict_strict_from_inj:
  fixes f::"nat \<Rightarrow> nat"
  assumes "inj_on f {0..<n}" shows "strict_mono_on (strict_from_inj n f) {0..<n}"
proof -
  let ?I="f`{0..<n}"
  have "strict_from_inj n f x < strict_from_inj n f y"
    if xy: "x < y" and x: "x \<in> {0..<n}" and y: "y \<in> {0..<n}" for x y
  proof -
    let ?xs = "(sorted_list_of_set ?I)"
    have sorted_xs: "sorted ?xs" by (rule sorted_sorted_list_of_set)
    have "strict_from_inj n f x = (sorted_list_of_set ?I) ! x"
      unfolding strict_from_inj_def using x by auto
    also have "... < (sorted_list_of_set ?I) ! y"
    proof (rule sorted_nth_strict_mono; clarsimp?)
      show "y < card (f ` {0..<n})"
        by (metis assms atLeastLessThan_iff card_atLeastLessThan card_image diff_zero y)
    qed (simp add: xy)
    also have "... = strict_from_inj n f y" using y unfolding strict_from_inj_def by simp
    finally show ?thesis .
  qed
  thus ?thesis unfolding strict_mono_on_def by simp
qed




lemma strict_from_inj_image':
  assumes f: "inj_on f {0..<n}"
  shows "strict_from_inj n f ` {0..<n} = f`{0..<n}"
proof (auto)
  let ?I = "f ` {0..<n}"
  fix xa assume xa: "xa < n"
  have inj_on: "inj_on f {0..<n}" using f  by auto
  have length_I: "length (sorted_list_of_set ?I) = n"
    by (metis card_atLeastLessThan card_image diff_zero distinct_card distinct_sorted_list_of_set
        finite_atLeastLessThan finite_imageI inj_on sorted_list_of_set(1))

  have "strict_from_inj n f xa = sorted_list_of_set ?I ! xa"
    using xa unfolding strict_from_inj_def by auto
  also have "... = pick ?I xa"
    by (rule sorted_list_of_set_eq_pick, unfold length_I, auto simp add: xa)
  also have "... \<in> f ` {0..<n}" by (rule pick_in_set_le, simp add: card_image inj_on xa)
  finally show "strict_from_inj n f xa \<in> f ` {0..<n}" .
  obtain i where "sorted_list_of_set (f`{0..<n}) ! i = f xa" and "i<n"
    by (metis atLeast0LessThan finite_atLeastLessThan finite_imageI imageI
        in_set_conv_nth length_I lessThan_iff sorted_list_of_set(1) xa)
  thus "f xa \<in> strict_from_inj n f ` {0..<n}"
    by (metis atLeast0LessThan imageI lessThan_iff strict_from_inj_def)
qed



definition "Z (n::nat) (m::nat) = {(f,\<pi>)|f \<pi>. f \<in> {0..<n} \<rightarrow> {0..<m}
  \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
  \<and> \<pi> permutes {0..<n}}"

lemma Z_alt_def: "Z n m = {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)} \<times> {\<pi>. \<pi> permutes {0..<n}}"
  unfolding Z_def by auto

lemma det_mul_finsum_alt:
  assumes A: "A \<in> carrier_mat n m"
    and B: "B \<in> carrier_mat m n"
  shows "det (A*B) = det (mat\<^sub>r n n (\<lambda>i. finsum_vec TYPE('a::comm_ring_1) n
  (\<lambda>k. B $$ (k, i) \<cdot>\<^sub>v Matrix.col A k) {0..<m}))"
proof -
  have AT: "A\<^sup>T \<in> carrier_mat m n" using A by auto
  have BT: "B\<^sup>T \<in> carrier_mat n m" using B by auto
  let ?f = "(\<lambda>i. finsum_vec TYPE('a) n (\<lambda>k. B\<^sup>T $$ (i, k) \<cdot>\<^sub>v Matrix.row A\<^sup>T k) {0..<m})"
  let ?g = "(\<lambda>i. finsum_vec TYPE('a) n (\<lambda>k. B $$ (k, i) \<cdot>\<^sub>v Matrix.col A k) {0..<m})"
  let ?lhs = "mat\<^sub>r n n ?f"
  let ?rhs = "mat\<^sub>r n n ?g"
  have lhs_rhs: "?lhs = ?rhs"
  proof (rule eq_matI)
    show "dim_row ?lhs = dim_row ?rhs" by auto
    show "dim_col ?lhs = dim_col ?rhs" by auto
    fix i j assume i: "i < dim_row ?rhs" and j: "j < dim_col ?rhs"
    have j_n: "j<n" using j by auto
    have "?lhs $$ (i, j) = ?f i $v j" by (rule index_mat, insert i j, auto)
    also have "... = (\<Sum>k\<in>{0..<m}. (B\<^sup>T $$ (i, k) \<cdot>\<^sub>v row A\<^sup>T k) $ j)"
      by (rule index_finsum_vec[OF _ j_n], auto simp add: A)
    also have "... = (\<Sum>k\<in>{0..<m}. (B $$ (k, i) \<cdot>\<^sub>v col A k) $ j)"
    proof (rule sum.cong, auto)
      fix x assume x: "x<m"
      have row_rw: "Matrix.row A\<^sup>T x = col A x" by (rule row_transpose, insert A x, auto)
      have B_rw: "B\<^sup>T $$ (i,x) = B $$ (x, i)"
        by (rule index_transpose_mat, insert x i B, auto)
      have "(B\<^sup>T $$ (i, x) \<cdot>\<^sub>v Matrix.row A\<^sup>T x) $v j = B\<^sup>T $$ (i, x) * Matrix.row A\<^sup>T x $v j"
        by (rule index_smult_vec, insert A j_n, auto)
      also have "... = B $$ (x, i) * col A x $v j" unfolding row_rw B_rw by simp
      also have "... = (B $$ (x, i) \<cdot>\<^sub>v col A x) $v j"
        by (rule index_smult_vec[symmetric], insert A j_n, auto)
      finally show " (B\<^sup>T $$ (i, x) \<cdot>\<^sub>v Matrix.row A\<^sup>T x) $v j = (B $$ (x, i) \<cdot>\<^sub>v col A x) $v j" .
    qed
    also have "... = ?g i $v j"
      by (rule index_finsum_vec[symmetric, OF _ j_n], auto simp add: A)
    also have "... = ?rhs $$ (i, j)" by (rule index_mat[symmetric], insert i j, auto)
    finally show "?lhs $$ (i, j) = ?rhs $$ (i, j)" .
  qed
  have "det (A*B) = det (B\<^sup>T*A\<^sup>T)"
    using det_transpose
    by (metis A B Matrix.transpose_mult mult_carrier_mat)
  also have "... =  det (mat\<^sub>r n n (\<lambda>i. finsum_vec TYPE('a) n (\<lambda>k. B\<^sup>T $$ (i, k) \<cdot>\<^sub>v Matrix.row A\<^sup>T k) {0..<m}))"
    using mat_mul_finsum_alt[OF BT AT] by auto
  also have "... = det (mat\<^sub>r n n (\<lambda>i. finsum_vec TYPE('a) n (\<lambda>k. B $$ (k, i) \<cdot>\<^sub>v Matrix.col A k) {0..<m}))"
    by (rule arg_cong[of _ _ det], rule lhs_rhs)
  finally show ?thesis .
qed


lemma det_cols_mul:
  assumes A: "A \<in> carrier_mat n m"
    and B: "B \<in> carrier_mat m n"
  shows "det (A*B) = (\<Sum>f | (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i).
       (\<Prod>i = 0..<n. B $$ (f i, i)) * Determinant.det (mat\<^sub>r n n (\<lambda>i. col A (f i))))"
proof -
  let ?V="{0..<n}"
  let ?U = "{0..<m}"
  let ?F = " {f. (\<forall>i\<in> {0..<n}. f i \<in> ?U) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  let ?g = "\<lambda>f. det (mat\<^sub>r n n (\<lambda> i. B $$ (f i, i) \<cdot>\<^sub>v col A (f i)))"
  have fm: "finite {0..<m}" by auto
  have fn: "finite {0..<n}" by auto
  have det_rw: "det (mat\<^sub>r n n (\<lambda>i. B $$ (f i, i) \<cdot>\<^sub>v col A (f i))) =
    (prod (\<lambda>i. B $$ (f i, i)) {0..<n}) * det (mat\<^sub>r n n (\<lambda>i. col A (f i)))"
    if  f: "(\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)" for f
    by (rule det_rows_mul, insert A col_dim, auto)
  have "det (A*B) = det (mat\<^sub>r n n (\<lambda>i. finsum_vec TYPE('a::comm_ring_1) n (\<lambda>k. B $$ (k, i) \<cdot>\<^sub>v Matrix.col A k) ?U))"
    by (rule det_mul_finsum_alt[OF A B])
  also have "... = sum ?g ?F" by (rule det_linear_rows_sum[OF fm], auto simp add: A)
  also have "... = (\<Sum>f\<in>?F. prod (\<lambda>i. B $$ (f i, i)) {0..<n} * det (mat\<^sub>r n n (\<lambda>i. col A (f i))))"
    using det_rw by auto
  finally show ?thesis .
qed

lemma det_cols_mul':
  assumes A: "A \<in> carrier_mat n m"
    and B: "B \<in> carrier_mat m n"
  shows "det (A*B) = (\<Sum>f | (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i).
       (\<Prod>i = 0..<n. A $$ (i, f i)) * det (mat\<^sub>r n n (\<lambda>i. row B (f i))))"
proof -
  let ?F="{f. (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  have t: "A * B = (B\<^sup>T*A\<^sup>T)\<^sup>T" using transpose_mult[OF A B] transpose_transpose by metis
  have "det (B\<^sup>T*A\<^sup>T) = (\<Sum>f\<in>?F. (\<Prod>i = 0..<n. A\<^sup>T $$ (f i, i)) * det (mat\<^sub>r n n (\<lambda>i. col B\<^sup>T (f i))))"
    by (rule det_cols_mul, auto simp add: A B)
  also have "... = (\<Sum>f \<in>?F. (\<Prod>i = 0..<n. A $$ (i, f i)) * det (mat\<^sub>r n n (\<lambda>i. row B (f i))))"
  proof (rule sum.cong, rule refl)
    fix f assume f: "f \<in> ?F"
    have "(\<Prod>i = 0..<n. A\<^sup>T $$ (f i, i)) = (\<Prod>i = 0..<n. A $$ (i, f i))"
    proof (rule prod.cong, rule refl)
      fix x assume x: "x \<in> {0..<n}"
      show "A\<^sup>T $$ (f x, x) = A $$ (x, f x)"
        by (rule index_transpose_mat(1), insert f A x, auto)
    qed
    moreover have "det (mat\<^sub>r n n (\<lambda>i. col B\<^sup>T (f i))) = det (mat\<^sub>r n n (\<lambda>i. row B (f i)))"
    proof -
      have row_eq_colT: "row B (f i) $v j = col B\<^sup>T (f i) $v j" if i: "i < n" and j: "j < n" for i j
      proof -
        have fi_m: "f i < m" using f i by auto
        have "col B\<^sup>T (f i) $v j = B\<^sup>T $$(j, f i)" by (rule index_col, insert B fi_m j, auto)
        also have "... = B $$ (f i, j)" using B fi_m j by auto
        also have "... = row B (f i) $v j" by (rule index_row[symmetric], insert B fi_m j, auto)
        finally show ?thesis ..
      qed
      show ?thesis by (rule arg_cong[of _ _ det], rule eq_matI, insert row_eq_colT, auto)
    qed
    ultimately show "(\<Prod>i = 0..<n. A\<^sup>T $$ (f i, i)) * det (mat\<^sub>r n n (\<lambda>i. col B\<^sup>T (f i))) =
         (\<Prod>i = 0..<n. A $$ (i, f i)) * det (mat\<^sub>r n n (\<lambda>i. row B (f i)))" by simp
  qed
  finally show ?thesis
    by (metis (no_types, lifting) A B det_transpose transpose_mult mult_carrier_mat)
qed

(*We need a more general version of this lemma*)
lemma
  assumes F: "F= {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  and p: " \<pi> permutes {0..<n}"
  shows " (\<Sum>f\<in>F. (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))) = (\<Sum>f\<in>F. (\<Prod>i = 0..<n. B $$ (f i, i)))"
proof -
  let ?h = "(\<lambda>f. f \<circ> \<pi>)"
  have inj_on_F: "inj_on ?h F"
  proof (rule inj_onI)
    fix f g assume fop: "f \<circ> \<pi> = g \<circ> \<pi>"
    have "f x = g x" for x
    proof (cases "x \<in> {0..<n}")
      case True
      then show ?thesis
        by (metis fop comp_apply p permutes_def)
    next
      case False
      then show ?thesis
        by (metis fop comp_eq_elim p permutes_def)
    qed
    thus "f = g" by auto
  qed
  have hF: "?h` F = F"
    unfolding image_def
  proof auto
    fix xa assume xa: "xa \<in> F" show "xa \<circ> \<pi> \<in> F"
      unfolding o_def F
      using F PiE p xa
      by (auto, smt F atLeastLessThan_iff mem_Collect_eq p permutes_def xa)
    show "\<exists>x\<in>F. xa = x \<circ> \<pi>"
    proof (rule bexI[of _ "xa \<circ> Hilbert_Choice.inv \<pi>"])
      show "xa = xa \<circ> Hilbert_Choice.inv \<pi> \<circ> \<pi>"
        using p by auto
      show "xa \<circ> Hilbert_Choice.inv \<pi> \<in> F"
        unfolding o_def F
        using F PiE p xa
        by (auto, smt atLeastLessThan_iff permutes_def permutes_less(3))
    qed
  qed
  have prod_rw: "(\<Prod>i = 0..<n. B $$ (f i, i)) = (\<Prod>i = 0..<n. B $$ (f (\<pi> i), \<pi> i))" if "f\<in>F" for f
  using prod.permute[OF p] by auto
  let ?g = "\<lambda>f. (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))"
  have "(\<Sum>f\<in>F. (\<Prod>i = 0..<n. B $$ (f i, i))) = (\<Sum>f\<in>F. (\<Prod>i = 0..<n. B $$ (f (\<pi> i), \<pi> i)))"
    using prod_rw by auto
  also have "... = (\<Sum>f\<in>(?h`F). \<Prod>i = 0..<n. B $$ (f i, \<pi> i))"
    using sum.reindex[OF inj_on_F, of ?g] unfolding hF by auto
  also have "... = (\<Sum>f\<in>F. \<Prod>i = 0..<n. B $$ (f i, \<pi> i))" unfolding hF by auto
  finally show ?thesis ..
qed


lemma detAB_Znm_aux:
  assumes F: "F= {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  shows"(\<Sum>\<pi> | \<pi> permutes {0..<n}. (\<Sum>f\<in>F. prod (\<lambda>i. B $$ (f i, i)) {0..<n}
        * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (\<pi> i, f i)))))
    = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>F. (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))
        * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (i, f i))))"
proof -
  have "(\<Sum>\<pi> | \<pi> permutes {0..<n}. (\<Sum>f\<in>F. prod (\<lambda>i. B $$ (f i, i)) {0..<n}
      * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (\<pi> i, f i))))) =
    (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>F. signof \<pi> * (\<Prod>i = 0..<n. B $$ (f i, i) * A $$ (\<pi> i, f i)))"
    by (smt mult.left_commute prod.cong prod.distrib sum.cong)
  also have "... = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>F. signof (Hilbert_Choice.inv \<pi>)
    * (\<Prod>i = 0..<n. B $$ (f i, i) * A $$ (Hilbert_Choice.inv \<pi> i, f i)))"
    by (rule sum_permutations_inverse)
  also have "... = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>F. signof (Hilbert_Choice.inv \<pi>)
    * (\<Prod>i = 0..<n. B $$ (f (\<pi> i), (\<pi> i)) * A $$ (Hilbert_Choice.inv \<pi> (\<pi> i), f (\<pi> i))))"
  proof (rule sum.cong)
    fix x assume x: "x \<in> {\<pi>. \<pi> permutes {0..<n}}"
    let ?inv_x = "Hilbert_Choice.inv x"
    have p: "x permutes {0..<n}" using x by simp
    have prod_rw: "(\<Prod>i = 0..<n. B $$ (f i, i) * A $$ (?inv_x i, f i))
        = (\<Prod>i = 0..<n. B $$ (f (x i), x i) * A $$ (?inv_x (x i), f (x i)))" if "f \<in> F" for f
      using prod.permute[OF p] by auto
    then show "(\<Sum>f\<in>F. signof ?inv_x * (\<Prod>i = 0..<n. B $$ (f i, i) * A $$ (?inv_x i, f i))) =
         (\<Sum>f\<in>F. signof ?inv_x * (\<Prod>i = 0..<n. B $$ (f (x i), x i) * A $$ (?inv_x (x i), f (x i))))"
      by auto
  qed (simp)
  also have "... = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>F. signof \<pi>
    * (\<Prod>i = 0..<n. B $$ (f (\<pi> i), (\<pi> i)) * A $$ (i, f (\<pi> i))))"
    by (rule sum.cong, auto, rule sum.cong, auto)
        (metis (no_types, lifting) finite_atLeastLessThan signof_inv)
  also have "... = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>F. signof \<pi>
    * (\<Prod>i = 0..<n. B $$ (f i, (\<pi> i)) * A $$ (i, f i)))"
  proof (rule sum.cong)
    fix \<pi> assume p: "\<pi> \<in> {\<pi>. \<pi> permutes {0..<n}}"
    hence p: "\<pi> permutes {0..<n}" by auto
    let ?inv_pi = "(Hilbert_Choice.inv \<pi>)"
    let ?h = "(\<lambda>f. f \<circ> (Hilbert_Choice.inv \<pi>))"
  have inj_on_F: "inj_on ?h F"
  proof (rule inj_onI)
    fix f g assume fop: "f \<circ> ?inv_pi = g \<circ> ?inv_pi"
    have "f x = g x" for x
    proof (cases "x \<in> {0..<n}")
      case True
      then show ?thesis
        by (metis fop o_inv_o_cancel p permutes_inj)
    next
      case False
      then show ?thesis
        by (metis fop o_inv_o_cancel p permutes_inj)
    qed
    thus "f = g" by auto
  qed
  have hF: "?h` F = F"
    unfolding image_def
  proof auto
    fix xa assume xa: "xa \<in> F" show "xa \<circ> ?inv_pi \<in> F"
      unfolding o_def F
      using F PiE p xa
      by (auto, smt atLeastLessThan_iff permutes_def permutes_less(3))
    show "\<exists>x\<in>F. xa = x \<circ> ?inv_pi"
    proof (rule bexI[of _ "xa \<circ> \<pi>"])
      show "xa = xa \<circ> \<pi> \<circ> Hilbert_Choice.inv \<pi> "
        using p by auto
      show "xa \<circ> \<pi> \<in> F"
        unfolding o_def F
        using F PiE p xa
        by (auto, smt atLeastLessThan_iff permutes_def permutes_less(3))
    qed
  qed
  let ?g = "\<lambda>f. signof \<pi> * (\<Prod>i = 0..<n. B $$ (f (\<pi> i), \<pi> i) * A $$ (i, f (\<pi> i)))"
    show "(\<Sum>f\<in>F. signof \<pi> * (\<Prod>i = 0..<n. B $$ (f (\<pi> i), \<pi> i) * A $$ (i, f (\<pi> i)))) =
         (\<Sum>f\<in>F. signof \<pi> * (\<Prod>i = 0..<n. B $$ (f i, \<pi> i) * A $$ (i, f i)))"
      using sum.reindex[OF inj_on_F, of "?g"] p unfolding hF unfolding o_def by auto
  qed (simp)
  also have "... = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>F. (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))
  * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (i, f i))))"
    by (smt mult.left_commute prod.cong prod.distrib sum.cong)
  finally show ?thesis .
qed


lemma detAB_Znm:
  assumes A: "A \<in> carrier_mat n m"
    and B: "B \<in> carrier_mat m n"
  shows "det (A*B) = (\<Sum>(f, \<pi>)\<in>Z n m. signof \<pi> * (\<Prod>i = 0..<n. A $$ (i, f i) * B $$ (f i, \<pi> i)))"
proof -
  let ?V="{0..<n}"
  let ?U = "{0..<m}"
  let ?PU = "{p. p permutes ?U}"
  let ?F = " {f. (\<forall>i\<in> {0..<n}. f i \<in> ?U) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  let ?f = "\<lambda>f. det (mat\<^sub>r n n (\<lambda> i. A $$ (i, f i) \<cdot>\<^sub>v row B (f i)))"
  let ?g = "\<lambda>f. det (mat\<^sub>r n n (\<lambda> i. B $$ (f i, i) \<cdot>\<^sub>v col A (f i)))"
  have fm: "finite {0..<m}" by auto
  have fn: "finite {0..<n}" by auto
  have F: "?F= {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}" by auto
  have det_rw: "det (mat\<^sub>r n n (\<lambda>i. B $$ (f i, i) \<cdot>\<^sub>v col A (f i))) =
    (prod (\<lambda>i. B $$ (f i, i)) {0..<n}) * det (mat\<^sub>r n n (\<lambda>i. col A (f i)))"
    if  f: "(\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)" for f
    by (rule det_rows_mul, insert A col_dim, auto)
  have det_rw2: "det (mat\<^sub>r n n (\<lambda>i. col A (f i)))
  = (\<Sum>\<pi> | \<pi> permutes {0..<n}. signof \<pi> * (\<Prod>i = 0..<n. A $$ (\<pi> i, f i)))"
    if f: "f \<in> ?F" for f
  proof (unfold Determinant.det_def, auto, rule sum.cong, auto)
    fix x assume x: "x permutes {0..<n}"
    have "(\<Prod>i = 0..<n. col A (f i) $v x i) = (\<Prod>i = 0..<n. A $$ (x i, f i))"
    proof (rule prod.cong)
      fix xa assume xa: "xa \<in> {0..<n}" show "col A (f xa) $v x xa = A $$ (x xa, f  xa)"
        by (metis A atLeastLessThan_iff carrier_matD(1) col_def index_vec permutes_less(1) x xa)
    qed (auto)
    then show "signof x * (\<Prod>i = 0..<n. col A (f i) $v x i)
      = signof x * (\<Prod>i = 0..<n. A $$ (x i, f i))" by auto
  qed
  have fin_n: "finite {0..<n}" and fin_m: "finite {0..<m}" by auto
  have "det (A*B) = det (mat\<^sub>r n n (\<lambda>i. finsum_vec TYPE('a::comm_ring_1) n
    (\<lambda>k. B $$ (k, i) \<cdot>\<^sub>v Matrix.col A k) {0..<m}))"
    by (rule det_mul_finsum_alt[OF A B])
  also have "... = sum ?g ?F" by (rule det_linear_rows_sum[OF fm], auto simp add: A)
  also have "... = (\<Sum>f\<in>?F. prod (\<lambda>i. B $$ (f i, i)) {0..<n} * det (mat\<^sub>r n n (\<lambda>i. col A (f i))))"
    using det_rw by auto
  also have "... = (\<Sum>f\<in>?F. prod (\<lambda>i. B $$ (f i, i)) {0..<n} *
  (\<Sum>\<pi> | \<pi> permutes {0..<n}. signof \<pi> * (\<Prod>i = 0..<n. A $$ (\<pi> i, f (i)))))"
    by (rule sum.cong, auto simp add: det_rw2)
  also have "... =
  (\<Sum>f\<in>?F. \<Sum>\<pi> | \<pi> permutes {0..<n}. prod (\<lambda>i. B $$ (f i, i)) {0..<n}
    * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (\<pi> i, f (i)))))"
    by (simp add: mult_hom.hom_sum)
  also have "... = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>?F.prod (\<lambda>i. B $$ (f i, i)) {0..<n}
    * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (\<pi> i, f i))))"
    by (rule VS_Connect.class_semiring.finsum_finsum_swap,
      insert finite_permutations finite_bounded_functions[OF fin_m fin_n], auto)
  thm detAB_Znm_aux
  also have "... = (\<Sum>\<pi> | \<pi> permutes {0..<n}. \<Sum>f\<in>?F. (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))
  * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (i, f i))))" by (rule detAB_Znm_aux, auto)
  also have "... = (\<Sum>f\<in>?F.\<Sum>\<pi> | \<pi> permutes {0..<n}. (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))
  * (signof \<pi> * (\<Prod>i = 0..<n. A $$ (i, f i))))"
    by (rule VS_Connect.class_semiring.finsum_finsum_swap,
      insert finite_permutations finite_bounded_functions[OF fin_m fin_n], auto)
  also have "... =  (\<Sum>f\<in>?F.\<Sum>\<pi> | \<pi> permutes {0..<n}. signof \<pi>
    * (\<Prod>i = 0..<n. A $$ (i, f i) * B $$ (f i, \<pi> i)))"
    unfolding prod.distrib by (rule sum.cong, auto, rule sum.cong, auto)
  also have "... = sum (\<lambda>(f,\<pi>). (signof \<pi>)
    * (prod (\<lambda>i. A$$(i,f i) * B $$ (f i, \<pi> i)) {0..<n})) (Z n m)"
    unfolding Z_alt_def unfolding sum.cartesian_product[symmetric] F by auto
  finally show ?thesis .
qed

(*Several lemmas here can be moved outside the context*)
context
  fixes n m and A B::"'a::comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat n m"
    and B: "B \<in> carrier_mat m n"
begin

private definition "Z_inj = ({f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
  \<and> inj_on f {0..<n}} \<times> {\<pi>. \<pi> permutes {0..<n}})"

private definition "Z_not_inj = ({f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
  \<and> \<not> inj_on f {0..<n}} \<times> {\<pi>. \<pi> permutes {0..<n}})"

private definition "Z_strict = ({f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
  \<and> strict_mono_on f {0..<n}} \<times> {\<pi>. \<pi> permutes {0..<n}})"

private definition "Z_not_strict = ({f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
  \<and> \<not> strict_mono_on f {0..<n}} \<times> {\<pi>. \<pi> permutes {0..<n}})"

private definition "weight f \<pi>
  = (signof \<pi>) * (prod (\<lambda>i. A$$(i,f i) * B $$ (f i, \<pi> i)) {0..<n})"

private definition "Z_good g = ({f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
  \<and> inj_on f {0..<n} \<and> (f`{0..<n} = g`{0..<n})} \<times> {\<pi>. \<pi> permutes {0..<n}})"

private definition "F_strict = {f. f \<in> {0..<n} \<rightarrow> {0..<m}
  \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) \<and> strict_mono_on f {0..<n}}"

private definition "F_inj = {f. f \<in> {0..<n} \<rightarrow> {0..<m}
  \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) \<and> inj_on f {0..<n}}"

private definition "F_not_inj = {f. f \<in> {0..<n} \<rightarrow> {0..<m}
  \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) \<and> \<not> inj_on f {0..<n}}"

private definition "F = {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"

text\<open>The Cauchy--Binet formula is proven in \url{https://core.ac.uk/download/pdf/82475020.pdf}
  In that work, they define @{text "\<sigma> \<equiv> inv \<phi> \<circ> \<pi>"}. I had problems following this proof
  in Isabelle, since I was demanded to show that such permutations commute, which is false.
  It is a notation problem of the  @{text "\<circ>"} operator, the author means @{text "\<sigma> \<equiv> \<pi> \<circ> inv \<phi>"} using
  the Isabelle notation (i.e., @{text "\<sigma> x = \<pi> ((inv \<phi>) x)"}).
\<close>

lemma step_weight:
  fixes \<phi> \<pi>
  defines "\<sigma> \<equiv> \<pi> \<circ> Hilbert_Choice.inv \<phi>"
  assumes f_inj: "f \<in> F_inj" and gF: "g \<in> F" and pi: "\<pi> permutes {0..<n}"
  and phi: "\<phi> permutes {0..<n}" and fg_phi: "\<forall>x \<in> {0..<n}. f x = g (\<phi> x)"
shows "weight f \<pi> = (signof \<phi>) * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i)))
  * (signof \<sigma>) * (\<Prod>i = 0..<n. B $$ (g i, \<sigma> i))"
proof -
  let ?A = "(\<Prod>i = 0..<n. A $$ (i, g (\<phi> i))) "
  let ?B = "(\<Prod>i = 0..<n. B $$ (g i, \<sigma> i))"
  have sigma: "\<sigma> permutes {0..<n}" unfolding \<sigma>_def
    by (rule permutes_compose[OF permutes_inv[OF phi] pi])
  have A_rw: "?A = (\<Prod>i = 0..<n. A $$ (i, f i))" using fg_phi by auto
  have "?B = (\<Prod>i = 0..<n. B $$ (g (\<phi> i), \<sigma> (\<phi> i)))"
    by (rule prod.permute[unfolded o_def, OF phi])
  also have "... = (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))"
    using fg_phi
    unfolding \<sigma>_def unfolding o_def unfolding permutes_inverses(2)[OF phi] by auto
  finally have B_rw: "?B = (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))" .
  have "(signof \<phi>) * ?A * (signof \<sigma>) * ?B = (signof \<phi>) * (signof \<sigma>) * ?A * ?B" by auto
  also have "... = signof (\<phi> \<circ> \<sigma>) * ?A * ?B" unfolding signof_compose[OF phi sigma] by simp
  also have "... = signof \<pi> * ?A * ?B"
    by (metis (no_types, lifting) \<sigma>_def mult.commute o_inv_o_cancel permutes_inj
        phi sigma signof_compose)
  also have "... = signof \<pi> * (\<Prod>i = 0..<n. A $$ (i, f i)) * (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))"
    using A_rw B_rw by auto
  also have "... = signof \<pi> * (\<Prod>i = 0..<n. A $$ (i, f i) * B $$ (f i, \<pi> i))" by auto
  also have "... = weight f \<pi>" unfolding weight_def by simp
  finally show ?thesis ..
qed


lemma Z_good_fun_alt_sum:
  fixes g
  defines "Z_good_fun \<equiv> {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
    \<and> inj_on f {0..<n} \<and> (f`{0..<n} = g`{0..<n})}"
  assumes g: "g \<in> F_inj"
  shows "(\<Sum>f\<in>Z_good_fun. P f)= (\<Sum>\<pi>\<in>{\<pi>. \<pi> permutes {0..<n}}. P (g \<circ> \<pi>))"
proof -
  let ?f = "\<lambda>\<pi>. g \<circ> \<pi>"
  let ?P = "{\<pi>. \<pi> permutes {0..<n}}"
  have fP: "?f`?P = Z_good_fun"
  proof (unfold Z_good_fun_def, auto)
    fix xa xb assume "xa permutes {0..<n}" and "xb < n"
    hence "xa xb < n" by auto
    thus "g (xa xb) < m" using g unfolding F_inj_def by fastforce
  next
    fix xa i assume "xa permutes {0..<n}" and i_ge_n: "\<not> i < n"
    hence "xa i = i" unfolding permutes_def by auto
    thus "g (xa i) = i" using g i_ge_n unfolding F_inj_def by auto
  next
    fix xa assume "xa permutes {0..<n}" thus "inj_on (g \<circ> xa) {0..<n}"
      by (metis (mono_tags, lifting) F_inj_def atLeast0LessThan comp_inj_on g
          mem_Collect_eq permutes_image permutes_inj_on)
  next
    fix \<pi> xb assume "\<pi> permutes {0..<n}" and "xb < n" thus " g xb \<in> (\<lambda>x. g (\<pi> x)) ` {0..<n}"
      by (metis (full_types) atLeast0LessThan imageI image_image lessThan_iff permutes_image)
  next
   fix x assume x1: "x \<in> {0..<n} \<rightarrow> {0..<m}" and x2: "\<forall>i. \<not> i < n \<longrightarrow> x i = i"
     and inj_on_x: "inj_on x {0..<n}" and xg: "x ` {0..<n} = g ` {0..<n}"
   let ?\<tau> = "\<lambda>i. if i<n then (THE j. j<n \<and> x i = g j) else i"
   show "x \<in> (\<circ>) g ` {\<pi>. \<pi> permutes {0..<n}}"
   proof (unfold image_def, auto, rule exI[of _ ?\<tau>], rule conjI)
     have "?\<tau> i = i" if i: "i \<notin> {0..<n}" for i
       using i by auto
     moreover have "\<exists>!j. ?\<tau> j = i" for i
     proof (cases "i<n")
       case True
       obtain a where xa_gi: "x a = g i" and a: "a < n" using xg True
         by (metis (mono_tags, hide_lams) atLeast0LessThan imageE imageI lessThan_iff)
       show ?thesis
       proof (rule ex1I[of _ a])
         have the_ai: "(THE j. j < n \<and> x a = g j) = i"
         proof (rule theI2)
           show "i < n \<and> x a = g i" using xa_gi True by auto
           fix xa assume "xa < n \<and> x a = g xa" thus "xa = i"
             by (metis (mono_tags, lifting) F_inj_def True atLeast0LessThan
                g inj_onD lessThan_iff mem_Collect_eq xa_gi)
           thus "xa = i" .
         qed
         thus ta: "?\<tau> a = i" using a by auto
         fix j assume tj: "?\<tau> j = i"
         show "j = a"
         proof (cases "j<n")
           case True
           obtain b where xj_gb: "x j = g b" and b: "b < n" using xg True
             by (metis (mono_tags, hide_lams) atLeast0LessThan imageE imageI lessThan_iff)
           let ?P = "\<lambda>ja. ja < n \<and> x j = g ja"
           have the_ji: "(THE ja. ja < n \<and> x j = g ja) = i" using tj True by auto
           have "?P (THE ja. ?P ja)"
           proof (rule theI)
            show "b < n \<and> x j = g b" using xj_gb b by auto
            fix xa assume "xa < n \<and> x j = g xa" thus "xa = b"
              by (metis (mono_tags, lifting) F_inj_def b atLeast0LessThan
                  g inj_onD lessThan_iff mem_Collect_eq xj_gb)
           qed
           hence "x j = g i" unfolding the_ji by auto
           hence "x j = x a" using xa_gi by auto
           then show ?thesis using inj_on_x a True unfolding inj_on_def by auto
         next
           case False
           then show ?thesis using tj True by auto
         qed
       qed
     next
       case False note i_ge_n = False
       show ?thesis
       proof (rule ex1I[of _ i])
         show "?\<tau> i = i" using False by simp
         fix j assume tj: "?\<tau> j = i"
         show "j = i"
         proof (cases "j<n")
           case True
           obtain a where xj_ga: "x j = g a" and a: "a < n" using xg True
             by (metis (mono_tags, hide_lams) atLeast0LessThan imageE imageI lessThan_iff)
           have "(THE ja. ja < n \<and> x j = g ja) < n"
           proof (rule theI2)
             show "a < n \<and> x j = g a" using xj_ga a by auto
             fix xa assume a1: "xa < n \<and> x j = g xa" thus "xa = a"
               using F_inj_def  a atLeast0LessThan g inj_on_eq_iff xj_ga by fastforce
             show "xa < n" by (simp add: a1)
           qed
            then show ?thesis using tj i_ge_n by auto
          next
            case False
            then show ?thesis using tj  by auto
          qed
       qed
     qed
     ultimately show "?\<tau> permutes {0..<n}" unfolding permutes_def by auto
     show "x = g \<circ> ?\<tau>"
     proof -
       have "x xa = g (THE j. j < n \<and> x xa = g j)" if xa: "xa < n" for xa
       proof -
         obtain c where c: "c < n" and xxa_gc: "x xa = g c"
           by (metis (mono_tags, hide_lams) atLeast0LessThan imageE imageI lessThan_iff xa xg)
         show ?thesis
         proof (rule theI2)
           show c1: "c < n \<and> x xa = g c" using c xxa_gc by auto
           fix xb assume c2: "xb < n \<and> x xa = g xb" thus "xb = c"
             by (metis (mono_tags, lifting) F_inj_def c1 atLeast0LessThan
                 g inj_onD lessThan_iff mem_Collect_eq)
           show "x xa = g xb" using c1 c2 by simp
         qed
       qed
       moreover have "x xa = g xa" if xa: "\<not> xa < n" for xa
         using g x1 x2 xa unfolding F_inj_def by simp
       ultimately show ?thesis unfolding o_def fun_eq_iff by auto
     qed
   qed
 qed
  have inj: "inj_on ?f ?P"
  proof (rule inj_onI)
    fix x y assume x: "x \<in> ?P" and y: "y \<in> ?P" and gx_gy: "g \<circ> x = g \<circ> y"
    have "x i = y i" for i
    proof (cases "i<n")
      case True
      hence xi: "x i \<in> {0..<n}" and yi: "y i \<in> {0..<n}" using x y by auto
      have "g (x i) = g (y i)" using gx_gy unfolding o_def by meson
      thus ?thesis using xi yi using g unfolding F_inj_def inj_on_def by blast
    next
      case False
      then show ?thesis using x y unfolding permutes_def by auto
    qed
    thus "x = y" unfolding fun_eq_iff by auto
  qed
  have "(\<Sum>f\<in>Z_good_fun. P f) = (\<Sum>f\<in>?f`?P. P f)" using fP by simp
  also have "... =  sum (P \<circ> (\<circ>) g) {\<pi>. \<pi> permutes {0..<n}}"
    by (rule sum.reindex[OF inj])
  also have "... =  (\<Sum>\<pi> | \<pi> permutes {0..<n}. P (g \<circ> \<pi>))" by auto
  finally show ?thesis .
qed


lemma F_injI:
  assumes "f \<in> {0..<n} \<rightarrow> {0..<m}"
  and "(\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)" and "inj_on f {0..<n}"
  shows "f \<in> F_inj" using assms unfolding F_inj_def by simp

lemma F_inj_composition_permutation:
  assumes phi: "\<phi> permutes {0..<n}"
  and g: "g \<in> F_inj"
  shows "g \<circ> \<phi> \<in> F_inj"
proof (rule F_injI)
  show "g \<circ> \<phi> \<in> {0..<n} \<rightarrow> {0..<m}"
    using g unfolding permutes_def F_inj_def
    by (simp add: Pi_iff phi)
  show "\<forall>i. i \<notin> {0..<n} \<longrightarrow> (g \<circ> \<phi>) i = i"
    using g phi unfolding permutes_def F_inj_def by simp
  show "inj_on (g \<circ> \<phi>) {0..<n}"
    by (rule comp_inj_on, insert g permutes_inj_on[OF phi] permutes_image[OF phi])
       (auto simp add: F_inj_def)
qed


lemma F_strict_imp_F_inj:
  assumes f: "f \<in> F_strict"
  shows "f \<in> F_inj"
  using f strict_mono_on_imp_inj_on
  unfolding F_strict_def F_inj_def by auto


lemma one_step:
  assumes g1: "g \<in> F_strict"
  shows "det (submatrix A UNIV (g`{0..<n})) * det (submatrix B (g`{0..<n}) UNIV)
    = (\<Sum>(x, y) \<in> Z_good g. weight x y)" (is "?lhs = ?rhs")
proof -
  define Z_good_fun where "Z_good_fun = {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
    \<and> inj_on f {0..<n} \<and> (f`{0..<n} = g`{0..<n})}"
  let ?Perm = "{\<pi>. \<pi> permutes {0..<n}}"
  let ?P = "(\<lambda>f. \<Sum>\<pi> \<in> ?Perm. weight f \<pi>)"
  let ?inv = "Hilbert_Choice.inv"
  have g: "g \<in> F_inj" by (rule F_strict_imp_F_inj[OF g1])
  have detA: "(\<Sum>\<phi>\<in>{\<pi>. \<pi> permutes {0..<n}}. signof \<phi> * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i))))
    = det (submatrix A UNIV (g`{0..<n}))"
  proof -
    have "{j. j < dim_col A \<and> j \<in> g ` {0..<n}} = {j. j \<in> g ` {0..<n}}"
      using g A unfolding F_inj_def by fastforce
    also have "card ... = n" using F_inj_def card_image g by force
    finally have card_J: "card {j. j < dim_col A \<and> j \<in> g ` {0..<n}} = n" by simp
    have subA_carrier: "submatrix A UNIV (g ` {0..<n}) \<in> carrier_mat n n"
      unfolding submatrix_def card_J using A by auto
    have "det (submatrix A UNIV (g`{0..<n})) = (\<Sum>p | p permutes {0..<n}.
            signof p * (\<Prod>i = 0..<n. submatrix A UNIV (g ` {0..<n}) $$ (i, p i)))"
      using subA_carrier unfolding Determinant.det_def by auto
    also have "... = (\<Sum>\<phi>\<in>{\<pi>. \<pi> permutes {0..<n}}. signof \<phi> * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i))))"
    proof (rule sum.cong)
      fix x assume x: "x \<in> {\<pi>. \<pi> permutes {0..<n}}"
      have "(\<Prod>i = 0..<n. submatrix A UNIV (g ` {0..<n}) $$ (i, x i))
          = (\<Prod>i = 0..<n. A $$ (i, g (x i)))"
      proof (rule prod.cong, rule refl)
        fix i assume i: "i \<in> {0..<n}"
        have pick_rw: "pick (g ` {0..<n}) (x i) = g (x i)"
        proof -
          have "index (sorted_list_of_set (g ` {0..<n})) (g (x i)) = x i"
          proof -
            have rw: "sorted_list_of_set (g ` {0..<n}) = map g [0..<n]"
              by (rule sorted_list_of_set_map_strict, insert g1, simp add: F_strict_def)
            have "index (sorted_list_of_set (g`{0..<n})) (g (x i)) = index (map g [0..<n]) (g (x i))"
              unfolding rw by auto
            also have "... = index [0..<n] (x i)"
              by (rule index_map_inj_on[of _ "{0..<n}"], insert x i g, auto simp add: F_inj_def)
            also have "... = x i" using x i by auto
            finally show ?thesis .
          qed
          moreover have "(g (x i))  \<in> (g ` {0..<n})" using x g i unfolding F_inj_def by auto
          moreover have "x i < card (g ` {0..<n})" using x i g by (simp add: F_inj_def card_image)
          ultimately show ?thesis using pick_index by auto
        qed
        have "submatrix A UNIV (g`{0..<n}) $$ (i, x i) = A $$ (pick UNIV i, pick (g`{0..<n}) (x i))"
          by (rule submatrix_index, insert i A card_J x, auto)
        also have "... = A $$ (i, g (x i))" using pick_rw pick_UNIV by auto
        finally show "submatrix A UNIV (g ` {0..<n}) $$ (i, x i) = A $$ (i, g (x i))" .
      qed
      thus "signof x * (\<Prod>i = 0..<n. submatrix A UNIV (g ` {0..<n}) $$ (i, x i))
        = signof x * (\<Prod>i = 0..<n. A $$ (i, g (x i)))" by auto
    qed (simp)
    finally show ?thesis by simp
  qed
  have detB_rw: "(\<Sum>\<pi> \<in> ?Perm. signof (\<pi> \<circ> ?inv \<phi>) * (\<Prod>i = 0..<n. B $$ (g i, (\<pi> \<circ> ?inv \<phi>) i)))
   = (\<Sum>\<pi> \<in> ?Perm. signof (\<pi>) * (\<Prod>i = 0..<n. B $$ (g i, \<pi> i)))"
    if phi: "\<phi> permutes {0..<n}" for \<phi>
  proof -
    let ?h="\<lambda>\<pi>. \<pi> \<circ> ?inv \<phi>"
    let ?g = "\<lambda>\<pi>. signof (\<pi>) * (\<Prod>i = 0..<n. B $$ (g i, \<pi> i))"
    have "?h`?Perm = ?Perm"
    proof -
      have "\<pi> \<circ> ?inv \<phi> permutes {0..<n}" if pi: "\<pi> permutes {0..<n}" for \<pi>
        using permutes_compose permutes_inv phi that by blast
      moreover have "x \<in> (\<lambda>\<pi>. \<pi> \<circ> ?inv \<phi>) ` ?Perm" if "x permutes {0..<n}" for x
      proof -
        have "x \<circ> \<phi> permutes {0..<n}"
          using permutes_compose phi that by blast
        moreover have "x = x \<circ> \<phi> \<circ> ?inv \<phi>" using phi by auto
        ultimately show ?thesis unfolding image_def by auto
      qed
      ultimately show ?thesis by auto
    qed
    hence "(\<Sum>\<pi> \<in> ?Perm. ?g \<pi>) = (\<Sum>\<pi> \<in> ?h`?Perm. ?g \<pi>)" by simp
    also have "... = sum (?g \<circ> ?h) ?Perm"
    proof (rule sum.reindex)
      show "inj_on (\<lambda>\<pi>. \<pi> \<circ> ?inv \<phi>) {\<pi>. \<pi> permutes {0..<n}}"
        by (metis (no_types, lifting) inj_onI o_inv_o_cancel permutes_inj phi)
    qed
    also have "... = (\<Sum>\<pi> \<in> ?Perm. signof (\<pi> \<circ> ?inv \<phi>) * (\<Prod>i = 0..<n. B $$ (g i, (\<pi> \<circ> ?inv \<phi>) i)))"
      unfolding o_def by auto
    finally show ?thesis by simp
  qed

  have detB: "det (submatrix B (g`{0..<n}) UNIV)
    = (\<Sum>\<pi> \<in> ?Perm. signof \<pi> * (\<Prod>i = 0..<n. B $$ (g i, \<pi> i)))"
  proof -
    have "{i. i < dim_row B \<and> i \<in> g ` {0..<n}} = {i. i \<in> g ` {0..<n}}"
     using g B unfolding F_inj_def by fastforce
    also have "card ... = n" using F_inj_def card_image g by force
    finally have card_I: "card {j. j < dim_row B \<and> j \<in> g ` {0..<n}} = n" by simp
    have subB_carrier: "submatrix B (g ` {0..<n}) UNIV \<in> carrier_mat n n"
      unfolding submatrix_def using card_I B by auto
    have "det (submatrix B (g`{0..<n}) UNIV) = (\<Sum>p \<in> ?Perm. signof p
      * (\<Prod>i=0..<n. submatrix B (g ` {0..<n}) UNIV $$ (i, p i)))"
      unfolding Determinant.det_def using subB_carrier by auto
    also have "... = (\<Sum>\<pi> \<in> ?Perm. signof \<pi> * (\<Prod>i = 0..<n. B $$ (g i, \<pi> i)))"
    proof (rule sum.cong, rule refl)
      fix x assume x: "x \<in> {\<pi>. \<pi> permutes {0..<n}}"
      have "(\<Prod>i=0..<n. submatrix B (g`{0..<n}) UNIV $$ (i, x i)) = (\<Prod>i=0..<n. B $$ (g i, x i))"
      proof (rule prod.cong, rule refl)
        fix i assume i: "i \<in> {0..<n}"
        have pick_rw: "pick (g ` {0..<n}) i = g i"
        proof -
          have "index (sorted_list_of_set (g ` {0..<n})) (g i) = i"
          proof -
            have rw: "sorted_list_of_set (g ` {0..<n}) = map g [0..<n]"
              by (rule sorted_list_of_set_map_strict, insert g1, simp add: F_strict_def)
            have "index (sorted_list_of_set (g`{0..<n})) (g i) = index (map g [0..<n]) (g i)"
              unfolding rw by auto
            also have "... = index [0..<n] (i)"
              by (rule index_map_inj_on[of _ "{0..<n}"], insert x i g, auto simp add: F_inj_def)
            also have "... = i" using i by auto
            finally show ?thesis .
          qed
          moreover have "(g i)  \<in> (g ` {0..<n})" using x g i unfolding F_inj_def by auto
          moreover have "i < card (g ` {0..<n})" using x i g by (simp add: F_inj_def card_image)
          ultimately show ?thesis using pick_index by auto
        qed
        have "submatrix B (g`{0..<n}) UNIV $$ (i, x i) = B $$ (pick (g`{0..<n}) i, pick UNIV (x i))"
          by (rule submatrix_index, insert i B card_I x, auto)
        also have "... = B $$ (g i, x i)" using pick_rw pick_UNIV by auto
        finally show "submatrix B (g ` {0..<n}) UNIV $$ (i, x i) = B $$ (g i, x i)" .
      qed
      thus "signof x * (\<Prod>i = 0..<n. submatrix B (g ` {0..<n}) UNIV $$ (i, x i))
          = signof x * (\<Prod>i = 0..<n. B $$ (g i, x i))" by simp
    qed
    finally show ?thesis .
  qed

  have "?rhs = (\<Sum>f\<in>Z_good_fun. \<Sum>\<pi>\<in>?Perm. weight f \<pi>)"
    unfolding Z_good_def sum.cartesian_product Z_good_fun_def by blast
  also have "... = (\<Sum>\<phi>\<in>{\<pi>. \<pi> permutes {0..<n}}. ?P (g \<circ> \<phi>))" unfolding Z_good_fun_def
    by (rule Z_good_fun_alt_sum[OF g])
  also have "... = (\<Sum>\<phi>\<in>{\<pi>. \<pi> permutes {0..<n}}. \<Sum>\<pi>\<in>{\<pi>. \<pi> permutes {0..<n}}.
    signof \<phi> * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i))) * signof (\<pi> \<circ> ?inv \<phi>)
    * (\<Prod>i = 0..<n. B $$ (g i, (\<pi> \<circ> ?inv \<phi>) i)))"
  proof (rule sum.cong, simp, rule sum.cong, simp)
    fix \<phi> \<pi> assume phi: "\<phi> \<in> ?Perm" and pi: "\<pi> \<in> ?Perm"
    show "weight (g \<circ> \<phi>) \<pi> = signof \<phi> * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i))) *
      signof (\<pi> \<circ> ?inv \<phi>) * (\<Prod>i = 0..<n. B $$ (g i, (\<pi> \<circ> ?inv \<phi>) i))"
    proof (rule step_weight)
      show "g \<circ> \<phi> \<in> F_inj" by (rule F_inj_composition_permutation[OF _ g], insert phi, auto)
      show "g \<in> F" using g unfolding F_def F_inj_def by simp
    qed (insert phi pi, auto)
  qed
  also have "... = (\<Sum>\<phi>\<in>{\<pi>. \<pi> permutes {0..<n}}. signof \<phi> * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i))) *
     (\<Sum>\<pi> | \<pi> permutes {0..<n}. signof (\<pi> \<circ> ?inv \<phi>) * (\<Prod>i = 0..<n. B $$ (g i, (\<pi> \<circ> ?inv \<phi>) i))))"
    by (metis (mono_tags, lifting) Groups.mult_ac(1) semiring_0_class.sum_distrib_left sum.cong)
  also have "... = (\<Sum>\<phi> \<in> ?Perm. signof \<phi> * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i))) *
    (\<Sum>\<pi> \<in> ?Perm. signof \<pi> * (\<Prod>i = 0..<n. B $$ (g i, \<pi> i))))" using detB_rw by auto
  also have "... = (\<Sum>\<phi> \<in> ?Perm. signof \<phi> * (\<Prod>i = 0..<n. A $$ (i, g (\<phi> i)))) *
    (\<Sum>\<pi> \<in> ?Perm. signof \<pi> * (\<Prod>i = 0..<n. B $$ (g i, \<pi> i)))"
    by (simp add: semiring_0_class.sum_distrib_right)
  also have "... = ?lhs" unfolding detA detB ..
  finally show ?thesis ..
qed


lemma gather_by_strictness:
"sum (\<lambda>g. sum (\<lambda>(f,\<pi>). weight f \<pi>) (Z_good g)) F_strict
  = sum (\<lambda>g. det (submatrix A UNIV (g`{0..<n})) * det (submatrix B (g`{0..<n}) UNIV)) F_strict"
proof (rule sum.cong)
  fix f assume f: "f \<in> F_strict"
  show "(\<Sum>(x, y)\<in>Z_good f. weight x y)
    = det (submatrix A UNIV (f ` {0..<n})) * det (submatrix B (f ` {0..<n}) UNIV)"
    by (rule one_step[symmetric], rule f)
qed (simp)

lemma finite_Z_strict[simp]: "finite Z_strict"
proof (unfold Z_strict_def, rule finite_cartesian_product)
  have finN: "finite {0..<n}" and finM: "finite {0..<m}" by auto
  let ?A="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) \<and> strict_mono_on f {0..<n}}"
  let ?B="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  have B: "{f. (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)} = ?B" by auto
  have "?A\<subseteq>?B" by auto
  moreover have "finite ?B" using B finite_bounded_functions[OF finM finN] by auto
  ultimately show "finite ?A" using rev_finite_subset by blast
  show "finite {\<pi>. \<pi> permutes {0..<n}}" using finite_permutations by blast
qed

lemma finite_Z_not_strict[simp]: "finite Z_not_strict"
proof (unfold Z_not_strict_def, rule finite_cartesian_product)
  have finN: "finite {0..<n}" and finM: "finite {0..<m}" by auto
  let ?A="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) \<and> \<not> strict_mono_on f {0..<n}}"
  let ?B="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  have B: "{f. (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)} = ?B" by auto
  have "?A\<subseteq>?B" by auto
  moreover have "finite ?B" using B finite_bounded_functions[OF finM finN] by auto
  ultimately show "finite ?A" using rev_finite_subset by blast
  show "finite {\<pi>. \<pi> permutes {0..<n}}" using finite_permutations by blast
qed

lemma finite_Znm[simp]: "finite (Z n m)"
proof (unfold Z_alt_def, rule finite_cartesian_product)
  have finN: "finite {0..<n}" and finM: "finite {0..<m}" by auto
  let ?A="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) }"
  let ?B="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  have B: "{f. (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)} = ?B" by auto
  have "?A\<subseteq>?B" by auto
  moreover have "finite ?B" using B finite_bounded_functions[OF finM finN] by auto
  ultimately show "finite ?A" using rev_finite_subset by blast
  show "finite {\<pi>. \<pi> permutes {0..<n}}" using finite_permutations by blast
qed

lemma finite_F_inj[simp]: "finite F_inj"
proof -
  have finN: "finite {0..<n}" and finM: "finite {0..<m}" by auto
  let ?A="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) \<and> inj_on f {0..<n}}"
  let ?B="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  have B: "{f. (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)} = ?B" by auto
  have "?A\<subseteq>?B" by auto
  moreover have "finite ?B" using B finite_bounded_functions[OF finM finN] by auto
  ultimately show "finite F_inj" unfolding F_inj_def using rev_finite_subset by blast
qed

lemma finite_F_strict[simp]: "finite F_strict"
proof -
 have finN: "finite {0..<n}" and finM: "finite {0..<m}" by auto
  let ?A="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i) \<and> strict_mono_on f {0..<n}}"
  let ?B="{f \<in> {0..<n} \<rightarrow> {0..<m}. (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  have B: "{f. (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)} = ?B" by auto
  have "?A\<subseteq>?B" by auto
  moreover have "finite ?B" using B finite_bounded_functions[OF finM finN] by auto
  ultimately show "finite F_strict" unfolding F_strict_def using rev_finite_subset by blast
qed

lemma nth_strict_mono:
  fixes f::"nat \<Rightarrow> nat"
  assumes  strictf: "strict_mono f" and i: "i<n"
shows "f i = (sorted_list_of_set (f`{0..<n})) ! i"
proof -
  let ?I = "f`{0..<n}"
  have "length (sorted_list_of_set (f ` {0..<n})) = card ?I"
    by (metis distinct_card finite_atLeastLessThan finite_imageI
        sorted_list_of_set(1) sorted_list_of_set(3))
  also have "... = n"
    by (simp add: card_image strict_mono_imp_inj_on strictf)
  finally have length_I: "length (sorted_list_of_set ?I) = n" .
  have card_eq: "card {a \<in> ?I. a < f i} = i"
    using i
  proof (induct i)
    case 0
    then show ?case
      by (auto simp add: strict_mono_less strictf)
  next
    case (Suc i)
    have i: "i < n" using Suc.prems by auto
    let ?J'="{a \<in> f ` {0..<n}. a < f i}"
    let ?J = "{a \<in> f ` {0..<n}. a < f (Suc i)}"
    have cardJ': "card ?J' = i" by (rule Suc.hyps[OF i])
    have J: "?J = insert (f i) ?J'"
    proof (auto)
      fix xa assume 1: "f xa \<noteq> f i" and 2: "f xa < f (Suc i)"
      show "f xa < f i"
        using 1 2 not_less_less_Suc_eq strict_mono_less strictf by fastforce
    next
      fix xa assume "f xa < f i" thus "f xa < f (Suc i)"
        using less_SucI strict_mono_less strictf by blast
    next
      show "f i \<in> f ` {0..<n}" using i by auto
      show "f i < f (Suc i)" using strictf strict_mono_less by auto
    qed
    have "card ?J = Suc (card ?J')" by (unfold J, rule card_insert_disjoint, auto)
    then show ?case using cardJ' by auto
  qed
  have "sorted_list_of_set ?I ! i = pick ?I i"
    by (rule sorted_list_of_set_eq_pick, simp add: \<open>card (f ` {0..<n}) = n\<close> i)
  also have "... =  pick ?I (card {a \<in> ?I. a < f i})" unfolding card_eq by simp
  also have "... = f i" by (rule pick_card_in_set, simp add: i)
  finally show ?thesis ..
qed

lemma nth_strict_mono_on:
  fixes f::"nat \<Rightarrow> nat"
  assumes  strictf: "strict_mono_on f {0..<n}" and i: "i<n"
shows "f i = (sorted_list_of_set (f`{0..<n})) ! i"
proof -
  let ?I = "f`{0..<n}"
  have "length (sorted_list_of_set (f ` {0..<n})) = card ?I"
    by (metis distinct_card finite_atLeastLessThan finite_imageI
        sorted_list_of_set(1) sorted_list_of_set(3))
  also have "... = n"
    by (metis (mono_tags, lifting) card_atLeastLessThan card_image diff_zero
        inj_on_def strict_mono_on_eqD strictf)
  finally have length_I: "length (sorted_list_of_set ?I) = n" .
  have card_eq: "card {a \<in> ?I. a < f i} = i"
    using i
  proof (induct i)
    case 0
    then show ?case
      by (auto, metis (no_types, lifting) atLeast0LessThan lessThan_iff less_Suc_eq
          not_less0 not_less_eq strict_mono_on_def strictf)
  next
    case (Suc i)
    have i: "i < n" using Suc.prems by auto
    let ?J'="{a \<in> f ` {0..<n}. a < f i}"
    let ?J = "{a \<in> f ` {0..<n}. a < f (Suc i)}"
    have cardJ': "card ?J' = i" by (rule Suc.hyps[OF i])
    have J: "?J = insert (f i) ?J'"
    proof (auto)
      fix xa assume 1: "f xa \<noteq> f i" and 2: "f xa < f (Suc i)" and 3: "xa < n"
      show "f xa < f i"
        by (metis (full_types) 1 2 3 antisym_conv3 atLeast0LessThan i lessThan_iff
            less_SucE order.asym strict_mono_onD strictf)
    next
      fix xa assume "f xa < f i" and "xa < n" thus "f xa < f (Suc i)"
        using less_SucI strictf
        by (metis (no_types, lifting) Suc.prems atLeast0LessThan
            lessI lessThan_iff less_trans strict_mono_onD)
    next
      show "f i \<in> f ` {0..<n}" using i by auto
      show "f i < f (Suc i)"
        using Suc.prems strict_mono_onD strictf by fastforce
    qed
    have "card ?J = Suc (card ?J')" by (unfold J, rule card_insert_disjoint, auto)
    then show ?case using cardJ' by auto
  qed
  have "sorted_list_of_set ?I ! i = pick ?I i"
    by (rule sorted_list_of_set_eq_pick, simp add: \<open>card (f ` {0..<n}) = n\<close> i)
  also have "... =  pick ?I (card {a \<in> ?I. a < f i})" unfolding card_eq by simp
  also have "... = f i" by (rule pick_card_in_set, simp add: i)
  finally show ?thesis ..
qed

lemma strict_fun_eq:
  assumes f: "f \<in> F_strict" and g: "g \<in> F_strict" and fg: "f`{0..<n} = g`{0..<n}"
  shows "f = g"
proof (unfold fun_eq_iff, auto)
  fix x
  show "f x = g x"
  proof (cases "x<n")
    case True
    have strictf: "strict_mono_on f {0..<n}" and strictg: "strict_mono_on g {0..<n}"
      using f g unfolding F_strict_def by auto
    have "f x = (sorted_list_of_set (f`{0..<n})) ! x" by (rule nth_strict_mono_on[OF strictf True])
    also have "... = (sorted_list_of_set (g`{0..<n})) ! x" unfolding fg by simp
    also have "... = g x" by (rule nth_strict_mono_on[symmetric, OF strictg True])
    finally show ?thesis .
  next
    case False
    then show ?thesis using f g unfolding F_strict_def by auto
  qed
qed


lemma strict_from_inj_preserves_F:
  assumes f: "f \<in> F_inj"
  shows "strict_from_inj n f \<in> F"
proof -
  {
    fix x assume x: "x < n"
    have inj_on: "inj_on f {0..<n}" using f unfolding F_inj_def by auto
    have "{a. a < m \<and> a \<in> f ` {0..<n}} = f`{0..<n}" using f unfolding F_inj_def by auto
    hence card_eq: "card {a. a < m \<and> a \<in> f ` {0..<n}} = n"
      by (simp add: card_image inj_on)
    let ?I = "f`{0..<n}"
    have "length (sorted_list_of_set (f ` {0..<n})) = card ?I"
      by (metis distinct_card finite_atLeastLessThan finite_imageI
          sorted_list_of_set(1) sorted_list_of_set(3))
    also have "... = n"
      by (simp add: card_image strict_mono_imp_inj_on inj_on)
    finally have length_I: "length (sorted_list_of_set ?I) = n" .
    have "sorted_list_of_set (f ` {0..<n}) ! x = pick (f ` {0..<n}) x"
      by (rule sorted_list_of_set_eq_pick, unfold length_I, auto simp add: x)
    also have "... < m" by (rule pick_le, unfold card_eq, rule x)
    finally have "sorted_list_of_set (f ` {0..<n}) ! x < m" .
  }
  thus ?thesis unfolding strict_from_inj_def F_def by auto
qed

lemma strict_from_inj_F_strict: "strict_from_inj n xa \<in> F_strict"
  if xa: "xa \<in> F_inj" for xa
proof -
  have "strict_mono_on (strict_from_inj n xa) {0..<n}"
    by (rule strict_strict_from_inj, insert xa, simp add: F_inj_def)
  thus ?thesis using strict_from_inj_preserves_F[OF xa] unfolding F_def F_strict_def by auto
qed

lemma strict_from_inj_image:
  assumes f: "f\<in> F_inj"
  shows "strict_from_inj n f ` {0..<n} = f`{0..<n}"
proof (auto)
  let ?I = "f ` {0..<n}"
  fix xa assume xa: "xa < n"
  have inj_on: "inj_on f {0..<n}" using f unfolding F_inj_def by auto
    have "{a. a < m \<and> a \<in> f ` {0..<n}} = f`{0..<n}" using f unfolding F_inj_def by auto
    hence card_eq: "card {a. a < m \<and> a \<in> f ` {0..<n}} = n"
      by (simp add: card_image inj_on)
    let ?I = "f`{0..<n}"
    have "length (sorted_list_of_set (f ` {0..<n})) = card ?I"
      by (metis distinct_card finite_atLeastLessThan finite_imageI
          sorted_list_of_set(1) sorted_list_of_set(3))
    also have "... = n"
      by (simp add: card_image strict_mono_imp_inj_on inj_on)
    finally have length_I: "length (sorted_list_of_set ?I) = n" .
  have "strict_from_inj n f xa = sorted_list_of_set ?I ! xa"
    using xa unfolding strict_from_inj_def by auto
  also have "... = pick ?I xa"
    by (rule sorted_list_of_set_eq_pick, unfold length_I, auto simp add: xa)
  also have "... \<in> f ` {0..<n}" by (rule pick_in_set_le, simp add: \<open>card (f ` {0..<n}) = n\<close> xa)
  finally show "strict_from_inj n f xa \<in> f ` {0..<n}" .
  obtain i where "sorted_list_of_set (f`{0..<n}) ! i = f xa" and "i<n"
    by (metis atLeast0LessThan finite_atLeastLessThan finite_imageI imageI
        in_set_conv_nth length_I lessThan_iff sorted_list_of_set(1) xa)
  thus "f xa \<in> strict_from_inj n f ` {0..<n}"
    by (metis atLeast0LessThan imageI lessThan_iff strict_from_inj_def)
qed


lemma Z_good_alt:
  assumes g: "g \<in> F_strict"
  shows "Z_good g = {x \<in> F_inj. strict_from_inj n x = g} \<times> {\<pi>. \<pi> permutes {0..<n}}"
proof -
  define Z_good_fun where "Z_good_fun = {f. f \<in> {0..<n} \<rightarrow> {0..<m} \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)
  \<and> inj_on f {0..<n} \<and> (f`{0..<n} = g`{0..<n})}"
  have "Z_good_fun = {x \<in> F_inj. strict_from_inj n x = g}"
  proof (auto)
    fix f assume f: "f \<in> Z_good_fun" thus f_inj: "f \<in> F_inj" unfolding F_inj_def Z_good_fun_def by auto
    show "strict_from_inj n f = g"
    proof (rule strict_fun_eq[OF _ g])
      show "strict_from_inj n f ` {0..<n} = g ` {0..<n}"
        using f_inj f strict_from_inj_image
        unfolding Z_good_fun_def F_inj_def by auto
      show "strict_from_inj n f \<in> F_strict"
        using F_strict_def f_inj strict_from_inj_F_strict by blast
    qed
  next
    fix f assume f_inj: "f \<in> F_inj" and g_strict_f: "g = strict_from_inj n f"
    have "f xa \<in> g ` {0..<n}" if "xa < n" for xa
      using f_inj g_strict_f strict_from_inj_image that by auto
    moreover have "g xa \<in> f ` {0..<n}" if "xa < n" for xa
      by (metis f_inj g_strict_f imageI lessThan_atLeast0 lessThan_iff strict_from_inj_image that)
    ultimately show "f \<in> Z_good_fun"
      using f_inj g_strict_f unfolding Z_good_fun_def F_inj_def
      by auto
  qed
  thus ?thesis unfolding Z_good_fun_def Z_good_def by simp
qed


lemma weight_0: "(\<Sum>(f, \<pi>) \<in> Z_not_inj. weight f \<pi>) = 0"
proof -
  let ?F="{f. (\<forall>i\<in>{0..<n}. f i \<in> {0..<m}) \<and> (\<forall>i. i \<notin> {0..<n} \<longrightarrow> f i = i)}"
  let ?Perm = "{\<pi>. \<pi> permutes {0..<n}}"
  have "(\<Sum>(f, \<pi>)\<in>Z_not_inj. weight f \<pi>)
    = (\<Sum>f \<in> F_not_inj. (\<Prod>i = 0..<n. A $$ (i, f i)) * det (mat\<^sub>r n n (\<lambda>i. row B (f i))))"
  proof -
    have dim_row_rw: "dim_row (mat\<^sub>r n n (\<lambda>i. col A (f i))) = n" for f by auto
    have dim_row_rw2: "dim_row (mat\<^sub>r n n (\<lambda>i. Matrix.row B (f i))) = n" for f by auto
    have prod_rw: "(\<Prod>i = 0..<n. B $$ (f i, \<pi> i)) =  (\<Prod>i = 0..<n. row B (f i) $v \<pi> i)"
      if f: "f \<in> F_not_inj" and pi: "\<pi> \<in> ?Perm" for f \<pi>
    proof (rule prod.cong, rule refl)
      fix x assume x: "x \<in> {0..<n}"
      have "f x < dim_row B" using f B x unfolding F_not_inj_def by fastforce
      moreover have "\<pi> x < dim_col B" using x pi B by auto
      ultimately show "B $$ (f x, \<pi> x) = Matrix.row B (f x) $v \<pi> x" by (rule index_row[symmetric])
    qed
    have sum_rw: "(\<Sum>\<pi> | \<pi> permutes {0..<n}. signof \<pi> * (\<Prod>i = 0..<n. B $$ (f i, \<pi> i)))
      = det (mat\<^sub>r n n (\<lambda>i. row B (f i)))" if f: "f \<in> F_not_inj" for f
      unfolding Determinant.det_def using dim_row_rw2 prod_rw f by auto
    have "(\<Sum>(f, \<pi>)\<in>Z_not_inj. weight f \<pi>) = (\<Sum>f\<in>F_not_inj.\<Sum>\<pi> \<in> ?Perm. weight f \<pi>)"
      unfolding Z_not_inj_def unfolding sum.cartesian_product
      unfolding F_not_inj_def by simp
    also have "... = (\<Sum>f\<in>F_not_inj. \<Sum>\<pi> | \<pi> permutes {0..<n}. signof \<pi>
      * (\<Prod>i = 0..<n. A $$ (i, f i) * B $$ (f i, \<pi> i)))"
      unfolding weight_def by simp
    also have "... = (\<Sum>f\<in>F_not_inj. (\<Prod>i = 0..<n. A $$ (i, f i))
      * (\<Sum>\<pi> | \<pi> permutes {0..<n}. signof \<pi> * (\<Prod>i = 0..<n. B $$ (f i, \<pi> i))))"
      by (rule sum.cong, rule refl, auto)
         (metis (no_types, lifting) mult.left_commute mult_hom.hom_sum sum.cong)
    also have "... = (\<Sum>f \<in> F_not_inj. (\<Prod>i = 0..<n. A $$ (i, f i))
      * det (mat\<^sub>r n n (\<lambda>i. row B (f i))))" using sum_rw by auto
    finally show ?thesis by auto
  qed
  also have "... = 0"
    by (rule sum.neutral, insert det_not_inj_on[of _ n B], auto simp add: F_not_inj_def)
  finally show ?thesis .
qed

subsection \<open>Final theorem\<close>

lemma Cauchy_Binet1:
  shows "det (A*B) =
  sum (\<lambda>f. det (submatrix A UNIV (f`{0..<n})) * det (submatrix B (f`{0..<n}) UNIV)) F_strict"
(is "?lhs = ?rhs")
proof -
  have sum0: "(\<Sum>(f, \<pi>) \<in> Z_not_inj. weight f \<pi>) = 0" by (rule weight_0)
  let ?f = "strict_from_inj n"
  have sum_rw: "sum g F_inj = (\<Sum>y \<in> F_strict. sum g {x \<in> F_inj. ?f x = y})" for g
    by (rule sum.group[symmetric], insert strict_from_inj_F_strict, auto)
  have Z_Union: "Z_inj \<union> Z_not_inj = Z n m"
    unfolding Z_def Z_not_inj_def Z_inj_def by auto
  have Z_Inter: "Z_inj \<inter> Z_not_inj = {}"
    unfolding Z_def Z_not_inj_def Z_inj_def by auto
  have "det (A*B) = (\<Sum>(f, \<pi>)\<in>Z n m. weight f \<pi>)"
    using detAB_Znm[OF A B] unfolding weight_def by auto
  also have "... = (\<Sum>(f, \<pi>)\<in>Z_inj. weight f \<pi>) + (\<Sum>(f, \<pi>)\<in>Z_not_inj. weight f \<pi>)"
    by (metis Z_Inter Z_Union finite_Un finite_Znm sum.union_disjoint)
  also have "... = (\<Sum>(f, \<pi>)\<in>Z_inj. weight f \<pi>)" using sum0 by force
  also have "... = (\<Sum>f \<in> F_inj. \<Sum>\<pi>\<in>{\<pi>. \<pi> permutes {0..<n}}. weight f \<pi>)"
    unfolding Z_inj_def unfolding F_inj_def sum.cartesian_product ..
  also have "... =  (\<Sum>y\<in>F_strict. \<Sum>f\<in>{x \<in> F_inj. strict_from_inj n x = y}.
    sum (weight f) {\<pi>. \<pi> permutes {0..<n}})" unfolding sum_rw ..
  also have "... =  (\<Sum>y\<in>F_strict. \<Sum>(f,\<pi>)\<in>({x \<in> F_inj. strict_from_inj n x = y}
  \<times> {\<pi>. \<pi> permutes {0..<n}}). weight f \<pi>)"
    unfolding F_inj_def sum.cartesian_product ..
  also have "... = sum (\<lambda>g. sum (\<lambda>(f,\<pi>). weight f \<pi>) (Z_good g)) F_strict"
    using Z_good_alt by auto
  also have "... = ?rhs" unfolding gather_by_strictness by simp
  finally show ?thesis .
qed


lemma Cauchy_Binet:
  "det (A*B) = (\<Sum>I\<in>{I. I\<subseteq>{0..<m} \<and> card I=n}. det (submatrix A UNIV I) * det (submatrix B I UNIV))"
proof -
  let ?f="(\<lambda>I. (\<lambda>i. if i<n then sorted_list_of_set I ! i else i))"
  let ?setI = "{I. I \<subseteq> {0..<m} \<and> card I = n}"
  have inj_on: "inj_on ?f ?setI"
  proof (rule inj_onI)
    fix I J assume I: "I \<in> ?setI" and J: "J \<in> ?setI" and fI_fJ: "?f I = ?f J"
    have "x \<in> J" if x: "x \<in> I" for x
      by (metis (mono_tags) fI_fJ I J distinct_card in_set_conv_nth mem_Collect_eq
          sorted_list_of_set(1) sorted_list_of_set(3) subset_eq_atLeast0_lessThan_finite x)
    moreover have "x \<in> I" if x: "x \<in> J" for x
      by (metis (mono_tags) fI_fJ I J distinct_card in_set_conv_nth mem_Collect_eq
          sorted_list_of_set(1) sorted_list_of_set(3) subset_eq_atLeast0_lessThan_finite x)
    ultimately show "I = J" by auto
  qed
  have rw: "?f I ` {0..<n} = I" if I: "I \<in> ?setI" for I
  proof -
    have "sorted_list_of_set I ! xa \<in> I" if "xa < n" for xa
      by (metis (mono_tags, lifting) I distinct_card distinct_sorted_list_of_set mem_Collect_eq
          nth_mem set_sorted_list_of_set subset_eq_atLeast0_lessThan_finite that)
    moreover have "\<exists>xa\<in>{0..<n}. x = sorted_list_of_set I ! xa" if x: "x\<in>I" for x
      by (metis (full_types) x I atLeast0LessThan distinct_card in_set_conv_nth mem_Collect_eq
         lessThan_iff sorted_list_of_set(1) sorted_list_of_set(3) subset_eq_atLeast0_lessThan_finite)
    ultimately show ?thesis unfolding image_def by auto
  qed
  have f_setI: "?f` ?setI = F_strict"
  proof -
    have "sorted_list_of_set I ! xa < m" if I: "I \<subseteq> {0..<m}" and "n = card I" and "xa < card I"
        for I xa
      by (metis I \<open>xa < card I\<close> atLeast0LessThan distinct_card finite_atLeastLessThan lessThan_iff
          pick_in_set_le rev_finite_subset sorted_list_of_set(1)
          sorted_list_of_set(3) sorted_list_of_set_eq_pick subsetCE)
    moreover have "strict_mono_on (\<lambda>i. if i < card I then sorted_list_of_set I ! i else i) {0..<card I}"
      if "I \<subseteq> {0..<m}" and "n = card I" for I
      by (smt \<open>I \<subseteq> {0..<m}\<close> atLeastLessThan_iff distinct_card finite_atLeastLessThan pick_mono_le
          rev_finite_subset sorted_list_of_set(1) sorted_list_of_set(3)
          sorted_list_of_set_eq_pick strict_mono_on_def)
    moreover have "x \<in> ?f ` {I. I \<subseteq> {0..<m} \<and> card I = n}"
      if x1: "x \<in> {0..<n} \<rightarrow> {0..<m}" and x2: "\<forall>i. \<not> i < n \<longrightarrow> x i = i"
      and s: "strict_mono_on x {0..<n}" for x
    proof -
      have inj_x: "inj_on x {0..<n}"
        using s strict_mono_on_imp_inj_on by blast
      hence card_xn: "card (x ` {0..<n}) = n" by (simp add: card_image)
      have x_eq: "x = (\<lambda>i. if i < n then sorted_list_of_set (x ` {0..<n}) ! i else i)"
        unfolding fun_eq_iff
        using nth_strict_mono_on s using x2 by auto
      show ?thesis
        unfolding image_def by (auto, rule exI[of _"x`{0..<n}"], insert card_xn x1 x_eq, auto)
    qed
    ultimately show ?thesis unfolding F_strict_def by auto
  qed
  let ?g = "(\<lambda>f. det (submatrix A UNIV (f`{0..<n})) * det(submatrix B (f`{0..<n}) UNIV))"
  have "det (A*B) = sum ((\<lambda>f. det (submatrix A UNIV (f ` {0..<n}))
    * det (submatrix B (f ` {0..<n}) UNIV)) \<circ> ?f) {I. I \<subseteq> {0..<m} \<and> card I = n}"
    unfolding Cauchy_Binet1 f_setI[symmetric] by (rule sum.reindex[OF inj_on])
  also have "... = (\<Sum>I\<in>{I. I\<subseteq>{0..<m} \<and> card I=n}.det(submatrix A UNIV I)*det(submatrix B I UNIV))"
    by (rule sum.cong, insert rw, auto)
  finally show ?thesis .
qed
end

end
