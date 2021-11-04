(*
    Author:      Jose Divasón
    Email:       jose.divason@unirioja.es
*)

section \<open>Uniqueness of the Smith normal form\<close>

theory SNF_Uniqueness
imports
  Cauchy_Binet
  Smith_Normal_Form_JNF
  Admits_SNF_From_Diagonal_Iff_Bezout_Ring
begin

lemma dvd_associated1:
  fixes a::"'a::comm_ring_1"
  assumes "\<exists>u. u dvd 1 \<and> a = u*b"
  shows "a dvd b \<and> b dvd a"
  using assms by auto


text \<open>This is a key lemma. It demands the type class to be an integral domain. This means that
the uniqueness result will be obtained for GCD domains, instead of rings.\<close>
lemma dvd_associated2:
  fixes a::"'a::idom"
  assumes ab: "a dvd b" and ba: "b dvd a" and a: "a\<noteq>0"
  shows "\<exists>u. u dvd 1 \<and> a = u*b"
proof -
  obtain k where a_kb: "a = k*b" using ab unfolding dvd_def
    by (metis Groups.mult_ac(2) ba dvdE)
  obtain q where b_qa: "b = q*a" using ba unfolding dvd_def
    by (metis Groups.mult_ac(2) ab dvdE)
  have 1: "a = k*q*a" using a_kb b_qa by auto
  hence "k*q = 1" using a by simp
  thus ?thesis using 1 by (metis a_kb dvd_triv_left)
qed

corollary dvd_associated:
  fixes a::"'a::idom"
  assumes "a\<noteq>0"
  shows "(a dvd b \<and> b dvd a) = (\<exists>u. u dvd 1 \<and> a = u*b)"
  using assms dvd_associated1 dvd_associated2 by metis


lemma exists_inj_ge_index:
  assumes S: "S \<subseteq> {0..<n}" and Sk: "card S = k"
  shows "\<exists>f. inj_on f {0..<k} \<and> f`{0..<k} = S \<and> (\<forall>i\<in>{0..<k}. i \<le> f i)"
proof -
  have "\<exists>h. bij_betw h {0..<k} S"
    using S Sk ex_bij_betw_nat_finite subset_eq_atLeast0_lessThan_finite by blast
  from this obtain g where inj_on_g: "inj_on g {0..<k}" and gk_S: "g`{0..<k} = S"
    unfolding bij_betw_def by blast
  let ?f = "strict_from_inj k g"
  have "strict_mono_on ?f {0..<k}" by (rule strict_strict_from_inj[OF inj_on_g])
  hence 1: "inj_on ?f {0..<k}" using strict_mono_on_imp_inj_on by blast
  have 2: "?f`{0..<k} = S" by (simp add: strict_from_inj_image' inj_on_g gk_S)
  have 3: "\<forall>i\<in>{0..<k}. i \<le> ?f i"
  proof
    fix i assume i: "i \<in> {0..<k}"
    let ?xs = "sorted_list_of_set (g`{0..<k})"
    have "strict_from_inj k g i = ?xs ! i" unfolding strict_from_inj_def using i by auto
    moreover have "i \<le> ?xs ! i"
    proof (rule sorted_wrt_less_idx, rule sorted_distinct_imp_sorted_wrt)
      show "sorted ?xs"
        using sorted_sorted_list_of_set by blast
      show "distinct ?xs" using distinct_sorted_list_of_set by blast
      show "i < length ?xs"
        by (metis S Sk atLeast0LessThan distinct_card distinct_sorted_list_of_set gk_S i
            lessThan_iff set_sorted_list_of_set subset_eq_atLeast0_lessThan_finite)
    qed
    ultimately show "i \<le> ?f i" by auto
  qed
  show ?thesis using 1 2 3 by auto
qed


subsection \<open>More specific results about submatrices\<close>


lemma diagonal_imp_submatrix0:
  assumes dA: "diagonal_mat A" and A_carrier: "A\<in> carrier_mat n m"
  and Ik: "card I = k" and Jk: "card J = k"
  and r: "\<forall>row_index \<in> I. row_index < n" (*I \<subseteq> {0..<n}*)
  and c: "\<forall>col_index \<in> J. col_index < m"
  and a: "a<k" and b: "b<k"
shows "submatrix A I J $$ (a, b) = 0 \<or> submatrix A I J $$ (a,b) = A $$(pick I a, pick I a)"
proof (cases "submatrix A I J $$ (a, b) = 0")
  case True
  then show ?thesis by auto
next
  case False note not0 = False
  have aux: "submatrix A I J $$ (a, b) = A $$(pick I a, pick J b)"
  proof (rule submatrix_index)
    have "card {i. i < dim_row A \<and> i \<in> I} = k"
      by (smt A_carrier Ik carrier_matD(1) equalityI mem_Collect_eq r subsetI)
    moreover have "card {i. i < dim_col A \<and> i \<in> J} = k"
      by (metis (no_types, lifting) A_carrier Jk c carrier_matD(2) carrier_mat_def
         equalityI mem_Collect_eq subsetI)
    ultimately show " a < card {i. i < dim_row A \<and> i \<in> I}"
      and "b < card {i. i < dim_col A \<and> i \<in> J}" using a b by auto
  qed
  thus ?thesis
  proof (cases "pick I a = pick J b")
    case True
    then show ?thesis using aux by auto
  next
    case False
    then show ?thesis
      by (metis aux A_carrier Ik Jk a b c carrier_matD dA diagonal_mat_def pick_in_set_le r)
  qed
qed



lemma diagonal_imp_submatrix_element_not0:
  assumes dA: "diagonal_mat A"
  and A_carrier: "A \<in> carrier_mat n m"
  and Ik: "card I = k" and Jk: "card J = k"
  and I: "I \<subseteq> {0..<n}"
  and J: "J \<subseteq> {0..<m}"
  and b: "b < k"
  and ex_not0: "\<exists>i. i<k \<and> submatrix A I J $$ (i, b) \<noteq> 0"
shows "\<exists>!i. i<k \<and> submatrix A I J $$ (i, b) \<noteq> 0"
proof -
  have I_eq: "I = {i. i < dim_row A \<and> i \<in> I}" using I A_carrier unfolding carrier_mat_def by auto
  have J_eq: "J = {i. i < dim_col A \<and> i \<in> J}" using J A_carrier unfolding carrier_mat_def by auto
  obtain a where sub_ab: "submatrix A I J $$ (a, b) \<noteq> 0" and ak: "a < k" using ex_not0 by auto
  moreover have "i = a" if sub_ib: "submatrix A I J $$ (i, b) \<noteq> 0" and ik: "i < k" for i
  proof -
    have 1: "pick I i < dim_row A"
      using I_eq Ik ik pick_in_set_le by auto
    have 2: "pick J b < dim_col A"
      using J_eq Jk b pick_le by auto
    have 3: "pick I a < dim_row A"
      using I_eq Ik calculation(2) pick_le by auto
    have "submatrix A I J $$ (i, b) = A $$ (pick I i, pick J b)"
      by (rule submatrix_index, insert I_eq Ik ik J_eq Jk b, auto)
    hence pick_Ii_Jb: "pick I i = pick J b" using dA sub_ib 1 2 unfolding diagonal_mat_def by auto
    have "submatrix A I J $$ (a, b) = A $$ (pick I a, pick J b)"
      by (rule submatrix_index, insert I_eq Ik ak J_eq Jk b, auto)
    hence pick_Ia_Jb: "pick I a = pick J b" using dA sub_ab 3 2 unfolding diagonal_mat_def by auto
    have pick_Ia_Ii: "pick I a = pick I i" using pick_Ii_Jb pick_Ia_Jb by simp
    thus ?thesis by (metis Ik ak ik nat_neq_iff pick_mono_le)
  qed
  ultimately show ?thesis by auto
qed


lemma submatrix_index_exists:
  assumes A_carrier: "A\<in> carrier_mat n m"
  and Ik: "card I = k" and Jk: "card J = k"
  and a: "a \<in> I" and b: "b \<in> J" and k: "k > 0"
  and I: "I \<subseteq> {0..<n}" and J: "J \<subseteq> {0..<m}"
shows "\<exists>a' b'. a' < k \<and> b' < k \<and> submatrix A I J $$ (a',b') = A $$ (a,b)
        \<and> a = pick I a' \<and> b = pick J b'"
proof -
  let ?xs = "sorted_list_of_set I"
  let ?ys = "sorted_list_of_set J"
  have finI: "finite I" and finJ: "finite J" using k Ik Jk card_ge_0_finite by metis+
  have set_xs: "set ?xs = I" by (rule set_sorted_list_of_set[OF finI])
  have set_ys: "set ?ys = J" by (rule set_sorted_list_of_set[OF finJ])
  have a_in_xs: "a \<in> set ?xs" and b_in_ys: "b \<in> set ?ys" using set_xs a set_ys b by auto
  have length_xs: "length ?xs = k" by (metis Ik distinct_card set_xs sorted_list_of_set(3))
  have length_ys: "length ?ys = k" by (metis Jk distinct_card set_ys sorted_list_of_set(3))
  obtain a' where a': "?xs ! a' = a" and a'_length: "a' < length ?xs"
    by (meson a_in_xs in_set_conv_nth)
  obtain b' where b': "?ys ! b' = b" and b'_length: "b' < length ?ys"
    by (meson b_in_ys in_set_conv_nth)
  have pick_a: "a = pick I a'" using a' a'_length finI sorted_list_of_set_eq_pick by auto
  have pick_b: "b = pick J b'" using b' b'_length finJ sorted_list_of_set_eq_pick by auto
  have I_rw: "I = {i. i < dim_row A \<and> i \<in> I}" and J_rw: "J = {i. i < dim_col A \<and> i \<in> J}"
    using I A_carrier J by auto
  have a'k: "a' < k" using a'_length length_xs by auto
  moreover have b'k: "b'<k" using b'_length length_ys by auto
  moreover have sub_eq: "submatrix A I J $$ (a', b') = A $$ (a, b)"
    unfolding pick_a pick_b
    by (rule submatrix_index, insert J_rw I_rw Ik Jk a'_length length_xs b'_length length_ys, auto)
  ultimately show ?thesis using pick_a pick_b by auto
qed


lemma mat_delete_submatrix_insert:
  assumes A_carrier: "A \<in> carrier_mat n m"
  and Ik: "card I = k" and Jk: "card J = k"
  and I: "I \<subseteq> {0..<n}" and J: "J \<subseteq> {0..<m}"
  and a: "a < n" and b: "b < m"
  and k: "k < min n m"
  and a_notin_I: "a \<notin> I" and b_notin_J: "b \<notin> J"
  and a'k: "a' < Suc k" and b'k:  "b' < Suc k"
  and a_def: "pick (insert a I) a' = a"
  and b_def: "pick (insert b J) b' = b"
shows "mat_delete (submatrix A (insert a I) (insert b J)) a' b' = submatrix A I J" (is "?lhs = ?rhs")
proof (rule eq_matI)
  have I_eq: "I = {i. i < dim_row A \<and> i \<in> I}"
    using I A_carrier unfolding carrier_mat_def by auto
  have J_eq: "J = {i. i < dim_col A \<and> i \<in> J}"
    using J A_carrier unfolding carrier_mat_def by auto
  have insert_I_eq: "insert a I = {i. i < dim_row A \<and> i \<in> insert a I}"
    using I A_carrier a k unfolding carrier_mat_def by auto
  have card_Suc_k: "card {i. i < dim_row A \<and> i \<in> insert a I} = Suc k"
    using insert_I_eq Ik a_notin_I
    by (metis I card_insert_disjoint finite_atLeastLessThan finite_subset)
  have insert_J_eq: "insert b J = {i. i < dim_col A \<and> i \<in> insert b J}"
    using J A_carrier b k unfolding carrier_mat_def by auto
  have card_Suc_k': "card {i. i < dim_col A \<and> i \<in> insert b J} = Suc k"
    using insert_J_eq Jk b_notin_J
    by (metis J card_insert_disjoint finite_atLeastLessThan finite_subset)
  show "dim_row ?lhs = dim_row ?rhs"
    unfolding mat_delete_dim unfolding dim_submatrix using card_Suc_k I_eq Ik by auto
  show "dim_col ?lhs = dim_col ?rhs"
    unfolding mat_delete_dim unfolding dim_submatrix using card_Suc_k' J_eq Jk by auto
  fix i j assume i: "i < dim_row (submatrix A I J)"
    and j: "j < dim_col (submatrix A I J)"
  have ik: "i < k" by (metis I_eq Ik dim_submatrix(1) i)
  have jk: "j < k" by (metis J_eq Jk dim_submatrix(2) j)
  show "?lhs $$ (i, j) = ?rhs $$ (i, j)"
  proof -
    have index_eq1: "pick (insert a I) (insert_index a' i) = pick I i"
      by (rule pick_insert_index[OF Ik a_notin_I ik a_def], simp add: Ik a'k)
    have index_eq2: "pick (insert b J) (insert_index b' j) = pick J j"
      by (rule pick_insert_index[OF Jk b_notin_J jk b_def], simp add: Jk b'k)
    have "?lhs $$ (i,j)
        = (submatrix A (insert a I) (insert b J)) $$ (insert_index a' i, insert_index b' j)"
    proof (rule mat_delete_index[symmetric, OF _ a'k b'k ik jk])
      show "submatrix A (insert a I) (insert b J) \<in> carrier_mat (Suc k) (Suc k)"
        by (metis card_Suc_k card_Suc_k' carrier_matI dim_submatrix(1) dim_submatrix(2))
    qed
    also have "... = A $$ (pick (insert a I) (insert_index a' i), pick (insert b J) (insert_index b' j))"
    proof (rule submatrix_index)
      show "insert_index a' i < card {i. i < dim_row A \<and> i \<in> insert a I}"
        using card_Suc_k ik insert_index_def by auto
      show "insert_index b' j < card {j. j < dim_col A \<and> j \<in> insert b J}"
        using card_Suc_k' insert_index_def jk by auto
    qed
    also have "... = A $$ (pick I i, pick J j)" unfolding index_eq1 index_eq2 by auto
    also have "... = submatrix A I J $$ (i,j)"
      by (rule submatrix_index[symmetric], insert ik I_eq Ik Jk J_eq jk, auto)
    finally show ?thesis .
  qed
qed



subsection \<open>On the minors of a diagonal matrix\<close>

lemma det_minors_diagonal:
  assumes dA: "diagonal_mat A" and A_carrier: "A \<in> carrier_mat n m"
    and Ik: "card I = k" and Jk: "card J = k"
    and r: "I \<subseteq> {0..<n}"
    and c: "J \<subseteq> {0..<m}" and k: "k>0"
  shows "det (submatrix A I J) = 0
  \<or> (\<exists>xs. (det (submatrix A I J) = prod_list xs \<or> det (submatrix A I J) = - prod_list xs)
  \<and> set xs \<subseteq> {A$$(i,i)|i. i<min n m \<and> A$$(i,i)\<noteq> 0} \<and> length xs = k)"
  using Ik Jk r c k
proof (induct k arbitrary: I J)
  case 0
  then show ?case by auto
next
  case (Suc k)
  note cardI = Suc.prems(1)
  note cardJ = Suc.prems(2)
  note I = Suc.prems(3)
  note J = Suc.prems(4)
  have *: "{i. i < dim_row A \<and> i \<in> I} = I" using I Ik A_carrier carrier_mat_def by auto
  have **: "{j. j < dim_col A \<and> j \<in> J} = J" using J Jk A_carrier carrier_mat_def by auto
  show ?case
  proof (cases "k = 0")
    case True note k0 = True
    from this obtain a where aI: "I = {a}" using True cardI card_1_singletonE by auto
    from this obtain b where bJ: "J = {b}" using True cardJ card_1_singletonE by auto
    have an: "a<n" using aI I by auto
    have bm: "b<m" using bJ J by auto
    have sub_carrier: "submatrix A {a} {b} \<in> carrier_mat 1 1"
      unfolding carrier_mat_def submatrix_def
      using * ** aI bJ by auto
    have 1: "det (submatrix A {a} {b}) = (submatrix A {a} {b}) $$ (0,0)"
      by (rule det_singleton[OF sub_carrier])
    have 2: "... = A $$ (a,b)"
      by (rule submatrix_singleton_index[OF A_carrier an bm])
    show ?thesis
    proof (cases "A $$ (a,b) \<noteq> 0")
      let ?xs = "[submatrix A {a} {b} $$ (0,0)]"
      case True
      hence "a = b" using dA A_carrier an bm unfolding diagonal_mat_def carrier_mat_def by auto
      hence "set ?xs \<subseteq> {A $$ (i, i) |i. i < min n m \<and> A $$ (i, i) \<noteq> 0}"
        using 2 True an bm by auto
      moreover have "det (submatrix A {a} {b}) = prod_list ?xs" using 1 by auto
      moreover have "length ?xs = Suc k" using k0 by auto
      ultimately show ?thesis using an bm unfolding aI bJ by blast
    next
      case False
      then show ?thesis using 1 2 aI bJ by auto
    qed
  next
    case False
    hence k0: "0 < k" by simp
    have k: "k < min n m"
      by (metis I J cardI cardJ le_imp_less_Suc less_Suc_eq_le min.commute
          min_def not_less subset_eq_atLeast0_lessThan_card)
    have subIJ_carrier: "(submatrix A I J) \<in> carrier_mat (Suc k) (Suc k)"
      unfolding carrier_mat_def using * ** cardI cardJ
      unfolding submatrix_def by auto
    obtain b' where b'k: "b' < Suc k" by auto
    let ?f="\<lambda>i. submatrix A I J $$ (i, b') * cofactor (submatrix A I J) i b'"
    have det_rw: "det (submatrix A I J)
        = (\<Sum>i<Suc k. submatrix A I J $$ (i, b') * cofactor (submatrix A I J) i b')"
      by (rule laplace_expansion_column[OF subIJ_carrier b'k])
    show ?thesis
    proof (cases "\<exists>a'<Suc k. submatrix A I J $$ (a',b') \<noteq> 0")
      case True
      obtain a' where sub_IJ_0: "submatrix A I J $$ (a',b') \<noteq> 0"
        and a'k: "a' < Suc k"
        and unique: "\<forall>j. j<Suc k \<and> submatrix A I J $$ (j,b') \<noteq> 0 \<longrightarrow> j = a'"
        using diagonal_imp_submatrix_element_not0[OF dA A_carrier cardI cardJ I J b'k True] by auto
      have "submatrix A I J $$ (a', b') = A $$ (pick I a', pick J b')"
        by (rule submatrix_index, auto simp add: "*" a'k cardI "**" b'k cardJ)
      from this obtain a b where an: "a < n" and bm:  "b < m"
        and sub_index: "submatrix A I J $$ (a', b') = A $$ (a, b)"
        and pick_a: "pick I a' = a" and pick_b: "pick J b' = b"
        using * ** A_carrier a'k b'k cardI cardJ pick_le by fastforce
      obtain I' where aI': "I = insert a I'" and a_notin: "a \<notin> I'"
        by (metis Set.set_insert a'k cardI pick_a pick_in_set_le)
      obtain J' where bJ': "J = insert b J'" and b_notin: "b \<notin> J'"
        by (metis Set.set_insert b'k cardJ pick_b pick_in_set_le)
      have Suc_k0: "0 < Suc k" by simp
      have aI: "a \<in> I" using aI' by auto
      have bJ: "b \<in> J" using bJ' by auto
      have cardI':  "card I' = k"
        by (metis aI' a_notin cardI card.infinite card_insert_disjoint
            finite_insert nat.inject nat.simps(3))
      have cardJ':  "card J' = k"
        by (metis bJ' b_notin cardJ card.infinite card_insert_disjoint
            finite_insert nat.inject nat.simps(3))
      have I': "I' \<subseteq> {0..<n}" using I aI' by blast
      have J': "J' \<subseteq> {0..<m}" using J bJ' by blast
      have det_sub_I'J': "Determinant.det (submatrix A I' J') = 0 \<or>
      (\<exists>xs. (det (submatrix A I' J') = prod_list xs \<or> det (submatrix A I' J') = - prod_list xs)
      \<and> set xs \<subseteq> {A $$ (i, i) |i. i < min n m \<and> A $$ (i, i) \<noteq> 0} \<and> length xs = k)"
      proof (rule Suc.hyps[OF cardI' cardJ' _ _ k0])
        show "I' \<subseteq> {0..<n}" using I aI' by blast
        show "J' \<subseteq> {0..<m}" using J bJ' by blast
      qed
      have mat_delete_sub:
        "mat_delete (submatrix A (insert a I') (insert b J')) a' b' = submatrix A I' J'"
        by (rule mat_delete_submatrix_insert[OF A_carrier cardI' cardJ' I' J' an bm k
              a_notin b_notin a'k b'k],insert pick_a pick_b aI' bJ', auto)
      have set_rw: "{0..<Suc k} = insert a' ({0..<Suc k}-{a'})"
        by (simp add: a'k insert_absorb)
      have rw0: "sum ?f ({0..<Suc k}-{a'}) = 0" by (rule sum.neutral, insert unique, auto)
      have "det (submatrix A I J)
        = (\<Sum>i<Suc k. submatrix A I J $$ (i, b') * cofactor (submatrix A I J) i b')"
        by (rule laplace_expansion_column[OF subIJ_carrier b'k])
      also have "... = ?f a' + sum ?f ({0..<Suc k}-{a'})"
        by (metis (no_types, lifting) Diff_iff atLeast0LessThan finite_atLeastLessThan
            finite_insert set_rw singletonI sum.insert)
      also have "... = ?f a'" using rw0 unfolding cofactor_def by auto
      also have "... = submatrix A I J $$ (a', b') * ((-1) ^ (a' + b') * det (submatrix A I' J'))"
        unfolding cofactor_def using mat_delete_sub aI' bJ' by simp
      finally have det_submatrix_IJ: "det (submatrix A I J)
         = A $$ (a, b) * ((- 1) ^ (a' + b') * det (submatrix A I' J'))" unfolding sub_index .
      show ?thesis
      proof (cases "det (submatrix A I' J') = 0")
        case True
        then show ?thesis using det_submatrix_IJ by auto
      next
        case False note det_not0 = False
        from this obtain xs where prod_list_xs: "det (submatrix A I' J') = prod_list xs
          \<or> det (submatrix A I' J') = - prod_list xs"
          and xs: "set xs \<subseteq> {A $$ (i, i) |i. i < min n m \<and> A $$ (i, i) \<noteq> 0}"
          and length_xs: "length xs = k"
          using det_sub_I'J' by blast
        let ?ys = "A$$(a,b) # xs"
        have length_ys: "length ?ys = Suc k" using length_xs by auto
        have a_eq_b: "a=b"
          using A_carrier an bm sub_IJ_0 sub_index dA unfolding diagonal_mat_def by auto
        have A_aa_in: "A$$(a,a) \<in> {A $$ (i, i) |i. i < min n m \<and> A $$ (i, i) \<noteq> 0}"
          using a_eq_b an bm sub_IJ_0 sub_index by auto
        have ys: "set ?ys \<subseteq> {A $$ (i, i) |i. i < min n m \<and> A $$ (i, i) \<noteq> 0}"
          using xs A_aa_in a_eq_b by auto
        show ?thesis
        proof (cases "even (a'+b')")
          case True
          have det_submatrix_IJ: "det (submatrix A I J) = A $$ (a, b) * det (submatrix A I' J')"
            using det_submatrix_IJ True by auto
          show ?thesis
          proof (cases "det (submatrix A I' J') = prod_list xs")
            case True
            have "det (submatrix A I J) = prod_list ?ys"
              using det_submatrix_IJ unfolding True by auto
            then show ?thesis using ys length_ys by blast
          next
            case False
            hence "det (submatrix A I' J') = - prod_list xs" using prod_list_xs by simp
            hence "det (submatrix A I J) = - prod_list ?ys" using det_submatrix_IJ by auto
            then show ?thesis using ys length_ys by blast
          qed
        next
          case False
          have det_submatrix_IJ: "det (submatrix A I J) = A $$ (a, b) * - det (submatrix A I' J')"
            using det_submatrix_IJ False by auto
          show ?thesis
          proof (cases "det (submatrix A I' J') = prod_list xs")
            case True
            have "det (submatrix A I J) = - prod_list ?ys"
              using det_submatrix_IJ unfolding True by auto
            then show ?thesis using ys length_ys by blast
          next
            case False
            hence "det (submatrix A I' J') = - prod_list xs" using prod_list_xs by simp
            hence "det (submatrix A I J) = prod_list ?ys" using det_submatrix_IJ by auto
            then show ?thesis using ys length_ys by blast
          qed
        qed
      qed
    next
      case False
      have "sum ?f {0..<Suc k} = 0" by (rule sum.neutral, insert False, auto)
      thus ?thesis using det_rw
        by (simp add: atLeast0LessThan)
    qed
  qed
qed


definition "minors A k = {det (submatrix A I J)| I J. I \<subseteq> {0..<dim_row A}
  \<and> J \<subseteq> {0..<dim_col A} \<and> card I = k \<and> card J = k}"


lemma Gcd_minors_dvd:
  fixes A::"'a::{semiring_Gcd,comm_ring_1} mat"
  assumes PAQ_B: "P * A * Q = B"
  and P: "P \<in> carrier_mat m m"
  and A: "A \<in> carrier_mat m n"
  and Q: "Q \<in> carrier_mat n n"
  and I: "I \<subseteq> {0..<dim_row A}" and J: "J \<subseteq> {0..<dim_col A}"
  and Ik: "card I = k" and Jk: "card J = k"
  shows "Gcd (minors A k) dvd det (submatrix B I J)"
proof -
  let ?subPA = "submatrix (P * A) I UNIV"
  let ?subQ = "submatrix Q UNIV J"
  have subPA: "?subPA \<in> carrier_mat k n"
  proof -
    have "I = {i. i < dim_row P \<and> i \<in> I}" using P I A by auto
    hence "card {i. i < dim_row P \<and> i \<in> I} = k" using Ik by auto
    thus ?thesis using A unfolding submatrix_def by auto
  qed
  have subQ: "submatrix Q UNIV J \<in> carrier_mat n k"
  proof -
    have J_eq: "J = {j. j < dim_col Q \<and> j \<in> J}" using Q J A by auto
    hence "card {j. j < dim_col Q \<and> j \<in> J} = k" using Jk by auto
    moreover have "card {i. i < dim_row Q \<and> i \<in> UNIV} = n" using Q by auto
    ultimately show ?thesis unfolding submatrix_def by auto
  qed
  have sub_sub_PA: "(submatrix ?subPA UNIV I') = submatrix (P * A) I I'" for I'
    using submatrix_split2[symmetric] by auto
  have det_subPA_rw: "det (submatrix (P * A) I I') =
    (\<Sum>J' | J' \<subseteq> {0..<m} \<and> card J' = k. det ((submatrix P I J')) * det (submatrix A J' I'))"
    if I'1: "I' \<subseteq> {0..<n}" and I'2: "card I' = k" for I'
  proof -
    have "submatrix (P * A) I I' = submatrix P I UNIV * submatrix A UNIV I'"
      unfolding submatrix_mult ..
    also have "det ... = (\<Sum>C | C \<subseteq> {0..<m} \<and> card C = k.
     det (submatrix (submatrix P I UNIV) UNIV C) * det (submatrix (submatrix A UNIV I') C UNIV))"
    proof (rule Cauchy_Binet)
      have "I = {i. i < dim_row P \<and> i \<in> I}" using P I A by auto
      thus "submatrix P I UNIV \<in> carrier_mat k m" using Ik P unfolding submatrix_def by auto
      have "I' = {j. j < dim_col A \<and> j \<in> I'}" using I'1 A by auto
      thus "submatrix A UNIV I' \<in> carrier_mat m k" using I'2 A unfolding submatrix_def by auto
    qed
    also have "... =  (\<Sum>J' | J' \<subseteq> {0..<m} \<and> card J' = k.
      det (submatrix P I J') * det (submatrix A J' I'))"
      unfolding submatrix_split2[symmetric] submatrix_split[symmetric] by simp
    finally show ?thesis .
  qed
  have "det (submatrix B I J) = det (submatrix (P*A*Q) I J)" using PAQ_B by simp
  also have "... = det (?subPA * ?subQ)" unfolding submatrix_mult by auto
  also have "... = (\<Sum>I' | I' \<subseteq> {0..<n} \<and> card I' = k. det (submatrix ?subPA UNIV I')
    * det (submatrix ?subQ I' UNIV))"
    by (rule Cauchy_Binet[OF subPA subQ])
  also have "... = (\<Sum>I' | I' \<subseteq> {0..<n} \<and> card I' = k.
    det (submatrix (P * A) I I') * det (submatrix Q I' J))"
    using submatrix_split[symmetric, of Q] submatrix_split2[symmetric, of "P*A"] by presburger
  also have "... = (\<Sum>I' | I' \<subseteq> {0..<n} \<and> card I' = k. \<Sum>J' | J' \<subseteq> {0..<m} \<and> card J' = k.
    det (submatrix P I J') * det (submatrix A J' I') * det (submatrix Q I' J))"
    using det_subPA_rw by (simp add: semiring_0_class.sum_distrib_right)
  finally have det_rw: "det (submatrix B I J) = (\<Sum>I' | I' \<subseteq> {0..<n} \<and> card I' = k.
    \<Sum>J' | J' \<subseteq> {0..<m} \<and> card J' = k.
    det (submatrix P I J') * det (submatrix A J' I') * det (submatrix Q I' J))" .
  show ?thesis
  proof (unfold det_rw, (rule dvd_sum)+)
    fix I' J'
    assume I': "I' \<in> {I'. I' \<subseteq> {0..<n} \<and> card I' = k}"
      and J': "J' \<in> {J'. J' \<subseteq> {0..<m} \<and> card J' = k}"
    have "Gcd (minors A k) dvd  det (submatrix A J' I')"
      by (rule Gcd_dvd, unfold minors_def, insert A I' J', auto)
    then show "Gcd (minors A k) dvd det (submatrix P I J') * det (submatrix A J' I')
          * det (submatrix Q I' J)" by auto
  qed
qed

(*The conclusion could be simplified since we have S = I.*)
lemma det_minors_diagonal2:
  assumes dA: "diagonal_mat A" and A_carrier: "A \<in> carrier_mat n m"
    and Ik: "card I = k" and Jk: "card J = k"
    and r: "I \<subseteq> {0..<n}"
    and c: "J \<subseteq> {0..<m}" and k: "k>0"
  shows "det (submatrix A I J) = 0 \<or> (\<exists>S. S \<subseteq> {0..<min n m} \<and> card S = k \<and> S=I \<and>
   (det (submatrix A I J) = (\<Prod>i\<in>S. A $$ (i,i)) \<or> det (submatrix A I J) = - (\<Prod>i\<in>S. A $$ (i,i))))"
  using Ik Jk r c k
proof (induct k arbitrary: I J)
 case 0
  then show ?case by auto
next
  case (Suc k)
  note cardI = Suc.prems(1)
  note cardJ = Suc.prems(2)
  note I = Suc.prems(3)
  note J = Suc.prems(4)
  have *: "{i. i < dim_row A \<and> i \<in> I} = I" using I Ik A_carrier carrier_mat_def by auto
  have **: "{j. j < dim_col A \<and> j \<in> J} = J" using J Jk A_carrier carrier_mat_def by auto
  show ?case
  proof (cases "k = 0")
    case True note k0 = True
    from this obtain a where aI: "I = {a}" using True cardI card_1_singletonE by auto
    from this obtain b where bJ: "J = {b}" using True cardJ card_1_singletonE by auto
    have an: "a<n" using aI I by auto
    have bm: "b<m" using bJ J by auto
    have sub_carrier: "submatrix A {a} {b} \<in> carrier_mat 1 1"
      unfolding carrier_mat_def submatrix_def
      using * ** aI bJ by auto
    have 1: "det (submatrix A {a} {b}) = (submatrix A {a} {b}) $$ (0,0)"
      by (rule det_singleton[OF sub_carrier])
    have 2: "... = A $$ (a,b)"
      by (rule submatrix_singleton_index[OF A_carrier an bm])
    show ?thesis
    proof (cases "A $$ (a,b) \<noteq> 0")
      let ?S="{a}"
      case True
      hence ab: "a = b" using dA A_carrier an bm unfolding diagonal_mat_def carrier_mat_def by auto
      hence "?S \<subseteq> {0..<min n m}" using an bm by auto
      moreover have "det (submatrix A {a} {b}) = (\<Prod>i\<in>?S. A $$ (i, i))" using 1 2 ab by auto
      moreover have "card ?S = Suc k" using k0 by auto
      ultimately show ?thesis using an bm unfolding aI bJ by blast
    next
      case False
      then show ?thesis using 1 2 aI bJ by auto
    qed
  next
    case False
    hence k0: "0 < k" by simp
    have k: "k < min n m"
      by (metis I J cardI cardJ le_imp_less_Suc less_Suc_eq_le min.commute
          min_def not_less subset_eq_atLeast0_lessThan_card)
    have subIJ_carrier: "(submatrix A I J) \<in> carrier_mat (Suc k) (Suc k)"
      unfolding carrier_mat_def using * ** cardI cardJ
      unfolding submatrix_def by auto
    obtain b' where b'k: "b' < Suc k" by auto
    let ?f="\<lambda>i. submatrix A I J $$ (i, b') * cofactor (submatrix A I J) i b'"
    have det_rw: "det (submatrix A I J)
        = (\<Sum>i<Suc k. submatrix A I J $$ (i, b') * cofactor (submatrix A I J) i b')"
      by (rule laplace_expansion_column[OF subIJ_carrier b'k])
    show ?thesis
    proof (cases "\<exists>a'<Suc k. submatrix A I J $$ (a',b') \<noteq> 0")
      case True
      obtain a' where sub_IJ_0: "submatrix A I J $$ (a',b') \<noteq> 0"
        and a'k: "a' < Suc k"
        and unique: "\<forall>j. j<Suc k \<and> submatrix A I J $$ (j,b') \<noteq> 0 \<longrightarrow> j = a'"
        using diagonal_imp_submatrix_element_not0[OF dA A_carrier cardI cardJ I J b'k True] by auto
      have "submatrix A I J $$ (a', b') = A $$ (pick I a', pick J b')"
        by (rule submatrix_index, auto simp add: "*" a'k cardI "**" b'k cardJ)
      from this obtain a b where an: "a < n" and bm:  "b < m"
        and sub_index: "submatrix A I J $$ (a', b') = A $$ (a, b)"
        and pick_a: "pick I a' = a" and pick_b: "pick J b' = b"
        using * ** A_carrier a'k b'k cardI cardJ pick_le by fastforce
      obtain I' where aI': "I = insert a I'" and a_notin: "a \<notin> I'"
        by (metis Set.set_insert a'k cardI pick_a pick_in_set_le)
      obtain J' where bJ': "J = insert b J'" and b_notin: "b \<notin> J'"
        by (metis Set.set_insert b'k cardJ pick_b pick_in_set_le)
      have Suc_k0: "0 < Suc k" by simp
      have aI: "a \<in> I" using aI' by auto
      have bJ: "b \<in> J" using bJ' by auto
      have cardI':  "card I' = k"
        by (metis aI' a_notin cardI card.infinite card_insert_disjoint
            finite_insert nat.inject nat.simps(3))
      have cardJ':  "card J' = k"
        by (metis bJ' b_notin cardJ card.infinite card_insert_disjoint
            finite_insert nat.inject nat.simps(3))
      have I': "I' \<subseteq> {0..<n}" using I aI' by blast
      have J': "J' \<subseteq> {0..<m}" using J bJ' by blast
      have det_sub_I'J': "det (submatrix A I' J') = 0 \<or> (\<exists>S\<subseteq>{0..<min n m}. card S = k \<and> S=I'
        \<and> (det (submatrix A I' J') = (\<Prod>i\<in>S. A $$ (i, i))
        \<or> det (submatrix A I' J') = - (\<Prod>i\<in>S. A $$ (i, i))))"
      proof (rule Suc.hyps[OF cardI' cardJ' _ _ k0])
        show "I' \<subseteq> {0..<n}" using I aI' by blast
        show "J' \<subseteq> {0..<m}" using J bJ' by blast
      qed
      have mat_delete_sub:
        "mat_delete (submatrix A (insert a I') (insert b J')) a' b' = submatrix A I' J'"
        by (rule mat_delete_submatrix_insert[OF A_carrier cardI' cardJ' I' J' an bm k
              a_notin b_notin a'k b'k],insert pick_a pick_b aI' bJ', auto)
      have set_rw: "{0..<Suc k} = insert a' ({0..<Suc k}-{a'})"
        by (simp add: a'k insert_absorb)
      have rw0: "sum ?f ({0..<Suc k}-{a'}) = 0" by (rule sum.neutral, insert unique, auto)
      have "det (submatrix A I J)
        = (\<Sum>i<Suc k. submatrix A I J $$ (i, b') * cofactor (submatrix A I J) i b')"
        by (rule laplace_expansion_column[OF subIJ_carrier b'k])
      also have "... = ?f a' + sum ?f ({0..<Suc k}-{a'})"
        by (metis (no_types, lifting) Diff_iff atLeast0LessThan finite_atLeastLessThan
            finite_insert set_rw singletonI sum.insert)
      also have "... = ?f a'" using rw0 unfolding cofactor_def by auto
      also have "... = submatrix A I J $$ (a', b') * ((-1) ^ (a' + b') * det (submatrix A I' J'))"
        unfolding cofactor_def using mat_delete_sub aI' bJ' by simp
      finally have det_submatrix_IJ: "det (submatrix A I J)
         = A $$ (a, b) * ((- 1) ^ (a' + b') * det (submatrix A I' J'))" unfolding sub_index .
      show ?thesis
      proof (cases "det (submatrix A I' J') = 0")
        case True
        then show ?thesis using det_submatrix_IJ by auto
      next
        case False note det_not0 = False
        from this obtain xs where prod_list_xs: "det (submatrix A I' J') = (\<Prod>i\<in>xs. A $$ (i, i))
          \<or> det (submatrix A I' J') = - (\<Prod>i\<in>xs. A $$ (i, i))"
          and xs: "xs\<subseteq>{0..<min n m}"
          and length_xs: "card xs = k"
          and xs_I': "xs=I'"
          using det_sub_I'J' by blast
        let ?ys = "insert a xs"
        have a_notin_xs: "a \<notin> xs"
          by (simp add: xs_I' a_notin)
        have length_ys: "card ?ys = Suc k"
          using length_xs a_notin_xs by (simp add: card_ge_0_finite k0)
        have a_eq_b: "a=b"
          using A_carrier an bm sub_IJ_0 sub_index dA unfolding diagonal_mat_def by auto
        have A_aa_in: "A$$(a,a) \<in> {A $$ (i, i) |i. i < min n m \<and> A $$ (i, i) \<noteq> 0}"
          using a_eq_b an bm sub_IJ_0 sub_index by auto
        show ?thesis
        proof (cases "even (a'+b')")
          case True
          have det_submatrix_IJ: "det (submatrix A I J) = A $$ (a, b) * det (submatrix A I' J')"
            using det_submatrix_IJ True by auto
          show ?thesis
          proof (cases "det (submatrix A I' J') = (\<Prod>i\<in>xs. A $$ (i, i))")
            case True
            have "det (submatrix A I J) = (\<Prod>i\<in>?ys. A $$ (i, i))"
              using det_submatrix_IJ unfolding True a_eq_b
              by (metis (no_types, lifting) a_notin_xs a_eq_b
                  card_ge_0_finite k0 length_xs prod.insert)
            then show ?thesis using length_ys
              using a_eq_b an bm xs xs_I'
              by (simp add: aI')
          next
            case False
            hence "det (submatrix A I' J') = - (\<Prod>i\<in>xs. A $$ (i, i))" using prod_list_xs by simp
            hence "det (submatrix A I J) = -(\<Prod>i\<in>?ys. A $$ (i, i))" using det_submatrix_IJ a_eq_b
              by (metis (no_types, lifting) a_notin_xs card_ge_0_finite k0
                  length_xs mult_minus_right prod.insert)
            then show ?thesis using length_ys
              using a_eq_b an bm xs aI' xs_I' by force
          qed
        next
          case False
          have det_submatrix_IJ: "det (submatrix A I J) = A $$ (a, b) * - det (submatrix A I' J')"
            using det_submatrix_IJ False by auto
          show ?thesis
          proof (cases "det (submatrix A I' J') = (\<Prod>i\<in>xs. A $$ (i, i))")
            case True
            have "det (submatrix A I J) = - (\<Prod>i\<in>?ys. A $$ (i, i))"
              using det_submatrix_IJ unfolding True
              by (metis (no_types, lifting) a_eq_b a_notin_xs card_ge_0_finite k0
                  length_xs mult_minus_right prod.insert)
            then show ?thesis using length_ys
              using a_eq_b an bm xs aI' xs_I' by force
          next
            case False
            hence "det (submatrix A I' J') = - (\<Prod>i\<in>xs. A $$ (i, i))" using prod_list_xs by simp
            hence "det (submatrix A I J) = (\<Prod>i\<in>?ys. A $$ (i, i))" using det_submatrix_IJ
              by (metis (mono_tags, lifting) a_eq_b a_notin_xs card_ge_0_finite
                  equation_minus_iff k0 length_xs prod.insert)
            then show ?thesis using length_ys
              using a_eq_b an bm xs aI' xs_I' by force
          qed
        qed
      qed
    next
      case False
      have "sum ?f {0..<Suc k} = 0" by (rule sum.neutral, insert False, auto)
      thus ?thesis using det_rw
        by (simp add: atLeast0LessThan)
    qed
  qed
qed


subsection \<open>Relating minors and GCD\<close>

lemma diagonal_dvd_Gcd_minors:
  fixes A::"'a::{semiring_Gcd,comm_ring_1} mat"
  assumes A: "A \<in> carrier_mat n m"
    and SNF_A: "Smith_normal_form_mat A"
shows "(\<Prod>i=0..<k. A $$ (i,i)) dvd Gcd (minors A k)"
proof (cases "k=0")
  case True
  then show ?thesis by auto
next
  case False
  hence k: "0<k" by simp
  show ?thesis
  proof (rule Gcd_greatest)
    have diag_A: "diagonal_mat A"
      using SNF_A unfolding Smith_normal_form_mat_def isDiagonal_mat_def diagonal_mat_def by auto
    fix b assume b_in_minors: "b \<in> minors A k"
    show "(\<Prod>i = 0..<k. A $$ (i, i)) dvd b"
    proof (cases "b=0")
      case True
      then show ?thesis by auto
    next
      case False
     obtain I J where b: "b = det (submatrix A I J)" and I: "I \<subseteq> {0..<dim_row A} "
    and J: "J \<subseteq> {0..<dim_col A}" and Ik: "card I = k" and Jk: "card J = k"
       using b_in_minors  unfolding minors_def by blast
    obtain S where S: "S \<subseteq> {0..<min n m}" and Sk: "card S = k"
      and det_subS: "det (submatrix A I J) = (\<Prod>i\<in>S. A $$ (i,i))
        \<or> det (submatrix A I J) = -(\<Prod>i\<in>S. A $$ (i,i))"
      using det_minors_diagonal2[OF diag_A A Ik Jk _ _ k] I J A False b by auto
    obtain f where inj_f: "inj_on f {0..<k}" and fk_S: "f`{0..<k} = S"
      and i_fi: " (\<forall>i\<in>{0..<k}. i \<le> f i)" using exists_inj_ge_index[OF S Sk] by blast
    have "(\<Prod>i = 0..<k. A $$ (i, i)) dvd (\<Prod>i\<in>{0..<k}. A $$ (f i,f i))"
      by (rule prod_dvd_prod, rule SNF_divides_diagonal[OF A SNF_A], insert fk_S S i_fi, force+)
    also have "... = (\<Prod>i\<in>f`{0..<k}. A $$ (i,i))"
      by (rule prod.reindex[symmetric, unfolded o_def, OF inj_f])
    also have "... = (\<Prod>i\<in>S. A $$ (i, i))" using fk_S by auto
    finally have *: "(\<Prod>i = 0..<k. A $$ (i, i)) dvd (\<Prod>i\<in>S. A $$ (i, i))" .
    show "(\<Prod>i = 0..<k. A $$ (i, i)) dvd b" using det_subS b * by auto
  qed
qed
qed


lemma Gcd_minors_dvd_diagonal:
  fixes A::"'a::{semiring_Gcd,comm_ring_1} mat"
  assumes A: "A \<in> carrier_mat n m"
    and SNF_A: "Smith_normal_form_mat A"
    and k: "k \<le> min n m"
  shows "Gcd (minors A k) dvd (\<Prod>i=0..<k. A $$ (i,i))"
proof (rule Gcd_dvd)
  define I where "I = {0..<k}"
  have "(\<Prod>i = 0..<k. A $$ (i, i)) = det (submatrix A I I)"
  proof -
    have sub_eq: "submatrix A I I = mat k k (\<lambda>(i, j). A $$ (i, j))"
    proof (rule eq_matI, auto)
      have "I = {i. i < dim_row A \<and> i \<in> I}" unfolding I_def using A k by auto
      hence ck: "card {i. i < dim_row A \<and> i \<in> I} = k"
        unfolding I_def using card_atLeastLessThan by presburger
      have "I = {i. i < dim_col A \<and> i \<in> I}" unfolding I_def using A k by auto
      hence ck2: "card {j. j < dim_col A \<and> j \<in> I} = k"
        unfolding I_def using card_atLeastLessThan by presburger
      show dr: "dim_row (submatrix A I I) = k" using ck unfolding submatrix_def by auto
      show dc: "dim_col (submatrix A I I) = k" using ck2 unfolding submatrix_def by auto
      fix i j assume i: "i < k" and j: "j < k"
      have p1: "pick I i = i"
      proof -
        have "{0..<i} = {a \<in> I. a < i}" using I_def i by auto
        hence i_eq: "i = card {a \<in> I. a < i}"
          by (metis card_atLeastLessThan diff_zero)
        have "pick I i = pick I (card {a \<in> I. a < i})" using i_eq by simp
        also have "... = i" by (rule pick_card_in_set, insert i I_def, simp)
        finally show ?thesis .
      qed
      have p2: "pick I j = j"
      proof -
        have "{0..<j} = {a \<in> I. a < j}" using I_def j by auto
        hence j_eq: "j = card {a \<in> I. a < j}"
          by (metis card_atLeastLessThan diff_zero)
        have "pick I j = pick I (card {a \<in> I. a < j})" using j_eq by simp
        also have "... = j" by (rule pick_card_in_set, insert j I_def, simp)
        finally show ?thesis .
      qed
      have "submatrix A I I $$ (i, j) = A $$ (pick I i, pick I j)"
      proof (rule submatrix_index)
        show "i < card {i. i < dim_row A \<and> i \<in> I}" by (metis dim_submatrix(1) dr i)
        show "j < card {j. j < dim_col A \<and> j \<in> I}" by (metis dim_submatrix(2) dc j)
      qed
      also have "... = A $$ (i,j)" using p1 p2 by simp
      finally show "submatrix A I I $$ (i, j) = A $$ (i, j)" .
    qed
    hence "det (submatrix A I I) = det (mat k k (\<lambda>(i, j). A $$ (i, j)))" by simp
    also have "... = prod_list (diag_mat (mat k k (\<lambda>(i, j). A $$ (i, j))))"
    proof (rule det_upper_triangular)
      show "mat k k (\<lambda>(i, j). A $$ (i, j)) \<in> carrier_mat k k" by auto
      show "upper_triangular (Matrix.mat k k (\<lambda>(i, j). A $$ (i, j)))"
        using SNF_A A k unfolding Smith_normal_form_mat_def isDiagonal_mat_def by auto
    qed
    also have "... = (\<Prod>i = 0..<k. A $$ (i, i))"
      by (metis (mono_tags, lifting) atLeastLessThan_iff dim_row_mat(1) index_mat(1)
          prod.cong prod_list_diag_prod split_conv)
    finally show ?thesis ..
  qed
  moreover have "I \<subseteq> {0..<dim_row A}" using k A I_def by auto
  moreover have "I \<subseteq> {0..<dim_col A}" using k A I_def by auto
  moreover have "card I = k" using I_def by auto
  ultimately show "(\<Prod>i = 0..<k. A $$ (i, i)) \<in> minors A k" unfolding minors_def by auto
qed



lemma Gcd_minors_A_dvd_Gcd_minors_PAQ:
 fixes A::"'a::{semiring_Gcd,comm_ring_1} mat"
 assumes A: "A \<in> carrier_mat m n"
    and P: "P \<in> carrier_mat m m" and Q: "Q \<in> carrier_mat n n"
  shows "Gcd (minors A k) dvd Gcd (minors (P*A*Q) k)"
proof (rule Gcd_greatest)
  let ?B="(P * A * Q)"
  fix b assume "b \<in> minors ?B k"
  from this  obtain I J where b: "b = det (submatrix ?B I J)" and I: "I \<subseteq> {0..<dim_row ?B}"
    and J: "J \<subseteq> {0..<dim_col ?B}" and Ik: "card I = k" and Jk: "card J = k"
    unfolding minors_def by blast
  have "Gcd (minors A k) dvd det (submatrix ?B I J)"
    by (rule Gcd_minors_dvd[OF _ P A Q _ _ Ik Jk], insert A I J P Q, auto)
  thus "Gcd (minors A k) dvd b" using b by simp
qed


lemma Gcd_minors_PAQ_dvd_Gcd_minors_A:
 fixes A::"'a::{semiring_Gcd,comm_ring_1} mat"
 assumes A: "A \<in> carrier_mat m n"
    and P: "P \<in> carrier_mat m m"
    and Q: "Q \<in> carrier_mat n n"
    and inv_P: "invertible_mat P"
    and inv_Q: "invertible_mat Q"
  shows "Gcd (minors (P*A*Q) k) dvd Gcd (minors A k)"
proof (rule Gcd_greatest)
  let ?B = "P * A * Q"
  fix b assume "b \<in> minors A k"
  from this obtain I J where b: "b = det (submatrix A I J)" and I: "I \<subseteq> {0..<dim_row A} "
    and J: "J \<subseteq> {0..<dim_col A}" and Ik: "card I = k" and Jk: "card J = k"
    unfolding minors_def by blast
  obtain P' where PP': "inverts_mat P P'" and P'P: "inverts_mat P' P"
    using inv_P unfolding invertible_mat_def by auto
  obtain Q' where QQ': "inverts_mat Q Q'" and Q'Q: "inverts_mat Q' Q"
    using inv_Q unfolding invertible_mat_def by auto
  have P': "P' \<in> carrier_mat m m" using PP' P'P unfolding inverts_mat_def
    by (metis P carrier_matD(1) carrier_matD(2) carrier_matI index_mult_mat(3) index_one_mat(3))
  have Q': "Q' \<in> carrier_mat n n"
    using QQ' Q'Q unfolding inverts_mat_def
    by (metis Q carrier_matD(1) carrier_matD(2) carrier_matI index_mult_mat(3) index_one_mat(3))
  have rw: "P' *?B *Q' = A"
  proof -
    have f1: "P' * P = 1\<^sub>m m"
      by (metis (no_types) P' P'P carrier_matD(1) inverts_mat_def)
    have *: "P' * P * A = P' * (P * A)"
      by (meson A P P' assoc_mult_mat)
    have " P' * (P * A * Q) * Q' =  P' * P * A * Q * Q'"
      by (smt A P P' Q assoc_mult_mat mult_carrier_mat)
    also have "... =  P' * P * (A * Q * Q')"
      using A P P' Q Q' f1 * by auto
    also have "... = A * Q * Q'" using P'P A P' unfolding inverts_mat_def by auto
    also have "... = A" using QQ' A Q' Q unfolding inverts_mat_def by auto
    finally show ?thesis .
  qed
  have "Gcd (minors ?B k) dvd det (submatrix (P'*?B*Q') I J)"
    by (rule Gcd_minors_dvd[OF _ P' _ Q' _ _ Ik Jk], insert P A Q I J, auto)
  also have "... = det (submatrix A I J)" using rw by simp
  finally show "Gcd (minors ?B k) dvd b" using b by simp
qed

lemma Gcd_minors_dvd_diag_PAQ:
  fixes P A Q::"'a::{semiring_Gcd,comm_ring_1} mat"
 assumes A: "A \<in> carrier_mat m n"
    and P: "P \<in> carrier_mat m m"
    and Q: "Q \<in> carrier_mat n n"
    and SNF: "Smith_normal_form_mat (P*A*Q)"
    and k: "k\<le>min m n"
  shows "Gcd (minors A k) dvd (\<Prod>i=0..<k. (P * A * Q) $$ (i,i))"
proof -
  have "Gcd (minors A k) dvd Gcd (minors (P * A * Q) k)"
    by (rule Gcd_minors_A_dvd_Gcd_minors_PAQ[OF A P Q])
  also have "... dvd (\<Prod>i=0..<k. (P*A*Q) $$ (i,i))"
    by (rule Gcd_minors_dvd_diagonal[OF _ SNF k], insert P A Q, auto)
  finally show ?thesis .
qed


lemma diag_PAQ_dvd_Gcd_minors:
  fixes P A Q::"'a::{semiring_Gcd,comm_ring_1} mat"
 assumes A: "A \<in> carrier_mat m n"
    and P: "P \<in> carrier_mat m m"
    and Q: "Q \<in> carrier_mat n n"
    and inv_P: "invertible_mat P"
    and inv_Q: "invertible_mat Q"
    and SNF: "Smith_normal_form_mat (P*A*Q)"
  shows "(\<Prod>i=0..<k. (P * A * Q) $$ (i,i)) dvd Gcd (minors A k)"
proof -
  have "(\<Prod>i=0..<k. (P*A*Q) $$ (i,i)) dvd Gcd (minors (P * A * Q) k)"
    by (rule diagonal_dvd_Gcd_minors[OF _ SNF], auto)
  also have "... dvd Gcd (minors A k)"
    by (rule Gcd_minors_PAQ_dvd_Gcd_minors_A[OF _ _ _ inv_P inv_Q], insert P A Q, auto)
  finally show ?thesis .
qed


(*This lemma requires semidom in order to apply prod_zero_iff*)
lemma Smith_prod_zero_imp_last_zero:
  fixes A::"'a::{semidom,comm_ring_1} mat"
  assumes  A: "A \<in> carrier_mat m n"
    and SNF: "Smith_normal_form_mat A"
    and prod_0: "(\<Prod>j=0..<Suc i. A $$ (j,j)) = 0"
  and i: "i<min m n"
  shows "A $$(i,i) = 0"
proof -
  obtain j where Ajj: "A$$(j,j) = 0" and j: "j<Suc i" using prod_0 prod_zero_iff by auto
  show "A $$(i,i) = 0" by (rule Smith_zero_imp_zero[OF A SNF Ajj i], insert j, auto)
qed

subsection \<open>Final theorem\<close>

lemma Smith_normal_form_uniqueness_aux:
  fixes P A Q::"'a::{idom,semiring_Gcd} mat"
  assumes A: "A \<in> carrier_mat m n"
  (*PAQ = B with B in SNF and P,Q invertible matrices*)
  and P: "P \<in> carrier_mat m m"
  and Q: "Q \<in> carrier_mat n n"
  and inv_P: "invertible_mat P"
  and inv_Q: "invertible_mat Q"
  and PAQ_B: "P*A*Q = B"
  and SNF: "Smith_normal_form_mat B"
  (*P'AQ' = B' with B' in SNF and P',Q' invertible matrices*)
  and P': "P' \<in> carrier_mat m m"
  and Q': "Q' \<in> carrier_mat n n"
  and inv_P': "invertible_mat P'"
  and inv_Q': "invertible_mat Q'"
  and P'AQ'_B': "P'*A*Q' = B'"
  and SNF_B': "Smith_normal_form_mat B'"
  and k: "k<min m n"
shows "\<forall>i\<le>k. B$$(i,i) dvd B'$$(i,i) \<and> B'$$(i,i) dvd B$$(i,i)"
proof (rule allI, rule impI)
  fix i assume ik: "i \<le> k"
  show " B $$ (i, i) dvd B' $$ (i, i) \<and> B' $$ (i, i) dvd B $$ (i, i)"
  proof -
    let ?\<Pi>Bi = "(\<Prod>i=0..<i. B $$ (i,i))"
    let ?\<Pi>B'i = "(\<Prod>i=0..<i. B' $$ (i,i))"
    have "?\<Pi>B'i dvd Gcd (minors A i)"
      by (unfold P'AQ'_B'[symmetric], rule diag_PAQ_dvd_Gcd_minors[OF A P' Q' inv_P' inv_Q'],
          insert P'AQ'_B' SNF_B' ik k, auto )
    also have "... dvd ?\<Pi>Bi"
      by (unfold PAQ_B[symmetric], rule Gcd_minors_dvd_diag_PAQ[OF A P Q],
          insert PAQ_B SNF ik k, auto)
    finally have B'_i_dvd_B_i: "?\<Pi>B'i dvd ?\<Pi>Bi" .
    have "?\<Pi>Bi dvd Gcd (minors A i)"
      by (unfold PAQ_B[symmetric], rule diag_PAQ_dvd_Gcd_minors[OF A P Q inv_P inv_Q],
          insert PAQ_B SNF ik k, auto )
    also have "... dvd ?\<Pi>B'i"
      by (unfold P'AQ'_B'[symmetric], rule Gcd_minors_dvd_diag_PAQ[OF A P' Q'],
          insert P'AQ'_B' SNF_B' ik k, auto)
    finally have B_i_dvd_B'_i: "?\<Pi>Bi dvd ?\<Pi>B'i" .
    let ?\<Pi>B_Suc = "(\<Prod>i=0..<Suc i. B $$ (i,i))"
    let ?\<Pi>B'_Suc = "(\<Prod>i=0..<Suc i. B' $$ (i,i))"
    have "?\<Pi>B'_Suc dvd Gcd (minors A (Suc i))"
      by (unfold P'AQ'_B'[symmetric], rule diag_PAQ_dvd_Gcd_minors[OF A P' Q' inv_P' inv_Q'],
          insert P'AQ'_B' SNF_B' ik k, auto )
    also have "... dvd ?\<Pi>B_Suc"
      by (unfold PAQ_B[symmetric], rule Gcd_minors_dvd_diag_PAQ[OF A P Q],
          insert PAQ_B SNF ik k, auto)
    finally have 3: "?\<Pi>B'_Suc dvd ?\<Pi>B_Suc" .
    have "?\<Pi>B_Suc dvd Gcd (minors A (Suc i))"
      by (unfold PAQ_B[symmetric], rule diag_PAQ_dvd_Gcd_minors[OF A P Q inv_P inv_Q],
          insert PAQ_B SNF ik k, auto )
    also have "... dvd ?\<Pi>B'_Suc"
      by (unfold P'AQ'_B'[symmetric], rule Gcd_minors_dvd_diag_PAQ[OF A P' Q'],
          insert P'AQ'_B' SNF_B' ik k, auto)
    finally have 4: "?\<Pi>B_Suc dvd ?\<Pi>B'_Suc" .
    show ?thesis
    proof (cases "?\<Pi>B_Suc = 0")
      case True
      have True2: "?\<Pi>B'_Suc = 0" using 4 True by fastforce
      have "B$$(i,i) = 0"
        by (rule Smith_prod_zero_imp_last_zero[OF _ SNF True], insert ik k PAQ_B P Q, auto)
      moreover have "B'$$(i,i) = 0"
        by (rule Smith_prod_zero_imp_last_zero[OF _ SNF_B' True2],
            insert ik k P'AQ'_B' P' Q', auto)
      ultimately show ?thesis by auto
    next
      case False
      have "\<exists>u. u dvd 1 \<and> ?\<Pi>B'i = u * ?\<Pi>Bi"
        by (rule dvd_associated2[OF B'_i_dvd_B_i B_i_dvd_B'_i], insert False B'_i_dvd_B_i, force)
      from this obtain u where eq1: "(\<Prod>i=0..<i. B' $$ (i,i)) = u * (\<Prod>i=0..<i. B $$ (i,i))"
        and u_dvd_1: "u dvd 1" by blast
      have "\<exists>u. u dvd 1 \<and> ?\<Pi>B_Suc = u * ?\<Pi>B'_Suc"
        by (rule dvd_associated2[OF 4 3 False])
      from this obtain w where eq2: "(\<Prod>i=0..<Suc i. B $$ (i,i)) = w * (\<Prod>i=0..<Suc i. B' $$ (i,i))"
        and w_dvd_1: "w dvd 1" by blast
      have "B $$ (i, i) * (\<Prod>i=0..<i. B $$ (i,i)) = (\<Prod>i=0..<Suc i. B $$ (i,i))"
        by (simp add: prod.atLeast0_lessThan_Suc ik)
      also have "... = w * (\<Prod>i=0..<Suc i. B' $$ (i,i))" unfolding eq2 by auto
      also have "... = w * (B' $$ (i,i) * (\<Prod>i=0..<i. B' $$ (i,i)))"
        by (simp add: prod.atLeast0_lessThan_Suc ik)
      also have "... = w * (B' $$ (i,i) * u * (\<Prod>i=0..<i. B $$ (i,i)))"
        unfolding eq1 by auto
      finally have "B $$ (i,i) = w * u * B' $$ (i,i)"
        using False by auto
      moreover have "w*u dvd 1" using u_dvd_1 w_dvd_1 by auto
      ultimately have "\<exists>u. is_unit u \<and> B $$ (i, i) = u * B' $$ (i, i)" by auto
      thus ?thesis using dvd_associated2 by force
    qed
  qed
qed


lemma Smith_normal_form_uniqueness:
  fixes P A Q::"'a::{idom,semiring_Gcd} mat"
  assumes A: "A \<in> carrier_mat m n"
    (*PAQ = B with B in SNF and P,Q invertible matrices*)
    and P: "P \<in> carrier_mat m m"
    and Q: "Q \<in> carrier_mat n n"
    and inv_P: "invertible_mat P"
    and inv_Q: "invertible_mat Q"
    and PAQ_B: "P*A*Q = B"
    and SNF: "Smith_normal_form_mat B"
    (*P'AQ' = B' with B' in SNF and P',Q' invertible matrices*)
    and P': "P' \<in> carrier_mat m m"
    and Q': "Q' \<in> carrier_mat n n"
    and inv_P': "invertible_mat P'"
    and inv_Q': "invertible_mat Q'"
    and P'AQ'_B': "P'*A*Q' = B'"
    and SNF_B': "Smith_normal_form_mat B'"
    and i: "i < min m n"
  shows "\<exists>u. u dvd 1 \<and> B $$ (i,i) = u * B' $$ (i,i)"
proof (cases "B $$ (i,i) = 0")
  case True
  let ?\<Pi>B_Suc = "(\<Prod>i=0..<Suc i. B $$ (i,i))"
  let ?\<Pi>B'_Suc = "(\<Prod>i=0..<Suc i. B' $$ (i,i))"
  have "?\<Pi>B_Suc dvd Gcd (minors A (Suc i))"
    by (unfold PAQ_B[symmetric], rule diag_PAQ_dvd_Gcd_minors[OF A P Q inv_P inv_Q],
        insert PAQ_B SNF i, auto)
  also have "... dvd ?\<Pi>B'_Suc"
    by (unfold P'AQ'_B'[symmetric], rule Gcd_minors_dvd_diag_PAQ[OF A P' Q'],
        insert P'AQ'_B' SNF_B' i, auto)
  finally have 4: "?\<Pi>B_Suc dvd ?\<Pi>B'_Suc" .
  have prod0: "?\<Pi>B_Suc=0" using True by auto
  have True2: "?\<Pi>B'_Suc = 0" using 4 by (metis dvd_0_left_iff prod0)
  have "B'$$(i,i) = 0"
    by (rule Smith_prod_zero_imp_last_zero[OF _ SNF_B' True2],
        insert i P'AQ'_B' P' Q', auto)
  thus ?thesis using True by auto
next
  case False
  have "\<forall>a\<le>i. B$$(a,a) dvd B'$$(a,a) \<and> B'$$(a,a) dvd B$$(a,a)"
    by (rule Smith_normal_form_uniqueness_aux[OF assms])
  hence "B$$(i,i) dvd B'$$(i,i) \<and> B'$$(i,i) dvd B$$(i,i)" using i by auto
  thus ?thesis using dvd_associated2 False by blast
qed

text \<open>The final theorem, moved to HOL Analysis\<close>

lemma Smith_normal_form_uniqueness_HOL_Analysis:
  fixes A::"'a::{idom,semiring_Gcd}^'m::mod_type^'n::mod_type"
  and P P'::"'a^'n::mod_type^'n::mod_type"
  and Q Q'::"'a^'m::mod_type^'m::mod_type"
  assumes
    (*PAQ = B with B in SNF and P,Q invertible matrices*)
    inv_P: "invertible P"
    and inv_Q: "invertible Q"
    and PAQ_B: "P**A**Q = B"
    and SNF: "Smith_normal_form B"
    (*P'AQ' = B' with B' in SNF and P',Q' invertible matrices*)
    and inv_P': "invertible P'"
    and inv_Q': "invertible Q'"
    and P'AQ'_B': "P'**A**Q' = B'"
    and SNF_B': "Smith_normal_form B'"
    and i: "i < min (nrows A) (ncols A)"
  shows "\<exists>u. u dvd 1 \<and> B $h Mod_Type.from_nat i $h Mod_Type.from_nat i
  = u * B' $h Mod_Type.from_nat i $h Mod_Type.from_nat i"
proof -
  let ?P = "Mod_Type_Connect.from_hma\<^sub>m P"
  let ?A = "Mod_Type_Connect.from_hma\<^sub>m A"
  let ?Q = "Mod_Type_Connect.from_hma\<^sub>m Q"
  let ?B = "Mod_Type_Connect.from_hma\<^sub>m B"
  let ?P' = "Mod_Type_Connect.from_hma\<^sub>m P'"
  let ?Q' = "Mod_Type_Connect.from_hma\<^sub>m Q'"
  let ?B' = "Mod_Type_Connect.from_hma\<^sub>m B'"
  let ?i = "(Mod_Type.from_nat i)::'n"
  let ?i' = "(Mod_Type.from_nat i)::'m"
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?P P" by (simp add: Mod_Type_Connect.HMA_M_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?A A" by (simp add: Mod_Type_Connect.HMA_M_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?Q Q" by (simp add: Mod_Type_Connect.HMA_M_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?B B" by (simp add: Mod_Type_Connect.HMA_M_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?P' P'" by (simp add: Mod_Type_Connect.HMA_M_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?Q' Q'" by (simp add: Mod_Type_Connect.HMA_M_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_M ?B' B'" by (simp add: Mod_Type_Connect.HMA_M_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_I i ?i"
    by (metis Mod_Type_Connect.HMA_I_def i min.strict_boundedE
        mod_type_class.to_nat_from_nat_id nrows_def)
  have [transfer_rule]: "Mod_Type_Connect.HMA_I i ?i'"
       by (metis Mod_Type_Connect.HMA_I_def i min.strict_boundedE
        mod_type_class.to_nat_from_nat_id ncols_def)
  have i2: "i < min CARD('m) CARD('n)" using i unfolding nrows_def ncols_def by auto
  have "\<exists>u. u dvd 1 \<and> ?B $$(i,i) = u * ?B' $$ (i,i)"
  proof (rule Smith_normal_form_uniqueness[of _ "CARD('n)" "CARD('m)"])
    show "?P*?A*?Q=?B" using PAQ_B by (transfer', auto)
    show "Smith_normal_form_mat ?B" using SNF by (transfer', auto)
    show "?P'*?A*?Q'=?B'" using P'AQ'_B' by (transfer', auto)
    show "Smith_normal_form_mat ?B'" using SNF_B' by (transfer', auto)
    show "invertible_mat ?P" using inv_P by (transfer, auto)
    show "invertible_mat ?P'" using inv_P' by (transfer, auto)
    show "invertible_mat ?Q" using inv_Q by (transfer, auto)
    show "invertible_mat ?Q'" using inv_Q' by (transfer, auto)
  qed (insert i2, auto)
  hence "\<exists>u. u dvd 1 \<and> (index_hma B ?i ?i') = u * (index_hma B' ?i ?i')" by (transfer', rule)
  thus ?thesis unfolding index_hma_def by simp
qed

subsection \<open>Uniqueness fixing a complete set of non-associates\<close>

definition "Smith_normal_form_wrt A \<Q> = (
    (\<forall>a b. Mod_Type.to_nat a = Mod_Type.to_nat b \<and> Mod_Type.to_nat a + 1 < nrows A
            \<and> Mod_Type.to_nat b + 1 < ncols A \<longrightarrow> A $h a $h b dvd A $h (a+1) $h (b+1))
    \<and> isDiagonal A \<and> Complete_set_non_associates \<Q>
    \<and> (\<forall>a b. Mod_Type.to_nat a = Mod_Type.to_nat b \<and> Mod_Type.to_nat a < min (nrows A) (ncols A)
       \<and> Mod_Type.to_nat b < min (nrows A) (ncols A) \<longrightarrow> A $h a $h b \<in> \<Q>)
  )"

lemma Smith_normal_form_wrt_uniqueness_HOL_Analysis:
  fixes A::"'a::{idom,semiring_Gcd}^'m::mod_type^'n::mod_type"
  and P P'::"'a^'n::mod_type^'n::mod_type"
  and Q Q'::"'a^'m::mod_type^'m::mod_type"
  assumes
    (*PAQ = S with S in SNF and P,Q invertible matrices*)
    P: "invertible P"
    and Q: "invertible Q"
    and PAQ_S: "P**A**Q = S"
    and SNF: "Smith_normal_form_wrt S \<Q>"
    (*P'AQ' = S' with S' in SNF and P',Q' invertible matrices*)
    and P': "invertible P'"
    and Q': "invertible Q'"
    and P'AQ'_S': "P'**A**Q' = S'"
    and SNF_S': "Smith_normal_form_wrt S' \<Q>"
  shows "S = S'"
proof -
  have "S $h i $h j = S' $h i $h j" for i j
  proof (cases "Mod_Type.to_nat i \<noteq> Mod_Type.to_nat j")
  case True
    then show ?thesis using SNF SNF_S' unfolding Smith_normal_form_wrt_def isDiagonal_def by auto
  next
    case False
    let ?i = "Mod_Type.to_nat i"
    let ?j = "Mod_Type.to_nat j"
    have complete_set: "Complete_set_non_associates \<Q>"
      using SNF_S' unfolding Smith_normal_form_wrt_def by simp
    have ij: "?i = ?j" using False by auto
    show ?thesis
    proof (rule ccontr)
      assume d: "S $h i $h j \<noteq> S' $h i $h j"
      have n: "normalize (S $h i $h j) \<noteq> normalize (S' $h i $h j)"
      proof (rule in_Ass_not_associated[OF complete_set _ _ d])
        show "S $h i $h j \<in> \<Q>" using SNF unfolding Smith_normal_form_wrt_def
          by (metis False min_less_iff_conj mod_type_class.to_nat_less_card ncols_def nrows_def)
        show "S' $h i $h j \<in> \<Q>" using SNF_S' unfolding Smith_normal_form_wrt_def
          by (metis False min_less_iff_conj mod_type_class.to_nat_less_card ncols_def nrows_def)
      qed
      have "\<exists>u. u dvd 1 \<and> S $h i $h j = u * S' $h i $h j"
      proof -
        have "\<exists>u. u dvd 1 \<and> S $h Mod_Type.from_nat ?i $h Mod_Type.from_nat ?i
          = u * S' $h Mod_Type.from_nat ?i $h Mod_Type.from_nat ?i"
        proof (rule Smith_normal_form_uniqueness_HOL_Analysis[OF P Q PAQ_S _ P' Q' P'AQ'_S' _])
          show "Smith_normal_form S" and "Smith_normal_form S'"
            using SNF SNF_S' Smith_normal_form_def Smith_normal_form_wrt_def by blast+
          show "?i < min (nrows A) (ncols A)"
            by (metis ij min_less_iff_conj mod_type_class.to_nat_less_card ncols_def nrows_def)
        qed
        thus ?thesis using False by auto
      qed
      from this obtain u where "is_unit u" and "S $h i $h j = u * S' $h i $h j" by auto
      thus False using n
        by (simp add: normalize_1_iff normalize_mult)
    qed
  qed
  thus ?thesis by vector
qed


end