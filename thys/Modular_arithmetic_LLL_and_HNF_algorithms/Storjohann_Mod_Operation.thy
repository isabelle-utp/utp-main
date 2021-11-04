section \<open>Storjohann's Lemma 13\<close>

text \<open>This theory contains the result that one can always perform a mod-operation on
  the entries of the $d\mu$-matrix.\<close>

theory Storjohann_Mod_Operation
  imports 
    LLL_Basis_Reduction.LLL_Certification
    Signed_Modulo
begin 

lemma map_vec_map_vec: "map_vec f (map_vec g v) = map_vec (f o g) v" 
  by (intro eq_vecI, auto)

context semiring_hom
begin

(* TODO: move *)
lemma mat_hom_add: assumes A: "A \<in> carrier_mat nr nc" and B: "B \<in> carrier_mat nr nc"
  shows "mat\<^sub>h (A + B) = mat\<^sub>h A + mat\<^sub>h B"
  by (intro eq_matI, insert A B, auto simp: hom_add)
end

text \<open>We now start to prove lemma 13 of Storjohann's paper.\<close>
context
  fixes A I :: "'a :: field mat" and n :: nat
  assumes A: "A \<in> carrier_mat n n" 
  and det: "det A \<noteq> 0" 
  and I: "I = the (mat_inverse A)" 
begin
lemma inverse_via_det: "I * A = 1\<^sub>m n" "A * I = 1\<^sub>m n" "I \<in> carrier_mat n n" 
  "I = mat n n (\<lambda> (i,j). det (replace_col A (unit_vec n j) i) / det A)"
proof -
  from det_non_zero_imp_unit[OF A det] 
  have Unit: "A \<in> Units (ring_mat TYPE('a) n n)" .
  from mat_inverse(1)[OF A, of n] Unit I have "mat_inverse A = Some I" 
    by (cases "mat_inverse A", auto)
  from mat_inverse(2)[OF A this]
  show left: "I * A = 1\<^sub>m n" and right: "A * I = 1\<^sub>m n" and I: "I \<in> carrier_mat n n" 
    by blast+
  {
    fix i j
    assume i: "i < n" and j: "j < n" 
    from I i j have cI: "col I j $ i = I $$ (i,j)" by simp
    from j have uv: "unit_vec n j \<in> carrier_vec n" by auto
    from j I have col: "col I j \<in> carrier_vec n" by auto
    from col_mult2[OF A I j, unfolded right] j
    have "A *\<^sub>v col I j = unit_vec n j" by simp
    from cramer_lemma_mat[OF A col i, unfolded this cI]
    have "I $$ (i,j) = det (replace_col A (unit_vec n j) i) / det A" using det by simp
  }
  thus "I = mat n n (\<lambda> (i,j). det (replace_col A (unit_vec n j) i) / det A)"
    by (intro eq_matI, use I in auto)
qed

lemma matrix_for_singleton_entry: assumes i: "i < n" and 
  j: "j < n" 
  and Rdef: "R = mat n n ( \<lambda> ij. if ij = (i,j) then c :: 'a else 0)" 
shows "mat n n
   (\<lambda>(i', j'). if i' = i then c * det (replace_col A (unit_vec n j') j) / det A
       else 0) * A = R" 
proof -
  note I = inverse_via_det(3)
  have R: "R \<in> carrier_mat n n" unfolding Rdef by auto
  have "(R * I) * A = R * (I * A)" using I A R by auto
  also have "I * A = 1\<^sub>m n" unfolding inverse_via_det(1) ..
  also have "R * \<dots> = R" using R by simp
  also have "R * I = mat n n (\<lambda> (i',j'). row R i' \<bullet> col I j')"
    using I R unfolding times_mat_def by simp
  also have "\<dots> = mat n n ( \<lambda> (i',j'). if i' = i then c * I $$ (j, j') else 0)" 
    (is "mat n n ?f = mat n n ?g")
  proof -
    {
      fix i' j'
      assume i': "i' < n" and j': "j' < n" 
      have "?f (i',j') = ?g (i',j')" 
      proof (cases "i' = i")
        case False
        hence "row R i' = 0\<^sub>v n" unfolding Rdef using i'
          by (intro eq_vecI, auto simp: Matrix.row_def)
        thus ?thesis using False i' j' I by simp
      next
        case True
        hence "row R i' = c \<cdot>\<^sub>v unit_vec n j" unfolding Rdef using i' j' i j
          by (intro eq_vecI, auto simp: Matrix.row_def)
        with True show ?thesis using i' j' I j by simp
      qed
    }
    thus ?thesis by auto
  qed
  finally show ?thesis unfolding inverse_via_det(4) using j 
    by (auto intro!: arg_cong[of _ _ "\<lambda> x. x * A"])
qed
end

lemma (in gram_schmidt_fs_Rn) det_M_1: "det (M m) = 1" 
proof -
  have "det (M m) = prod_list (diag_mat (M m))" 
    by (rule det_lower_triangular[of m], auto simp: \<mu>.simps)
  also have "\<dots> = 1" 
    by (rule prod_list_neutral, auto simp: diag_mat_def \<mu>.simps)
  finally show ?thesis .
qed

context gram_schmidt_fs_int
begin
lemma assumes IM: "IM = the (mat_inverse (M m))" 
  shows inv_mu_lower_triangular: "\<And> k i. k < i \<Longrightarrow> i < m \<Longrightarrow> IM $$ (k, i) = 0"
  and inv_mu_diag: "\<And> k. k < m \<Longrightarrow> IM $$ (k, k) = 1"
  and d_inv_mu_integer: "\<And> i j. i < m \<Longrightarrow> j < m \<Longrightarrow> d i * IM $$ (i,j) \<in> \<int>" 
  and inv_mu_inverse: "IM * M m = 1\<^sub>m m" "M m * IM = 1\<^sub>m m" "IM \<in> carrier_mat m m" 
proof - 
  note * = inverse_via_det[OF M_dim(3) _ IM, unfolded det_M_1]
  from * show inv: "IM * M m = 1\<^sub>m m" "M m * IM = 1\<^sub>m m" 
    and IM: "IM \<in> carrier_mat m m"  by auto
  from * have IM_det: "IM = mat m m (\<lambda>(i, j). det (replace_col (M m) ((unit_vec m) j) i))" 
    by auto
  from matrix_equality have "IM * FF = IM * ((M m) * Fs)" by simp
  also have "\<dots> = (IM * M m) * Fs" using M_dim(3) IM Fs_dim(3)
    by (metis assoc_mult_mat)
  also have "\<dots> = Fs" unfolding inv using Fs_dim(3) by simp
  finally have equality: "IM * FF = Fs" .
  {
    fix i k
    assume i: "k < i" "i < m" 
    show "IM $$ (k, i) = 0" using i M_dim unfolding IM_det
      by (simp, subst det_lower_triangular[of m], auto simp: replace_col_def \<mu>.simps diag_mat_def)
  } note IM_lower_triag = this
  {
    fix k
    assume k: "k < m" 
    show "IM $$ (k,k) = 1" using k M_dim unfolding IM_det
      by (simp, subst det_lower_triangular[of m], auto simp: replace_col_def \<mu>.simps diag_mat_def
        intro!: prod_list_neutral)
  } note IM_diag_1 = this
  {
    fix k
    assume k: "k < m" 
    let ?f = "\<lambda> i. IM $$ (k, i) \<cdot>\<^sub>v fs ! i" 
    let ?sum = "M.sumlist (map ?f [0..<m])" 
    let ?sumk = "M.sumlist (map ?f [0..<k])" 
    have set: "set (map ?f [0..<m]) \<subseteq> carrier_vec n" using fs_carrier by auto
    hence sum: "?sum \<in> carrier_vec n" by simp
    from set k have setk: "set (map ?f [0..<k]) \<subseteq> carrier_vec n" by auto
    hence sumk: "?sumk \<in> carrier_vec n" by simp
    from sum have dim_sum: "dim_vec ?sum = n" by simp
    have "gso k = row Fs k" using k by auto
    also have "\<dots> = row (IM * FF) k" unfolding equality ..
    also have "IM * FF = mat m n (\<lambda> (i,j). row IM i  \<bullet> col FF j)" 
      unfolding times_mat_def using IM FF_dim by auto
    also have "row \<dots> k = vec n (\<lambda> j. row IM k \<bullet> col FF j)" 
      unfolding Matrix.row_def using IM FF_dim k by auto
    also have "\<dots> = vec n (\<lambda> j. \<Sum> i < m. IM $$ (k, i) * fs ! i $ j)" 
      by (intro eq_vecI, insert IM k, auto simp: scalar_prod_def Matrix.row_def intro!: sum.cong)
    also have "\<dots> = ?sum" 
      by (intro eq_vecI, insert IM, unfold dim_sum, subst sumlist_vec_index, 
        auto simp: o_def sum_list_sum_nth intro!: sum.cong)
    also have "[0..<m] = [0..<k] @ [k] @ [Suc k ..<m]" using k
      by (simp add: list_trisect)
    also have "M.sumlist (map ?f \<dots>) = ?sumk + 
      (?f k + M.sumlist (map ?f [Suc k ..< m]))" 
      unfolding map_append 
      by (subst M.sumlist_append; (subst M.sumlist_append)?, insert k fs_carrier, auto)
    also have "M.sumlist (map ?f [Suc k ..< m]) = 0\<^sub>v n" 
      by (rule sumlist_neutral, insert IM_lower_triag, auto)
    also have "IM $$ (k,k) = 1" using IM_diag_1[OF k] .
    finally have gso: "gso k = ?sumk + fs ! k"  using k by simp
    define b where "b = vec k (\<lambda> j. fs ! j \<bullet> fs ! k)" 
    {
      fix j
      assume jk: "j < k" 
      with k have j: "j < m" by auto
      have "fs ! j \<bullet> gso k = fs ! j \<bullet> (?sumk + fs ! k)" 
        unfolding gso by simp
      also have "fs ! j \<bullet> gso k = 0" using jk k
        by (simp add: fi_scalar_prod_gso gram_schmidt_fs.\<mu>.simps)
      also have "fs ! j \<bullet> (?sumk + fs ! k)
         = fs ! j \<bullet> ?sumk + fs ! j \<bullet> fs ! k" 
        by (rule scalar_prod_add_distrib[OF _ sumk], insert j k, auto)
      also have "fs ! j \<bullet> fs ! k = b $ j" unfolding b_def using jk by simp
      finally have "b $ j = - (fs ! j \<bullet> ?sumk)" by linarith
    } note b_index = this
    let ?x = "vec k (\<lambda> i. - IM $$ (k, i))" 
    have x: "?x \<in> carrier_vec k" by auto
    from k have km: "k \<le> m" by simp 
    have bGx: "b = Gramian_matrix fs k *\<^sub>v (vec k (\<lambda> i. - IM $$ (k, i)))" 
      unfolding Gramian_matrix_alt_alt_def[OF km]
    proof (rule eq_vecI; simp)
      fix i
      assume i: "i < k" 
      have "b $ i = - (\<Sum>x\<leftarrow>[0..<k]. fs ! i \<bullet> (IM $$ (k, x) \<cdot>\<^sub>v fs ! x))" 
        unfolding b_index[OF i]
        by (subst scalar_prod_right_sum_distrib, insert setk i k, auto simp: o_def)
      also have "\<dots> = vec k (\<lambda>j. fs ! i \<bullet> fs ! j) \<bullet> vec k (\<lambda>i. - IM $$ (k, i))" 
        by (subst (3) scalar_prod_def, insert i k, auto simp: o_def sum_list_sum_nth simp flip: sum_negf
          intro!: sum.cong)
      finally show "b $ i = vec k (\<lambda>j. fs ! i \<bullet> fs ! j) \<bullet> vec k (\<lambda>i. - IM $$ (k, i))" .
    qed (simp add: b_def)
    have G: "Gramian_matrix fs k \<in> carrier_mat k k" 
      unfolding Gramian_matrix_alt_alt_def[OF km] by simp
    from cramer_lemma_mat[OF G x, folded bGx Gramian_determinant_def]
    have "i < k \<Longrightarrow> 
      d k * IM $$ (k, i) = - det (replace_col (Gramian_matrix fs k) (vec k (\<lambda> j. fs ! j \<bullet> fs ! k)) i)" 
      for i unfolding b_def by simp
  } note IM_lower_values = this
  {
    fix i j
    assume i: "i < m" and j: "j < m" 
    from i have im: "i \<le> m" by auto
    consider (1) "j < i" | (2) "j = i" | (3) "i < j" by linarith
    thus "d i * IM $$ (i,j) \<in> \<int>"
    proof cases
      case 1
      show ?thesis unfolding IM_lower_values[OF i 1] replace_col_def Gramian_matrix_alt_alt_def[OF im]
        by (intro Ints_minus Ints_det, insert i j, auto intro!: Ints_scalar_prod[of _ n] fs_int)
    next
      case 3
      show ?thesis unfolding IM_lower_triag[OF 3 j] by simp
    next
      case 2
      show ?thesis unfolding IM_diag_1[OF i] 2 using i unfolding Gramian_determinant_def
         Gramian_matrix_alt_alt_def[OF im]
        by (intro Ints_mult Ints_det, insert i j, auto intro!: Ints_scalar_prod[of _ n] fs_int)
    qed 
  }
qed

definition inv_mu_ij_mat :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int mat" where
 "inv_mu_ij_mat i j c = (let
    B = mat m m (\<lambda> ij. if ij = (i,j) then c else 0);
    C = mat m m (\<lambda> (i,j). the_inv (of_int :: _ \<Rightarrow> 'a) (d i * the (mat_inverse (M m)) $$ (i,j)))
   in B * C + 1\<^sub>m m)" 

lemma inv_mu_ij_mat: assumes i: "i < m" and ji: "j < i" 
  shows 
(* Effect on \<mu> *)
   "map_mat of_int (inv_mu_ij_mat i j c) * M m =
    mat m m (\<lambda>ij. if ij = (i, j) then of_int c * d j else 0) + M m" (* only change value of \<mu>_ij *)
(* Effect on A *)
  "A \<in> carrier_mat m n \<Longrightarrow> c mod p = 0 \<Longrightarrow> map_mat (\<lambda> x. x mod p) (inv_mu_ij_mat i j c * A) = 
    (map_mat (\<lambda> x. x mod p) A)" (* no change (mod p) *)
(* The transformation-matrix is ... *)
  "inv_mu_ij_mat i j c \<in> carrier_mat m m" (* ... of dimension m*m *)
  "i' < j' \<Longrightarrow> j' < m \<Longrightarrow> inv_mu_ij_mat i j c $$ (i',j') = 0" (* ... lower triangular *)
  "k < m \<Longrightarrow> inv_mu_ij_mat i j c $$ (k,k) = 1" (* ... with diagonal all 1 *)  
proof -
  obtain IM where IM: "IM = the (mat_inverse (M m))" by auto
  let ?oi = "of_int :: _ \<Rightarrow> 'a" 
  let ?C = "mat m m (\<lambda> ij. if ij = (i,j) then ?oi c else 0)" 
  let ?D = "mat m m (\<lambda> (i,j). d i * IM $$ (i,j))" 
  have oi: "inj ?oi" unfolding inj_on_def by auto
  have C: "?C \<in> carrier_mat m m" by auto
  from i ji have j: "j < m" by auto
  from j have jm: "{0..<m} = {0..<j} \<union> {j} \<union> {Suc j..<m}" by auto
  note IM_props = d_inv_mu_integer[OF IM] inv_mu_inverse[OF IM]
  have mat_oi: "map_mat ?oi (inv_mu_ij_mat i j c) = ?C * ?D + 1\<^sub>m m" (is "?MM = _")
    unfolding inv_mu_ij_mat_def Let_def IM[symmetric]
    apply (subst of_int_hom.mat_hom_add, force, force)
    apply (rule arg_cong2[of _ _ _ _ "(+)"])
     apply (subst of_int_hom.mat_hom_mult, force, force)
     apply (rule arg_cong2[of _ _ _ _ "(*)"])
      apply force
     apply (rule eq_matI, (auto)[3], goal_cases)
  proof -
    case (1 i j)
    from IM_props(1)[OF 1]
    show ?case unfolding Ints_def using the_inv_f_f[OF oi] by auto
  qed auto
  have "map_mat ?oi (inv_mu_ij_mat i j c) * M m = (?C * ?D) * M m + M m" unfolding mat_oi
    by (subst add_mult_distrib_mat[of _ m m], auto)
  also have "(?C * ?D) * M m = ?C * (?D * M m)" 
    by (rule assoc_mult_mat, auto)
  also have "?D = mat m m (\<lambda> (i,j). if i = j then d j else 0) * IM" (is "_ = ?E * _")
  proof (rule eq_matI, insert IM_props(4), auto simp: scalar_prod_def, goal_cases)
    case (1 i j)
    hence id: "{0..<m} = {0..<i} \<union> {i} \<union> {Suc i ..<m}" 
      by (auto simp add: list_trisect)
    show ?case unfolding id
      by (auto simp: sum.union_disjoint)
  qed
  also have "\<dots> * M m = ?E * (IM * M m)" 
    by (rule assoc_mult_mat[of _ m m], insert IM_props, auto)
  also have "IM * M m = 1\<^sub>m m" by fact
  also have "?E * 1\<^sub>m m = ?E" by simp
  also have "?C * ?E = mat m m (\<lambda> ij. if ij = (i,j) then ?oi c * d j else 0)" 
    by (rule eq_matI, auto simp: scalar_prod_def, auto simp: jm sum.union_disjoint)
  finally show "map_mat ?oi (inv_mu_ij_mat i j c) * M m = 
    mat m m (\<lambda> ij. if ij = (i,j) then ?oi c * d j else 0) + M m" .
  show carr: "inv_mu_ij_mat i j c \<in> carrier_mat m m"
    unfolding inv_mu_ij_mat_def by auto
  {
    assume k: "k < m" 
    have "of_int (inv_mu_ij_mat i j c $$ (k,k)) = ?MM $$ (k,k)" 
      using carr k by auto
    also have "\<dots> = (?C * ?D) $$ (k,k) + 1" unfolding mat_oi using k by simp
    also have "(?C * ?D) $$ (k,k) = 0" using k
      by (auto simp: scalar_prod_def, auto simp: jm sum.union_disjoint 
        inv_mu_lower_triangular[OF IM ji i])
    finally show "inv_mu_ij_mat i j c $$ (k,k) = 1" by simp
  }
  {
    assume ij': "i' < j'" "j' < m"  
    have "of_int (inv_mu_ij_mat i j c $$ (i',j')) = ?MM $$ (i',j')" 
      using carr ij' by auto
    also have "\<dots> = (?C * ?D) $$ (i',j')" unfolding mat_oi using ij' by simp
    also have "(?C * ?D) $$ (i',j') = (if i' = i then ?oi c * (d j * IM $$ (j, j')) else 0)" 
      using ij' i j by (auto simp: scalar_prod_def, auto simp: jm sum.union_disjoint)
    also have "\<dots> = 0" using inv_mu_lower_triangular[OF IM _ ij'(2), of j] ij' i ji by auto
    finally show "inv_mu_ij_mat i j c $$ (i',j') = 0" by simp
  }
  {
    assume A: "A \<in> carrier_mat m n" and c: "c mod p = 0" 
    let ?mod = "map_mat (\<lambda> x. x mod p)" 
    let ?C = "mat m m (\<lambda> ij. if ij = (i,j) then c else 0)" 
    let ?D = "mat m m (\<lambda> ij. if ij = (i,j) then 1 else (0 :: int))" 
    define B where "B = mat m m (\<lambda> (i,j). the_inv ?oi (d i * the (mat_inverse (M m)) $$ (i,j)))" 
    have B: "B \<in> carrier_mat m m" unfolding B_def by auto
    define BA where "BA = B * A" 
    have BA: "BA \<in> carrier_mat m n" unfolding BA_def using A B by auto
    define DBA where "DBA = ?D * BA" 
    have DBA: "DBA \<in> carrier_mat m n" unfolding DBA_def using BA by auto
    have "?mod (inv_mu_ij_mat i j c * A) = 
     ?mod ((?C * B + 1\<^sub>m m) * A)" 
      unfolding inv_mu_ij_mat_def B_def by simp
    also have "(?C * B + 1\<^sub>m m) * A = ?C * B * A + A" 
      by (subst add_mult_distrib_mat, insert A B, auto)
    also have "?C * B * A = ?C * BA" 
      unfolding BA_def
      by (rule assoc_mult_mat, insert A B, auto)
    also have "?C = c \<cdot>\<^sub>m ?D" 
      by (rule eq_matI, auto)
    also have "\<dots> * BA = c \<cdot>\<^sub>m DBA" using BA unfolding DBA_def by auto
    also have "?mod (\<dots> + A) = ?mod A" 
      by (rule eq_matI, insert DBA A c, auto simp: mult.assoc) 
    finally show "?mod (inv_mu_ij_mat i j c * A) = ?mod A" .
  }
qed   
end
 
lemma Gramian_determinant_of_int: assumes fs: "set fs \<subseteq> carrier_vec n" 
  and j: "j \<le> length fs" 
shows "of_int (gram_schmidt.Gramian_determinant n fs j)
  = gram_schmidt.Gramian_determinant n (map (map_vec rat_of_int) fs) j" 
proof -
  from j have j: "k < j \<Longrightarrow> k < length fs" for k by auto
  show ?thesis
  unfolding gram_schmidt.Gramian_determinant_def
  by (subst of_int_hom.hom_det[symmetric], rule arg_cong[of _ _ det],
      unfold gram_schmidt.Gramian_matrix_def Let_def, subst of_int_hom.mat_hom_mult, force, force,
      unfold map_mat_transpose[symmetric],
      rule arg_cong2[of _ _ _ _ "\<lambda> x y. x * y\<^sup>T"], insert fs[unfolded set_conv_nth] 
      j, (fastforce intro!: eq_matI)+)
qed

context LLL
begin

(* this lemma might also be useful for swap/add-operation *)
lemma multiply_invertible_mat: assumes lin: "lin_indep fs" 
  and len: "length fs = m" 
  and A: "A \<in> carrier_mat m m" 
  and A_invertible: "\<exists> B. B \<in> carrier_mat m m \<and> B * A = 1\<^sub>m m" 
  and fs'_prod: "fs' = Matrix.rows (A * mat_of_rows n fs)" 
shows "lattice_of fs' = lattice_of fs" 
  "lin_indep fs'" 
  "length fs' = m" 
proof -
  let ?Mfs = "mat_of_rows n fs" 
  let ?Mfs' = "mat_of_rows n fs'" 
  from A_invertible obtain B where B: "B \<in> carrier_mat m m" and inv: "B * A = 1\<^sub>m m" by auto
  from lin have fs: "set fs \<subseteq> carrier_vec n" unfolding gs.lin_indpt_list_def by auto
  with len have Mfs: "?Mfs \<in> carrier_mat m n" by auto
  from A Mfs have prod: "A * ?Mfs \<in> carrier_mat m n" by auto
  hence fs': "length fs' = m" "set fs' \<subseteq> carrier_vec n" unfolding fs'_prod
    by (auto simp: Matrix.rows_def Matrix.row_def)  
  have Mfs_prod': "?Mfs' = A * ?Mfs" 
    unfolding arg_cong[OF fs'_prod, of "mat_of_rows n"]
    by (intro eq_matI, auto simp: mat_of_rows_def)
  have "B * ?Mfs' = B * (A * ?Mfs)" 
    unfolding Mfs_prod' by simp
  also have "\<dots> = (B * A) * ?Mfs"
    by (subst assoc_mult_mat[OF _ A Mfs], insert B, auto)
  also have "B * A = 1\<^sub>m m" by fact
  also have "\<dots> * ?Mfs = ?Mfs" using Mfs by auto
  finally have Mfs_prod: "?Mfs = B * ?Mfs'" ..  
  interpret LLL: LLL_with_assms n m fs 2
    by (unfold_locales, auto simp: len lin)
  from LLL.LLL_change_basis[OF fs'(2,1) B A Mfs_prod Mfs_prod']
  show latt': "lattice_of fs' = lattice_of fs" and lin': "gs.lin_indpt_list (RAT fs')" 
    and len': "length fs' = m" 
    by (auto simp add: LLL_with_assms_def)
qed

text \<open>This is the key lemma.\<close>
lemma change_single_element: assumes lin: "lin_indep fs" 
  and len: "length fs = m" 
  and i: "i < m" and ji: "j < i"  
  and A: "A = gram_schmidt_fs_int.inv_mu_ij_mat n (RAT fs)"    \<comment> \<open>the transformation matrix A\<close>
  and fs'_prod: "fs' = Matrix.rows (A i j c * mat_of_rows n fs)" \<comment> \<open>fs' is the new basis\<close>
  and latt: "lattice_of fs = L" 
shows "lattice_of fs' = L"
  "c mod p = 0 \<Longrightarrow> map (map_vec (\<lambda> x. x mod p)) fs' = map (map_vec (\<lambda> x. x mod p)) fs" 
  "lin_indep fs'" 
  "length fs' = m" 
  "\<And> k. k < m \<Longrightarrow> gso fs' k = gso fs k" 
  "\<And> k. k \<le> m \<Longrightarrow> d fs' k = d fs k" 
  "i' < m \<Longrightarrow> j' < m \<Longrightarrow> 
    \<mu> fs' i' j' = (if (i',j') = (i,j) then rat_of_int (c * d fs j) + \<mu> fs i' j' else \<mu> fs i' j')" 
  "i' < m \<Longrightarrow> j' < m \<Longrightarrow> 
    d\<mu> fs' i' j' = (if (i',j') = (i,j) then c * d fs j * d fs (Suc j) + d\<mu> fs i' j' else d\<mu> fs i' j')" 
proof -
  let ?A = "A i j c" 
  let ?Mfs = "mat_of_rows n fs" 
  let ?Mfs' = "mat_of_rows n fs'" 
  from lin have fs: "set fs \<subseteq> carrier_vec n" unfolding gs.lin_indpt_list_def by auto
  with len have Mfs: "?Mfs \<in> carrier_mat m n" by auto
  interpret gsi: gram_schmidt_fs_int n "RAT fs"
    rewrites "gsi.inv_mu_ij_mat = A" using lin unfolding A
    by (unfold_locales, insert lin[unfolded gs.lin_indpt_list_def], auto simp: set_conv_nth)
  note A = gsi.inv_mu_ij_mat[unfolded length_map len, OF i ji, where c = c]
  from A(3) Mfs have prod: "?A * ?Mfs \<in> carrier_mat m n" by auto
  hence fs': "length fs' = m" "set fs' \<subseteq> carrier_vec n" unfolding fs'_prod
    by (auto simp: Matrix.rows_def Matrix.row_def)  
  have Mfs_prod': "?Mfs' = ?A * ?Mfs" 
    unfolding arg_cong[OF fs'_prod, of "mat_of_rows n"]
    by (intro eq_matI, auto simp: mat_of_rows_def)
  have detA: "det ?A = 1" 
    by (subst det_lower_triangular[OF A(4) A(3)], insert A, auto intro!: prod_list_neutral 
      simp: diag_mat_def)
  have "\<exists> B. B \<in> carrier_mat m m \<and> B * ?A = 1\<^sub>m m" 
    by (intro exI[of _ "adj_mat ?A"], insert adj_mat[OF A(3)], auto simp: detA)
  from multiply_invertible_mat[OF lin len A(3) this fs'_prod] latt
  show latt': "lattice_of fs' = L" and lin': "gs.lin_indpt_list (RAT fs')" 
    and len': "length fs' = m" by auto
  interpret LLL: LLL_with_assms n m fs 2
    by (unfold_locales, auto simp: len lin)
  interpret fs: fs_int_indpt n fs
    by (standard, auto simp: lin)
  interpret fs': fs_int_indpt n fs'
    by (standard, auto simp: lin')
  {
    assume c: "c mod p = 0" 
    have id: "rows (map_mat f A) = map (map_vec f) (rows A)" for f A
      unfolding rows_def by auto
    have rows_id: "set fs \<subseteq> carrier_vec n \<Longrightarrow> rows (mat_of_rows n fs) = fs" for fs
      unfolding mat_of_rows_def rows_def 
      by (force simp: Matrix.row_def set_conv_nth intro!: nth_equalityI)
    from A(2)[OF Mfs c]
    have "rows (map_mat (\<lambda>x. x mod p) ?Mfs') = rows (map_mat (\<lambda>x. x mod p) ?Mfs)" unfolding Mfs_prod'
      by simp
    from this[unfolded id rows_id[OF fs] rows_id[OF fs'(2)]]
    show "map (map_vec (\<lambda> x. x mod p)) fs' = map (map_vec (\<lambda> x. x mod p)) fs" .
  }
  {
    define B where "B = ?A" 
    have gs_eq: "k < m \<Longrightarrow> gso fs' k = gso fs k" for k
    proof(induct rule: nat_less_induct)
      case (1 k)
      then show ?case 
      proof(cases "k = 0")
        case True
        then show ?thesis 
        proof -
          have "row ?Mfs' 0 = row ?Mfs 0"
          proof -
            have 2: "0\<in> {0..<m}" and 3: "{1..<m} = {0..<m} - {0}" 
              and 4: "finite {0..<m}" using 1 by auto
            have "row ?Mfs' 0 = vec n (\<lambda>j. row B 0 \<bullet> col ?Mfs j)" 
              using row_mult A(3) Mfs 1 Mfs_prod' unfolding B_def by simp
            also have "\<dots> = vec n (\<lambda>j. (\<Sum>l\<in>{0..<m}. B $$ (0, l) * ?Mfs $$ (l, j)))"
              using Mfs A(3) len 1 B_def unfolding scalar_prod_def by auto
            also have "\<dots> = vec n (\<lambda>j. B $$ (0, 0) * ?Mfs $$ (0, j) + 
              (\<Sum>l\<in>{1..<m}. B $$ (0, l) * ?Mfs $$ (l, j)))"
              using Groups_Big.comm_monoid_add_class.sum.remove[OF 4 2] 3
              by (simp add: \<open>\<And>g. sum g {0..<m} = g 0 + sum g ({0..<m} - {0})\<close>)
            also have "\<dots> = row ?Mfs 0" 
              using A(4-) 1 unfolding B_def[symmetric] by (simp add: row_def)
            finally show ?thesis by (simp add: B_def Mfs_prod')
          qed
          then show ?thesis using True 1 fs'.f_carrier fs.f_carrier 
            fs'.gs.fs0_gso0 len' len gsi.fs0_gso0 by auto
        qed
      next
        case False
        then show ?thesis
        proof -
          have gso0kcarr: "gsi.gso ` {0 ..<k} \<subseteq> carrier_vec n"
            using 1(2) gsi.gso_carrier len by auto
          hence gsospancarr: "gs.span(gsi.gso ` {0 ..<k}) \<subseteq> carrier_vec n " 
            using span_is_subset2 by auto

          have fs'_gs_diff_span: 
            "(RAT fs') !  k - fs'.gs.gso k \<in> gs.span (gsi.gso ` {0 ..<k})"
          proof -
            define gs'sum where "gs'sum =
              gs.M.sumlist (map (\<lambda>ja. fs'.gs.\<mu> k ja \<cdot>\<^sub>v fs'.gs.gso ja) [0..<k])"
            define gssum where "gssum = 
              gs.M.sumlist (map (\<lambda>ja. fs'.gs.\<mu> k ja \<cdot>\<^sub>v gsi.gso ja) [0..<k])"
            have "set (map (\<lambda>ja. fs'.gs.\<mu> k ja \<cdot>\<^sub>v gsi.gso ja) [0..<k]) 
              \<subseteq> gs.span(gsi.gso ` {0 ..<k})" using 1(2) gs.span_mem gso0kcarr
              by auto
            hence gssumspan: "gssum \<in> gs.span(gsi.gso ` {0 ..<k})"
              using atLeastLessThan_iff gso0kcarr imageE set_map set_upt 
                vec_space.sumlist_in_span 
              unfolding gssum_def by (smt subsetD)
            hence gssumcarr: "gssum \<in> carrier_vec n" 
              using gsospancarr gssum_def by blast
            have sumid: "gs'sum = gssum"
            proof -
              have "map (\<lambda>ja. fs'.gs.\<mu> k ja \<cdot>\<^sub>v fs'.gs.gso ja) [0..<k] =
                map (\<lambda>ja. fs'.gs.\<mu> k ja \<cdot>\<^sub>v gsi.gso ja) [0..<k]"
                using 1 by simp
              thus ?thesis unfolding gs'sum_def gssum_def by argo
            qed
            have "(RAT fs') !  k = fs'.gs.gso k + gssum" 
              using fs'.gs.fs_by_gso_def len' False 1 sumid 
              unfolding gs'sum_def by auto
            hence "(RAT fs') !  k - fs'.gs.gso k = gssum" 
              using gssumcarr 1(2) len' by auto
            thus ?thesis using gssumspan by simp
          qed

          define v2 where "v2 = sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..< k])"
          have v2carr: "v2 \<in> carrier_vec n" 
          proof -
            have "set (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..< k]) \<subseteq> carrier_vec n"
              using len 1(2) fs.f_carrier by auto
            thus ?thesis unfolding v2_def by simp
          qed
          define ratv2 where "ratv2 = (map_vec rat_of_int v2)"
          have ratv2carr: "ratv2 \<in> carrier_vec n" 
            unfolding ratv2_def using v2carr by simp
          have fs'id: "(RAT fs') ! k = (RAT fs) ! k + ratv2"
          proof -
            have zkm: "[0..<m] = [0..<(Suc k)] @ [(Suc k)..<m]" using 1(2) 
              by (metis Suc_lessI append_Nil2 upt_append upt_rec zero_less_Suc)
            have prep: "set (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<m]) \<subseteq> carrier_vec n" 
              using len fs.f_carrier by auto

            have "fs' ! k = vec n (\<lambda>j. row B k \<bullet> col ?Mfs j)"
              using 1(2) Mfs B_def A(3) fs'_prod by simp
            also have "\<dots> = sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<m])"
            proof -
              {
                fix i
                assume i: "i < n"
                have "(vec n (\<lambda>j. row B k \<bullet> col ?Mfs j)) $ i = row B k \<bullet> col ?Mfs i" 
                  using i by auto
                also have "\<dots> = (\<Sum>j = 0..<m. B $$ (k, j) * ?Mfs $$ (j,i))" 
                  using A(3) unfolding B_def[symmetric] 
                  by (smt 1(2) Mfs R.finsum_cong' i atLeastLessThan_iff carrier_matD
                      dim_col index_col index_row(1) scalar_prod_def)
                also have "\<dots> = (\<Sum>j = 0..<m. B $$ (k, j) * (fs ! j $ i))"
                  by (metis (no_types, lifting) R.finsum_cong' atLeastLessThan_iff i
                      len mat_of_rows_index)
                also have "\<dots> = 
                  (\<Sum>j = 0..<m. (map (\<lambda>ja.  B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<m]) ! j $ i)"
                proof -
                  have "\<forall>j<m. \<forall>i<n. B $$ (k, j) * (fs ! j $ i) = 
                    (map (\<lambda>ja.  B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<m]) ! j $ i" 
                    using 1(2) i A(3) len fs.f_carrier
                    unfolding B_def[symmetric] by auto
                  then show ?thesis using i by auto
                qed
                also have "\<dots> = sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<m]) $ i"
                  using sumlist_nth i fs.f_carrier carrier_vecD len by simp
                finally have "(vec n (\<lambda>j. row B k \<bullet> col ?Mfs j)) $ i =
                  sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<m]) $ i" by auto
              }
              then show ?thesis using fs.f_carrier len dim_sumlist by auto
            qed
            also have "\<dots> = sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) 
              ([0..<(Suc k)] @ [(Suc k)..<m]))" 
              using zkm by simp
            also have "\<dots> = sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<(Suc k)]) +
              sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [(Suc k)..<m])"
              (is "\<dots> = ?L2 + ?L3")
              using fs.f_carrier len dim_sumlist sumlist_append prep zkm by auto
            also have "?L3 = 0\<^sub>v n"
              using A(4) fs.f_carrier len sumlist_nth carrier_vecD sumlist_carrier 
                prep zkm unfolding B_def[symmetric] by auto
            also have "?L2 = sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<k]) +
              B $$ (k, k) \<cdot>\<^sub>v fs ! k" using prep zkm sumlist_snoc by simp
            also have "\<dots> = sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<k]) + fs ! k"
              using A(5) 1(2) unfolding B_def[symmetric] by simp
            finally have "fs' ! k = fs ! k + 
              sumlist (map (\<lambda>ja. B $$ (k, ja) \<cdot>\<^sub>v fs ! ja) [0..<k])"
              using prep zkm by (simp add: M.add.m_comm)
            then have "fs' !  k = fs !  k + v2" unfolding v2_def by simp
            then show ?thesis using v2carr 1(2) len len' ratv2_def by force
          qed
          have ratv2span: "ratv2 \<in> gs.span (gsi.gso ` {0 ..<k})" 
          proof -
            have rat: "ratv2 = gs.M.sumlist
              (map (\<lambda>j. of_int (B $$ (k, j)) \<cdot>\<^sub>v (RAT fs) ! j) [0..<k])"
            proof -
              have "set (map (\<lambda>j. of_int (B $$ (k, j)) \<cdot>\<^sub>v (RAT fs) ! j) [0..<k]) 
                \<subseteq> carrier_vec n"
                using fs.f_carrier 1(2) len by auto
              hence carr: "gs.M.sumlist 
                (map (\<lambda>j. of_int (B $$ (k, j)) \<cdot>\<^sub>v (RAT fs) ! j) [0..<k]) \<in> carrier_vec n"
                by auto
              have "set (map (\<lambda>j. B $$ (k, j) \<cdot>\<^sub>v fs ! j) [0..<k]) \<subseteq> carrier_vec n"
                using fs.f_carrier 1(2) len by auto
              hence "\<And>i j. i < n \<Longrightarrow> j < k \<Longrightarrow> of_int ((B $$ (k, j) \<cdot>\<^sub>v fs ! j) $ i)
                = (of_int (B $$ (k, j)) \<cdot>\<^sub>v (RAT fs) ! j) $ i"
                using 1(2) len by fastforce
              hence "\<And>i. i < n \<Longrightarrow> ratv2 $ i = gs.M.sumlist
                (map (\<lambda>j. (of_int (B $$ (k, j)) \<cdot>\<^sub>v (RAT fs) ! j)) [0..<k]) $ i"
                using fs.f_carrier 1(2) len v2carr gs.sumlist_nth sumlist_nth 
                  ratv2_def v2_def by simp
              then show ?thesis using ratv2carr carr by auto
            qed
            have "\<And>i. i < k \<Longrightarrow> (RAT fs) ! i = 
              gs.M.sumlist (map (\<lambda> j. gsi.\<mu> i j \<cdot>\<^sub>v gsi.gso j) [0 ..< Suc i])"
              using gsi.fi_is_sum_of_mu_gso len 1(2) by auto
            moreover have "\<And>i. i < k \<Longrightarrow> (\<lambda> j. gsi.\<mu> i j \<cdot>\<^sub>v gsi.gso j) ` {0 ..< Suc i}
              \<subseteq> gs.span (gsi.gso ` {0 ..<k})"
              using gs.span_mem gso0kcarr by auto
            ultimately have "\<And>i. i < k \<Longrightarrow> (RAT fs) ! i \<in> gs.span (gsi.gso ` {0 ..<k})"
              using gso0kcarr set_map set_upt vec_space.sumlist_in_span subsetD by smt
            then show ?thesis using rat atLeastLessThan_iff set_upt gso0kcarr imageE 
              set_map gs.smult_in_span vec_space.sumlist_in_span by smt
          qed
          have fs_gs_diff_span:
            "(RAT fs) !  k - fs'.gs.gso k \<in> gs.span (gsi.gso ` {0 ..<k})"
          proof -
            from fs'_gs_diff_span obtain v3 where sp: "v3 \<in> gs.span (gsi.gso ` {0 ..<k})"
              and eq: "(RAT fs) ! k - fs'.gs.gso k = v3 - ratv2" 
              using fs'.gs.gso_carrier len' 1(2) ratv2carr fs'id by fastforce
            have "v3+(-ratv2) \<in> gs.span(gsi.gso ` {0 ..<k})"
              by (metis sp gs.span_add1 gso0kcarr gram_schmidt.inv_in_span 
                  gso0kcarr ratv2span)
            moreover have "v3+(-ratv2) = v3-ratv2" using ratv2carr by auto
            ultimately have "v3 - ratv2 \<in> gs.span (gsi.gso ` {0 ..<k})" by simp
            then show ?thesis using eq by auto
          qed
          {
            fix i
            assume i: "i < k"
            hence "fs'.gs.gso k \<bullet> fs'.gs.gso i = 0" using 1(2) fs'.gs.orthogonal len' by auto
            hence "fs'.gs.gso k \<bullet> gsi.gso i = 0" using 1 i by simp
          }
          hence "\<And>x. x \<in> gsi.gso ` {0..<k} \<Longrightarrow> fs'.gs.gso k \<bullet> x = 0" by auto

          then show ?thesis
            using gsi.oc_projection_unique len len' fs_gs_diff_span 1(2) by auto
        qed
      qed
    qed

    have "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> \<mu> fs' i' j' = 
      (map_mat of_int (A i j c) * gsi.M m) $$ (i',j')" and
      "\<And> k. k < m \<Longrightarrow> gso fs' k = gso fs k"
    proof -
      define rB where "rB = map_mat rat_of_int B"
      have rBcarr: "rB \<in> carrier_mat m m" using A(3) unfolding rB_def B_def by simp
      define rfs where "rfs = mat_of_rows n (RAT fs)"
      have rfscarr: "rfs \<in> carrier_mat m n" using Mfs unfolding rfs_def by simp

      {
        fix i'
        fix j'
        assume i': "i' < m"
        assume j': "j' < m"
        have prep: 
          "of_int_hom.vec_hom (row (B * mat_of_rows n fs) i') = row (rB * rfs) i'" 
          using len i' B_def A(3) rB_def rfs_def by (auto simp: scalar_prod_def)
        have prep2: "row (rB * rfs) i' = vec n (\<lambda>l. row rB i' \<bullet> col rfs l)"
          using len fs.f_carrier i' B_def A(3) scalar_prod_def rB_def
          unfolding rfs_def by auto
        have prep3: "(vec m (\<lambda> j1. row rfs j1 \<bullet> gsi.gso j' / \<parallel>gsi.gso j'\<parallel>\<^sup>2)) =
          (vec m (\<lambda> j1. (gsi.M m) $$ (j1, j')))"
        proof -
          {
            fix x y
            assume x: "x < m" and y: "y < m"
            have "(gsi.M m) $$ (x,y) = (if y < x then map of_int_hom.vec_hom fs ! x 
              \<bullet> fs'.gs.gso y / \<parallel>fs'.gs.gso y\<parallel>\<^sup>2 else if x = y then 1 else 0)" 
              using gsi.\<mu>.simps x y j' len gs_eq gsi.M_index by auto
            hence "row rfs x \<bullet> gsi.gso y / \<parallel>gsi.gso y\<parallel>\<^sup>2 = (gsi.M m) $$ (x,y)"
              unfolding rfs_def 
              by (metis carrier_matD(1) divide_eq_eq fs'.gs.\<beta>_zero fs'.gs.gso_norm_beta 
                  gs_eq gsi.\<mu>.simps gsi.fi_scalar_prod_gso gsi.fs_carrier len len' 
                  length_map nth_rows rfs_def rfscarr rows_mat_of_rows x y)
          }
          then show ?thesis using j' by auto
        qed
        have prep4: "(1 / \<parallel>gsi.gso j'\<parallel>\<^sup>2) \<cdot>\<^sub>v (vec m (\<lambda>j1. row rfs j1 \<bullet> gsi.gso j')) =
          (vec m (\<lambda>j1. row rfs j1 \<bullet> gsi.gso j' / \<parallel>gsi.gso j'\<parallel>\<^sup>2))" by auto

        have "map of_int_hom.vec_hom fs' ! i' \<bullet> fs'.gs.gso j' / \<parallel>fs'.gs.gso j'\<parallel>\<^sup>2
           = map of_int_hom.vec_hom fs' ! i' \<bullet> gsi.gso j' / \<parallel>gsi.gso j'\<parallel>\<^sup>2"
          using gs_eq j' by simp
        also have "\<dots> = row (rB * rfs) i' \<bullet> gsi.gso j' / \<parallel>gsi.gso j'\<parallel>\<^sup>2"
          using prep i' len' unfolding rB_def B_def by (simp add: fs'_prod)
        also have "\<dots> = 
          (vec n (\<lambda>l. row rB i' \<bullet> col rfs l)) \<bullet> gsi.gso j' / \<parallel>gsi.gso j'\<parallel>\<^sup>2"
          using prep2 by auto
        also have "vec n (\<lambda>l. row rB i' \<bullet> col rfs l) = 
            (vec n (\<lambda>l. (\<Sum>j1=0..<m. (row rB i') $ j1 * (col rfs l) $ j1)))"
          using gsi.gso_carrier
          by (metis (no_types) carrier_matD(1) col_def dim_vec rfscarr scalar_prod_def)
        also have "\<dots> = 
            (vec n (\<lambda>l. (\<Sum>j1=0..<m. rB $$ (i', j1) * rfs $$ (j1, l))))" 
          using rBcarr rfscarr i' by auto
        also have "\<dots> \<bullet> gsi.gso j' = 
            (\<Sum>j2=0..<n. (vec n 
            (\<lambda>l. (\<Sum>j1=0..<m. rB $$ (i', j1) * rfs $$ (j1, l)))) $ j2 * (gsi.gso j') $ j2)"
          using gsi.gso_carrier len j' scalar_prod_def 
          by (smt gs.R.finsum_cong' gsi.gso_dim length_map)
        also have "\<dots> = (\<Sum>j2=0..<n.
            (\<Sum>j1=0..<m. rB $$ (i', j1) * rfs $$ (j1, j2)) * (gsi.gso j') $ j2)"
          using gsi.gso_carrier len j' by simp
        also have "\<dots> = (\<Sum>j2=0..<n. (\<Sum>j1=0..<m.
            rB $$ (i', j1) * rfs $$ (j1, j2) * (gsi.gso j') $ j2))" 
          by (smt gs.R.finsum_cong' sum_distrib_right)
        also have "\<dots> = (\<Sum>j1=0..<m. (\<Sum>j2=0..<n.
            rB $$ (i', j1) * rfs $$ (j1, j2) * (gsi.gso j') $ j2))"
          using sum.swap by auto
        also have "\<dots> = (\<Sum>j1=0..<m. rB $$ (i', j1) * (\<Sum>j2=0..<n. 
            rfs $$ (j1, j2) * (gsi.gso j') $ j2))"
          using gs.R.finsum_cong' sum_distrib_left by (smt gs.m_assoc)
        also have "\<dots> = row rB i' \<bullet> (vec m (\<lambda> j1. (\<Sum>j2=0..<n.
            rfs $$ (j1, j2) * (gsi.gso j') $ j2)))" 
          using rBcarr rfscarr i' scalar_prod_def
          by (smt atLeastLessThan_iff carrier_matD(1) carrier_matD(2) dim_vec 
              gs.R.finsum_cong' index_row(1) index_vec)
        also have "(vec m (\<lambda> j1. (\<Sum>j2=0..<n. rfs $$ (j1, j2) * (gsi.gso j') $ j2)))
            =  (vec m (\<lambda> j1. row rfs j1 \<bullet> gsi.gso j'))"
          using rfscarr gsi.gso_carrier len j' rfscarr by (auto simp add: scalar_prod_def)
        also have "row rB i' \<bullet> \<dots> / \<parallel>gsi.gso j'\<parallel>\<^sup>2 =
          row rB i' \<bullet> vec m (\<lambda> j1. row rfs j1 \<bullet> gsi.gso j' / \<parallel>gsi.gso j'\<parallel>\<^sup>2)"
          using prep4 scalar_prod_smult_right rBcarr carrier_matD(2) dim_vec row_def 
          by (smt gs.l_one times_divide_eq_left)
        also have "\<dots> = (rB * (gsi.M m)) $$ (i', j')" 
          using rBcarr i' j' prep3 gsi.M_def by (simp add: col_def)
        finally have 
          "map of_int_hom.vec_hom fs' ! i' \<bullet> fs'.gs.gso j' / \<parallel>fs'.gs.gso j'\<parallel>\<^sup>2 =
          (rB * (gsi.M m)) $$ (i', j')" by auto
      }
      then show "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> \<mu> fs' i' j' = 
        (map_mat of_int (A i j c) * gsi.M m) $$ (i',j')" 
        using B_def fs'.gs.\<beta>_zero fs'.gs.fi_scalar_prod_gso fs'.gs.gso_norm_beta
          len' rB_def by auto
      show "\<And> k. k < m \<Longrightarrow> gso fs' k = gso fs k" using gs_eq by auto
    qed
  } note mu_gso = this

  show "\<And> k. k < m \<Longrightarrow> gso fs' k = gso fs k" by fact
  {
    fix k
    have "k \<le> m \<Longrightarrow> rat_of_int (d fs' k) = rat_of_int (d fs k)" for k
    proof (induct k)
      case 0
      show ?case by (simp add: d_def)
    next
      case (Suc k)
      hence k: "k \<le> m" "k < m" by auto 
      show ?case
        by (subst (1 2) LLL_d_Suc[OF _ k(2)], auto simp: Suc(1)[OF k(1)] mu_gso(2)[OF k(2)]
          LLL_invariant_weak_def lin lin' len len' latt latt')
    qed
    thus "k \<le> m \<Longrightarrow> d fs' k = d fs k" by simp
  } note d = this
  {
    assume i': "i' < m" and j': "j' < m"
    have "\<mu> fs' i' j' = (of_int_hom.mat_hom (A i j c) * gsi.M m) $$ (i',j')" by (rule mu_gso(1)[OF i' j'])
    also have "\<dots> = (if (i',j') = (i,j) then of_int c * gsi.d j else 0) + gsi.M m $$ (i',j')" 
      unfolding A(1) using i' j' by (auto simp: gsi.M_def)
    also have "gsi.M m $$ (i',j') = \<mu> fs i' j'" 
      unfolding gsi.M_def using i' j' by simp
    also have "gsi.d j = of_int (d fs j)" 
      unfolding d_def by (subst Gramian_determinant_of_int[OF fs], insert ji i len, auto)
    finally show mu: "\<mu> fs' i' j' = (if (i',j') = (i,j) then rat_of_int (c * d fs j) + \<mu> fs i' j' else \<mu> fs i' j')" 
      by simp
    let ?d = "d fs (Suc j')" 
    have d_fs: "of_int (d\<mu> fs i' j') = rat_of_int ?d * \<mu> fs i' j'" 
      unfolding d\<mu>_def 
      using fs.fs_int_mu_d_Z_m_m[unfolded len, OF i' j'] 
      by (metis LLL.LLL.d_def assms(2) fs.fs_int_mu_d_Z_m_m fs_int.d_def i' 
          int_of_rat(2) j')
    have "rat_of_int (d\<mu> fs' i' j') = rat_of_int (d fs' (Suc j')) * \<mu> fs' i' j'" 
      unfolding d\<mu>_def 
      using fs'.fs_int_mu_d_Z_m_m[unfolded len', OF i' j']
      using LLL.LLL.d_def fs'(1) fs'.d\<mu> fs'.d\<mu>_def fs_int.d_def i' j' by auto
    also have "d fs' (Suc j') = ?d" by (rule d, insert j', auto)
    also have "rat_of_int \<dots> * \<mu> fs' i' j' = 
      (if (i',j') = (i,j) then rat_of_int (c * d fs j * ?d) else 0) + of_int (d\<mu> fs i' j')" 
      unfolding mu d_fs by (simp add: field_simps)
    also have "\<dots> = rat_of_int ((if (i',j') = (i,j) then c * d fs j * ?d else 0) + d\<mu> fs i' j')"
      by simp
    also have "\<dots> = rat_of_int ((if (i',j') = (i,j) then c * d fs j * d fs (Suc j) + d\<mu> fs i' j' else d\<mu> fs i' j'))"
      by simp
    finally show "d\<mu> fs' i' j' = (if (i',j') = (i,j) then c * d fs j * d fs (Suc j) + d\<mu> fs i' j' else d\<mu> fs i' j')" 
      by simp
  }
qed

text \<open>Eventually: Lemma 13 of Storjohann's paper.\<close>
lemma mod_single_element: assumes lin: "lin_indep fs" 
  and len: "length fs = m" 
  and i: "i < m" and ji: "j < i"  
  and latt: "lattice_of fs = L" 
  and pgtz: "p > 0"
shows "\<exists> fs'. lattice_of fs' = L \<and> 
  map (map_vec (\<lambda> x. x mod p)) fs' = map (map_vec (\<lambda> x. x mod p)) fs \<and>
  map (map_vec (\<lambda> x. x symmod p)) fs' = map (map_vec (\<lambda> x. x symmod p)) fs \<and>
  lin_indep fs' \<and>
  length fs' = m \<and> 
  (\<forall> k < m. gso fs' k = gso fs k) \<and> 
  (\<forall> k \<le> m. d fs' k = d fs k) \<and>
  (\<forall> i' < m. \<forall> j' < m. d\<mu> fs' i' j' = (if (i',j') = (i,j) then d\<mu> fs i j' symmod (p * d fs j' * d fs (Suc j')) else d\<mu> fs i' j'))" 
proof -
  have inv: "LLL_invariant_weak fs" using LLL_invariant_weak_def assms by simp
  let ?mult = "d fs j * d fs (Suc j)" 
  define M where "M = ?mult" 
  define pM where "pM = p * M" 
  then have pMgtz: "pM > 0" using pgtz unfolding pM_def M_def using LLL_d_pos[OF inv] i ji by simp
  let ?d = "d\<mu> fs i j" 
  define c where "c = - (?d symdiv pM)" 
  have d_mod: "?d symmod pM = c * pM + ?d" unfolding c_def using pMgtz sym_mod_sym_div by simp
  define A where "A = gram_schmidt_fs_int.inv_mu_ij_mat n (RAT fs)" 
  define fs' where fs': "fs' = Matrix.rows (A i j (c * p) * mat_of_rows n fs)"
  note main = change_single_element[OF lin len i ji A_def fs' latt]
  have "map (map_vec (\<lambda>x. x mod p)) fs' = map (map_vec (\<lambda>x. x mod p)) fs" 
    by (intro main, auto)
  from arg_cong[OF this, of "map (map_vec (poly_mod.inv_M p))"]
  have id: "map (map_vec (\<lambda>x. x symmod p)) fs' = map (map_vec (\<lambda>x. x symmod p)) fs" 
    unfolding map_map o_def sym_mod_def map_vec_map_vec .
  show ?thesis
  proof (intro exI[of _ fs'] conjI main allI impI id)
    fix i' j'
    assume ij: "i' < m" "j' < m" 
    have "d\<mu> fs' i' j' = (if (i', j') = (i, j) then (c * p) * M + ?d else d\<mu> fs i' j')" 
      unfolding main(8)[OF ij] M_def by simp
    also have "(c * p) * M + ?d = ?d symmod pM" 
      unfolding d_mod by (simp add: pM_def)
    finally show "d\<mu> fs' i' j' = (if (i',j') = (i,j) then d\<mu> fs i j' symmod (p * d fs j' * d fs (Suc j')) else d\<mu> fs i' j')" 
      by (auto simp: pM_def M_def ac_simps)
  qed auto
qed 

text \<open>A slight generalization to perform modulo on arbitrary set of indices $I$.\<close>
lemma mod_finite_set: assumes lin: "lin_indep fs" 
  and len: "length fs = m" 
  and I: "I \<subseteq> {(i,j). i < m \<and> j < i}"
  and latt: "lattice_of fs = L" 
  and pgtz: "p > 0"
shows "\<exists> fs'. lattice_of fs' = L \<and>
  map (map_vec (\<lambda> x. x mod p)) fs' = map (map_vec (\<lambda> x. x mod p)) fs \<and>
  map (map_vec (\<lambda> x. x symmod p)) fs' = map (map_vec (\<lambda> x. x symmod p)) fs \<and>
  lin_indep fs' \<and>
  length fs' = m \<and> 
  (\<forall> k < m. gso fs' k = gso fs k) \<and> 
  (\<forall> k \<le> m. d fs' k = d fs k) \<and>
  (\<forall> i' < m. \<forall> j' < m. d\<mu> fs' i' j' = 
     (if (i',j') \<in> I then d\<mu> fs i' j' symmod (p * d fs j' * d fs (Suc j')) else d\<mu> fs i' j'))"
proof -
  let ?exp = "\<lambda> fs' I i' j'. 
    d\<mu> fs' i' j' = (if (i',j') \<in> I then d\<mu> fs i' j' symmod (p * d fs j' * d fs (Suc j')) else d\<mu> fs i' j')" 
  let ?prop = "\<lambda> fs fs'. lattice_of fs' = L \<and> 
    map (map_vec (\<lambda> x. x mod p)) fs' = map (map_vec (\<lambda> x. x mod p)) fs \<and>
    map (map_vec (\<lambda> x. x symmod p)) fs' = map (map_vec (\<lambda> x. x symmod p)) fs \<and>
    lin_indep fs' \<and>
    length fs' = m \<and> 
    (\<forall> k < m. gso fs' k = gso fs k) \<and> 
    (\<forall> k \<le> m. d fs' k = d fs k)" 
  have "finite I" 
  proof (rule finite_subset[OF I], rule finite_subset)
    show "{(i, j). i < m \<and> j < i} \<subseteq> {0..m} \<times> {0..m}" by auto
  qed auto
  from this I have "\<exists> fs'. ?prop fs fs' \<and> (\<forall> i' < m. \<forall> j' < m. ?exp fs' I i' j')"
  proof (induct I)
    case empty
    show ?case
      by (intro exI[of _ fs], insert assms, auto)
  next
    case (insert ij I)
    obtain i j where ij: "ij = (i,j)" by force
    from ij insert(4) have i: "i < m" "j < i" by auto
    from insert(3,4) obtain gs where gs: "?prop fs gs" 
      and exp: "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> ?exp gs I i' j'" by auto
    from gs have "lin_indep gs" "lattice_of gs = L" "length gs = m" by auto
    from mod_single_element[OF this(1,3) i this(2), of p] 
    obtain hs where hs: "?prop gs hs" 
      and exp': "\<And> i' j'. i' < m \<Longrightarrow> j' < m \<Longrightarrow> 
      d\<mu> hs i' j' = (if (i', j') = (i, j) 
         then d\<mu> gs i j' symmod (p * d gs j' * d gs (Suc j')) else d\<mu> gs i' j')" 
      using pgtz by auto
    from gs i have id: "d gs j = d fs j" "d gs (Suc j) = d fs (Suc j)" by auto
    show ?case 
    proof (intro exI[of _ hs], rule conjI; (intro allI impI)?)
      show "?prop fs hs" using gs hs by auto
      fix i' j'
      assume *: "i' < m" "j' < m" 
      show "?exp hs (insert ij I) i' j'" unfolding exp'[OF *] ij using exp * i
        by (auto simp: id)
    qed
  qed
  thus ?thesis by auto
qed

end

end