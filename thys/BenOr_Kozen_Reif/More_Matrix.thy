theory More_Matrix
  imports "Jordan_Normal_Form.Matrix"
    "Jordan_Normal_Form.DL_Rank"
    "Jordan_Normal_Form.VS_Connect"
    "Jordan_Normal_Form.Gauss_Jordan_Elimination"
begin

section "Kronecker Product"

definition kronecker_product :: "'a :: ring mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "kronecker_product A B =
  (let ra = dim_row A; ca = dim_col A;
       rb = dim_row B; cb = dim_col B
  in
    mat (ra*rb) (ca*cb)
    (\<lambda>(i,j).
      A $$ (i div rb, j div cb) *
      B $$ (i mod rb, j mod cb)
  ))"

lemma arith:
  assumes "d < a"
  assumes "c < b"
  shows "b*d+c < a*(b::nat)"
proof -
  have "b*d+c < b*(d+1)"
    by (simp add: assms(2))
  thus ?thesis
    by (metis One_nat_def Suc_leI add.right_neutral add_Suc_right assms(1) less_le_trans mult.commute mult_le_cancel2)
qed

lemma dim_kronecker[simp]:
  "dim_row (kronecker_product A B) = dim_row A * dim_row B"
  "dim_col (kronecker_product A B) = dim_col A * dim_col B"
  unfolding kronecker_product_def Let_def by auto

lemma kronecker_inverse_index:
  assumes "r < dim_row A" "s < dim_col A"
  assumes "v < dim_row B" "w < dim_col B"
  shows "kronecker_product A B $$ (dim_row B*r+v, dim_col B*s+w) = A $$ (r,s) * B $$ (v,w)"
proof -
  from arith[OF assms(1) assms(3)]
  have "dim_row B*r+v < dim_row A * dim_row B" .
  moreover from arith[OF assms(2) assms(4)]
  have "dim_col B * s + w < dim_col A * dim_col B" .
  ultimately show ?thesis
    unfolding kronecker_product_def Let_def
    using assms by auto
qed

lemma kronecker_distr_left:
  assumes "dim_row B = dim_row C" "dim_col B = dim_col C"
  shows "kronecker_product A (B+C) = kronecker_product A B + kronecker_product A C"
  unfolding kronecker_product_def Let_def
  using assms apply (auto simp add: mat_eq_iff) 
  by (metis (no_types, lifting) distrib_left index_add_mat(1) mod_less_divisor mult_eq_0_iff neq0_conv not_less_zero)

lemma kronecker_distr_right:
  assumes "dim_row B = dim_row C" "dim_col B = dim_col C"
  shows "kronecker_product (B+C) A = kronecker_product B A + kronecker_product C A"
  unfolding kronecker_product_def Let_def
  using assms by (auto simp add: mat_eq_iff less_mult_imp_div_less distrib_right)

lemma index_mat_mod[simp]: "nr > 0 & nc > 0 \<Longrightarrow> mat nr nc f $$ (i mod nr,j mod nc) = f (i mod nr,j mod nc)"
  by auto

lemma kronecker_assoc:
  shows "kronecker_product A (kronecker_product B C) = kronecker_product (kronecker_product A B) C"
  unfolding kronecker_product_def Let_def
  apply (case_tac "dim_row B * dim_row C > 0 & dim_col B * dim_col C > 0")
   apply (auto simp add: mat_eq_iff less_mult_imp_div_less)
  by (smt div_mult2_eq div_mult_mod_eq kronecker_inverse_index less_mult_imp_div_less linordered_semiring_strict_class.mult_pos_pos mod_less_divisor mod_mult2_eq mult.assoc mult.commute)

lemma sum_sum_mod_div:
  "(\<Sum>ia = 0::nat..<x. \<Sum>ja = 0..<y. f ia ja) =
   (\<Sum>ia = 0..<x*y. f (ia div y) (ia mod y))"
proof -
  have 1: "inj_on (\<lambda>ia. (ia div y, ia mod y)) {0..<x * y}"
    by (smt (verit, best) Pair_inject div_mod_decomp inj_onI)
  have 21: "{0..<x} \<times> {0..<y} \<subseteq> (\<lambda>ia. (ia div y, ia mod y)) ` {0..<x * y}"
  proof clarsimp
    fix a b
    assume *:"a < x" "b < y"
    have "a * y +  b \<in> {0..<x*y}"
      by (metis arith * atLeastLessThan_iff le0 mult.commute)
    thus "(a, b) \<in> (\<lambda>ia. (ia div y, ia mod y)) ` {0..<x * y}"
      by (metis (no_types, lifting) "*"(2) Euclidean_Division.div_eq_0_iff add_cancel_right_right div_mult_self3 gr_implies_not0 image_iff mod_less mod_mult_self3)
  qed
  have 22:"(\<lambda>ia. (ia div y, ia mod y)) ` {0..<x * y} \<subseteq> {0..<x} \<times> {0..<y}"
    using less_mult_imp_div_less apply auto
    by (metis mod_less_divisor mult.commute neq0_conv not_less_zero)
  have 2: "{0..<x} \<times> {0..<y} = (\<lambda>ia. (ia div y, ia mod y)) ` {0..<x * y}"
    using 21 22 by auto
  have *: "(\<Sum>ia = 0::nat..<x. \<Sum>ja = 0..<y. f ia ja) =
        (\<Sum>(x, y)\<in>{0..<x} \<times> {0..<y}. f x y)"
    by (auto simp add: sum.cartesian_product)
  show ?thesis unfolding *
    apply (intro sum.reindex_cong[of "\<lambda>ia. (ia div y, ia mod y)"])
    using 1 2 by auto
qed

(* Kronecker product distributes over matrix multiplication *)
lemma kronecker_of_mult:
  assumes "dim_col (A :: 'a :: comm_ring mat) = dim_row C"
  assumes "dim_col B = dim_row D"
  shows "kronecker_product A B * kronecker_product C D = kronecker_product (A * C) (B * D)"
  unfolding kronecker_product_def Let_def mat_eq_iff
proof clarsimp
  fix i j
  assume ij: "i < dim_row A * dim_row B" "j < dim_col C * dim_col D"
  have 1: "(A * C) $$ (i div dim_row B, j div dim_col D) =
    row A (i div dim_row B) \<bullet> col C (j div dim_col D)"
    using ij less_mult_imp_div_less by (auto intro!: index_mult_mat)
  have 2: "(B * D) $$ (i mod dim_row B, j mod dim_col D) =
    row B (i mod dim_row B) \<bullet> col D (j mod dim_col D)"
    using ij apply (auto intro!: index_mult_mat)
    using gr_implies_not0 apply fastforce
    using gr_implies_not0 by fastforce
  have 3: "\<And>x. x < dim_row C * dim_row D \<Longrightarrow>
         A $$ (i div dim_row B, x div dim_row D) *
         B $$ (i mod dim_row B, x mod dim_row D) *
         (C $$ (x div dim_row D, j div dim_col D) *
          D $$ (x mod dim_row D, j mod dim_col D)) =
         row A (i div dim_row B) $ (x div dim_row D) *
         col C (j div dim_col D) $ (x div dim_row D) *
         (row B (i mod dim_row B) $ (x mod dim_row D) *
          col D (j mod dim_col D) $ (x mod dim_row D))"
  proof -
    fix x
    assume *:"x < dim_row C * dim_row D"
    have 1: "row A (i div dim_row B) $ (x div dim_row D) = A $$ (i div dim_row B, x div dim_row D)"
      by (simp add: * assms(1) less_mult_imp_div_less row_def)
    have 2: "row B (i mod dim_row B) $ (x mod dim_row D) = B $$ (i mod dim_row B, x mod dim_row D)"
      by (metis "*" assms(2) ij(1) index_row(1) mod_less_divisor nat_0_less_mult_iff neq0_conv not_less_zero)
    have 3: "col C (j div dim_col D) $ (x div dim_row D) = C $$ (x div dim_row D, j div dim_col D)"
      by (simp add: "*" ij(2) less_mult_imp_div_less)
    have 4: "col D (j mod dim_col D) $ (x mod dim_row D) = D $$ (x mod dim_row D, j mod dim_col D)"
      by (metis "*" Euclidean_Division.div_eq_0_iff gr_implies_not0 ij(2) index_col mod_div_trivial mult_not_zero)
    show "A $$ (i div dim_row B, x div dim_row D) *
         B $$ (i mod dim_row B, x mod dim_row D) *
         (C $$ (x div dim_row D, j div dim_col D) *
          D $$ (x mod dim_row D, j mod dim_col D)) =
         row A (i div dim_row B) $ (x div dim_row D) *
         col C (j div dim_col D) $ (x div dim_row D) *
         (row B (i mod dim_row B) $ (x mod dim_row D) *
          col D (j mod dim_col D) $ (x mod dim_row D))" unfolding 1 2 3 4
      by (simp add: mult.assoc mult.left_commute)
  qed
  have *: "(A * C) $$ (i div dim_row B, j div dim_col D) *
        (B * D) $$ (i mod dim_row B, j mod dim_col D) =
    (\<Sum>ia = 0..<dim_row C * dim_row D.
               A $$ (i div dim_row B, ia div dim_row D) *
               B $$ (i mod dim_row B, ia mod dim_row D) *
               (C $$ (ia div dim_row D, j div dim_col D) *
                D $$ (ia mod dim_row D, j mod dim_col D)))"
    unfolding 1 2 scalar_prod_def sum_product sum_sum_mod_div
    apply (auto simp add: sum_product sum_sum_mod_div intro!: sum.cong)
    using 3 by presburger
  show "vec (dim_col A * dim_col B)
          (\<lambda>j. A $$ (i div dim_row B, j div dim_col B) *
               B $$ (i mod dim_row B, j mod dim_col B)) \<bullet>
       vec (dim_row C * dim_row D)
          (\<lambda>i. C $$ (i div dim_row D, j div dim_col D) *
               D $$ (i mod dim_row D, j mod dim_col D)) =
        (A * C) $$ (i div dim_row B, j div dim_col D) *
        (B * D) $$ (i mod dim_row B, j mod dim_col D)"
    unfolding * scalar_prod_def
    by (auto simp add: assms sum_product sum_sum_mod_div intro!: sum.cong)
qed

lemma inverts_mat_length:
  assumes "square_mat A" "inverts_mat A B" "inverts_mat B A"
  shows "dim_row B = dim_row A" "dim_col B = dim_col A"
   apply (metis assms(1) assms(3) index_mult_mat(3) index_one_mat(3) inverts_mat_def square_mat.simps)
  by (metis assms(1) assms(2) index_mult_mat(3) index_one_mat(3) inverts_mat_def square_mat.simps)

lemma less_mult_imp_mod_less:
  "m mod i < i" if "m < n * i" for m n i :: nat
  using gr_implies_not_zero that by fastforce

lemma kronecker_one:
  shows "kronecker_product ((1\<^sub>m x)::'a :: ring_1 mat) (1\<^sub>m y) = 1\<^sub>m (x*y)"
  unfolding kronecker_product_def Let_def
  apply  (auto simp add:mat_eq_iff less_mult_imp_div_less less_mult_imp_mod_less)
  by (metis div_mult_mod_eq)

lemma kronecker_invertible:
  assumes "invertible_mat (A :: 'a :: comm_ring_1 mat)" "invertible_mat B"
  shows "invertible_mat (kronecker_product A B)"
proof -
  obtain Ai where Ai: "inverts_mat A Ai" "inverts_mat Ai A" using assms invertible_mat_def by blast
  obtain Bi where Bi: "inverts_mat B Bi" "inverts_mat Bi B" using assms invertible_mat_def by blast
  have "square_mat (kronecker_product A B)"
    by (metis (no_types, lifting) assms(1) assms(2) dim_col_mat(1) dim_row_mat(1) invertible_mat_def kronecker_product_def square_mat.simps)
  moreover have "inverts_mat (kronecker_product A B) (kronecker_product Ai Bi)"
    using Ai Bi unfolding inverts_mat_def
    by (metis (no_types, lifting) dim_kronecker(1) index_mult_mat(3) index_one_mat(3) kronecker_of_mult kronecker_one)
  moreover have "inverts_mat (kronecker_product Ai Bi) (kronecker_product A B)"
    using Ai Bi unfolding inverts_mat_def
    by (metis (no_types, lifting) dim_kronecker(1) index_mult_mat(3) index_one_mat(3) kronecker_of_mult kronecker_one)
  ultimately show ?thesis unfolding invertible_mat_def by blast
qed

section "More DL Rank"

(* conjugate matrices *)
instantiation mat :: (conjugate) conjugate
begin

definition conjugate_mat :: "'a :: conjugate mat \<Rightarrow> 'a mat"
  where "conjugate m = mat (dim_row m) (dim_col m) (\<lambda>(i,j). conjugate (m $$ (i,j)))"

lemma dim_row_conjugate[simp]: "dim_row (conjugate m) = dim_row m"
  unfolding conjugate_mat_def by auto

lemma dim_col_conjugate[simp]: "dim_col (conjugate m) = dim_col m"
  unfolding conjugate_mat_def by auto

lemma carrier_vec_conjugate[simp]: "m \<in> carrier_mat nr nc \<Longrightarrow> conjugate m \<in> carrier_mat nr nc"
  by (auto)

lemma mat_index_conjugate[simp]:
  shows "i < dim_row m \<Longrightarrow> j < dim_col m \<Longrightarrow> conjugate m  $$ (i,j) = conjugate (m $$ (i,j))"
  unfolding conjugate_mat_def by auto

lemma row_conjugate[simp]: "i < dim_row m \<Longrightarrow> row (conjugate m) i = conjugate (row m i)"
  by (auto)

lemma col_conjugate[simp]: "i < dim_col m \<Longrightarrow> col (conjugate m) i = conjugate (col m i)"
  by (auto)

lemma rows_conjugate: "rows (conjugate m) = map conjugate (rows m)"
  by (simp add: list_eq_iff_nth_eq)

lemma cols_conjugate: "cols (conjugate m) = map conjugate (cols m)"
  by (simp add: list_eq_iff_nth_eq)

instance
proof
  fix a b :: "'a mat"
  show "conjugate (conjugate a) = a"
    unfolding mat_eq_iff by auto
  let ?a = "conjugate a"
  let ?b = "conjugate b"
  show "conjugate a = conjugate b \<longleftrightarrow> a = b"
    by (metis dim_col_conjugate dim_row_conjugate mat_index_conjugate conjugate_cancel_iff mat_eq_iff)
qed

end

abbreviation conjugate_transpose :: "'a::conjugate mat  \<Rightarrow> 'a mat"
  where "conjugate_transpose A \<equiv> conjugate (A\<^sup>T)"

notation conjugate_transpose ("(_\<^sup>H)" [1000])

lemma transpose_conjugate:
  shows "(conjugate A)\<^sup>T = A\<^sup>H"
  unfolding conjugate_mat_def
  by auto

lemma vec_module_col_helper:
  fixes A:: "('a :: field) mat"
  shows "(0\<^sub>v (dim_row A) \<in> LinearCombinations.module.span class_ring \<lparr>carrier = carrier_vec (dim_row A), mult = undefined, one = undefined, zero = 0\<^sub>v (dim_row A), add = (+), smult = (\<cdot>\<^sub>v)\<rparr> (set (cols A)))"
proof -
  have "\<forall>v. (0::'a) \<cdot>\<^sub>v v + v = v"
    by auto
  then show "0\<^sub>v (dim_row A) \<in> LinearCombinations.module.span class_ring \<lparr>carrier = carrier_vec (dim_row A), mult = undefined, one = undefined, zero = 0\<^sub>v (dim_row A), add = (+), smult = (\<cdot>\<^sub>v)\<rparr> (set (cols A))"
    by (metis cols_dim module_vec_def right_zero_vec smult_carrier_vec vec_space.prod_in_span zero_carrier_vec)
qed

lemma vec_module_col_helper2:
  fixes A:: "('a :: field) mat"
  shows "\<And>a x. x \<in> LinearCombinations.module.span class_ring
                \<lparr>carrier = carrier_vec (dim_row A), mult = undefined, one = undefined,
                   zero = 0\<^sub>v (dim_row A), add = (+), smult = (\<cdot>\<^sub>v)\<rparr>
                (set (cols A)) \<Longrightarrow>
           (\<And>a b v. (a + b) \<cdot>\<^sub>v v = a \<cdot>\<^sub>v v + b \<cdot>\<^sub>v v) \<Longrightarrow>
           a \<cdot>\<^sub>v x
           \<in> LinearCombinations.module.span class_ring
               \<lparr>carrier = carrier_vec (dim_row A), mult = undefined, one = undefined,
                  zero = 0\<^sub>v (dim_row A), add = (+), smult = (\<cdot>\<^sub>v)\<rparr>
               (set (cols A))"
proof -
  fix a :: 'a and x :: "'a vec"
  assume "x \<in> LinearCombinations.module.span class_ring \<lparr>carrier = carrier_vec (dim_row A), mult = undefined, one = undefined, zero = 0\<^sub>v (dim_row A), add = (+), smult = (\<cdot>\<^sub>v)\<rparr> (set (cols A))"
  then show "a \<cdot>\<^sub>v x \<in> LinearCombinations.module.span class_ring \<lparr>carrier = carrier_vec (dim_row A), mult = undefined, one = undefined, zero = 0\<^sub>v (dim_row A), add = (+), smult = (\<cdot>\<^sub>v)\<rparr> (set (cols A))"
    by (metis (full_types) cols_dim idom_vec.smult_in_span module_vec_def)
qed

lemma vec_module_col: "module (class_ring :: 'a :: field ring)
  (module_vec TYPE('a) 
    (dim_row A)
      \<lparr>carrier :=
         LinearCombinations.module.span
          class_ring (module_vec TYPE('a) (dim_row A)) (set (cols A))\<rparr>)"
proof -
  interpret abelian_group "module_vec TYPE('a) (dim_row A)
      \<lparr>carrier :=
         LinearCombinations.module.span
          class_ring (module_vec TYPE('a) (dim_row A)) (set (cols A))\<rparr>"
    apply (unfold_locales)
          apply (auto simp add:module_vec_def)
          apply (metis cols_dim module_vec_def partial_object.select_convs(1) ring.simps(2) vec_vs vectorspace.span_add1)
         apply (metis assoc_add_vec cols_dim module_vec_def vec_space.cV vec_vs vectorspace.span_closed)
    using vec_module_col_helper[of A] apply (auto)    
       apply (metis cols_dim left_zero_vec module_vec_def partial_object.select_convs(1) vec_vs vectorspace.span_closed)
      apply (metis cols_dim module_vec_def partial_object.select_convs(1) right_zero_vec vec_vs vectorspace.span_closed)
     apply (metis cols_dim comm_add_vec module_vec_def vec_space.cV vec_vs vectorspace.span_closed)
    unfolding Units_def apply auto
    by (smt cols_dim module_vec_def partial_object.select_convs(1) uminus_l_inv_vec uminus_r_inv_vec vec_space.vec_neg vec_vs vectorspace.span_closed vectorspace.span_neg)
  show ?thesis
    apply (unfold_locales)
    unfolding class_ring_simps apply auto
    unfolding module_vec_simps using add_smult_distrib_vec apply auto
     apply (auto simp add:module_vec_def)
    using vec_module_col_helper2
     apply blast
    using cols_dim module_vec_def partial_object.select_convs(1) smult_add_distrib_vec vec_vs vectorspace.span_closed
    by (smt (z3))
qed

(* The columns of a matrix form a vectorspace *)
lemma vec_vs_col: "vectorspace (class_ring :: 'a :: field ring)
  (module_vec TYPE('a) (dim_row A)
      \<lparr>carrier :=
         LinearCombinations.module.span
          class_ring
          (module_vec TYPE('a)
            (dim_row A))
          (set (cols A))\<rparr>)"
  unfolding vectorspace_def
  using vec_module_col class_field 
  by (auto simp: class_field_def)

lemma cols_mat_mul_map:
  shows "cols (A * B) = map ((*\<^sub>v) A) (cols B)"
  unfolding list_eq_iff_nth_eq
  by auto

lemma cols_mat_mul:
  shows "set (cols (A * B)) = (*\<^sub>v) A ` set (cols B)"
  by (simp add: cols_mat_mul_map)

lemma set_obtain_sublist:
  assumes "S \<subseteq> set ls"
  obtains ss where "distinct ss" "S = set ss"
  using assms finite_distinct_list infinite_super by blast

lemma mul_mat_of_cols:
  assumes "A \<in> carrier_mat nr n"
  assumes "\<And>j. j < length cs \<Longrightarrow> cs ! j \<in> carrier_vec n"
  shows "A * (mat_of_cols n cs) = mat_of_cols nr (map ((*\<^sub>v) A) cs)"
  unfolding mat_eq_iff
  using assms apply auto
  apply (subst mat_of_cols_index)
  by auto

lemma helper:
  fixes x y z ::"'a :: {conjugatable_ring, comm_ring}"
  shows "x * (y * z) = y * x * z"
  by (simp add: mult.assoc mult.left_commute)

lemma cscalar_prod_conjugate_transpose:
  fixes x y ::"'a :: {conjugatable_ring, comm_ring} vec"
  assumes "A \<in> carrier_mat nr nc"
  assumes "x \<in> carrier_vec nr"
  assumes "y \<in> carrier_vec nc"
  shows "x \<bullet>c (A *\<^sub>v y) = (A\<^sup>H *\<^sub>v x) \<bullet>c y"
  unfolding mult_mat_vec_def scalar_prod_def
  using assms apply (auto simp add: sum_distrib_left sum_distrib_right sum_conjugate conjugate_dist_mul)
  apply (subst sum.swap)
  by (meson helper mult.assoc mult.left_commute sum.cong)

lemma mat_mul_conjugate_transpose_vec_eq_0:                        
  fixes v ::"'a :: {conjugatable_ordered_ring,semiring_no_zero_divisors,comm_ring} vec"
  assumes "A \<in> carrier_mat nr nc"
  assumes "v \<in> carrier_vec nr"
  assumes "A *\<^sub>v (A\<^sup>H *\<^sub>v v) = 0\<^sub>v nr"
  shows "A\<^sup>H *\<^sub>v v = 0\<^sub>v nc"
proof -
  have "(A\<^sup>H *\<^sub>v v) \<bullet>c (A\<^sup>H *\<^sub>v v) = (A *\<^sub>v (A\<^sup>H *\<^sub>v v)) \<bullet>c v"
    by (metis (mono_tags, lifting) Matrix.carrier_vec_conjugate assms(1) assms(2) assms(3) carrier_matD(2) conjugate_zero_vec cscalar_prod_conjugate_transpose dim_row_conjugate index_transpose_mat(2) mult_mat_vec_def scalar_prod_left_zero scalar_prod_right_zero vec_carrier)
  also have "... = 0"
    by (simp add: assms(2) assms(3))
      (* this step requires real entries *)
  ultimately have "(A\<^sup>H *\<^sub>v v) \<bullet>c (A\<^sup>H *\<^sub>v v) = 0" by auto
  thus ?thesis
    apply (subst conjugate_square_eq_0_vec[symmetric])
    using assms(1) carrier_dim_vec apply fastforce
    by auto
qed

lemma row_mat_of_cols:
  assumes "i < nr"
  shows "row (mat_of_cols nr ls) i = vec (length ls) (\<lambda>j. (ls ! j) $i)"
  by (smt assms dim_vec eq_vecI index_row(1) index_row(2) index_vec mat_of_cols_carrier(2) mat_of_cols_carrier(3) mat_of_cols_index)

lemma mat_of_cols_cons_mat_vec:
  fixes v ::"'a::comm_ring vec"
  assumes "v \<in> carrier_vec (length ls)"
  assumes "dim_vec a = nr"
  shows
    "mat_of_cols nr (a # ls) *\<^sub>v (vCons m v) =
   m \<cdot>\<^sub>v a + mat_of_cols nr ls *\<^sub>v v"
  unfolding mult_mat_vec_def vec_eq_iff
  using assms by
    (auto simp add: row_mat_of_cols vec_Suc o_def mult.commute)

lemma smult_vec_zero:
  fixes v ::"'a::ring vec"
  shows "0 \<cdot>\<^sub>v v = 0\<^sub>v (dim_vec v)"
  unfolding smult_vec_def vec_eq_iff
  by (auto)

lemma helper2:
  fixes A ::"'a::comm_ring mat"
  fixes v ::"'a vec"
  assumes "v \<in> carrier_vec (length ss)"
  assumes "\<And>x. x \<in> set ls \<Longrightarrow> dim_vec x = nr"
  shows
    "mat_of_cols nr ss *\<^sub>v v =
   mat_of_cols nr (ls @ ss) *\<^sub>v (0\<^sub>v (length ls) @\<^sub>v v)"
  using assms(2)
proof (induction ls)
  case Nil
  then show ?case by auto
next
  case (Cons a ls)
  then show ?case apply (auto simp add:zero_vec_Suc)
    apply (subst mat_of_cols_cons_mat_vec)
    by (auto simp add:assms smult_vec_zero)
qed

lemma mat_of_cols_mult_mat_vec_permute_list:
  fixes v ::"'a::comm_ring list"
  assumes "f permutes {..<length ss}"
  assumes "length ss = length v"
  shows
    "mat_of_cols nr (permute_list f ss) *\<^sub>v vec_of_list (permute_list f v) =
     mat_of_cols nr ss *\<^sub>v vec_of_list v"
  unfolding mat_of_cols_def mult_mat_vec_def vec_eq_iff scalar_prod_def
proof clarsimp
  fix i
  assume "i < nr"
  from sum.permute[OF assms(1)]
  have "(\<Sum>ia<length ss. ss ! f ia $ i * v ! f ia) =
  sum ((\<lambda>ia. ss ! f ia $ i * v ! f ia) \<circ> f) {..<length ss}" .
  also have "... = (\<Sum>ia = 0..<length v. ss ! f ia $ i * v ! f ia)"
    using assms(2) calculation lessThan_atLeast0 by auto
  ultimately have *: "(\<Sum>ia = 0..<length v.
             ss ! f ia $ i * v ! f ia) =
         (\<Sum>ia = 0..<length v.
             ss ! ia $ i * v ! ia)"
    by (metis (mono_tags, lifting) \<open>\<And>g. sum g {..<length ss} = sum (g \<circ> f) {..<length ss}\<close> assms(2) comp_apply lessThan_atLeast0 sum.cong)
  show "(\<Sum>ia = 0..<length v.
         vec (length ss) (\<lambda>j. permute_list f ss ! j $ i) $ ia *
         vec_of_list (permute_list f v) $ ia) =
         (\<Sum>ia = 0..<length v. vec (length ss) (\<lambda>j. ss ! j $ i) $ ia * vec_of_list v $ ia)"
    using assms * by (auto simp add: permute_list_nth vec_of_list_index)
qed

(* permute everything in a subset of the indices to the back *)
lemma subindex_permutation:
  assumes "distinct ss" "set ss \<subseteq> {..<length ls}"
  obtains f where "f permutes {..<length ls}"
    "permute_list f ls = map ((!) ls) (filter (\<lambda>i. i \<notin> set ss) [0..<length ls]) @ map ((!) ls) ss"
proof -
  have "set [0..<length ls] = set (filter (\<lambda>i. i \<notin> set ss) [0..<length ls] @ ss)"
    using assms unfolding multiset_eq_iff by auto
  then have "mset [0..<length ls] = mset (filter (\<lambda>i. i \<notin> set ss) [0..<length ls] @ ss)"
    apply (subst set_eq_iff_mset_eq_distinct[symmetric])
    using assms by auto  
  then have "mset ls = mset (map ((!) ls)
           (filter (\<lambda>i. i \<notin> set ss)
             [0..<length ls]) @ map ((!) ls) ss)"
    by (smt length_map map_append map_nth mset_eq_permutation mset_permute_list permute_list_map)
  thus ?thesis
    by (metis mset_eq_permutation that)
qed

lemma subindex_permutation2:
  assumes "distinct ss" "set ss \<subseteq> {..<length ls}"
  obtains f where "f permutes {..<length ls}"
    "ls = permute_list f (map ((!) ls) (filter (\<lambda>i. i \<notin> set ss) [0..<length ls]) @ map ((!) ls) ss)"
  using subindex_permutation
  by (metis assms(1) assms(2) length_permute_list mset_eq_permutation mset_permute_list)

lemma distinct_list_subset_nths:
  assumes "distinct ss" "set ss \<subseteq> set ls"
  obtains ids where "distinct ids" "set ids \<subseteq> {..<length ls}" "ss = map ((!) ls) ids"
proof -
  let ?ids = "map (\<lambda>i. @j. j < length ls \<and> ls!j = i ) ss"
  have 1: "distinct ?ids" unfolding distinct_map
    using assms apply (auto simp add: inj_on_def)
    by (smt in_mono in_set_conv_nth tfl_some)
  have 2: "set ?ids \<subseteq> {..<length ls}"
    using assms apply (auto)
    by (metis (mono_tags, lifting) in_mono in_set_conv_nth tfl_some)
  have 3: "ss = map ((!) ls) ?ids"
    using assms apply (auto simp add: list_eq_iff_nth_eq)
    by (smt imageI in_set_conv_nth subset_iff tfl_some)
  show "(\<And>ids. distinct ids \<Longrightarrow>
            set ids \<subseteq> {..<length ls} \<Longrightarrow>
            ss = map ((!) ls) ids \<Longrightarrow> thesis) \<Longrightarrow>
    thesis" using 1 2 3 by blast
qed

lemma helper3: 
  fixes A ::"'a::comm_ring mat"
  assumes A: "A \<in> carrier_mat nr nc"
  assumes ss:"distinct ss" "set ss \<subseteq> set (cols A)"
  assumes "v \<in> carrier_vec (length ss)"
  obtains c where "mat_of_cols nr ss *\<^sub>v v = A *\<^sub>v c" "dim_vec c = nc"
proof -
  from distinct_list_subset_nths[OF ss]
  obtain ids where ids: "distinct ids" "set ids \<subseteq> {..<length (cols A)}"
    and ss: "ss = map ((!) (cols A)) ids" by blast
  let ?ls = " map ((!) (cols A)) (filter (\<lambda>i. i \<notin> set ids) [0..<length (cols A)])"
  from subindex_permutation2[OF ids] obtain f where
    f: "f permutes {..<length (cols A)}"
    "cols A = permute_list f (?ls @ ss)" using ss by blast
  have *: "\<And>x. x \<in> set ?ls \<Longrightarrow> dim_vec x = nr"
    using A by auto
  let ?cs1 = "(list_of_vec (0\<^sub>v (length ?ls) @\<^sub>v v))"
  from helper2[OF assms(4) ]
  have "mat_of_cols nr ss *\<^sub>v v = mat_of_cols nr (?ls @ ss) *\<^sub>v vec_of_list (?cs1)"
    using *
    by (metis vec_list)
  also have "... = mat_of_cols nr (permute_list f (?ls @ ss)) *\<^sub>v vec_of_list (permute_list f ?cs1)"
    apply (auto intro!: mat_of_cols_mult_mat_vec_permute_list[symmetric])
     apply (metis cols_length f(1) f(2) length_append length_map length_permute_list)
    using assms(4) by auto
  also have "... =  A *\<^sub>v vec_of_list (permute_list f ?cs1)" using f(2) assms by auto
  ultimately show
    "(\<And>c. mat_of_cols nr ss *\<^sub>v v = A *\<^sub>v c \<Longrightarrow> dim_vec c = nc \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    by (metis A assms(4) carrier_matD(2) carrier_vecD cols_length dim_vec_of_list f(2) index_append_vec(2) index_zero_vec(2) length_append length_list_of_vec length_permute_list)
qed

lemma mat_mul_conjugate_transpose_sub_vec_eq_0:                        
  fixes A ::"'a :: {conjugatable_ordered_ring,semiring_no_zero_divisors,comm_ring} mat"
  assumes "A \<in> carrier_mat nr nc"
  assumes "distinct ss" "set ss \<subseteq> set (cols (A\<^sup>H))"
  assumes "v \<in> carrier_vec (length ss)"
  assumes "A *\<^sub>v (mat_of_cols nc ss *\<^sub>v v) = 0\<^sub>v nr"
  shows "(mat_of_cols nc ss *\<^sub>v v) = 0\<^sub>v nc"
proof -
  have "A\<^sup>H \<in> carrier_mat nc nr" using assms(1) by auto
  from  helper3[OF this assms(2-4)]
  obtain c where c: "mat_of_cols nc ss *\<^sub>v v = A\<^sup>H *\<^sub>v c" "dim_vec c = nr" by blast
  have 1: "c \<in> carrier_vec nr"
    using c carrier_vec_dim_vec by blast
  have 2: "A *\<^sub>v (A\<^sup>H *\<^sub>v c) = 0\<^sub>v nr" using c assms(5) by auto
  from mat_mul_conjugate_transpose_vec_eq_0[OF assms(1) 1 2]
  have "A\<^sup>H *\<^sub>v c = 0\<^sub>v nc" .
  thus ?thesis unfolding c(1)[symmetric] .
qed

lemma Units_invertible:
  fixes A:: "'a::semiring_1 mat"
  assumes "A \<in> Units (ring_mat TYPE('a) n b)"
  shows "invertible_mat A"
  using assms unfolding Units_def invertible_mat_def
  apply (auto simp add: ring_mat_def)
  using inverts_mat_def by blast

lemma invertible_Units:
  fixes A:: "'a::semiring_1 mat"
  assumes "invertible_mat A"
  shows "A \<in> Units (ring_mat TYPE('a) (dim_row A) b)"
  using assms unfolding Units_def invertible_mat_def
  apply (auto simp add: ring_mat_def)
  by (metis assms carrier_mat_triv invertible_mat_def inverts_mat_def inverts_mat_length(1) inverts_mat_length(2))

lemma invertible_det:
  fixes A:: "'a::field mat"
  assumes "A \<in> carrier_mat n n"
  shows "invertible_mat A \<longleftrightarrow> det A \<noteq> 0"
  apply auto
  using invertible_Units unit_imp_det_non_zero apply fastforce
  using assms by (auto intro!: Units_invertible det_non_zero_imp_unit)

context vec_space begin

lemma find_indices_distinct:
  assumes "distinct ss"
  assumes "i < length ss"
  shows "find_indices (ss ! i) ss = [i]"
proof -
  have "set (find_indices (ss ! i) ss) = {i}"
    using assms apply auto by (simp add: assms(1) assms(2) nth_eq_iff_index_eq)
  thus ?thesis
    by (metis distinct.simps(2) distinct_find_indices empty_iff empty_set insert_iff list.exhaust list.simps(15)) 
qed

lemma lin_indpt_lin_comb_list:
  assumes "distinct ss"
  assumes "lin_indpt (set ss)"
  assumes "set ss \<subseteq> carrier_vec n"
  assumes "lincomb_list f ss = 0\<^sub>v n"
  assumes "i < length ss"
  shows "f i = 0"
proof -
  from lincomb_list_as_lincomb[OF assms(3)]
  have "lincomb_list f ss = lincomb (mk_coeff ss f) (set ss)" .
  also have "... = lincomb  (\<lambda>v. sum f (set (find_indices v ss))) (set ss)"
    unfolding mk_coeff_def
    apply (subst R.sumlist_map_as_finsum)
    by (auto simp add: distinct_find_indices)
  ultimately have "lincomb_list f ss = lincomb  (\<lambda>v. sum f (set (find_indices v ss))) (set ss)" by auto
  then have *:"lincomb (\<lambda>v. sum f (set (find_indices v ss))) (set ss) = 0\<^sub>v n"
    using assms(4) by auto
  have "finite (set ss)" by simp
  from not_lindepD[OF assms(2) this _ _ *]
  have "(\<lambda>v. sum f (set (find_indices v ss))) \<in> set ss \<rightarrow> {0}"
    by auto
  from funcset_mem[OF this]
  have "sum f (set (find_indices (nth ss i) ss)) \<in> {0}"
    using assms(5) by auto
  thus ?thesis unfolding find_indices_distinct[OF assms(1) assms(5)]
    by auto
qed

(* Note: in this locale dim_row A = n, e.g.:
lemma foo:
  assumes "dim_row A = n"
  shows "rank A = vec_space.rank (dim_row A) A"
  by (simp add: assms) *)

lemma span_mat_mul_subset:
  assumes "A \<in> carrier_mat n d"
  assumes "B \<in> carrier_mat d nc"
  shows "span (set (cols (A * B))) \<subseteq> span (set (cols A))"
proof -
  have *: "\<And>v. \<exists>ca. lincomb_list v (cols (A * B)) =
              lincomb_list ca  (cols A)"
  proof -
    fix v
    have "lincomb_list v (cols (A * B)) = (A * B) *\<^sub>v vec nc v"
      apply (subst lincomb_list_as_mat_mult)
       apply (metis assms(1) carrier_dim_vec carrier_matD(1) cols_dim index_mult_mat(2) subset_code(1))
      by (metis assms(1) assms(2) carrier_matD(1) carrier_matD(2) cols_length index_mult_mat(2) index_mult_mat(3) mat_of_cols_cols)
    also have "... = A *\<^sub>v (B *\<^sub>v vec nc v)"
      using assms(1) assms(2) by auto
    also have "... = lincomb_list (\<lambda>i. (B *\<^sub>v vec nc v) $ i) (cols A)"
      apply (subst lincomb_list_as_mat_mult)
      using assms(1) carrier_dim_vec cols_dim apply blast
      by (metis assms(1) assms(2) carrier_matD(1) carrier_matD(2) cols_length dim_mult_mat_vec dim_vec eq_vecI index_vec mat_of_cols_cols)
    ultimately have "lincomb_list v (cols (A * B)) =
              lincomb_list (\<lambda>i. (B *\<^sub>v vec nc v) $ i) (cols A)" by auto
    thus "\<exists>ca. lincomb_list v (cols (A * B)) = lincomb_list ca (cols A)" by auto
  qed
  show ?thesis
    apply (subst span_list_as_span[symmetric])
     apply (metis assms(1) carrier_matD(1) cols_dim index_mult_mat(2))
    apply (subst span_list_as_span[symmetric])
    using assms(1) cols_dim apply blast
    by (auto simp add:span_list_def *)
qed

lemma rank_mat_mul_right:
  assumes "A \<in> carrier_mat n d"
  assumes "B \<in> carrier_mat d nc"
  shows "rank (A * B) \<le> rank A"
proof -
  have "subspace class_ring (local.span (set (cols (A*B))))
        (vs (local.span (set (cols A))))"
    unfolding subspace_def
    by (metis assms(1) assms(2) carrier_matD(1) cols_dim index_mult_mat(2) nested_submodules span_is_submodule vec_space.span_mat_mul_subset vec_vs_col)
  from vectorspace.subspace_dim[OF _ this]
  have "vectorspace.dim class_ring
   (vs (local.span (set (cols A)))
    \<lparr>carrier := local.span (set (cols (A * B)))\<rparr>) \<le>
  vectorspace.dim class_ring
      (vs (local.span (set (cols A))))"
    apply auto
    by (metis (no_types) assms(1) carrier_matD(1) fin_dim_span_cols index_mult_mat(2) mat_of_cols_carrier(1) mat_of_cols_cols vec_vs_col)
  thus ?thesis unfolding rank_def
    by auto
qed

lemma sumlist_drop:
  assumes "\<And>v. v \<in> set ls \<Longrightarrow> dim_vec v = n"
  shows "sumlist ls = sumlist (filter (\<lambda>v. v \<noteq> 0\<^sub>v n) ls)"
  using assms
proof (induction ls)
  case Nil
  then show ?case by auto
next
  case (Cons a ls)
  then show ?case using dim_sumlist by auto
qed

lemma lincomb_list_alt:
  shows "lincomb_list c s =
    sumlist (map2 (\<lambda>i j. i \<cdot>\<^sub>v s ! j) (map (\<lambda>i. c i) [0..<length s]) [0..<length s])"
  unfolding lincomb_list_def
  by (smt length_map map2_map_map map_nth nth_equalityI nth_map)

lemma lincomb_list_alt2:
  assumes "\<And>v. v \<in> set s \<Longrightarrow> dim_vec v = n"
  assumes "\<And>i. i \<in> set ls \<Longrightarrow> i < length s"
  shows "
    sumlist (map2 (\<lambda>i j. i \<cdot>\<^sub>v s ! j) (map (\<lambda>i. c i) ls) ls) =
    sumlist (map2 (\<lambda>i j. i \<cdot>\<^sub>v s ! j) (map (\<lambda>i. c i) (filter (\<lambda>i. c i \<noteq> 0) ls)) (filter (\<lambda>i. c i \<noteq> 0) ls))"
  using assms(2)
proof (induction ls)
  case Nil
  then show ?case by auto
next
  case (Cons a s)
  then show ?case
    apply auto
    apply (subst smult_l_null)
     apply (simp add: assms(1) carrier_vecI)
    apply (subst left_zero_vec)
     apply (subst sumlist_carrier)
      apply auto
    by (metis (no_types, lifting) assms(1) carrier_dim_vec mem_Collect_eq nth_mem set_filter set_zip_rightD)
qed 

lemma two_set:
  assumes "distinct ls"
  assumes "set ls = set [a,b]"
  assumes "a \<noteq> b"
  shows "ls = [a,b] \<or> ls = [b,a]"
  apply (cases ls)
  using assms(2) apply auto[1]
proof -
  fix x xs
  assume ls:"ls = x # xs"
  obtain y ys where xs:"xs = y # ys"
    by (metis (no_types) \<open>ls = x # xs\<close> assms(2) assms(3) list.set_cases list.set_intros(1) list.set_intros(2) set_ConsD)
  have 1:"x = a \<or> x = b"
    using \<open>ls = x # xs\<close> assms(2) by auto
  have 2:"y = a \<or> y = b"
    using \<open>ls = x # xs\<close> \<open>xs = y # ys\<close> assms(2) by auto
  have 3:"ys = []"
    by (metis (no_types) \<open>ls = x # xs\<close> \<open>xs = y # ys\<close> assms(1) assms(2) distinct.simps(2) distinct_length_2_or_more in_set_member member_rec(2) neq_Nil_conv set_ConsD)
  show "ls = [a, b] \<or> ls = [b, a]" using ls xs 1 2 3 assms
    by auto
qed

lemma filter_disj_inds:
  assumes "i < length ls" "j < length ls" "i \<noteq> j"
  shows "filter (\<lambda>ia. ia \<noteq> j \<longrightarrow> ia = i) [0..<length ls] = [i, j] \<or>
  filter (\<lambda>ia. ia \<noteq> j \<longrightarrow> ia = i) [0..<length ls] = [j,i]"
proof -
  have 1: "distinct (filter (\<lambda>ia. ia = i \<or> ia = j) [0..<length ls])"
    using distinct_filter distinct_upt by blast
  have 2:"set (filter (\<lambda>ia. ia = i \<or> ia = j) [0..<length ls]) = {i, j}"
    using assms by auto
  show ?thesis using two_set[OF 1]
    using assms(3) empty_set filter_cong list.simps(15)
    by (smt "2" assms(3) empty_set filter_cong list.simps(15))
qed

lemma lincomb_list_indpt_distinct:
  assumes "\<And>v. v \<in> set ls \<Longrightarrow> dim_vec v = n"
  assumes
    "\<And>c. lincomb_list c ls = 0\<^sub>v n \<Longrightarrow> (\<forall>i. i < (length ls) \<longrightarrow> c i = 0)"
  shows "distinct ls"
  unfolding distinct_conv_nth
proof clarsimp
  fix i j
  assume ij: "i < length ls" "j < length ls" "i \<noteq> j" 
  assume lsij: "ls ! i = ls ! j"
  have "lincomb_list (\<lambda>k. if k = i then 1 else if k = j then -1 else 0) ls =
     (ls ! i) - (ls ! j)"
    unfolding lincomb_list_alt
    apply (subst lincomb_list_alt2[OF assms(1)])
      apply auto
    using  filter_disj_inds[OF ij]
    apply auto
    using ij(3) apply force
    using assms(1) ij(2) apply auto[1]
    using ij(3) apply blast
    using assms(1) ij(2) by auto
  also have "...  = 0\<^sub>v n" unfolding lsij
    apply (rule minus_cancel_vec)
    using \<open>j < length ls\<close> assms(1)
    using carrier_vec_dim_vec nth_mem by blast
  ultimately have "lincomb_list (\<lambda>k. if k = i then 1 else if k = j then -1 else 0) ls = 0\<^sub>v n" by auto
  from assms(2)[OF this]
  show False
    using \<open>i < length ls\<close> by auto
qed

end

locale conjugatable_vec_space = vec_space f_ty n for
  f_ty::"'a::conjugatable_ordered_field itself"
  and n
begin                                                           

lemma transpose_rank_mul_conjugate_transpose:
  fixes A :: "'a mat"
  assumes "A \<in> carrier_mat n nc"
  shows "vec_space.rank nc A\<^sup>H \<le> rank (A * A\<^sup>H)"
proof -
  have 1: "A\<^sup>H \<in> carrier_mat nc n" using assms by auto
  have 2: "A * A\<^sup>H \<in> carrier_mat n n" using assms by auto
      (* S is a maximal linearly independent set of rows A (or cols A\<^sup>T) *)
  let ?P = "(\<lambda>T. T \<subseteq> set (cols A\<^sup>H) \<and> module.lin_indpt class_ring (module_vec TYPE('a) nc) T)"
  have *:"\<And>A. ?P A \<Longrightarrow> finite A \<and> card A \<le> n"
  proof clarsimp
    fix S
    assume S: "S \<subseteq> set (cols A\<^sup>H)"
    have "card S \<le> card (set (cols A\<^sup>H))" using S
      using card_mono by blast
    also have "... \<le> length (cols A\<^sup>H)" using card_length by blast
    also have "... \<le> n" using assms by auto
    ultimately show "finite S \<and> card S \<le> n"
      by (meson List.finite_set S dual_order.trans finite_subset)
  qed
  have **:"?P {}"
    apply (subst module.lin_dep_def)
    by (auto simp add: vec_module)
  from maximal_exists[OF *]
  obtain S where S: "maximal S ?P" using **
    by (metis (no_types, lifting)) 
      (* Some properties of S *)
  from vec_space.rank_card_indpt[OF 1 S]
  have rankeq: "vec_space.rank nc A\<^sup>H = card S" .

  have s_hyp: "S \<subseteq> set (cols A\<^sup>H)"
    using S unfolding maximal_def by simp
  have modhyp: "module.lin_indpt class_ring (module_vec TYPE('a) nc) S" 
    using S unfolding maximal_def by simp

(* switch to a list representation *)
  obtain ss where ss: "set ss = S" "distinct ss"
    by (metis (mono_tags) S maximal_def set_obtain_sublist)
  have ss2: "set (map ((*\<^sub>v) A) ss) = (*\<^sub>v) A ` S"
    by (simp add: ss(1))
  have rw_hyp: "cols (mat_of_cols n (map ((*\<^sub>v) A) ss)) = cols  (A * mat_of_cols nc ss)" 
    unfolding cols_def apply (auto)
    using mat_vec_as_mat_mat_mult[of A n nc]
    by (metis (no_types, lifting) "1" assms carrier_matD(1) cols_dim mul_mat_of_cols nth_mem s_hyp ss(1) subset_code(1))
  then have rw: "mat_of_cols n (map ((*\<^sub>v) A) ss) = A * mat_of_cols nc ss"
    by (metis assms carrier_matD(1) index_mult_mat(2) mat_of_cols_carrier(2) mat_of_cols_cols) 
  have indpt: "\<And>c. lincomb_list c (map ((*\<^sub>v) A) ss) = 0\<^sub>v n \<Longrightarrow>
      \<forall>i. (i < (length ss) \<longrightarrow> c i = 0)"
  proof clarsimp
    fix c i
    assume *: "lincomb_list c (map ((*\<^sub>v) A) ss) = 0\<^sub>v n"
    assume i: "i < length ss"
    have "\<forall>w\<in>set (map ((*\<^sub>v) A) ss). dim_vec w = n"
      using assms by auto
    from lincomb_list_as_mat_mult[OF this]
    have "A * mat_of_cols nc ss *\<^sub>v  vec (length ss) c = 0\<^sub>v n"
      using * rw by auto
    then have hq: "A *\<^sub>v (mat_of_cols nc ss *\<^sub>v vec (length ss) c) =  0\<^sub>v n"
      by (metis assms assoc_mult_mat_vec mat_of_cols_carrier(1) vec_carrier)

    then have eq1: "(mat_of_cols nc ss *\<^sub>v vec (length ss) c) =  0\<^sub>v nc"
      apply (intro mat_mul_conjugate_transpose_sub_vec_eq_0)
      using assms ss s_hyp by auto

(* Rewrite the inner vector back to a lincomb_list *)
    have dim_hyp2: "\<forall>w\<in>set ss. dim_vec w = nc"
      using ss(1) s_hyp
      by (metis "1" carrier_matD(1) carrier_vecD cols_dim subsetD) 
    from vec_module.lincomb_list_as_mat_mult[OF this, symmetric]
    have "mat_of_cols nc ss *\<^sub>v vec (length ss) c = module.lincomb_list (module_vec TYPE('a) nc) c ss" .
    then have "module.lincomb_list (module_vec TYPE('a) nc) c ss = 0\<^sub>v nc" using eq1 by auto
    from vec_space.lin_indpt_lin_comb_list[OF ss(2) _ _ this i]
    show "c i = 0" using modhyp ss s_hyp
      using "1" cols_dim by blast
  qed
  have distinct: "distinct (map ((*\<^sub>v) A) ss)"
    by (metis (no_types, lifting) assms carrier_matD(1) dim_mult_mat_vec imageE indpt length_map lincomb_list_indpt_distinct ss2)
  then have 3: "card S = card ((*\<^sub>v) A ` S)"
    by (metis ss distinct_card image_set length_map)
  then have 4: "(*\<^sub>v) A ` S \<subseteq> set (cols (A * A\<^sup>H))"
    using cols_mat_mul \<open>S \<subseteq> set (cols A\<^sup>H)\<close> by blast
  have 5: "lin_indpt ((*\<^sub>v) A ` S)"
  proof clarsimp
    assume ld:"lin_dep ((*\<^sub>v) A ` S)"
    have *: "finite ((*\<^sub>v) A ` S)"
      by (metis List.finite_set ss2)
    have **: "(*\<^sub>v) A ` S \<subseteq> carrier_vec n"
      using "2" "4" cols_dim by blast
    from finite_lin_dep[OF * ld **]
    obtain a v where
      a: "lincomb a ((*\<^sub>v) A ` S) = 0\<^sub>v n" and
      v: "v \<in> (*\<^sub>v) A ` S" "a v \<noteq> 0" by blast
    obtain i where i:"v = map ((*\<^sub>v) A) ss ! i" "i < length ss"
      using v unfolding ss2[symmetric]
      using find_first_le nth_find_first by force
    from ss2[symmetric]
    have "set (map ((*\<^sub>v) A) ss)\<subseteq> carrier_vec n" using ** ss2 by auto
    from lincomb_as_lincomb_list_distinct[OF this distinct] have
      "lincomb_list
     (\<lambda>i. a (map ((*\<^sub>v) A) ss ! i))  (map ((*\<^sub>v) A) ss) = 0\<^sub>v n"
      using a ss2 by auto
    from indpt[OF this]
    show False using v i by simp
  qed
  from rank_ge_card_indpt[OF 2 4 5]
  have "card ((*\<^sub>v) A ` S) \<le> rank (A * A\<^sup>H)" .
  thus ?thesis using rankeq 3 by linarith
qed

lemma conjugate_transpose_rank_le:
  assumes "A \<in> carrier_mat n nc"
  shows "vec_space.rank nc (A\<^sup>H) \<le> rank A"
  by (metis assms carrier_matD(2) carrier_mat_triv dim_row_conjugate dual_order.trans index_transpose_mat(2) rank_mat_mul_right transpose_rank_mul_conjugate_transpose)

lemma conjugate_finsum:
  assumes f: "f : U \<rightarrow> carrier_vec n"
  shows "conjugate (finsum V f U) = finsum V (conjugate \<circ> f) U"
  using f
proof (induct U rule: infinite_finite_induct)
  case (infinite A)
  then show ?case by auto
next
  case empty
  then show ?case by auto
next
  case (insert u U)
  hence f: "f : U \<rightarrow> carrier_vec n" "f u : carrier_vec n"  by auto
  then have cf: "conjugate \<circ> f : U \<rightarrow> carrier_vec n"
    "(conjugate \<circ> f) u : carrier_vec n"
     apply (simp add: Pi_iff)
    by (simp add: f(2))
  then show ?case
    unfolding finsum_insert[OF insert(1) insert(2) f]
    unfolding finsum_insert[OF insert(1) insert(2) cf ]
    apply (subst conjugate_add_vec[of _ n])
    using f(2) apply blast
    using M.finsum_closed f(1) apply blast
    by (simp add: comp_def f(1) insert.hyps(3))
qed

lemma rank_conjugate_le:
  assumes A:"A \<in> carrier_mat n d"
  shows "rank (conjugate (A)) \<le> rank A"
proof -
  (* S is a maximal linearly independent set of (conjugate A) *)
  let ?P = "(\<lambda>T. T \<subseteq> set (cols (conjugate A)) \<and> lin_indpt T)"
  have *:"\<And>A. ?P A \<Longrightarrow> finite A \<and> card A \<le> d"
    by (metis List.finite_set assms card_length card_mono carrier_matD(2) cols_length dim_col_conjugate dual_order.trans rev_finite_subset)
  have **:"?P {}"
    by (simp add: finite_lin_indpt2)
  from maximal_exists[OF *]
  obtain S where S: "maximal S ?P" using **
    by (metis (no_types, lifting))
  have s_hyp: "S \<subseteq> set (cols (conjugate A))" "lin_indpt S"
    using S unfolding maximal_def
     apply blast
    by (metis (no_types, lifting) S maximal_def)
  from rank_card_indpt[OF _ S, of d]
  have rankeq: "rank (conjugate A) = card S" using assms by auto 
  have 1:"conjugate ` S \<subseteq> set (cols A)"
    using S apply auto
    by (metis (no_types, lifting) cols_conjugate conjugate_id image_eqI in_mono list.set_map s_hyp(1))
  have 2: "lin_indpt (conjugate ` S)"
    apply (rule ccontr)
    apply (auto simp add: lin_dep_def)
  proof -
    fix T c v
    assume T: "T \<subseteq> conjugate ` S" "finite T" and
      lc:"lincomb c T = 0\<^sub>v n" and "v \<in> T"  "c v \<noteq> 0"
    let ?T = "conjugate ` T"
    let ?c = "conjugate \<circ> c \<circ> conjugate"
    have 1: "finite ?T"  using T by auto
    have 2: "?T \<subseteq> S"  using T by auto
    have 3: "?c \<in> ?T \<rightarrow> UNIV" by auto
    have "lincomb ?c ?T = (\<Oplus>\<^bsub>V\<^esub>x\<in>T. conjugate (c x) \<cdot>\<^sub>v conjugate x)"
      unfolding lincomb_def
      apply (subst finsum_reindex)
        apply auto
       apply (metis "2" carrier_vec_conjugate assms carrier_matD(1) cols_dim image_eqI s_hyp(1) subsetD)
      by (meson conjugate_cancel_iff inj_onI)
    also have "... = (\<Oplus>\<^bsub>V\<^esub>x\<in>T. conjugate (c x \<cdot>\<^sub>v x)) "
      by (simp add: conjugate_smult_vec)
    also have "... = conjugate (\<Oplus>\<^bsub>V\<^esub>x\<in>T. (c x \<cdot>\<^sub>v x))"
      apply(subst conjugate_finsum[of "\<lambda>x.(c x \<cdot>\<^sub>v x)" T])
       apply (auto simp add:o_def)
      by (smt Matrix.carrier_vec_conjugate Pi_I' T(1) assms carrier_matD(1) cols_dim dim_row_conjugate imageE s_hyp(1) smult_carrier_vec subset_eq) 
    also have "... = conjugate (lincomb c T)"
      using lincomb_def by presburger
    ultimately have "lincomb ?c ?T = conjugate (lincomb c T)" by auto
    then have 4:"lincomb ?c ?T = 0\<^sub>v n" using lc by auto
    from not_lindepD[OF s_hyp(2) 1 2 3 4]
    have "conjugate \<circ> c \<circ> conjugate \<in> conjugate ` T \<rightarrow> {0}" .
    then have "c v = 0"
      by (simp add: Pi_iff \<open>v \<in> T\<close>)
    thus False using \<open>c v \<noteq> 0\<close> by auto
  qed
  from rank_ge_card_indpt[OF A 1 2]
  have 3:"card (conjugate ` S) \<le> rank A" .
  have 4: "card (conjugate ` S) = card S"
    apply (auto intro!: card_image)
    by (meson conjugate_cancel_iff inj_onI)
  show ?thesis using rankeq 3 4 by auto
qed

lemma rank_conjugate:
  assumes "A \<in> carrier_mat n d"
  shows "rank (conjugate A) = rank A"
  using  rank_conjugate_le
  by (metis carrier_vec_conjugate assms conjugate_id dual_order.antisym)

end (* exit the context *)

lemma conjugate_transpose_rank:
  fixes A::"'a::{conjugatable_ordered_field} mat"
  shows "vec_space.rank (dim_row A) A = vec_space.rank (dim_col A) (A\<^sup>H)"
  using  conjugatable_vec_space.conjugate_transpose_rank_le
  by (metis (no_types, lifting) Matrix.transpose_transpose carrier_matI conjugate_id dim_col_conjugate dual_order.antisym index_transpose_mat(2) transpose_conjugate)

lemma transpose_rank:
  fixes A::"'a::{conjugatable_ordered_field} mat"
  shows "vec_space.rank (dim_row A) A = vec_space.rank (dim_col A) (A\<^sup>T)"
  by (metis carrier_mat_triv conjugatable_vec_space.rank_conjugate conjugate_transpose_rank index_transpose_mat(2))

lemma rank_mat_mul_left:
  fixes A::"'a::{conjugatable_ordered_field} mat"
  assumes "A \<in> carrier_mat n d"
  assumes "B \<in> carrier_mat d nc"
  shows "vec_space.rank n (A * B) \<le> vec_space.rank d B"
  by (metis (no_types, lifting) Matrix.transpose_transpose assms(1) assms(2) carrier_matD(1) carrier_matD(2) carrier_mat_triv conjugatable_vec_space.rank_conjugate conjugate_transpose_rank index_mult_mat(3) index_transpose_mat(3) transpose_mult vec_space.rank_mat_mul_right)

section "Results on Invertibility"

(* Extract specific columns of a matrix  *)
definition take_cols :: "'a mat \<Rightarrow> nat list \<Rightarrow> 'a mat"
  where "take_cols A inds = mat_of_cols (dim_row A) (map ((!) (cols A)) (filter ((>) (dim_col A)) inds))"

definition take_cols_var :: "'a mat \<Rightarrow> nat list \<Rightarrow> 'a mat"
  where "take_cols_var A inds = mat_of_cols (dim_row A) (map ((!) (cols A)) (inds))"

definition take_rows :: "'a mat \<Rightarrow> nat list \<Rightarrow> 'a mat"
  where "take_rows A inds = mat_of_rows (dim_col A) (map ((!) (rows A)) (filter ((>) (dim_row A)) inds))"

lemma cong1:
  "x = y \<Longrightarrow>  mat_of_cols n x = mat_of_cols n y"
  by auto

lemma nth_filter:
  assumes "j < length (filter P ls)"
  shows "P  ((filter P ls) ! j)"
  by (simp add: assms list_ball_nth)

lemma take_cols_mat_mul:
  assumes "A \<in> carrier_mat nr n"
  assumes "B \<in> carrier_mat n nc"
  shows "A * take_cols B inds = take_cols (A * B) inds"
proof -
  have "\<And>j. j < length (map ((!) (cols B)) (filter ((>) nc) inds)) \<Longrightarrow>
      (map ((!) (cols B)) (filter ((>) nc) inds)) ! j \<in> carrier_vec n"
    using assms apply auto
    apply (subst cols_nth)
    using nth_filter by auto
  from mul_mat_of_cols[OF assms(1) this]
  have "A *  take_cols B inds = mat_of_cols nr (map (\<lambda>x. A *\<^sub>v cols B ! x) (filter ((>) (dim_col B)) inds))"
    unfolding take_cols_def using assms by (auto simp add: o_def)
  also have "... = take_cols (A * B) inds"
    unfolding take_cols_def using assms apply (auto intro!: cong1)
    by (simp add: mult_mat_vec_def)
  ultimately show ?thesis by auto
qed

lemma take_cols_carrier_mat:
  assumes "A \<in> carrier_mat nr nc"
  obtains n where "take_cols A inds \<in> carrier_mat nr n"
  unfolding take_cols_def
  using assms
  by fastforce

lemma take_cols_carrier_mat_strict:
  assumes "A \<in> carrier_mat nr nc"
  assumes "\<And>i. i \<in> set inds \<Longrightarrow> i < nc"
  shows "take_cols A inds \<in> carrier_mat nr (length inds)"
  unfolding take_cols_def
  using assms by auto

lemma gauss_jordan_take_cols:  
  assumes "gauss_jordan A (take_cols A inds) = (C,D)"
  shows "D = take_cols C inds"
proof -
  obtain nr nc where A: "A  \<in> carrier_mat nr nc" by auto
  from take_cols_carrier_mat[OF this]
  obtain n where B: "take_cols A inds \<in> carrier_mat nr n" by auto
  from gauss_jordan_transform[OF A B assms, of undefined]
  obtain P where PP:"P\<in>Units (ring_mat TYPE('a) nr undefined)" and
    CD: "C = P * A" "D = P * take_cols A inds" by blast
  have P: "P \<in> carrier_mat nr nr"
    by (metis (no_types, lifting) Units_def PP mem_Collect_eq partial_object.select_convs(1) ring_mat_def)
  from take_cols_mat_mul[OF P A]
  have "P * take_cols A inds = take_cols (P * A) inds" .
  thus ?thesis using CD by blast  
qed

lemma dim_col_take_cols:
  assumes "\<And>j. j \<in> set inds \<Longrightarrow> j < dim_col A"
  shows "dim_col (take_cols A inds) = length inds"
  unfolding take_cols_def
  using assms by auto

lemma dim_col_take_rows[simp]:
  shows "dim_col (take_rows A inds) = dim_col A"
  unfolding take_rows_def by auto

lemma cols_take_cols_subset:
  shows "set (cols (take_cols A inds)) \<subseteq> set (cols A)"
  unfolding take_cols_def
  apply (subst cols_mat_of_cols)
   apply auto
  using in_set_conv_nth by fastforce

lemma dim_row_take_cols[simp]:
  shows "dim_row (take_cols A ls) = dim_row A"
  by (simp add: take_cols_def)

lemma dim_row_append_rows[simp]:
  shows "dim_row (A @\<^sub>r B) = dim_row A + dim_row B"
  by (simp add: append_rows_def)

lemma rows_inj:
  assumes "dim_col A = dim_col B"
  assumes "rows A = rows B"
  shows "A = B"
  unfolding mat_eq_iff
  apply auto
    apply (metis assms(2) length_rows)
  using assms(1) apply blast
  by (metis assms(1) assms(2) mat_of_rows_rows)

lemma append_rows_index:
  assumes "dim_col A = dim_col B"
  assumes "i < dim_row A + dim_row B"
  assumes "j < dim_col A"
  shows "(A @\<^sub>r B) $$ (i,j) = (if i < dim_row A then A $$ (i,j) else B $$ (i-dim_row A,j))"
  unfolding append_rows_def
  apply (subst index_mat_four_block)
  using assms by auto

lemma row_append_rows:
  assumes "dim_col A = dim_col B"
  assumes "i < dim_row A + dim_row B"
  shows "row (A @\<^sub>r B) i = (if i < dim_row A then row A i else row B (i-dim_row A))"
  unfolding vec_eq_iff
  using assms by (auto simp add: append_rows_def)

lemma append_rows_mat_mul:
  assumes "dim_col A = dim_col B"
  shows "(A @\<^sub>r B) * C = A * C @\<^sub>r B * C"
  unfolding mat_eq_iff
  apply auto
   apply (simp add: append_rows_def)
  apply (subst index_mult_mat)
    apply auto
   apply (simp add: append_rows_def)
  apply (subst  append_rows_index)
     apply auto
    apply (simp add: append_rows_def)
   apply (metis add.right_neutral append_rows_def assms index_mat_four_block(3) index_mult_mat(1) index_mult_mat(3) index_zero_mat(3) row_append_rows trans_less_add1)
  by (metis add_cancel_right_right add_diff_inverse_nat append_rows_def assms index_mat_four_block(3) index_mult_mat(1) index_mult_mat(3) index_zero_mat(3) nat_add_left_cancel_less row_append_rows)

lemma cardlt:
  shows "card  {i. i < (n::nat)} \<le> n"
  by simp

lemma row_echelon_form_zero_rows:
  assumes row_ech: "row_echelon_form A"
  assumes dim_asm: "dim_col A \<ge> dim_row A"
  shows "take_rows A [0..<length (pivot_positions A)] @\<^sub>r  0\<^sub>m (dim_row A - length (pivot_positions A))  (dim_col A) = A"
proof -
  have ex_pivot_fun: "\<exists> f. pivot_fun A f (dim_col A)" using row_ech unfolding row_echelon_form_def by auto
  have len_help: "length (pivot_positions A) = card {i. i < dim_row A \<and> row A i \<noteq> 0\<^sub>v (dim_col A)}"
    using ex_pivot_fun pivot_positions[where A = "A",where nr = "dim_row A", where nc = "dim_col A"]
    by auto
  then have len_help2: "length (pivot_positions A) \<le> dim_row A"
    by (metis (no_types, lifting) card_mono cardlt finite_Collect_less_nat le_trans mem_Collect_eq subsetI)
  have fileq: "filter (\<lambda>y. y < dim_row A) [0..< length (pivot_positions A)] = [0..<length (pivot_positions A)]"
    apply (rule filter_True)
    using len_help2 by auto
  have "\<forall>n. card {i. i < n  \<and> row A i \<noteq> 0\<^sub>v (dim_col A)} \<le> n"
  proof clarsimp 
    fix n
    have h: "\<forall>x. x \<in> {i. i < n \<and> row A i \<noteq> 0\<^sub>v (dim_col A)} \<longrightarrow> x\<in>{..<n}"
      by simp
    then have h1: "{i. i < n  \<and> row A i \<noteq> 0\<^sub>v (dim_col A)} \<subseteq> {..<n}"
      by blast
    then have h2: "(card {i. i < n  \<and> row A i \<noteq> 0\<^sub>v (dim_col A)}::nat) \<le> (card {..<n}::nat)"
      using card_mono by blast 
    then show "(card {i. i < n \<and> row A i \<noteq> 0\<^sub>v (dim_col A)}::nat) \<le> (n::nat)" using h2 card_lessThan[of n]
      by auto
  qed
  then have pivot_len: "length (pivot_positions A) \<le> dim_row A "  using len_help
    by simp
  have alt_char: "mat_of_rows (dim_col A)
         (map ((!) (rows A)) (filter (\<lambda>y. y < dim_col A) [0..<length (pivot_positions A)])) = 
      mat_of_rows (dim_col A) (map ((!) (rows A))  [0..<length (pivot_positions A)])"
    using pivot_len dim_asm
    by auto
  have h1: "\<And>i j. i < dim_row A \<Longrightarrow>
           j < dim_col A \<Longrightarrow>
           i < dim_row (take_rows A [0..<length (pivot_positions A)]) \<Longrightarrow>
           take_rows A [0..<length (pivot_positions A)] $$ (i, j) = A $$ (i, j)"
  proof - 
    fix i 
    fix j
    assume "i < dim_row A"
    assume j_lt: "j < dim_col A"
    assume i_lt: "i < dim_row (take_rows A [0..<length (pivot_positions A)])" 
    have lt: "length (pivot_positions A) \<le> dim_row A" using pivot_len by auto
    have h1: "take_rows A [0..<length (pivot_positions A)] $$ (i, j) = (row (take_rows A [0..<length (pivot_positions A)]) i)$j"
      by (simp add: i_lt j_lt)
    then have h2: "(row (take_rows A [0..<length (pivot_positions A)]) i)$j = (row A i)$j"
      using lt alt_char i_lt unfolding take_rows_def by auto
    show "take_rows A [0..<length (pivot_positions A)] $$ (i, j) = A $$ (i, j)"
      using h1 h2
      by (simp add: \<open>i < dim_row A\<close> j_lt) 
  qed
  let ?nc = "dim_col A"
  let ?nr = "dim_row A"
  have h2: "\<And>i j. i < dim_row A \<Longrightarrow>
           j < dim_col A \<Longrightarrow>
           \<not> i < dim_row (take_rows A [0..<length (pivot_positions A)]) \<Longrightarrow>
           0\<^sub>m (dim_row A - length (pivot_positions A)) (dim_col A) $$
           (i - dim_row (take_rows A [0..<length (pivot_positions A)]), j) =
           A $$ (i, j)"
  proof - 
    fix i
    fix j
    assume lt_i: "i < dim_row A"
    assume lt_j: "j < dim_col A"
    assume not_lt: "\<not> i < dim_row (take_rows A [0..<length (pivot_positions A)])"
    let ?ip = "i+1"
    have h0: "\<exists>f. pivot_fun A f (dim_col A) \<and> f i = ?nc"
    proof -  
      have half1: "\<exists>f. pivot_fun A f (dim_col A)" using assms unfolding row_echelon_form_def
        by blast
      have half2: "\<forall>f. pivot_fun A f (dim_col A) \<longrightarrow> f i = ?nc " 
      proof clarsimp
        fix f
        assume is_piv: "pivot_fun A f (dim_col A)"
        have len_pp: "length (pivot_positions A) = card {i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc}" using is_piv pivot_positions[of A ?nr ?nc f]
          by auto
        have  "\<forall>i. (i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc) \<longleftrightarrow>  (i < ?nr \<and> f i \<noteq> ?nc)"
          using is_piv pivot_fun_zero_row_iff[of A f ?nc ?nr]
          by blast
        then have len_pp_var: "length (pivot_positions A) = card {i. i < ?nr \<and> f i \<noteq> ?nc}" 
          using len_pp  by auto 
        have allj_hyp: "\<forall>j < ?nr. f j = ?nc \<longrightarrow> ((Suc j) < ?nr \<longrightarrow> f (Suc j) = ?nc)" 
          using is_piv unfolding pivot_fun_def 
          using lt_i
          by (metis le_antisym le_less) 
        have if_then_bad: "f i \<noteq> ?nc \<longrightarrow> (\<forall>j. j \<le> i \<longrightarrow> f j \<noteq> ?nc)"
        proof clarsimp 
          fix j
          assume not_i: "f i \<noteq> ?nc"
          assume j_leq: "j \<le> i"
          assume bad_asm: "f j = ?nc"
          have "\<And>k. k \<ge> j \<Longrightarrow>  k < ?nr \<Longrightarrow> f k = ?nc"
          proof -
            fix k :: nat
            assume a1: "j \<le> k"
            assume a2: "k < dim_row A"
            have f3: "\<And>n. \<not> n < dim_row A \<or> f n \<noteq> f j \<or> \<not> Suc n < dim_row A \<or> f (Suc n) = f j"
              using allj_hyp bad_asm by presburger
            obtain nn :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> nat" where
              f4: "\<And>n na p nb nc. (\<not> n \<le> na \<or> Suc n \<le> Suc na) \<and> (\<not> p nb \<or> \<not> nc \<le> nb \<or> \<not> p (nn nc nb p) \<or> p nc) \<and> (\<not> p nb \<or> \<not> nc \<le> nb \<or> p nc \<or> p (Suc (nn nc nb p)))"
              using inc_induct order_refl by moura
            then have f5: "\<And>p. \<not> p k \<or> p j \<or> p (Suc (nn j k p))"
              using a1 by presburger
            have f6: "\<And>p. \<not> p k \<or> \<not> p (nn j k p) \<or> p j"
              using f4 a1 by meson
            { assume "nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A) < dim_row A \<and> f (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A)) \<noteq> dim_col A"
              moreover
              { assume "(nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A) < dim_row A \<and> f (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A)) \<noteq> dim_col A) \<and> (\<not> j < dim_row A \<or> f j = dim_col A)"
                then have "\<not> k < dim_row A \<or> f k = dim_col A"
                  using f6
                  by (metis (mono_tags, lifting)) }
              ultimately have "(\<not> j < dim_row A \<or> f j = dim_col A) \<and> (\<not> Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A)) < dim_row A \<or> f (Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A))) = dim_col A) \<or> \<not> k < dim_row A \<or> f k = dim_col A"
                using bad_asm
                by blast }
            moreover
            { assume "(\<not> j < dim_row A \<or> f j = dim_col A) \<and> (\<not> Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A)) < dim_row A \<or> f (Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A))) = dim_col A)"
              then have "\<not> k < dim_row A \<or> f k = dim_col A"
                using f5
              proof -
                have "\<not> (Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A)) < dim_row A \<and> f (Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A))) \<noteq> dim_col A) \<and> \<not> (j < dim_row A \<and> f j \<noteq> dim_col A)"
                  using \<open>(\<not> j < dim_row A \<or> f j = dim_col A) \<and> (\<not> Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A)) < dim_row A \<or> f (Suc (nn j k (\<lambda>n. n < dim_row A \<and> f n \<noteq> dim_col A))) = dim_col A)\<close> by linarith
                then have "\<not> (k < dim_row A \<and> f k \<noteq> dim_col A)"
                  by (metis (mono_tags, lifting) a2 bad_asm f5 le_less)
                then show ?thesis
                  by meson
              qed }
            ultimately show "f k = dim_col A"
              using f3 a2 by (metis (lifting) Suc_lessD bad_asm)
          qed
          then show "False" using lt_i not_i
            using j_leq by blast 
        qed
        have "f i \<noteq> ?nc \<longrightarrow> ({0..<?ip} \<subseteq> {y. y < ?nr \<and> f y \<noteq> dim_col A})"
        proof -
          have h1: "f i \<noteq> dim_col A \<longrightarrow> (\<forall>j\<le>i. j < ?nr \<and> f j \<noteq> dim_col A)"
            using if_then_bad lt_i by auto
          then show ?thesis by auto
        qed
        then have gteq: "f i \<noteq> ?nc \<longrightarrow> (card {i. i < ?nr \<and> f i \<noteq> dim_col A} \<ge> (i+1))"
          using card_lessThan[of ?ip] card_mono[where B = "{i. i < ?nr \<and> f i \<noteq> dim_col A} ", where A = "{0..<?ip}"]
          by auto
        then have clear: "dim_row (take_rows A [0..<length (pivot_positions A)]) = length (pivot_positions A)"
          unfolding take_rows_def using dim_asm fileq by (auto)
        have "i + 1 > length (pivot_positions A)" using not_lt clear by auto
        then show "f i = ?nc" using gteq len_pp_var by auto
      qed
      show ?thesis using half1 half2
        by blast 
    qed
    then have h1a: "row A i =  0\<^sub>v (dim_col A)" 
      using pivot_fun_zero_row_iff[of A _ ?nc ?nr]
      using lt_i by blast
    then have h1: "A $$ (i, j) = 0"
      using index_row(1) lt_i lt_j by fastforce 
    have h2a: "i - dim_row (take_rows A [0..<length (pivot_positions A)]) < dim_row A - length (pivot_positions A)"
      using pivot_len lt_i not_lt
      by (simp add: take_rows_def)
    then have h2: "0\<^sub>m (dim_row A - length (pivot_positions A)) (dim_col A) $$
           (i - dim_row (take_rows A [0..<length (pivot_positions A)]), j) = 0 " 
      unfolding zero_mat_def using pivot_len lt_i lt_j
      using index_mat(1) by blast 
    then show "0\<^sub>m (dim_row A - length (pivot_positions A)) (dim_col A) $$
           (i - dim_row (take_rows A [0..<length (pivot_positions A)]), j) =
           A $$ (i, j)" using h1 h2
      by simp 
  qed
  have h3: "(dim_row (take_rows A [0..<length (pivot_positions A)])::nat) + ((dim_row A::nat) - (length (pivot_positions A)::nat)) =
    dim_row A"
  proof - 
    have h0: "dim_row (take_rows A [0..<length (pivot_positions A)]) = (length (pivot_positions A)::nat)" 
      by (simp add: take_rows_def fileq)
    then show ?thesis using add_diff_inverse_nat  pivot_len
      by linarith
  qed
  have h4: " \<And>i j. i < dim_row A \<Longrightarrow>
           j < dim_col A \<Longrightarrow>
           i < dim_row (take_rows A [0..<length (pivot_positions A)]) +
               (dim_row A - length (pivot_positions A))"
    using pivot_len
    by (simp add: h3) 
  then show ?thesis apply (subst mat_eq_iff)
    using h1 h2 h3 h4 by (auto simp add: append_rows_def)
qed

lemma length_pivot_positions_dim_row:
  assumes "row_echelon_form A"
  shows "length (pivot_positions A) \<le> dim_row A"
proof -
  have 1: "A \<in> carrier_mat (dim_row A) (dim_col A)" by auto
  obtain f where 2: "pivot_fun A f (dim_col A)"
    using assms row_echelon_form_def by blast
  from pivot_positions(4)[OF 1 2] have
    "length (pivot_positions A) = card {i. i < dim_row A \<and> row A i \<noteq> 0\<^sub>v (dim_col A)}" .
  also have "... \<le> card {i. i < dim_row A}"
    apply (rule card_mono)
    by auto
  ultimately show ?thesis by auto
qed

lemma rref_pivot_positions:
  assumes "row_echelon_form R"
  assumes R: "R \<in> carrier_mat nr nc"
  shows "\<And>i j. (i,j) \<in> set (pivot_positions R) \<Longrightarrow> i < nr \<and> j < nc"
proof -
  obtain f where f: "pivot_fun R f nc"
    using assms(1) assms(2) row_echelon_form_def by blast
  have *: "\<And>i. i < nr \<Longrightarrow> f i \<le> nc" using f
    using R pivot_funD(1) by blast
  from pivot_positions[OF R f]
  have "set (pivot_positions R) = {(i, f i) |i. i < nr \<and> f i \<noteq> nc}" by auto
  then have **: "set (pivot_positions R) = {(i, f i) |i. i < nr \<and> f i < nc}"
    using *
    by fastforce
  fix i j
  assume "(i, j) \<in> set (pivot_positions R)"
  thus "i < nr \<and> j < nc" using **
    by simp
qed

lemma pivot_fun_monoton: 
  assumes pf: "pivot_fun A f (dim_col A)"
  assumes dr: "dim_row A = nr"
  shows "\<And> i. i < nr \<Longrightarrow> (\<And> k. ((k < nr \<and> i < k) \<longrightarrow> f i \<le> f k))"
proof -
  fix i
  assume "i < nr"
  show "(\<And> k. ((k < nr \<and> i < k) \<longrightarrow> f i \<le> f k))"
  proof -
    fix k
    show "((k < nr \<and> i < k) \<longrightarrow> f i \<le> f k)"
    proof (induct k)
      case 0
      then show ?case
        by blast 
    next
      case (Suc k)
      then show ?case 
        by (smt dr le_less_trans less_Suc_eq less_imp_le_nat pf pivot_funD(1) pivot_funD(3))
    qed
  qed
qed

lemma pivot_positions_contains:
  assumes row_ech: "row_echelon_form A"
  assumes dim_h: "dim_col A \<ge> dim_row A"
  assumes "pivot_fun A f (dim_col A)"
  shows "\<forall>i < (length (pivot_positions A)). (i, f i) \<in> set (pivot_positions A)"
proof - 
  let ?nr = "dim_row A"
  let ?nc = "dim_col A"
  let ?pp = "pivot_positions A"          
  have i_nr: "\<forall>i < (length ?pp). i < ?nr" using rref_pivot_positions assms
    using length_pivot_positions_dim_row less_le_trans by blast 
  have i_nc: "\<forall>i < (length ?pp). f i < ?nc"
  proof clarsimp 
    fix i
    assume i_lt: "i < length ?pp"
    have fis_nc: "f i = ?nc \<Longrightarrow> (\<forall> k > i. k < ?nr \<longrightarrow> f k = ?nc)"
    proof -
      assume is_nc: "f i = ?nc"
      show "(\<forall> k > i. k < ?nr \<longrightarrow> f k = ?nc)" 
      proof clarsimp
        fix k
        assume k_gt: "k > i"
        assume k_lt: "k < ?nr"
        have fk_lt: "f k \<le> ?nc" using pivot_funD(1)[of A ?nr f ?nc k] k_lt apply (auto)
          using \<open>pivot_fun A f (dim_col A)\<close> by blast 
        show "f k = ?nc"
          using fk_lt is_nc k_gt k_lt assms pivot_fun_monoton[of A f ?nr i k]
          using \<open>pivot_fun A f (dim_col A)\<close> by auto 
      qed
    qed
    have ncimp: "f i = ?nc \<Longrightarrow> (\<forall> k \<ge>i. k \<notin> { i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc})"
    proof -
      assume nchyp: "f i = ?nc"
      show "(\<forall> k \<ge>i. k \<notin> { i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc})"
      proof clarsimp 
        fix k
        assume i_lt: "i \<le> k" 
        assume k_lt: "k < dim_row A"
        show "row A k = 0\<^sub>v (dim_col A) "
          using i_lt k_lt fis_nc
          using pivot_fun_zero_row_iff[of A f ?nc ?nr]
          using \<open>pivot_fun A f (dim_col A)\<close> le_neq_implies_less nchyp by blast 
      qed
    qed
    then have "f i = ?nc \<Longrightarrow> card { i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc} \<le> i"
    proof - 
      assume nchyp: "f i = ?nc"
      have h: "{ i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc} \<subseteq> {0..<i}"
        using atLeast0LessThan le_less_linear nchyp ncimp by blast
      then show " card { i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc} \<le> i"
        using card_lessThan
        using subset_eq_atLeast0_lessThan_card by blast 
    qed
    then show "f i < ?nc" using i_lt pivot_positions(4)[of A ?nr ?nc f]
      apply (auto)
      by (metis \<open>pivot_fun A f (dim_col A)\<close> i_nr le_neq_implies_less not_less pivot_funD(1)) 
  qed
  then show ?thesis
    using pivot_positions(1)
    by (smt \<open>pivot_fun A f (dim_col A)\<close> carrier_matI i_nr less_not_refl mem_Collect_eq)
qed

lemma pivot_positions_form_helper_1:
  shows "(a, b) \<in> set (pivot_positions_main_gen z A nr nc i j) \<Longrightarrow> i \<le> a"
proof  (induct i j rule: pivot_positions_main_gen.induct[of nr nc A z])
  case (1 i j)
  then show ?case using  pivot_positions_main_gen.simps[of z A nr nc i j]
    apply (auto)
    by (smt Suc_leD le_refl old.prod.inject set_ConsD)
qed

lemma pivot_positions_form_helper_2:
  shows "strict_sorted (map fst (pivot_positions_main_gen z A nr nc i j))"
proof  (induct i j rule: pivot_positions_main_gen.induct[of nr nc A z])
  case (1 i j)
  then show ?case using  pivot_positions_main_gen.simps[of z A nr nc i j]
    apply (auto) using pivot_positions_form_helper_1
    by (simp add: pivot_positions_form_helper_1 Suc_le_lessD)
qed

lemma sorted_pivot_positions:
  shows "strict_sorted (map fst (pivot_positions A))"
  using pivot_positions_form_helper_2
  by (simp add: pivot_positions_form_helper_2 pivot_positions_gen_def) 

lemma pivot_positions_form:
  assumes row_ech: "row_echelon_form A"
  assumes dim_h: "dim_col A \<ge> dim_row A"
  shows "\<forall> i < (length (pivot_positions A)). fst ((pivot_positions A) ! i) = i"
proof clarsimp 
  let ?nr = "dim_row A"
  let ?nc = "dim_col A"
  let ?pp = "pivot_positions A :: (nat \<times> nat) list"
  fix i
  assume i_lt: "i < length (pivot_positions A)"
  have "\<exists>f. pivot_fun A f ?nc" using row_ech unfolding row_echelon_form_def
    by blast
  then obtain f where pf:"pivot_fun A f ?nc"
    by blast                  
  have all_f_in: "\<forall>i < (length ?pp). (i, f i) \<in> set ?pp"
    using pivot_positions_contains pf
      assms 
    by blast   
  have sorted_hyp: "\<And> (p::nat) (q::nat). p < (length ?pp) \<Longrightarrow> q < (length ?pp) \<Longrightarrow> p < q \<Longrightarrow> (fst (?pp ! p) < fst (?pp ! q))"
  proof -
    fix p::nat
    fix q::nat
    assume p_lt: "p < q"
    assume p_welldef: "p < (length ?pp)"
    assume q_welldef: "q < (length ?pp)"
    show "fst (?pp ! p) < fst (?pp ! q)"
      using sorted_pivot_positions p_lt p_welldef q_welldef apply (auto)
      by (smt find_first_unique length_map nat_less_le nth_map p_welldef sorted_nth_mono sorted_pivot_positions strict_sorted_iff)     
  qed
  have h: "i < (length ?pp) \<longrightarrow> fst (pivot_positions A ! i) = i"
  proof (induct i)
    case 0
    have "\<exists>j. fst (pivot_positions A ! j) = 0"
      by (metis all_f_in fst_conv i_lt in_set_conv_nth length_greater_0_conv list.size(3) not_less0)
    then obtain j where jth:" fst (pivot_positions A ! j) = 0"
      by blast      
    have "j \<noteq> 0 \<longrightarrow> (fst (pivot_positions A ! 0) > 0 \<longrightarrow> j \<le> 0)"
      using sorted_hyp apply (auto)
      by (metis all_f_in fst_conv i_lt in_set_conv_nth length_greater_0_conv list.size(3) neq0_conv not_less0)  
    then show ?case
      using jth neq0_conv by blast
  next
    case (Suc i)
    have ind_h: "i < length (pivot_positions A) \<longrightarrow> fst (pivot_positions A ! i) = i"
      using Suc.hyps by blast 
    have thesis_h: "(Suc i) < length (pivot_positions A) \<Longrightarrow> fst (pivot_positions A ! (Suc i)) = (Suc i)"
    proof - 
      assume suc_i_lt: "(Suc i) < length (pivot_positions A)"
      have fst_i_is: "fst (pivot_positions A ! i) = i" using suc_i_lt ind_h
        using Suc_lessD by blast 
      have "(\<exists>j < (length ?pp). fst (pivot_positions A ! j) = (Suc i))"
        by (metis suc_i_lt all_f_in fst_conv  in_set_conv_nth)
      then obtain j where jth: "j < (length ?pp) \<and> fst (pivot_positions A ! j) = (Suc i)"
        by blast
      have "j > i"
        using sorted_hyp apply (auto)
        by (metis Suc_lessD \<open>fst (pivot_positions A ! i) = i\<close> jth less_not_refl linorder_neqE_nat n_not_Suc_n suc_i_lt)
      have "j > (Suc i) \<Longrightarrow> False"
      proof -
        assume j_gt: "j > (Suc i)"
        then have h1: "fst (pivot_positions A ! (Suc i)) > i"
          using fst_i_is sorted_pivot_positions
          using sorted_hyp suc_i_lt by force
        have "fst (pivot_positions A ! j) > fst (pivot_positions A ! (Suc i))"
          using jth j_gt sorted_hyp apply (auto)
          by fastforce 
        then have h2: "fst (pivot_positions A ! (Suc i)) < (Suc i)" 
          using jth
          by simp   
        show "False" using h1 h2
          using not_less_eq by blast 
      qed
      show "fst (pivot_positions A ! (Suc i)) = (Suc i)"
        using Suc_lessI \<open>Suc i < j \<Longrightarrow> False\<close> \<open>i < j\<close> jth by blast
    qed
    then show ?case
      by blast 
  qed
  then show "fst (pivot_positions A ! i) = i"
    using i_lt by auto
qed

lemma take_cols_pivot_eq:
  assumes row_ech: "row_echelon_form A"
  assumes dim_h: "dim_col A \<ge> dim_row A"
  shows "take_cols A (map snd (pivot_positions A)) =
    1\<^sub>m (length (pivot_positions A)) @\<^sub>r
    0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A))"
proof - 
  let ?nr = "dim_row A"
  let ?nc = "dim_col A"
  have h1: " dim_col
     (1\<^sub>m (length (pivot_positions A)) @\<^sub>r
      0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A))) = (length (pivot_positions A))"
    by (simp add: append_rows_def)
  have len_pivot: "length (pivot_positions A) = card {i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc}"
    using row_ech pivot_positions(4) row_echelon_form_def by blast
  have pp_leq_nc: "\<forall>f. pivot_fun A f ?nc \<longrightarrow> (\<forall>i < ?nr. f i \<le> ?nc)" unfolding pivot_fun_def
    by meson 
  have pivot_set: "\<exists>f. pivot_fun A f ?nc \<and> set (pivot_positions A) = {(i, f i) | i. i < ?nr \<and> f i \<noteq> ?nc}"
    using row_ech row_echelon_form_def pivot_positions(1)
    by (smt (verit) Collect_cong carrier_matI)
  then have pivot_set_alt: "\<exists>f. pivot_fun A f ?nc \<and> set (pivot_positions A) = {(i, f i) | i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc}"
    using pivot_positions pivot_fun_zero_row_iff Collect_cong carrier_mat_triv
    by (smt (verit, best))
  have "\<exists>f. pivot_fun A f ?nc \<and> set (pivot_positions A) = {(i, f i) | i. f i \<le> ?nc \<and> i < ?nr \<and> f i \<noteq> ?nc}"
    using pivot_set pp_leq_nc by auto
  then have pivot_set_var: "\<exists>f. pivot_fun A f ?nc \<and> set (pivot_positions A) = {(i, f i) | i. i < ?nr \<and> f i < ?nc}"
    by auto
  have "length (map snd (pivot_positions A)) = card (set (map snd (pivot_positions A)))" 
    using row_ech row_echelon_form_def pivot_positions(3) distinct_card[where xs = "map snd (pivot_positions A)"]
    by (metis carrier_mat_triv)
  then have "length (map snd (pivot_positions A)) = card (set (pivot_positions A))"
    by (metis card_distinct distinct_card distinct_map length_map) 
  then have "length (map snd (pivot_positions A)) = card {i. i < ?nr \<and> row A i \<noteq> 0\<^sub>v ?nc}"
    using pivot_set_alt
    by (simp add: len_pivot) 
  then have length_asm: "length (map snd (pivot_positions A)) = length (pivot_positions A)"
    using len_pivot by linarith
  then have "\<forall>a. List.member (map snd (pivot_positions A)) a \<longrightarrow> a < dim_col A"
  proof clarsimp 
    fix a
    assume a_in: "List.member (map snd (pivot_positions A)) a"
    have "\<exists>v \<in> set (pivot_positions A). a = snd v" 
      using a_in in_set_member[where xs = "(pivot_positions A)"] apply (auto)
      by (metis in_set_impl_in_set_zip2 in_set_member length_map snd_conv zip_map_fst_snd) 
    then show "a < dim_col A"
      using pivot_set_var in_set_member by auto
  qed
  then have h2b: "(filter (\<lambda>y. y < dim_col A) (map snd (pivot_positions A))) =  (map snd (pivot_positions A))"
    by (meson filter_True in_set_member)
  then have h2a: "length (map ((!) (cols A)) (filter (\<lambda>y. y < dim_col A) (map snd (pivot_positions A)))) = length (pivot_positions A)"
    using length_asm
    by (simp add: h2b) 
  then have h2: "length (pivot_positions A) \<le> dim_row A \<Longrightarrow>
    dim_col (take_cols A (map snd (pivot_positions A))) = (length (pivot_positions A))" 
    unfolding take_cols_def using mat_of_cols_carrier by auto
  have h_len: "length (pivot_positions A) \<le> dim_row A \<Longrightarrow>
    dim_col (take_cols A (map snd (pivot_positions A))) =
    dim_col
     (1\<^sub>m (length (pivot_positions A)) @\<^sub>r
      0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A)))" 
    using h1 h2
    by (simp add: h1 assms length_pivot_positions_dim_row)
  have h2: "\<And>i j. length (pivot_positions A) \<le> dim_row A \<Longrightarrow>
           i < dim_row A \<Longrightarrow>
           j < dim_col
                (1\<^sub>m (length (pivot_positions A)) @\<^sub>r
                 0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A))) \<Longrightarrow>
           take_cols A (map snd (pivot_positions A)) $$ (i, j) =
           (1\<^sub>m (length (pivot_positions A)) @\<^sub>r
            0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A))) $$
           (i, j)" 
  proof -
    fix i 
    fix j 
    let ?pp = "(pivot_positions A)"
    assume len_lt: "length (pivot_positions A) \<le> dim_row A" 
    assume i_lt: " i < dim_row A" 
    assume j_lt: "j < dim_col
                (1\<^sub>m (length (pivot_positions A)) @\<^sub>r
                 0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A)))"
    let ?w = "((map snd (pivot_positions A)) ! j)"
    have breaking_it_down: "mat_of_cols (dim_row A)
     (map ((!) (cols A)) (map snd (pivot_positions A))) $$ (i, j)  
     =  ((cols A) ! ?w) $ i"
      apply (auto)
      by (metis comp_apply h1 i_lt j_lt length_map mat_of_cols_index nth_map) 
    have h1a: "i < (length ?pp) \<Longrightarrow> (mat_of_cols (dim_row A) (map ((!) (cols A)) (map snd (pivot_positions A))) $$ (i, j) 
        = (1\<^sub>m (length (pivot_positions A))) $$ (i, j))"
    proof - 
      (* need to, using row_ech, rely heavily on pivot_fun_def, that num_cols \<ge> num_rows, and row_echelon form*)
      assume "i < (length ?pp)"
      have "\<exists>f. pivot_fun A f ?nc" using row_ech unfolding row_echelon_form_def
        by blast
      then obtain f where "pivot_fun A f ?nc"
        by blast
      have j_nc: "j < (length ?pp)" using j_lt
        by (simp add: h1) 
      then have j_lt_nr: "j < ?nr" using dim_h
        using len_lt by linarith 
      then have is_this_true: "(pivot_positions A) ! j = (j, f j)" 
        using pivot_positions_form pivot_positions(1)[of A ?nr ?nc f]
      proof -
        have "pivot_positions A ! j \<in> set (pivot_positions A)"
          using j_nc nth_mem by blast
        then have "\<exists>n. pivot_positions A ! j = (n, f n) \<and> n < dim_row A \<and> f n \<noteq> dim_col A"
          using \<open>\<lbrakk>A \<in> carrier_mat (dim_row A) (dim_col A); pivot_fun A f (dim_col A)\<rbrakk> \<Longrightarrow> set (pivot_positions A) = {(i, f i) |i. i < dim_row A \<and> f i \<noteq> dim_col A}\<close> \<open>pivot_fun A f (dim_col A)\<close> by blast
        then show ?thesis
          by (metis (no_types) \<open>\<And>A. \<lbrakk>row_echelon_form A; dim_row A \<le> dim_col A\<rbrakk> \<Longrightarrow> \<forall>i<length (pivot_positions A). fst (pivot_positions A ! i) = i\<close> dim_h fst_conv j_nc row_ech)
      qed
      then have w_is: "?w = f j"
        by (metis h1 j_lt nth_map snd_conv)
      have h0: "i = j \<longrightarrow> ((cols A) ! ?w) $ i = 1" using w_is pivot_funD(4)[of A ?nr f ?nc i]
        by (metis \<open>\<forall>a. List.member (map snd (pivot_positions A)) a \<longrightarrow> a < dim_col A\<close> \<open>i < length (pivot_positions A)\<close> \<open>pivot_fun A f (dim_col A)\<close> cols_length i_lt in_set_member length_asm mat_of_cols_cols mat_of_cols_index nth_mem)
      have h1:  "i \<noteq> j \<longrightarrow> ((cols A) ! ?w) $ i = 0" using w_is pivot_funD(5)
        by (metis \<open>\<forall>a. List.member (map snd (pivot_positions A)) a \<longrightarrow> a < dim_col A\<close> \<open>pivot_fun A f (dim_col A)\<close> cols_length h1 i_lt in_set_member j_lt len_lt length_asm less_le_trans mat_of_cols_cols mat_of_cols_index nth_mem)
      show "(mat_of_cols (dim_row A) (map ((!) (cols A)) (map snd (pivot_positions A))) $$ (i, j) 
        = (1\<^sub>m (length (pivot_positions A))) $$ (i, j))" using h0 h1 breaking_it_down
        by (metis \<open>i < length (pivot_positions A)\<close> h2 h_len index_one_mat(1) j_lt len_lt) 
    qed
    have h1b: "i \<ge> (length ?pp) \<Longrightarrow> (mat_of_cols (dim_row A) (map ((!) (cols A)) (map snd (pivot_positions A))) $$ (i, j)  = 0)"
    proof - 
      assume i_gt: "i \<ge> (length ?pp)"
      have h0a: "((cols A) ! ((map snd (pivot_positions A)) ! j)) $ i = (row A i) $ ?w"
        by (metis \<open>\<forall>a. List.member (map snd (pivot_positions A)) a \<longrightarrow> a < dim_col A\<close> cols_length h1 i_lt in_set_member index_row(1) j_lt length_asm mat_of_cols_cols mat_of_cols_index nth_mem)
      have h0b: 
        "take_rows A [0..<length (pivot_positions A)] @\<^sub>r 0\<^sub>m (dim_row A - length (pivot_positions A)) (dim_col A) = A"
        using assms row_echelon_form_zero_rows[of A]
        by blast 
      then have h0c: "(row A i) = 0\<^sub>v (dim_col A)"  using i_gt
        using add_diff_cancel_right' add_less_cancel_left diff_is_0_eq' dim_col_take_rows dim_row_append_rows i_lt index_zero_mat(2) index_zero_mat(3) le_add_diff_inverse len_lt less_not_refl3 row_append_rows row_zero zero_less_diff
        by (smt add_diff_cancel_right' add_less_cancel_left diff_is_0_eq' dim_col_take_rows dim_row_append_rows i_lt index_zero_mat(2) index_zero_mat(3) le_add_diff_inverse len_lt less_not_refl3 row_append_rows row_zero zero_less_diff) 
      then show ?thesis using h0a breaking_it_down apply (auto)
        by (metis \<open>\<forall>a. List.member (map snd (pivot_positions A)) a \<longrightarrow> a < dim_col A\<close> h1 in_set_member index_zero_vec(1) j_lt length_asm nth_mem) 
    qed
    have h1: " mat_of_cols (dim_row A)
     (map ((!) (cols A)) (map snd (pivot_positions A))) $$ (i, j) =
           (1\<^sub>m (length (pivot_positions A)) @\<^sub>r
            0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A))) $$
           (i, j) " using h1a h1b
      apply (auto)
      by (smt add_diff_inverse_nat add_less_cancel_left append_rows_index h1 i_lt index_one_mat(2) index_one_mat(3) index_zero_mat(1) index_zero_mat(2) index_zero_mat(3) j_lt len_lt not_less)  
    then show "take_cols A (map snd (pivot_positions A)) $$ (i, j) =
           (1\<^sub>m (length (pivot_positions A)) @\<^sub>r
            0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A))) $$
           (i, j)" 
      unfolding take_cols_def
      by (simp add: h2b)
  qed
  show ?thesis
    unfolding mat_eq_iff
    using length_pivot_positions_dim_row[OF assms(1)] h_len h2 by auto
qed

lemma rref_right_mul:
  assumes "row_echelon_form A"
  assumes "dim_col A \<ge> dim_row A"
  shows
    "take_cols A (map snd (pivot_positions A)) * take_rows A [0..<length (pivot_positions A)] = A"
proof -
  from take_cols_pivot_eq[OF assms] have
    1: "take_cols A (map snd (pivot_positions A)) =
    1\<^sub>m (length (pivot_positions A)) @\<^sub>r
    0\<^sub>m (dim_row A - length (pivot_positions A)) (length (pivot_positions A))" .
  have 2: "take_cols A (map snd (pivot_positions A)) * take_rows A [0..<length (pivot_positions A)] =
    take_rows A [0..<length (pivot_positions A)]  @\<^sub>r 0\<^sub>m (dim_row A - length (pivot_positions A)) (dim_col A)"
    unfolding 1
    apply (auto simp add: append_rows_mat_mul)
    by (smt add_diff_cancel_right' assms diff_diff_cancel dim_col_take_rows dim_row_append_rows index_zero_mat(2) left_mult_one_mat' left_mult_zero_mat' length_pivot_positions_dim_row row_echelon_form_zero_rows)   
  from row_echelon_form_zero_rows[OF assms] have
    "... = A" .
  thus ?thesis
    by (simp add: "2")
qed

context conjugatable_vec_space begin

lemma lin_indpt_id:
  shows "lin_indpt (set (cols (1\<^sub>m n)::'a vec list))"
proof -
  have *: "set (cols (1\<^sub>m n)) = set (rows (1\<^sub>m n))"
    by (metis cols_transpose transpose_one)
  have "det (1\<^sub>m n) \<noteq> 0" using det_one by auto
  from det_not_0_imp_lin_indpt_rows[OF _ this]
  have "lin_indpt (set (rows (1\<^sub>m n)))"
    using one_carrier_mat by blast
  thus ?thesis
    by (simp add: *) 
qed

lemma lin_indpt_take_cols_id:
  shows "lin_indpt (set (cols (take_cols (1\<^sub>m n) inds)))"
proof - 
  have subset_h: "set (cols (take_cols (1\<^sub>m n) inds)) \<subseteq> set (cols (1\<^sub>m n)::'a vec list)"
    using cols_take_cols_subset by blast
  then show ?thesis using lin_indpt_id subset_li_is_li by auto
qed

lemma cols_id_unit_vecs:
  shows "cols (1\<^sub>m d) = unit_vecs d"
  unfolding unit_vecs_def list_eq_iff_nth_eq
  by auto

lemma distinct_cols_id:
  shows "distinct (cols (1\<^sub>m d)::'a vec list)"
  by (simp add: conjugatable_vec_space.cols_id_unit_vecs vec_space.unit_vecs_distinct)

lemma distinct_map_nth:
  assumes "distinct ls"
  assumes "distinct inds"
  assumes "\<And>j. j \<in> set inds \<Longrightarrow> j < length ls"
  shows "distinct (map ((!) ls) inds)"
  by (simp add: assms(1) assms(2) assms(3) distinct_map inj_on_nth)

lemma distinct_take_cols_id:
  assumes "distinct inds"
  shows "distinct (cols (take_cols (1\<^sub>m n) inds) :: 'a vec list)"
  unfolding take_cols_def
  apply (subst cols_mat_of_cols)
   apply (auto intro!:  distinct_map_nth simp add: distinct_cols_id)
  using assms distinct_filter by blast

lemma rank_take_cols:
  assumes "distinct inds"
  shows "rank (take_cols (1\<^sub>m n) inds) = length (filter ((>) n) inds)"
  apply (subst lin_indpt_full_rank[of _ "length (filter ((>) n) inds)"])
     apply (auto simp add: lin_indpt_take_cols_id)
   apply (metis (full_types) index_one_mat(2) index_one_mat(3) length_map mat_of_cols_carrier(1) take_cols_def)
  by (simp add: assms distinct_take_cols_id)

lemma rank_mul_left_invertible_mat:
  fixes A::"'a mat"
  assumes "invertible_mat A"
  assumes "A \<in> carrier_mat n n"
  assumes "B \<in> carrier_mat n nc"
  shows "rank (A * B) = rank B"
proof -
  obtain C where C: "inverts_mat A C" "inverts_mat C A"
    using assms invertible_mat_def by blast 
  from C have ceq: "C * A = 1\<^sub>m n"
    by (metis assms(2) carrier_matD(2) index_mult_mat(3) index_one_mat(3) inverts_mat_def)
  then have *:"B = C*A*B"
    using assms(3) by auto
  from rank_mat_mul_left[OF assms(2-3)]
  have **: "rank (A*B) \<le> rank B" .
  have 1: "C \<in> carrier_mat n n" using C ceq
    by (metis assms(2) carrier_matD(1) carrier_matI index_mult_mat(3) index_one_mat(3) inverts_mat_def) 
  have 2: "A * B \<in> carrier_mat n nc" using assms by auto  
  have "rank B = rank (C* A * B)" using * by auto
  also have "... \<le> rank (A*B)" using rank_mat_mul_left[OF 1 2]
    using "1" assms(2) assms(3) by auto
  ultimately show ?thesis using ** by auto
qed

lemma invertible_take_cols_rank:
  fixes A::"'a mat"
  assumes "invertible_mat A"
  assumes "A \<in> carrier_mat n n"
  assumes "distinct inds"
  shows "rank (take_cols A inds) = length (filter ((>) n) inds)"
proof -
  have " A = A * 1\<^sub>m n" using assms(2) by auto
  then have "take_cols A inds = A * take_cols (1\<^sub>m n) inds"
    by (metis assms(2) one_carrier_mat take_cols_mat_mul)
  then have "rank (take_cols A inds) = rank (take_cols (1\<^sub>m n) inds)"
    by (metis assms(1) assms(2) conjugatable_vec_space.rank_mul_left_invertible_mat one_carrier_mat take_cols_carrier_mat)
  thus ?thesis
    by (simp add: assms(3) conjugatable_vec_space.rank_take_cols)
qed

lemma rank_take_cols_leq:
  assumes R:"R \<in> carrier_mat n nc"
  shows "rank (take_cols R ls) \<le> rank R"
proof -
  from take_cols_mat_mul[OF R]
  have "take_cols R ls =  R * take_cols (1\<^sub>m nc) ls"
    by (metis assms one_carrier_mat right_mult_one_mat)
  thus ?thesis
    by (metis assms one_carrier_mat take_cols_carrier_mat vec_space.rank_mat_mul_right)
qed

lemma rank_take_cols_geq:
  assumes R:"R \<in> carrier_mat n nc"
  assumes t:"take_cols R ls \<in> carrier_mat n r"
  assumes B:"B \<in> carrier_mat r nc"
  assumes "R = (take_cols R ls) * B"
  shows "rank (take_cols R ls) \<ge> rank R"
  by (metis B assms(4) t vec_space.rank_mat_mul_right)

lemma rref_drop_pivots:
  assumes row_ech: "row_echelon_form R"
  assumes dims: "R \<in> carrier_mat n nc"
  assumes order: "nc \<ge> n"
  shows "rank (take_cols R (map snd (pivot_positions R))) = rank R"
proof -
  let ?B = "take_rows R [0..<length (pivot_positions R)]"
  have equa: "R = take_cols R (map snd (pivot_positions R)) * ?B" using assms rref_right_mul
    by (metis carrier_matD(1) carrier_matD(2))
  have ex_r: "\<exists>r. take_cols R (map snd (pivot_positions R)) \<in> carrier_mat n r \<and> ?B \<in> carrier_mat r nc"
  proof - 
    have h1:
      "take_cols R (map snd (pivot_positions R)) \<in> carrier_mat n (length (pivot_positions R))"
      using assms
      by (metis in_set_impl_in_set_zip2 length_map rref_pivot_positions take_cols_carrier_mat_strict zip_map_fst_snd)
    have "\<exists> f. pivot_fun R f nc" using row_ech unfolding row_echelon_form_def using dims
      by blast
    then have "length (pivot_positions R) = card {i. i < n \<and> row R i \<noteq> 0\<^sub>v nc}"
      using pivot_positions[of R n nc]
      using dims by auto 
    then have "nc \<ge> length (pivot_positions R)" using order
      using carrier_matD(1) dims dual_order.trans length_pivot_positions_dim_row row_ech by blast
    then have "dim_col R \<ge> length (pivot_positions R)" using dims by auto
    then have h2: "?B \<in> carrier_mat (length (pivot_positions R)) nc" unfolding take_rows_def
      using dims 
      by (smt atLeastLessThan_iff carrier_matD(2) filter_True le_eq_less_or_eq length_map length_pivot_positions_dim_row less_trans map_nth mat_of_cols_carrier(1) row_ech set_upt transpose_carrier_mat transpose_mat_of_rows) 
    show ?thesis using h1 h2
      by blast
  qed
    (* prove the other two dimensionality assumptions *)
  have "rank R  \<le> rank (take_cols R (map snd (pivot_positions R)))"
    using dims ex_r rank_take_cols_geq[where R = "R", where B = "?B", where ls = "(map snd (pivot_positions R))", where nc = "nc"]
    using equa by blast
  thus ?thesis
    using assms(2) conjugatable_vec_space.rank_take_cols_leq le_antisym by blast
qed

lemma gjs_and_take_cols_var:
  fixes A::"'a mat"
  assumes A:"A \<in> carrier_mat n nc"
  assumes order: "nc \<ge> n"
  shows "(take_cols A (map snd (pivot_positions (gauss_jordan_single A)))) = 
  (take_cols_var A (map snd (pivot_positions (gauss_jordan_single A))))"
proof -
  let ?gjs = "(gauss_jordan_single A)"
  have "\<forall>x. List.member (map snd (pivot_positions (gauss_jordan_single A))) x \<longrightarrow> x \<le> dim_col A"  
    using rref_pivot_positions gauss_jordan_single(3) carrier_matD(2) gauss_jordan_single(2) in_set_impl_in_set_zip2 in_set_member length_map less_irrefl less_trans not_le_imp_less zip_map_fst_snd
    by (smt A carrier_matD(2) gauss_jordan_single(2) in_set_impl_in_set_zip2 in_set_member length_map less_irrefl less_trans not_le_imp_less zip_map_fst_snd)
  then have "(filter (\<lambda>y. y < dim_col A) (map snd (pivot_positions (gauss_jordan_single A)))) = 
    (map snd (pivot_positions (gauss_jordan_single A)))"
    by (metis (no_types, lifting) A carrier_matD(2) filter_True gauss_jordan_single(2) gauss_jordan_single(3) in_set_impl_in_set_zip2 length_map rref_pivot_positions zip_map_fst_snd)
  then show ?thesis unfolding take_cols_def take_cols_var_def
    by simp
qed

lemma gauss_jordan_single_rank:
  fixes A::"'a mat"
  assumes A:"A \<in> carrier_mat n nc"
  assumes order: "nc \<ge> n"
  shows "rank (take_cols A (map snd (pivot_positions (gauss_jordan_single A)))) = rank A"
proof -
  let ?R = "gauss_jordan_single A"
  obtain P where P:"P\<in>Units (ring_mat TYPE('a) n undefined)" and
    i: "?R = P * A" using gauss_jordan_transform[OF A]
    using A assms det_mult det_non_zero_imp_unit det_one gauss_jordan_single(4) mult_not_zero one_neq_zero
    by (smt A assms det_mult det_non_zero_imp_unit det_one gauss_jordan_single(4) mult_not_zero one_neq_zero)
  have pcarrier: "P \<in> carrier_mat n n" using P unfolding Units_def
    by (auto simp add: ring_mat_def)
  have "invertible_mat P" using P unfolding invertible_mat_def Units_def inverts_mat_def
    apply auto
     apply (simp add: ring_mat_simps(5))
    by (metis index_mult_mat(2) index_one_mat(2) ring_mat_simps(1) ring_mat_simps(3))
  then
  obtain Pi where Pi: "invertible_mat Pi" "Pi * P = 1\<^sub>m n"
  proof -
    assume a1: "\<And>Pi. \<lbrakk>invertible_mat Pi; Pi * P = 1\<^sub>m n\<rbrakk> \<Longrightarrow> thesis"
    have "dim_row P = n"
      by (metis (no_types) A assms(1) carrier_matD(1) gauss_jordan_single(2) i index_mult_mat(2))
    then show ?thesis
      using a1 by (metis (no_types) \<open>invertible_mat P\<close> index_mult_mat(3) index_one_mat(3) invertible_mat_def inverts_mat_def square_mat.simps)
  qed
  then have pi_carrier:"Pi \<in> carrier_mat n n"
    by (metis carrier_mat_triv index_mult_mat(2) index_one_mat(2) invertible_mat_def square_mat.simps)
  have R1:"row_echelon_form ?R"
    using assms(2) gauss_jordan_single(3) by blast
  have R2: "?R \<in> carrier_mat n nc"
    using A assms(2) gauss_jordan_single(2) by auto
  have Rcm: "take_cols ?R (map snd (pivot_positions ?R))
    \<in> carrier_mat n (length (map snd (pivot_positions ?R)))"
    apply (rule take_cols_carrier_mat_strict[OF R2])
    using rref_pivot_positions[OF R1 R2] by auto
  have "Pi * ?R = A" using i Pi
    by (smt A \<open>invertible_mat P\<close> assoc_mult_mat carrier_mat_triv index_mult_mat(2) index_mult_mat(3) index_one_mat(3) invertible_mat_def left_mult_one_mat square_mat.simps)
  then have "rank (take_cols A (map snd (pivot_positions ?R))) = rank (take_cols (Pi * ?R) (map snd (pivot_positions ?R)))"
    by auto
  also have "... = rank ( Pi * take_cols ?R (map snd (pivot_positions ?R)))"
    by (metis A gauss_jordan_single(2) pi_carrier take_cols_mat_mul)
  also have "... = rank (take_cols ?R (map snd (pivot_positions ?R)))"
    by (intro rank_mul_left_invertible_mat[OF Pi(1) pi_carrier Rcm])
  also have "... = rank ?R"
    using assms(2) conjugatable_vec_space.rref_drop_pivots gauss_jordan_single(3)
    using R1 R2 by blast
  ultimately show ?thesis                                                            
    using A \<open>P \<in> carrier_mat n n\<close> \<open>invertible_mat P\<close> conjugatable_vec_space.rank_mul_left_invertible_mat i
    by auto
qed

lemma lin_indpt_subset_cols:
  fixes A:: "'a mat"
  fixes B:: "'a vec set"
  assumes "A \<in> carrier_mat n n"
  assumes inv: "invertible_mat A"
  assumes "B \<subseteq> set (cols A)"
  shows "lin_indpt B"
proof -
  have "det A \<noteq> 0"
    using assms(1) inv invertible_det by blast
  then have "lin_indpt (set (rows A\<^sup>T))"
    using assms(1) idom_vec.lin_dep_cols_imp_det_0 by auto
  thus ?thesis using subset_li_is_li assms(3)
    by auto
qed

lemma rank_invertible_subset_cols:
  fixes A:: "'a mat"
  fixes B:: "'a vec list"
  assumes inv: "invertible_mat A"
  assumes A_square: "A \<in> carrier_mat n n"
  assumes set_sub: "set (B) \<subseteq> set (cols A)"
  assumes dist_B: "distinct B"
  shows "rank (mat_of_cols n B) = length B"
proof - 
  let ?B_mat = "(mat_of_cols n B)"
  have h1: "lin_indpt (set(B))" 
    using assms lin_indpt_subset_cols[of A] by auto
  have "set B \<subseteq> carrier_vec n"
    using set_sub A_square cols_dim[of A] by auto
  then have cols_B: "cols (mat_of_cols n B) = B" using cols_mat_of_cols by auto
  then have "maximal (set B) (\<lambda>T. T \<subseteq> set (B) \<and> lin_indpt T)" using h1
    by (simp add: maximal_def subset_antisym)
  then have h2: "maximal (set B) (\<lambda>T. T \<subseteq> set (cols (mat_of_cols n B)) \<and> lin_indpt T)"
    using cols_B by auto
  have h3: "rank (mat_of_cols n B) = card (set B)"
    using h1 h2 rank_card_indpt[of ?B_mat]
    using mat_of_cols_carrier(1) by blast 
  then show ?thesis using assms distinct_card by auto
qed

end

end