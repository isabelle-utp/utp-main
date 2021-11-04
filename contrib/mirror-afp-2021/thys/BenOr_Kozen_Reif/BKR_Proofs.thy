theory BKR_Proofs
  imports "Matrix_Equation_Construction"

begin

definition well_def_signs:: "nat => rat list list \<Rightarrow> bool"
  where "well_def_signs num_polys sign_conds \<equiv> \<forall> signs \<in> set(sign_conds). (length signs = num_polys)"

definition satisfies_properties:: "real poly \<Rightarrow> real poly list \<Rightarrow> nat list list \<Rightarrow> rat list list \<Rightarrow> rat mat \<Rightarrow> bool"
  where "satisfies_properties p qs subsets signs matrix = 
  ( all_list_constr subsets (length qs) \<and> well_def_signs (length qs) signs \<and> distinct signs
  \<and> satisfy_equation p qs subsets signs \<and>  invertible_mat matrix  \<and> matrix = matrix_A signs subsets
  \<and> set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)
  )"

section "Base Case"

lemma mat_base_case:
  shows "matrix_A [[1],[-1]] [[],[0]] = (mat_of_rows_list 2 [[1, 1], [1, -1]])"
  unfolding matrix_A_def mtx_row_def z_def apply (auto)
  by (simp add: numeral_2_eq_2)

lemma base_case_sgas:
  fixes q p:: "real poly"
  assumes nonzero: "p \<noteq> 0"
  assumes rel_prime: "coprime p q"
  shows "set (characterize_consistent_signs_at_roots_copr p [q]) \<subseteq> {[1], [- 1]}"
  unfolding characterize_consistent_signs_at_roots_copr_def consistent_sign_vec_copr_def by auto

lemma base_case_sgas_alt:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  assumes len1: "length qs = 1"
  assumes nonzero: "p \<noteq> 0"
  assumes rel_prime: "\<forall>q. (List.member qs q) \<longrightarrow> coprime p q"
  shows "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> {[1], [- 1]}"
proof - 
  have ex_q: "\<exists>(q::real poly). qs = [q]" 
    using len1    
    using length_Suc_conv[of qs 0] by auto
  then show ?thesis using base_case_sgas nonzero rel_prime
    apply (auto)
    using characterize_consistent_signs_at_roots_copr_def consistent_sign_vec_copr_def by auto
qed

lemma base_case_satisfy_equation:
  fixes q p:: "real poly"
  assumes nonzero: "p \<noteq> 0"
  assumes rel_prime: "coprime p q"
  shows "satisfy_equation p [q] [[],[0]] [[1],[-1]]"
proof - 
  have h1: "set (characterize_consistent_signs_at_roots_copr p [q]) \<subseteq> {[1], [- 1]}"
    using base_case_sgas assms by auto
  have h2: " \<forall>qa. List.member [q] qa \<longrightarrow> coprime p qa" using rel_prime
    by (simp add: member_rec(1) member_rec(2))
  have h3: "all_list_constr [[], [0]] (Suc 0)" unfolding all_list_constr_def
    by (simp add: list_constr_def member_def)
  then show ?thesis using matrix_equation[where p = "p", where qs = "[q]", where signs = "[[1],[-1]]", where subsets = "[[],[0]]"]
      nonzero h1 h2 h3 by auto
qed

lemma base_case_satisfy_equation_alt:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  assumes len1: "length qs = 1"
  assumes nonzero: "p \<noteq> 0"
  assumes rel_prime: "\<forall>q. (List.member qs q) \<longrightarrow> coprime p q"
  shows "satisfy_equation p qs [[],[0]] [[1],[-1]]"
proof - 
  have ex_q: "\<exists>(q::real poly). qs = [q]" 
    using len1    
    using length_Suc_conv[of qs 0] by auto
  then show ?thesis using base_case_satisfy_equation nonzero rel_prime
    apply (auto)
    by (simp add: member_rec(1)) 
qed

lemma base_case_matrix_eq:
  fixes q p:: "real poly"
  assumes nonzero: "p \<noteq> 0"
  assumes rel_prime: "coprime p q"
  shows "(mult_mat_vec (mat_of_rows_list 2 [[1, 1], [1, -1]]) (construct_lhs_vector p [q] [[1],[-1]]) = 
    (construct_rhs_vector p [q] [[],[0]]))"                      
  using mat_base_case base_case_satisfy_equation unfolding satisfy_equation_def
  by (simp add: nonzero rel_prime)

lemma less_two:
  shows "j < Suc (Suc 0) \<longleftrightarrow> j = 0 \<or> j = 1" by auto 

lemma inverse_mat_base_case: 
  shows "inverts_mat (mat_of_rows_list 2 [[1/2, 1/2], [1/2, -(1/2)]]::rat mat) (mat_of_rows_list 2 [[1, 1], [1, -1]]::rat mat)"
  unfolding inverts_mat_def mat_of_rows_list_def mat_eq_iff apply auto
  unfolding less_two by (auto simp add: scalar_prod_def)

lemma inverse_mat_base_case_2: 
  shows "inverts_mat (mat_of_rows_list 2 [[1, 1], [1, -1]]::rat mat) (mat_of_rows_list 2 [[1/2, 1/2], [1/2, -(1/2)]]::rat mat) "
  unfolding inverts_mat_def mat_of_rows_list_def mat_eq_iff apply auto
  unfolding less_two by (auto simp add: scalar_prod_def)

lemma base_case_invertible_mat: 
  shows "invertible_mat (matrix_A [[1], [- 1]] [[], [0]])"
  unfolding invertible_mat_def using inverse_mat_base_case inverse_mat_base_case_2
  apply (auto)
   apply (simp add: mat_base_case mat_of_rows_list_def)
  using mat_base_case by auto 

section "Inductive Step"

subsection "Lemmas on smashing subsets and signs"

lemma signs_smash_property:
  fixes signs1 signs2 :: "'a list list"
  fixes a b:: "nat"
  shows "\<forall> (elem :: 'a list). (elem \<in> (set (signs_smash signs1 signs2)) \<longrightarrow> 
    (\<exists> n m :: nat. 
      elem = ((nth signs1 n)@(nth signs2 m))))"
proof clarsimp 
  fix elem 
  assume assum: "elem \<in> set (signs_smash signs1 signs2)"
  show "\<exists>n m. elem = signs1 ! n @ signs2 ! m"
    using assum unfolding signs_smash_def apply (auto)
    by (metis in_set_conv_nth) 
qed

lemma signs_smash_property_set:
  fixes signs1 signs2 :: "'a list list"
  fixes a b:: "nat"
  shows "\<forall> (elem :: 'a list). (elem \<in> (set (signs_smash signs1 signs2)) \<longrightarrow> 
    (\<exists> (elem1::'a list). \<exists> (elem2::'a list). 
      (elem1 \<in> set(signs1) \<and> elem2 \<in> set(signs2) \<and> elem = (elem1@elem2))))"
proof clarsimp 
  fix elem 
  assume assum: "elem \<in> set (signs_smash signs1 signs2)"
  show "\<exists>elem1. elem1 \<in> set signs1 \<and> (\<exists>elem2. elem2 \<in> set signs2 \<and> elem = elem1 @ elem2)"
    using assum unfolding signs_smash_def by auto
qed

lemma subsets_smash_property:
  fixes subsets1 subsets2 :: "nat list list"
  fixes n:: "nat"
  shows "\<forall> (elem :: nat list). (List.member (subsets_smash n subsets1 subsets2) elem) \<longrightarrow> 
    (\<exists> (elem1::nat list). \<exists> (elem2::nat list).
      (elem1 \<in> set(subsets1) \<and> elem2 \<in> set(subsets2) \<and> elem = (elem1 @ ((map ((+) n) elem2)))))"
proof - 
  let ?new_subsets = "(map (map ((+) n)) subsets2)"
    (* a slightly unorthodox use of signs_smash, but it closes the proof *)
  have "subsets_smash n subsets1 subsets2 = signs_smash subsets1 ?new_subsets" 
    unfolding subsets_smash_def signs_smash_def apply (auto)
    by (simp add: comp_def) 
  then show ?thesis
    by (smt imageE in_set_member set_map signs_smash_property_set)
qed

  (* If subsets for smaller systems are well-defined, then subsets for combined systems
   are well-defined *)
subsection "Well-defined subsets preserved when smashing"

lemma list_constr_append:
  "list_constr a n \<and> list_constr b n \<longrightarrow> list_constr (a@b) n"
  apply (auto) unfolding list_constr_def
  using list_all_append by blast 

lemma well_def_step: 
  fixes qs1 qs2 :: "real poly list"
  fixes subsets1 subsets2 :: "nat list list"
  assumes well_def_subsets1: "all_list_constr (subsets1) (length qs1)"
  assumes well_def_subsets2: "all_list_constr (subsets2) (length qs2)"
  shows "all_list_constr ((subsets_smash (length qs1) subsets1 subsets2))
     (length (qs1 @ qs2))"
proof - 
  have h1: "\<forall>elem.
     List.member (subsets_smash (length qs1) subsets1 subsets2) elem \<longrightarrow>
     (\<exists>elem1 elem2. elem1 \<in> set subsets1 \<and> elem2 \<in> set subsets2 \<and> elem = elem1 @ map ((+) (length qs1)) elem2)"
    using subsets_smash_property by blast
  have h2: "\<forall>elem1 elem2. (elem1 \<in> set subsets1 \<and> elem2 \<in> set subsets2) \<longrightarrow> list_constr (elem1 @ map ((+) (length qs1)) elem2) (length (qs1 @ qs2))"
  proof clarsimp 
    fix elem1
    fix elem2
    assume e1: "elem1 \<in> set subsets1"
    assume e2: "elem2 \<in> set subsets2"
    have h1: "list_constr elem1  (length qs1 + length qs2) " 
    proof - 
      have h1: "list_constr elem1  (length qs1)"  using e1 well_def_subsets1 
        unfolding all_list_constr_def
        by (simp add: in_set_member) 
      then show ?thesis unfolding list_constr_def
        by (simp add: list.pred_mono_strong) 
    qed
    have h2: "list_constr (map ((+) (length qs1)) elem2) (length qs1 + length qs2)"
    proof - 
      have h1: "list_constr elem2  (length qs2)"  using e2 well_def_subsets2 
        unfolding all_list_constr_def
        by (simp add: in_set_member) 
      then show ?thesis unfolding list_constr_def
        by (simp add: list_all_length)
    qed    
    show "list_constr (elem1 @ map ((+) (length qs1)) elem2) (length qs1 + length qs2)" 
      using h1 h2 list_constr_append
      by blast 
  qed
  then show ?thesis using h1 unfolding all_list_constr_def by auto
qed

subsection "Well def signs preserved when smashing"
lemma well_def_signs_step: 
  fixes qs1 qs2 :: "real poly list"
  fixes signs1 signs2 :: "rat list list"
  assumes "length qs1 > 0"
  assumes "length qs2 > 0"
  assumes well_def1: "well_def_signs (length qs1) signs1"
  assumes well_def2: "well_def_signs (length qs2) signs2"
  shows "well_def_signs (length (qs1@qs2)) (signs_smash signs1 signs2)"
  using well_def1 well_def2 unfolding well_def_signs_def using signs_smash_property_set[of signs1 signs2] length_append by auto

subsection "Distinct signs preserved when smashing"

lemma distinct_map_append:
  assumes "distinct ls"
  shows "distinct (map ((@) xs) ls)"
  unfolding distinct_map inj_on_def using assms by auto

lemma length_eq_append:
  assumes "length y = length b"
  shows "(x @ y = a @ b) \<longleftrightarrow> x=a \<and> y = b"
  by (simp add: assms)

lemma distinct_step:
  fixes qs1 qs2 :: "real poly list"
  fixes signs1 signs2 :: "rat list list"
  assumes well_def1: "well_def_signs n1 signs1"
  assumes well_def2: "well_def_signs n2 signs2"
  assumes distinct1: "distinct signs1"
  assumes distinct2: "distinct signs2"
  shows "distinct (signs_smash signs1 signs2)"
  unfolding signs_smash_def
  using distinct1
proof(induction signs1)
  case Nil
  then show ?case by auto
next
  case (Cons a signs1)
  then show ?case apply (auto simp add: distinct2 distinct_map_append)
    using assms unfolding well_def_signs_def
    by (simp add: distinct1 distinct2 length_eq_append)
qed

(* In this section we will show that if signs1 contains all consistent sign assignments and signs2 
contains all consistent sign assignments, then their smash contains all consistent sign assignments.  
Intuitively, this makes sense because signs1 and signs2 are carrying information about different 
sets of polynomials, and their smash contains all possible combinations of that information.
*)
subsection "Consistent sign assignments preserved when smashing"

lemma subset_smash_signs: 
  fixes a1 b1 a2 b2:: "rat list list"
  assumes sub1: "set a1 \<subseteq> set a2"
  assumes sub2: "set b1 \<subseteq> set b2"
  shows "set (signs_smash a1 b1) \<subseteq> set (signs_smash a2 b2)"
proof -
  have h1: "\<forall>x\<in>set (signs_smash a1 b1). x\<in>set (signs_smash a2 b2)"
  proof clarsimp 
    fix x
    assume x_in: "x \<in> set (signs_smash a1 b1)"
    have h1: "\<exists> n m :: nat. x = (nth a1 n)@(nth b1 m)"
      using signs_smash_property[of a1 b1] x_in
      by blast
    then have h2: "\<exists> p q::nat. x = (nth a2 p)@(nth b2 q)"
      using sub1 sub2 apply (auto)
      by (metis nth_find_first signs_smash_property_set subset_code(1) x_in) 
    then show "x \<in> set (signs_smash a2 b2)" 
      unfolding signs_smash_def apply (auto)
      using signs_smash_property_set sub1 sub2 x_in by fastforce 
  qed
  then show ?thesis
    by blast 
qed

lemma subset_helper:
  fixes p:: "real poly"
  fixes qs1 qs2 :: "real poly list"
  fixes signs1 signs2 :: "rat list list"
  shows "\<forall> x \<in> set (characterize_consistent_signs_at_roots_copr p (qs1 @ qs2)). 
        \<exists> x1 \<in> set (characterize_consistent_signs_at_roots_copr p qs1). 
        \<exists> x2 \<in> set (characterize_consistent_signs_at_roots_copr p qs2).
        x = x1@x2"
proof clarsimp 
  fix x
  assume  x_in: "x \<in> set (characterize_consistent_signs_at_roots_copr p (qs1 @ qs2))" 
  have x_in_csv: "x \<in> set(map (consistent_sign_vec_copr (qs1 @ qs2)) (characterize_root_list_p p))"  
    using x_in unfolding characterize_consistent_signs_at_roots_copr_def by simp
  have csv_hyp: "\<forall>r. consistent_sign_vec_copr (qs1 @ qs2) r = (consistent_sign_vec_copr qs1 r)@(consistent_sign_vec_copr qs2 r)"
    unfolding consistent_sign_vec_copr_def by auto
  have exr_iff: "(\<exists>r \<in> set (characterize_root_list_p p). x = consistent_sign_vec_copr (qs1 @ qs2) r) \<longleftrightarrow> (\<exists>r \<in> set (characterize_root_list_p p). x = (consistent_sign_vec_copr qs1 r)@(consistent_sign_vec_copr qs2 r))"
    using csv_hyp by auto
  have exr: "x \<in> set(map (consistent_sign_vec_copr (qs1 @ qs2)) (characterize_root_list_p p)) \<longrightarrow> (\<exists>r \<in> set (characterize_root_list_p p). x = consistent_sign_vec_copr (qs1 @ qs2) r)"
    by auto
  have mem_list1: "\<forall> r \<in> set (characterize_root_list_p p). (consistent_sign_vec_copr qs1 r) \<in> set(map (consistent_sign_vec_copr qs1) (characterize_root_list_p p))"
    by simp
  have mem_list2: "\<forall> r \<in> set (characterize_root_list_p p). (consistent_sign_vec_copr qs2 r) \<in> set(map (consistent_sign_vec_copr qs2) (characterize_root_list_p p))"
    by simp
  then show "\<exists>x1\<in>set (characterize_consistent_signs_at_roots_copr p qs1).
            \<exists>x2\<in>set (characterize_consistent_signs_at_roots_copr p qs2). x = x1 @ x2"
    using x_in_csv exr mem_list1 mem_list2 characterize_consistent_signs_at_roots_copr_def exr_iff by auto
qed

lemma subset_step:  
  fixes p:: "real poly"
  fixes qs1 qs2 :: "real poly list"
  fixes signs1 signs2 :: "rat list list"
  assumes csa1: "set (characterize_consistent_signs_at_roots_copr p qs1) \<subseteq> set (signs1)"
  assumes csa2: "set (characterize_consistent_signs_at_roots_copr p qs2) \<subseteq> set (signs2)"  
  shows "set (characterize_consistent_signs_at_roots_copr p
          (qs1 @ qs2))
    \<subseteq> set (signs_smash signs1 signs2)"
proof - 
  have h0: "\<forall> x \<in> set (characterize_consistent_signs_at_roots_copr p (qs1 @ qs2)). \<exists> x1 \<in> set (characterize_consistent_signs_at_roots_copr p qs1). \<exists> x2 \<in> set (characterize_consistent_signs_at_roots_copr p qs2).
     (x = x1@x2)" using subset_helper[of p qs1 qs2]
    by blast 
  then have "\<forall>x \<in> set (characterize_consistent_signs_at_roots_copr p (qs1 @ qs2)). 
          x \<in> set (signs_smash (characterize_consistent_signs_at_roots_copr p qs1) 
          (characterize_consistent_signs_at_roots_copr p qs2))"
    unfolding signs_smash_def apply (auto)
    by fastforce 
  then have "\<forall>x \<in> set (characterize_consistent_signs_at_roots_copr p
          (qs1 @ qs2)). x \<in> set (signs_smash signs1 signs2)"
    using csa1 csa2 subset_smash_signs[of _ signs1 _ signs2] apply (auto)
    by blast 
  thus ?thesis
    by blast 
qed

subsection "Main Results"

lemma dim_row_mat_of_rows_list[simp]:
  shows "dim_row (mat_of_rows_list nr ls) = length ls"
  unfolding mat_of_rows_list_def by auto

lemma dim_col_mat_of_rows_list[simp]:
  shows "dim_col (mat_of_rows_list nr ls) = nr"
  unfolding mat_of_rows_list_def by auto

lemma dim_row_matrix_A[simp]:
  shows "dim_row (matrix_A signs subsets) = length subsets"
  unfolding matrix_A_def by auto

lemma dim_col_matrix_A[simp]:
  shows "dim_col (matrix_A signs subsets) = length signs"
  unfolding matrix_A_def by auto

lemma length_signs_smash:
  shows
    "length (signs_smash signs1 signs2) = length signs1 * length signs2"
  unfolding signs_smash_def length_concat
  by (auto simp add: o_def sum_list_triv)

lemma length_subsets_smash:
  shows
    "length (subsets_smash n subs1 subs2) = length subs1 * length subs2"
  unfolding subsets_smash_def length_concat
  by (auto simp add: o_def sum_list_triv)

lemma length_eq_concat:
  assumes "\<And>x. x \<in> set ls \<Longrightarrow> length x = n"
  assumes "i < n * length ls"
  shows "concat ls ! i = ls ! (i div n) ! (i mod n)"
  using assms
proof (induct ls arbitrary: i)
  case Nil
  then show ?case
    by simp
next
  case (Cons a ls)
  then show ?case
    apply (auto simp add: nth_append)
    using div_if mod_geq by auto
qed

lemma z_append:
  assumes "\<And>i. i \<in> set xs \<Longrightarrow> i < length as"
  shows "z (xs @ (map ((+) (length as)) ys)) (as @ bs) = z xs as * z ys bs"
proof -
  have 1: "map ((!) (as @ bs)) xs = map ((!) as) xs"
    unfolding list_eq_iff_nth_eq
    using assms by (auto simp add:nth_append)
  have 2: "map ((!) (as @ bs) \<circ> (+) (length as)) ys = map ((!) bs) ys"
    unfolding list_eq_iff_nth_eq
    using assms by auto
  show ?thesis
    unfolding z_def apply auto
    unfolding 1 2 by auto
qed

(* Shows that the matrix of a smashed system is the Kronecker product of the matrices of the two
  systems being combined *)
lemma matrix_construction_is_kronecker_product: 
  fixes qs1 :: "real poly list"
  fixes subs1 subs2 :: "nat list list"
  fixes signs1 signs2 :: "rat list list"
    (* n1 is the number of polynomials in the "1" sets *)
  assumes "\<And>l i. l \<in> set subs1 \<Longrightarrow> i \<in> set l \<Longrightarrow> i < n1"
  assumes "\<And>j. j \<in> set signs1 \<Longrightarrow> length j = n1"
  shows "
    (matrix_A (signs_smash signs1 signs2) (subsets_smash n1 subs1 subs2)) =
    kronecker_product (matrix_A signs1 subs1) (matrix_A signs2 subs2)"
  unfolding mat_eq_iff dim_row_matrix_A dim_col_matrix_A
    length_subsets_smash length_signs_smash dim_kronecker
proof safe
  fix i j
  assume i: "i < length subs1 * length subs2"
     and j: "j < length signs1 * length signs2"
  have ld: "i div length subs2 < length subs1"
    "j div length signs2 < length signs1"
    using i j less_mult_imp_div_less by auto
  have lm: "i mod length subs2 < length subs2"
    "j mod length signs2 < length signs2"
    using i j less_mult_imp_mod_less by auto

  have n1: "n1 = length (signs1 ! (j div length signs2))"
    using assms(2) ld(2) nth_mem by blast

  have 1: "matrix_A (signs_smash signs1 signs2) (subsets_smash n1 subs1 subs2) $$ (i, j) =
    z (subsets_smash n1 subs1 subs2 ! i) (signs_smash signs1 signs2 ! j)"
    unfolding mat_of_rows_list_def matrix_A_def mtx_row_def
    using i j
    by (simp add: length_signs_smash length_subsets_smash)
  have 2: " ... = z (subs1 ! (i div length subs2) @ map ((+) n1) (subs2 ! (i mod length subs2)))
     (signs1 ! (j div length signs2) @ signs2 ! (j mod length signs2))"
    unfolding signs_smash_def subsets_smash_def
    apply (subst length_eq_concat)
    using i apply (auto simp add: mult.commute)
    apply (subst length_eq_concat)
    using j apply (auto simp add: mult.commute)
    using ld lm by auto
  have 3: "... =
  z (subs1 ! (i div length subs2)) (signs1 ! (j div length signs2)) *
  z (subs2 ! (i mod length subs2)) (signs2 ! (j mod length signs2))"
    unfolding n1
    apply (subst z_append)
     apply (auto simp add: n1[symmetric])
    using assms(1) ld(1) nth_mem by blast
  have 4: "kronecker_product (matrix_A signs1 subs1) (matrix_A signs2 subs2) $$ (i,j) =
    z (subs1 ! (i div length subs2))
     (signs1 ! (j div length signs2)) *
    z (subs2 ! (i mod length subs2))
     (signs2 ! (j mod length signs2))"
    unfolding kronecker_product_def matrix_A_def mat_of_rows_list_def mtx_row_def
    using i j apply (auto simp add: Let_def)
    apply (subst index_mat(1)[OF ld])
    apply (subst index_mat(1)[OF lm])
    using ld lm by auto
  show "matrix_A (signs_smash signs1 signs2) (subsets_smash n1 subs1 subs2) $$ (i, j) =
        kronecker_product (matrix_A signs1 subs1) (matrix_A signs2 subs2) $$ (i, j)"
    using 1 2 3 4 by auto 
qed

(* Given that two smaller systems satisfy some mild constraints, show that their combined system
  (after smashing the signs and subsets) satisfies the matrix equation, and that the matrix of the
  combined system is invertible. *)
lemma inductive_step:
  fixes p:: "real poly"
  fixes qs1 qs2 :: "real poly list"
  fixes subsets1 subsets2 :: "nat list list"
  fixes signs1 signs2 :: "rat list list"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes nontriv2: "length qs2 > 0"
  assumes pairwise_rel_prime1: "\<forall>q. ((List.member qs1 q) \<longrightarrow> (coprime p q))"
  assumes pairwise_rel_prime2: "\<forall>q. ((List.member qs2 q) \<longrightarrow> (coprime p q))"
  assumes welldefined_signs1: "well_def_signs (length qs1) signs1"
  assumes welldefined_signs2: "well_def_signs (length qs2) signs2"
  assumes distinct_signs1: "distinct signs1"
  assumes distinct_signs2: "distinct signs2"
  assumes all_info1: "set (characterize_consistent_signs_at_roots_copr p qs1) \<subseteq> set(signs1)"
  assumes all_info2: "set (characterize_consistent_signs_at_roots_copr p qs2) \<subseteq> set(signs2)"
  assumes welldefined_subsets1: "all_list_constr (subsets1) (length qs1)"
  assumes welldefined_subsets2: "all_list_constr (subsets2) (length qs2)"
  assumes invertibleMtx1: "invertible_mat (matrix_A signs1 subsets1)"
  assumes invertibleMtx2: "invertible_mat (matrix_A signs2 subsets2)"
  shows "satisfy_equation p (qs1@qs2) (subsets_smash (length qs1) subsets1 subsets2) (signs_smash signs1 signs2) 
        \<and> invertible_mat (matrix_A (signs_smash signs1 signs2) (subsets_smash (length qs1) subsets1 subsets2))"
proof - 
  have h1: "invertible_mat (matrix_A (signs_smash signs1 signs2) (subsets_smash (length qs1) subsets1 subsets2))"
    using matrix_construction_is_kronecker_product
      kronecker_invertible invertibleMtx1 invertibleMtx2
      welldefined_subsets1 welldefined_subsets2 unfolding all_list_constr_def list_constr_def
    by (smt in_set_conv_nth in_set_member list_all_length well_def_signs_def welldefined_signs1)
  have h2a: "distinct (signs_smash signs1 signs2)" 
    using distinct_signs1 distinct_signs2 welldefined_signs1 welldefined_signs2 nontriv1 nontriv2 
      distinct_step by auto
  have h2ba: "\<forall> q. List.member (qs1 @ qs2) q \<longrightarrow> (List.member qs1 q \<or> List.member qs2 q)" 
    unfolding member_def 
    by auto
  have h2b: "\<forall>q. ((List.member (qs1@qs2) q) \<longrightarrow> (coprime p q))" 
    using h2ba pairwise_rel_prime1 pairwise_rel_prime2 by auto
  have h2c: "all_list_constr ((subsets_smash (length qs1) subsets1 subsets2)) (length (qs1@qs2))" 
    using well_def_step
      welldefined_subsets1 welldefined_subsets2
    by blast
  have h2d: "set (characterize_consistent_signs_at_roots_copr p (qs1@qs2)) \<subseteq> set(signs_smash signs1 signs2)" 
    using subset_step all_info1 all_info2
    by simp 
  have h2: "satisfy_equation p (qs1@qs2) (subsets_smash (length qs1) subsets1 subsets2) (signs_smash signs1 signs2)"
    using matrix_equation[where p="p", where qs="qs1@qs2", where subsets = "subsets_smash (length qs1) subsets1 subsets2",
        where signs = "signs_smash signs1 signs2"] 
        h2a h2b h2c h2d apply (auto) using nonzero by blast
  show ?thesis using h1 h2 by blast
qed

section "Reduction Step Proofs"
  
(* Some definitions *)
definition get_matrix:: "(rat mat \<times> (nat list list \<times> rat list list)) \<Rightarrow> rat mat"
  where "get_matrix data = fst(data)"

definition get_subsets:: "(rat mat \<times> (nat list list \<times> rat list list)) \<Rightarrow> nat list list"
  where "get_subsets data = fst(snd(data))"

definition get_signs:: "(rat mat \<times> (nat list list \<times> rat list list)) \<Rightarrow> rat list list"
  where "get_signs data = snd(snd(data))"

definition reduction_signs:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list \<Rightarrow> nat list list \<Rightarrow> rat mat \<Rightarrow> rat list list" 
  where "reduction_signs p qs signs subsets matr = 
    (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets matr)))"

definition reduction_subsets:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list \<Rightarrow> nat list list \<Rightarrow> rat mat \<Rightarrow> nat list list" 
  where "reduction_subsets p qs signs subsets matr = 
    (take_indices subsets (rows_to_keep (reduce_mat_cols matr (solve_for_lhs p qs subsets matr))))"

(* Some basic lemmas *)
lemma reduction_signs_is_get_signs: "reduction_signs p qs signs subsets m =  get_signs (reduce_system p (qs, (m, (subsets, signs))))"
  unfolding reduction_signs_def get_signs_def
  by (metis reduce_system.simps reduction_step.elims snd_conv) 

lemma reduction_subsets_is_get_subsets: "reduction_subsets p qs signs subsets m =  get_subsets (reduce_system p (qs, (m, (subsets, signs))))"
  unfolding reduction_subsets_def get_subsets_def
  by (metis fst_conv reduce_system.simps reduction_step.elims snd_conv)

lemma find_zeros_from_vec_prop:
  fixes input_vec :: "rat vec"
  shows "\<forall>n < (dim_vec input_vec). ((input_vec $ n \<noteq> 0) \<longleftrightarrow>
         List.member (find_nonzeros_from_input_vec input_vec) n)"
proof - 
  have h1: "\<forall>n < (dim_vec input_vec). ((input_vec $ n \<noteq> 0) \<longrightarrow>  List.member (find_nonzeros_from_input_vec input_vec) n)" 
    unfolding find_nonzeros_from_input_vec_def List.member_def  by auto
  have h2: "\<forall>n < (dim_vec input_vec). (List.member (find_nonzeros_from_input_vec input_vec) n \<longrightarrow> (input_vec $ n \<noteq> 0) )" 
    unfolding find_nonzeros_from_input_vec_def List.member_def by auto
  show ?thesis using h1 h2 by auto
qed


subsection "Showing sign conditions preserved when reducing"

lemma take_indices_lem:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes arb_list :: "'a list list"
  fixes index_list :: "nat list" 
  fixes n:: "nat"
  assumes lest: "n < length (take_indices arb_list index_list)"
  assumes well_def: "\<forall>q.(List.member index_list q \<longrightarrow> q < length arb_list)"
  shows "\<exists>k<length arb_list.
            (take_indices arb_list index_list) ! n =  arb_list ! k"
  using lest well_def unfolding take_indices_def apply (auto)
  by (metis in_set_member nth_mem)

lemma invertible_means_mult_id:
  fixes A:: "'a::field mat"
  assumes assm: "invertible_mat A"
  shows "matr_option (dim_row A)
     (mat_inverse (A))*A = 1\<^sub>m (dim_row A)"
proof (cases "mat_inverse(A)")
  obtain n where n: "A \<in> carrier_mat n n"
    using assms invertible_mat_def square_mat.simps by blast
  case None
  then have "A \<notin> Units (ring_mat TYPE('a) n n)"
    by (simp add: mat_inverse(1) n)
  thus ?thesis
    by (meson assms det_non_zero_imp_unit invertible_Units n unit_imp_det_non_zero) 
next
  case (Some a)
  then show ?thesis
    by (metis assms carrier_matI invertible_mat_def mat_inverse(2) matr_option.simps(2) square_mat.elims(2))
qed

lemma dim_invertible:
  fixes A:: "'a::field mat"
  fixes n:: "nat"
  assumes assm: "invertible_mat A"
  assumes dim: "A \<in> carrier_mat n n"
  shows "matr_option (dim_row A)
     (mat_inverse (A)) \<in> carrier_mat n n"
proof (cases "mat_inverse(A)")
  obtain n where n: "A \<in> carrier_mat n n"
    using assms invertible_mat_def square_mat.simps by blast
  case None
  then have "A \<notin> Units (ring_mat TYPE('a) n n)"
    by (simp add: mat_inverse(1) n)
  thus ?thesis
    by (meson assms det_non_zero_imp_unit invertible_Units n unit_imp_det_non_zero) 
next
  case (Some a)
  then show ?thesis
    using dim mat_inverse(2) by auto 
qed

lemma mult_assoc:
  fixes A B:: "rat mat"
  fixes v:: "rat vec"
  fixes n:: "nat"
  assumes "A \<in> carrier_mat n n"
  assumes "B \<in> carrier_mat n n"
  assumes "dim_vec v = n"
  shows "A *\<^sub>v (mult_mat_vec B v) =  (A*B)*\<^sub>v v"
  using assms(1) assms(2) assms(3) by auto

lemma size_of_mat:
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  shows "(matrix_A signs subsets) \<in> carrier_mat (length subsets) (length signs)"
  unfolding matrix_A_def carrier_mat_def by auto

lemma size_of_lhs: 
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes signs :: "rat list list" 
  shows "dim_vec (construct_lhs_vector p qs signs) = length signs"
  unfolding construct_lhs_vector_def
  by simp

lemma size_of_rhs: 
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list" 
  shows "dim_vec (construct_rhs_vector p qs subsets) = length subsets"
  unfolding construct_rhs_vector_def
  by simp

lemma same_size:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes invertible_mat: "invertible_mat (matrix_A signs subsets)"
  shows "length subsets = length signs"
  using invertible_mat unfolding invertible_mat_def
  using size_of_mat[of signs subsets] size_of_lhs[of p qs signs] size_of_rhs[of p qs subsets]
  by simp

lemma mat_equal_list_lem:
  fixes A:: "'a::field mat"
  fixes B:: "'a::field mat"
  shows "(dim_row A = dim_row B \<and> dim_col A = dim_col B \<and> mat_to_list A = mat_to_list B)
    \<Longrightarrow> A = B"
proof - 
  assume hyp: "dim_row A = dim_row B \<and> dim_col A = dim_col B \<and> mat_to_list A = mat_to_list B"
  then have "\<And>i j. i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> B $$ (i, j) = A $$ (i, j)"
    unfolding mat_to_list_def by auto
  then show ?thesis using hyp
    unfolding mat_to_list_def
    using eq_matI[of A B]
    by metis 
qed

lemma mat_inverse_same: "mat_inverse_var A = mat_inverse A"
  unfolding mat_inverse_var_def mat_inverse_def mat_equal_def
  using mat_equal_list_lem apply (simp)
  by (smt case_prod_beta index_one_mat(2) index_one_mat(3) mat_equal_list_lem) 

lemma construct_lhs_matches_solve_for_lhs:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes match: "satisfy_equation p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A signs subsets)"
  shows "(construct_lhs_vector p qs signs) = solve_for_lhs p qs subsets (matrix_A signs subsets)"
proof -
  have matrix_equation_hyp: "(mult_mat_vec (matrix_A signs subsets) (construct_lhs_vector p qs signs) = (construct_rhs_vector p qs subsets))"
    using match unfolding satisfy_equation_def by blast
  then have eqn_hyp: " ((matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) *\<^sub>v (mult_mat_vec (matrix_A signs subsets) (construct_lhs_vector p qs signs)) = 
      mult_mat_vec (matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) (construct_rhs_vector p qs subsets))"
    using invertible_mat 
    by (simp add: matrix_equation_hyp) 
  have match_hyp: "length subsets = length signs" using same_size invertible_mat by auto 
  then have dim_hyp1: "matrix_A signs subsets \<in> carrier_mat (length signs) (length signs)"
    using size_of_mat
    by auto 
  then have dim_hyp2: "matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets)) \<in> carrier_mat (length signs) (length signs)"
    using invertible_mat dim_invertible
    by blast 
  have mult_assoc_hyp: "((matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) *\<^sub>v (mult_mat_vec (matrix_A signs subsets) (construct_lhs_vector p qs signs)))
    = (((matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) * (matrix_A signs subsets)) *\<^sub>v  (construct_lhs_vector p qs signs))"
    using mult_assoc dim_hyp1 dim_hyp2 size_of_lhs by auto
  have cancel_helper: "(((matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) * (matrix_A signs subsets)) *\<^sub>v  (construct_lhs_vector p qs signs))
  = (1\<^sub>m (length signs)) *\<^sub>v   (construct_lhs_vector p qs signs)"
    using invertible_means_mult_id[where A= "matrix_A signs subsets"] dim_hyp1
    by (simp add: invertible_mat match_hyp) 
  then have cancel_hyp: "(((matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) * (matrix_A signs subsets)) *\<^sub>v  (construct_lhs_vector p qs signs))
  = (construct_lhs_vector p qs signs)"
    apply (auto)
    by (metis carrier_vec_dim_vec one_mult_mat_vec size_of_lhs)
  then have mult_hyp: "((matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) *\<^sub>v (mult_mat_vec (matrix_A signs subsets) (construct_lhs_vector p qs signs)))
    = (construct_lhs_vector p qs signs)"
    using mult_assoc_hyp cancel_hyp  
    by simp
  then have "(construct_lhs_vector p qs signs) =  (mult_mat_vec (matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets))) (construct_rhs_vector p qs subsets)) "
    using eqn_hyp
    by simp 
  then show ?thesis
    unfolding solve_for_lhs_def
    by (simp add: mat_inverse_same)
qed

(* If set(A) is a subset of B then for all n, nth c n = 0 means nth a n not in B  *)
lemma reduction_signs_set_helper_lemma:
  fixes A:: "rat list set"
  fixes C:: "rat vec"
  fixes B:: "rat list list"
  assumes "dim_vec C = length B"
  assumes sub: "A \<subseteq> set(B)"
  assumes not_in_hyp: "\<forall> n < dim_vec C. C $ n = 0 \<longrightarrow> (nth B n) \<notin> A"
  shows "A \<subseteq> set (take_indices B
             (find_nonzeros_from_input_vec C))"
proof - 
  have unfold: "\<And> x. (x \<in> A \<Longrightarrow> x \<in> set (take_indices B
             (find_nonzeros_from_input_vec C)))"   
  proof -
    fix x
    assume in_a: "x \<in> A"
    have "x \<in> set (B)" 
      using sub in_a by blast
    then have "\<exists> n < length B. nth B n = x"
      by (simp add: in_set_conv_nth)
    then have "\<exists> n < length B. (nth B n = x \<and> (List.member (find_nonzeros_from_input_vec C) n) = True)"
      using not_in_hyp find_zeros_from_vec_prop[of C]
      using assms(1) in_a by auto 
    thus "x \<in> set (take_indices B
             (find_nonzeros_from_input_vec C))" 
      unfolding take_indices_def
      using member_def by fastforce 
  qed
  then show ?thesis
    by blast 
qed

lemma reduction_signs_set_helper_lemma2:
  fixes A:: "rat list set"
  fixes C:: "rat vec"
  fixes B:: "rat list list"
  assumes dist: "distinct B"
  assumes eq_len: "dim_vec C = length B"
  assumes sub: "A \<subseteq> set(B)"
  assumes not_in_hyp: "\<forall> n < dim_vec C. C $ n \<noteq> 0 \<longrightarrow> (nth B n) \<in> A"
  shows "set (take_indices B
             (find_nonzeros_from_input_vec C)) \<subseteq> A"
proof - 
  have unfold: "\<And> x. (x \<in> (set (take_indices B
             (find_nonzeros_from_input_vec C))) \<Longrightarrow> x \<in> A)"   
  proof -
    fix x
    assume in_set: "x \<in> set (take_indices B (find_nonzeros_from_input_vec C))"
    have h: "\<exists>n< dim_vec C. (C $ n \<noteq> 0 \<and> (nth B n) = x)"
    proof - 
      have h1: "\<exists>n < length B.(nth B n) = x" 
        using in_set unfolding take_indices_def
          find_nonzeros_from_input_vec_def eq_len by auto
      have h2: "\<forall>n< length B. (nth B n = x \<longrightarrow> List.member (find_nonzeros_from_input_vec C) n)"
      proof clarsimp 
        fix n
        assume leq_hyp: "n < length B"
        assume x_eq: "x = B ! n"
        have h: "(B !n) \<in> set (map ((!) B) (find_nonzeros_from_input_vec C))"
          using x_eq in_set
          by (simp add: take_indices_def) 
        then have h2: "List.member (map ((!) B) (find_nonzeros_from_input_vec C)) (B ! n)"
          using in_set
          by (meson in_set_member) 
        then have h3: "\<exists>k< length B. (List.member (find_nonzeros_from_input_vec C) k \<and> ((B ! k) = (B ! n)))"
          by (smt atLeastLessThan_iff eq_len find_nonzeros_from_input_vec_def imageE in_set_member mem_Collect_eq set_filter set_map set_upt)
        have h4: "\<forall>v< length B. ((B ! v) = (B ! n) \<longrightarrow> v = n)"
          using dist apply (auto)
          using leq_hyp nth_eq_iff_index_eq by blast
        then show "List.member (find_nonzeros_from_input_vec C) n"
          using h2 h3 h4 by auto
      qed
      then have "\<forall>n<length B. (nth B n = x \<longrightarrow> C $ n \<noteq> 0)" 
        using find_zeros_from_vec_prop [of C]
        by (simp add: eq_len)
      then show ?thesis using h1 eq_len
        by auto 
    qed
    thus "x \<in> A" using not_in_hyp 
      by blast 
  qed
  then show ?thesis
    by blast 
qed

(* Show that dropping columns doesn't affect the consistent sign assignments *)
lemma reduction_doesnt_break_things_signs:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A signs subsets)"
  shows "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(reduction_signs p qs signs subsets (matrix_A signs subsets))"
proof - 
  have dim_hyp2: "matr_option (dim_row (matrix_A signs subsets))
     (mat_inverse (matrix_A signs subsets)) \<in> carrier_mat (length signs) (length signs)"
    using invertible_mat dim_invertible
    using same_size by fastforce 
  have "(construct_lhs_vector p qs signs) = solve_for_lhs p qs subsets (matrix_A signs subsets)"
    using construct_lhs_matches_solve_for_lhs assms by auto
  then have "(solve_for_lhs p qs subsets (matrix_A signs subsets)) =
   vec_of_list (map rat_of_nat (map (\<lambda>s. card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}) signs))" 
    using construct_lhs_vector_cleaner assms
    by (metis (mono_tags, lifting) list.map_cong map_map o_apply of_int_of_nat_eq)
  then have "\<forall> n < (dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))). 
       (((solve_for_lhs p qs subsets (matrix_A signs subsets)) $ n = 0) \<longrightarrow>
       (nth signs n) \<notin> set (characterize_consistent_signs_at_roots_copr p qs))"
  proof - 
    have h0: "\<forall> n < (dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))). 
       (((solve_for_lhs p qs subsets (matrix_A signs subsets)) $ n = 0) \<longrightarrow> 
       rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = (nth signs n)}) = 0)"
      by (metis (mono_tags, lifting) \<open>construct_lhs_vector p qs signs = solve_for_lhs p qs subsets (matrix_A signs subsets)\<close> construct_lhs_vector_clean nonzero of_nat_0_eq_iff of_rat_of_nat_eq size_of_lhs)
    have h1: "\<forall> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}) = 0 \<longrightarrow> 
        (\<nexists> x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w))"
    proof clarsimp 
      fix x
      assume card_asm: "card {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = consistent_sign_vec_copr qs x} = 0"
      assume zero_asm: "poly p x = 0"
      have card_hyp: "{xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = consistent_sign_vec_copr qs x} = {}"
        using card_eq_0_iff
        using card_asm nonzero poly_roots_finite by fastforce 
      have "x \<in> {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = consistent_sign_vec_copr qs x}"
        using zero_asm by auto
      thus "False" using card_hyp
        by blast
    qed
    have h2: "\<And> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}) = 0 \<Longrightarrow>
       (\<not>List.member (characterize_consistent_signs_at_roots_copr p qs) w))"
      by (smt (verit, best) characterize_consistent_signs_at_roots_copr_def characterize_root_list_p_def h1 imageE in_set_member mem_Collect_eq nonzero poly_roots_finite set_map set_remdups sorted_list_of_set(1))
    then have h3: "\<forall> w. rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}) = 0 \<longrightarrow> 
        w \<notin> set (characterize_consistent_signs_at_roots_copr p qs)"
      by (simp add: in_set_member)
    show ?thesis using h0 h3
      by blast 
  qed
  then have "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set (take_indices signs
             (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))"
    using all_info
      reduction_signs_set_helper_lemma[where A = "set (characterize_consistent_signs_at_roots_copr p qs)", where B = "signs",
      where C = "(solve_for_lhs p qs subsets (matrix_A signs subsets))"]
    using dim_hyp2 solve_for_lhs_def by (simp add: mat_inverse_same)
  then show ?thesis unfolding reduction_signs_def by auto
qed

lemma reduction_deletes_bad_sign_conds:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A signs subsets)"
  shows "set (characterize_consistent_signs_at_roots_copr p qs) = set(reduction_signs p qs signs subsets (matrix_A signs subsets))"
proof - 
  have dim_hyp2: "matr_option (dim_row (matrix_A signs subsets))
       (mat_inverse (matrix_A signs subsets)) \<in> carrier_mat (length signs) (length signs)"
    using invertible_mat dim_invertible
    using same_size by fastforce 
  have supset: "set (characterize_consistent_signs_at_roots_copr p qs) \<supseteq> set(reduction_signs p qs signs subsets (matrix_A signs subsets))" 
  proof - 
    have "(construct_lhs_vector p qs signs) = solve_for_lhs p qs subsets (matrix_A signs subsets)"
      using construct_lhs_matches_solve_for_lhs assms by auto
    then have "(solve_for_lhs p qs subsets (matrix_A signs subsets)) =
       vec_of_list (map rat_of_nat (map (\<lambda>s. card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}) signs))" 
      using construct_lhs_vector_cleaner assms
      by (metis (mono_tags, lifting) list.map_cong map_map o_apply of_int_of_nat_eq)
    then have "\<forall> n < (dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))). 
           (((solve_for_lhs p qs subsets (matrix_A signs subsets)) $ n \<noteq> 0) \<longrightarrow>
           (nth signs n) \<in> set (characterize_consistent_signs_at_roots_copr p qs))"
    proof - 
      have h0: "\<forall> n < (dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))). 
           (((solve_for_lhs p qs subsets (matrix_A signs subsets)) $ n = 0) \<longrightarrow> 
           rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = (nth signs n)}) = 0)"
        by (metis (mono_tags, lifting) \<open>construct_lhs_vector p qs signs = solve_for_lhs p qs subsets (matrix_A signs subsets)\<close> construct_lhs_vector_clean nonzero of_nat_0_eq_iff of_rat_of_nat_eq size_of_lhs)
      have h1: "\<forall> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}) \<noteq> 0 \<longrightarrow> 
            (\<exists> x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w))"
      proof clarsimp 
        fix w
        assume card_asm: "0 < card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}"
        show "\<exists>x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w"
          by (metis (mono_tags, lifting) Collect_empty_eq card_asm card_eq_0_iff gr_implies_not0)
      qed
      have h2: "\<And> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}) \<noteq> 0 \<Longrightarrow>
           (List.member (characterize_consistent_signs_at_roots_copr p qs) w))"
      proof clarsimp 
        fix w
        assume card_asm: " 0 < card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}"
        have h0: "\<exists>x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w"
          using card_asm
          by (simp add: h1) 
        then show "List.member (characterize_consistent_signs_at_roots_copr p qs) w" 
          unfolding characterize_consistent_signs_at_roots_copr_def
          using in_set_member nonzero poly_roots_finite characterize_root_list_p_def by fastforce
      qed
      then have h3: "\<forall> w. rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = w}) \<noteq> 0 \<longrightarrow> 
            w \<in> set (characterize_consistent_signs_at_roots_copr p qs)"
        by (simp add: in_set_member)
      show ?thesis using h0 h3
        by (metis (no_types, lifting) \<open>solve_for_lhs p qs subsets (matrix_A signs subsets) = vec_of_list (map rat_of_nat (map (\<lambda>s. card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}) signs))\<close> dim_vec_of_list length_map nth_map vec_of_list_index)
    qed
    then have "set (take_indices signs
                 (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) \<subseteq>
              set (characterize_consistent_signs_at_roots_copr p qs)"
      using all_info
        reduction_signs_set_helper_lemma2[where A = "set (characterize_consistent_signs_at_roots_copr p qs)", where B = "signs",
        where C = "(solve_for_lhs p qs subsets (matrix_A signs subsets))"]
      using distinct_signs dim_hyp2 solve_for_lhs_def
      by (simp add: mat_inverse_same)
    then show ?thesis unfolding reduction_signs_def by auto
  qed
  have subset: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(reduction_signs p qs signs subsets (matrix_A signs subsets))" 
    using reduction_doesnt_break_things_signs[of p qs signs subsets] assms
    by blast 
  then show ?thesis using supset subset by auto 
qed

theorem reduce_system_sign_conditions:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A signs subsets)"
  shows "set (get_signs (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs))))) = set (characterize_consistent_signs_at_roots_copr p qs)"
  unfolding get_signs_def
  using reduction_deletes_bad_sign_conds[of p qs signs subsets] apply (auto)
   apply (simp add: all_info distinct_signs match nonzero reduction_signs_def welldefined_signs1)
  using nonzero invertible_mat apply (metis snd_conv)
  by (metis all_info distinct_signs invertible_mat match nonzero reduction_signs_def snd_conv welldefined_signs1) 

subsection "Showing matrix equation preserved when reducing"
lemma rows_to_keep_lem:
  fixes A:: "('a::field) mat"
  shows "\<And>ell. ell \<in> set (rows_to_keep A) \<Longrightarrow> ell < dim_row A"
  unfolding rows_to_keep_def
  apply auto
  using rref_pivot_positions
  by (metis carrier_mat_triv gauss_jordan_single(2) gauss_jordan_single(3) index_transpose_mat(3)) 

lemma reduce_system_matrix_equation_preserved:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs: "well_def_signs (length qs) signs"
  assumes welldefined_subsets: "all_list_constr (subsets) (length qs)"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A signs subsets)"
  assumes pairwise_rel_prime: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  shows "satisfy_equation p qs (get_subsets (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))
  (get_signs (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))"
proof - 
  have poly_type_hyp: "p \<noteq> 0" using nonzero by auto
  have distinct_signs_hyp: "distinct (snd (snd (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs))))))" 
  proof - 
    let ?sym = "(find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
    have h1: "\<forall> i < length (take_indices signs ?sym). \<forall>j < length(take_indices signs ?sym).
      i \<noteq> j \<longrightarrow> nth (take_indices signs ?sym) i \<noteq> nth (take_indices signs ?sym) j" 
      using distinct_signs unfolding take_indices_def 
    proof clarsimp 
      fix i
      fix j
      assume "distinct signs"
      assume "i < length
                (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
      assume "j < length
                (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
      assume neq_hyp: "i \<noteq> j"
      assume "signs ! (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets 
              (matrix_A signs subsets)) ! i) =
           signs ! (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets 
              (matrix_A signs subsets)) ! j)"
      have h1: "find_nonzeros_from_input_vec (solve_for_lhs p qs subsets 
              (matrix_A signs subsets)) ! i \<noteq> find_nonzeros_from_input_vec (solve_for_lhs p qs subsets 
              (matrix_A signs subsets)) ! j"
        unfolding find_nonzeros_from_input_vec_def using neq_hyp
        by (metis \<open>i < length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> \<open>j < length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> distinct_conv_nth distinct_filter distinct_upt find_nonzeros_from_input_vec_def) 
      then show "False" using distinct_signs
      proof -
        have f1: "\<forall>p ns n. ((n::nat) \<in> {n \<in> set ns. p n}) = (n \<in> set ns \<and> n \<in> Collect p)"
          by simp
        then have f2: "filter (\<lambda>n. solve_for_lhs p qs subsets (matrix_A signs subsets) $ n \<noteq> 0) [0..<dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))] ! i \<in> set [0..<length signs]"
          by (metis (full_types) \<open>i < length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> construct_lhs_matches_solve_for_lhs find_nonzeros_from_input_vec_def invertible_mat match nth_mem set_filter size_of_lhs)
        have "filter (\<lambda>n. solve_for_lhs p qs subsets (matrix_A signs subsets) $ n \<noteq> 0) [0..<dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))] ! j \<in> set [0..<length signs]"
          using f1 by (metis (full_types) \<open>j < length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> construct_lhs_matches_solve_for_lhs find_nonzeros_from_input_vec_def invertible_mat match nth_mem set_filter size_of_lhs)
        then show ?thesis
          using f2 by (metis \<open>signs ! (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)) ! i) = signs ! (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)) ! j)\<close> atLeastLessThan_iff distinct_conv_nth distinct_signs find_nonzeros_from_input_vec_def h1 set_upt)
      qed
    qed
    then have "distinct (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))"
      using distinct_conv_nth by blast 
    then show ?thesis
      using get_signs_def reduction_signs_def reduction_signs_is_get_signs by auto 
  qed
  have all_info_hyp: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(snd (snd (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs))))))"
    using reduce_system_sign_conditions assms unfolding get_signs_def by auto
  have pairwise_rel_prime_hyp: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))" 
    using pairwise_rel_prime by auto
  have welldefined_hyp: "all_list_constr (fst (snd (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))) (length qs)"
    using welldefined_subsets rows_to_keep_lem
    unfolding all_list_constr_def List.member_def list_constr_def list_all_def
    apply (auto simp add: Let_def take_indices_def take_cols_from_matrix_def)
    using nth_mem by fastforce
  then show ?thesis using poly_type_hyp distinct_signs_hyp all_info_hyp pairwise_rel_prime_hyp welldefined_hyp
    using matrix_equation unfolding get_subsets_def get_signs_def
    by blast 
qed

(* Show that we are tracking the correct matrix in the algorithm *)
subsection "Showing matrix preserved"
lemma reduce_system_matrix_signs_helper_aux:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length signs"
  assumes nonzero: "p \<noteq> 0"
  shows "alt_matrix_A (take_indices signs S) subsets = take_cols_from_matrix (alt_matrix_A signs subsets) S"
proof - 
  have h0a: "dim_col (take_cols_from_matrix (alt_matrix_A signs subsets) S) = length (take_indices signs S)" 
    unfolding take_cols_from_matrix_def apply (auto) unfolding take_indices_def by auto
  have h0: "\<forall>i < length (take_indices signs S). (col (alt_matrix_A (take_indices signs S) subsets ) i = 
col (take_cols_from_matrix (alt_matrix_A signs subsets) S) i)" 
  proof clarsimp
    fix i
    assume asm: "i < length (take_indices signs S)"
    have i_lt: "i < length (map ((!) (cols (alt_matrix_A signs subsets))) S)" using asm
      apply (auto) unfolding take_indices_def by auto
    have h0: " vec (length subsets) (\<lambda>j. z (subsets ! j) (map ((!) signs) S ! i)) = 
      vec (length subsets) (\<lambda>j. z (subsets ! j) (signs ! (S ! i)))" using nth_map
      by (metis \<open>i < length (take_indices signs S)\<close> length_map take_indices_def) 
    have dim: "(map ((!) (cols (alt_matrix_A signs subsets))) S) ! i \<in> carrier_vec (dim_row (alt_matrix_A signs subsets))"
    proof - 
      have "dim_col (alt_matrix_A signs subsets) = length (signs)"
        by (simp add: alt_matrix_A_def) 
      have well_d: "S ! i < length (signs)" using well_def_h
        using i_lt in_set_member by fastforce 
      have 
        map_eq: "(map ((!) (cols (alt_matrix_A signs subsets))) S) ! i  = nth (cols (alt_matrix_A signs subsets))  (S ! i)"
        using i_lt by auto
      have "nth (cols (alt_matrix_A signs subsets))  (S ! i) \<in> carrier_vec (dim_row (alt_matrix_A signs subsets))"
        using col_dim unfolding cols_def using nth_map well_d
        by (simp add: \<open>dim_col (alt_matrix_A signs subsets) = length signs\<close>) 
      then show ?thesis using map_eq unfolding alt_matrix_A_def by auto
    qed
    have h1: "col (take_cols_from_matrix (alt_matrix_A signs subsets) S) i = 
      col (mat_of_cols (dim_row (alt_matrix_A signs subsets)) (map ((!) (cols (alt_matrix_A signs subsets))) S)) i "
      by (simp add: take_cols_from_matrix_def take_indices_def)
    have h2: "col (mat_of_cols (dim_row (alt_matrix_A signs subsets)) (map ((!) (cols (alt_matrix_A signs subsets))) S)) i 
      = nth (map ((!) (cols (alt_matrix_A signs subsets))) S) i " 
      using dim i_lt asm col_mat_of_cols[where j = "i", where n = "(dim_row (alt_matrix_A signs subsets))",
          where vs = "(map ((!) (cols (alt_matrix_A signs subsets))) S)"]
      by blast 
    have h3: "col (take_cols_from_matrix (alt_matrix_A signs subsets) S) i = (col (alt_matrix_A signs subsets) (S !i))"
      using h1 h2 apply (auto)
      by (metis alt_matrix_char asm cols_nth dim_col_mat(1) in_set_member length_map mat_of_rows_list_def matrix_A_def nth_map nth_mem take_indices_def well_def_h)
    have "vec (length subsets) (\<lambda>j. z (subsets ! j) (signs ! (S ! i))) = (col (alt_matrix_A signs subsets) (S !i))"
      by (metis asm in_set_member length_map nth_mem signs_are_cols take_indices_def well_def_h)
    then have "vec (length subsets) (\<lambda>j. z (subsets ! j) (take_indices signs S ! i)) =
      col (take_cols_from_matrix (alt_matrix_A signs subsets) S) i "
      using h0 h3
      by (simp add: take_indices_def) 
    then show "col (alt_matrix_A (take_indices signs S) subsets) i =
         col (take_cols_from_matrix (alt_matrix_A signs subsets) S) i "
      using asm signs_are_cols[where signs = "(take_indices signs S)", where subsets = "subsets"] 
      by auto
  qed
  then show ?thesis   unfolding alt_matrix_A_def take_cols_from_matrix_def apply (auto) 
    using h0a mat_col_eqI
    by (metis alt_matrix_A_def dim_col_mat(1) dim_row_mat(1) h0 mat_of_cols_def take_cols_from_matrix_def) 
qed


lemma reduce_system_matrix_signs_helper:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length signs"
  assumes nonzero: "p \<noteq> 0"
  shows "matrix_A (take_indices signs S) subsets = take_cols_from_matrix (matrix_A signs subsets) S"
  using reduce_system_matrix_signs_helper_aux alt_matrix_char assms by auto

lemma reduce_system_matrix_subsets_helper_aux:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes inv: "length subsets \<ge> length signs"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length subsets"
  assumes nonzero: "p \<noteq> 0"
  shows "alt_matrix_A signs (take_indices subsets S) = take_rows_from_matrix (alt_matrix_A signs subsets) S"
proof - 
  have h0a: "dim_row (take_rows_from_matrix (alt_matrix_A signs subsets) S) = length (take_indices subsets S)" 
    unfolding take_rows_from_matrix_def apply (auto) unfolding take_indices_def by auto
  have h0: "\<forall>i < length (take_indices subsets S). (row (alt_matrix_A signs (take_indices subsets S) ) i = 
row (take_rows_from_matrix (alt_matrix_A signs subsets) S) i)" 
  proof clarsimp
    fix i
    assume asm: "i < length (take_indices subsets S)"
    have i_lt: "i < length (map ((!) (rows (alt_matrix_A signs subsets))) S)" using asm
      apply (auto) unfolding take_indices_def by auto
    have h0: "row (take_rows_from_matrix (alt_matrix_A signs subsets) S) i =
    row (mat_of_rows (dim_col (alt_matrix_A signs subsets)) (map ((!) (rows (alt_matrix_A signs subsets))) S)) i "
      unfolding take_rows_from_matrix_def take_indices_def by auto
    have dim: "(map ((!) (rows (alt_matrix_A signs subsets))) S) ! i \<in> carrier_vec (dim_col (alt_matrix_A signs subsets))"
    proof - 
      have "dim_col (alt_matrix_A signs subsets) = length (signs)"
        by (simp add: alt_matrix_A_def) 
      then have lenh: "dim_col (alt_matrix_A signs subsets) \<le> length (subsets)"
        using assms
        by auto 
      have well_d: "S ! i < length (subsets)" using well_def_h
        using i_lt in_set_member by fastforce 
      have 
        map_eq: "(map ((!) (rows (alt_matrix_A signs subsets))) S) ! i  = nth (rows (alt_matrix_A signs subsets))  (S ! i)"
        using i_lt by auto
      have "nth (rows (alt_matrix_A signs subsets))  (S ! i) \<in> carrier_vec (dim_col (alt_matrix_A signs subsets))"
        using col_dim unfolding rows_def using nth_map well_d
        using lenh
        by (simp add: alt_matrix_A_def) 
      then show ?thesis using map_eq unfolding alt_matrix_A_def by auto
    qed
    have h1: " row (mat_of_rows (dim_col (alt_matrix_A signs subsets)) (map ((!) (rows (alt_matrix_A signs subsets))) S)) i
      = (row  (alt_matrix_A signs subsets) (S ! i)) "
      using dim i_lt mat_of_rows_row[where i = "i", where n = "(dim_col (alt_matrix_A signs subsets))",
          where vs = "(map ((!) (rows (alt_matrix_A signs subsets))) S)"]
      using alt_matrix_char in_set_member nth_mem well_def_h by fastforce
    have "row (alt_matrix_A signs (take_indices subsets S) ) i = (row  (alt_matrix_A signs subsets) (S ! i))"
      using subsets_are_rows
    proof -
      have f1: "i < length S"
        by (metis (no_types) asm length_map take_indices_def)
      then have "List.member S (S ! i)"
        by (meson in_set_member nth_mem)
      then show ?thesis
        using f1 by (simp add: \<open>\<And>subsets signs. \<forall>i<length subsets. row (alt_matrix_A signs subsets) i = vec (length signs) (\<lambda>j. z (subsets ! i) (signs ! j))\<close> take_indices_def well_def_h)
    qed 
    then show "(row (alt_matrix_A signs (take_indices subsets S) ) i = 
      row (take_rows_from_matrix (alt_matrix_A signs subsets) S) i)" 
      using h0 h1 unfolding take_indices_def by auto
  qed
  then show ?thesis  unfolding alt_matrix_A_def take_rows_from_matrix_def apply (auto) 
    using eq_rowI
    by (metis alt_matrix_A_def dim_col_mat(1) dim_row_mat(1) h0 length_map mat_of_rows_def take_indices_def take_rows_from_matrix_def) 
qed


lemma reduce_system_matrix_subsets_helper:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes nonzero: "p \<noteq> 0"
  assumes inv: "length subsets \<ge> length signs"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length subsets"
  shows "matrix_A signs (take_indices subsets S) = take_rows_from_matrix (matrix_A signs subsets) S"
  using assms reduce_system_matrix_subsets_helper_aux alt_matrix_char
  by auto

lemma reduce_system_matrix_match:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  assumes inv: "invertible_mat (matrix_A signs subsets)"
  shows "matrix_A (get_signs (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))
  (get_subsets (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs))))) = 
  (get_matrix (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))"
proof -
  let ?A = "(matrix_A signs subsets)"
  let ?lhs_vec = "(solve_for_lhs p qs subsets (matrix_A signs subsets))"
  let ?red_mtx = "(take_rows_from_matrix (reduce_mat_cols (matrix_A signs subsets) ?lhs_vec) (rows_to_keep (reduce_mat_cols (matrix_A signs subsets) ?lhs_vec)))"
  have h1: "matrix_A (get_signs (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))
  (get_subsets (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))
   = matrix_A (reduction_signs p qs signs subsets (matrix_A signs subsets)) (reduction_subsets p qs signs subsets (matrix_A signs subsets))"
    using reduction_signs_is_get_signs reduction_subsets_is_get_subsets by auto
  have h1_var: "matrix_A (get_signs (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))
  (get_subsets (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))
   = matrix_A (take_indices signs (find_nonzeros_from_input_vec ?lhs_vec)) (take_indices subsets (rows_to_keep (reduce_mat_cols ?A ?lhs_vec)))"
    using h1 reduction_signs_def reduction_subsets_def by auto 
  have h2: "?red_mtx = (take_rows_from_matrix (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec)) (rows_to_keep (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec))))"
    by simp
  have h30: "(construct_lhs_vector p qs signs) = ?lhs_vec"
    using assms construct_lhs_matches_solve_for_lhs
    by simp 
  have h3a: "\<forall>x. List.member (find_nonzeros_from_input_vec ?lhs_vec) x \<longrightarrow>x < length (signs)" 
    using h30 size_of_lhs unfolding find_nonzeros_from_input_vec_def apply (auto)
    by (metis atLeastLessThan_iff filter_is_subset member_def set_upt subset_eq) 
  have h3b_a: "\<forall>x. List.member (find_nonzeros_from_input_vec ?lhs_vec) x \<longrightarrow>x < length (subsets)" 
    using assms h30 size_of_lhs same_size unfolding find_nonzeros_from_input_vec_def apply (auto)
    by (simp add: find_nonzeros_from_input_vec_def h3a)
  have h3ba: "length
     (filter (\<lambda>i. solve_for_lhs p qs subsets (matrix_A signs subsets) $ i \<noteq> 0)
       [0..<length subsets])
    \<le> length subsets" using length_filter_le[where P = "(\<lambda>i. solve_for_lhs p qs subsets (matrix_A signs subsets) $ i \<noteq> 0)",
    where xs = "[0..<length subsets]"] length_upto by auto
  have " length subsets = dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))"
    using h30 inv size_of_lhs same_size[of signs subsets] apply (auto)
    by metis 
  then have "length
     (filter (\<lambda>i. solve_for_lhs p qs subsets (matrix_A signs subsets) $ i \<noteq> 0)
       [0..<dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))])
    \<le> length subsets" using h3ba
    by auto
  then have h3b: "length subsets \<ge> length (take_indices signs (find_nonzeros_from_input_vec ?lhs_vec))" 
    unfolding take_indices_def find_nonzeros_from_input_vec_def by auto
  have h3c: "\<forall>x. List.member (rows_to_keep (reduce_mat_cols ?A ?lhs_vec)) x \<longrightarrow> x < length (subsets)"
  proof clarsimp
    fix x
    assume x_mem: "List.member (rows_to_keep
            (take_cols_from_matrix (matrix_A signs subsets)
              (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))) x"
    obtain nn :: "rat list list \<Rightarrow> nat list \<Rightarrow> nat" where
      "\<forall>x2 x3. (\<exists>v4. v4 \<in> set x3 \<and> \<not> v4 < length x2) = (nn x2 x3 \<in> set x3 \<and> \<not> nn x2 x3 < length x2)"
      by moura
    then have f4: "nn signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<in> set (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<and> \<not> nn signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) < length signs \<or> matrix_A (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) subsets = take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
      using h3a nonzero reduce_system_matrix_signs_helper by auto
    then have "matrix_A (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) subsets = take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<and> x \<in> set (map snd (pivot_positions (gauss_jordan_single (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))\<^sup>T)))"
      using f4
      by (metis h3a in_set_member rows_to_keep_def x_mem)
    thus "x < length (subsets)" using x_mem unfolding rows_to_keep_def
      by (metis (no_types) dim_row_matrix_A rows_to_keep_def rows_to_keep_lem)
  qed
  have h3: "matrix_A (take_indices signs (find_nonzeros_from_input_vec ?lhs_vec)) (take_indices subsets (rows_to_keep (reduce_mat_cols ?A ?lhs_vec))) = 
    (take_rows_from_matrix (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec)) (rows_to_keep (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec))))" 
    using inv h3a h3b h3c reduce_system_matrix_subsets_helper reduce_system_matrix_signs_helper
      assms by auto
  show ?thesis using h1 h2 h3
    by (metis fst_conv get_matrix_def h1_var reduce_system.simps reduction_step.simps)
qed

(* gauss_jordan_single_rank is crucial in this section *)
subsection "Showing invertibility preserved when reducing"

(* Overall:
  Start with a matrix equation.
  Input a matrix, subsets, and signs.
  Drop columns of the matrix based on the 0's on the LHS---so extract a list of 0's. Reduce signs accordingly.
  Then find a list of rows to delete based on using rank (use the transpose result, pivot positions!),
   and delete those rows.  Reduce subsets accordingly.
  End with a reduced system! *)
lemma well_def_find_zeros_from_lhs_vec:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  shows "(\<And>j. j \<in> set (find_nonzeros_from_input_vec
                    (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<Longrightarrow>
          j < length (cols (matrix_A signs subsets)))"
proof - 
  fix i
  fix j
  assume j_in: " j \<in> set (find_nonzeros_from_input_vec
                      (solve_for_lhs p qs subsets (matrix_A signs subsets))) "
  let ?og_mat = "(matrix_A signs subsets)"
  let ?lhs = "(solve_for_lhs p qs subsets ?og_mat)"
  let ?new_mat = "(take_rows_from_matrix (reduce_mat_cols ?og_mat ?lhs) (rows_to_keep (reduce_mat_cols ?og_mat ?lhs)))"
  have "square_mat (matrix_A signs subsets)" using inv
    using invertible_mat_def by blast
  then have mat_size: "?og_mat \<in> carrier_mat (length signs) (length signs)" 
    using size_of_mat
    by auto 
  have "dim_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)) = (length signs)"
    using size_of_lhs construct_lhs_matches_solve_for_lhs assms
    by (metis (full_types))
  then have h: "j < (length signs)"
    using j_in unfolding find_nonzeros_from_input_vec_def
    by simp 
  then show "j <  length (cols (matrix_A signs subsets))" 
    using mat_size by auto
qed

lemma take_cols_subsets_og_cols:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  shows "set (take_indices (cols (matrix_A signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))
    \<subseteq> set (cols (matrix_A signs subsets))"
proof -
  have well_def: "(\<And>j. j \<in> set (find_nonzeros_from_input_vec
                    (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<Longrightarrow>
          j < length (cols (matrix_A signs subsets)))"
    using assms well_def_find_zeros_from_lhs_vec by auto
  have "\<forall>x. x \<in> set (take_indices (cols (matrix_A signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) 
    \<longrightarrow> x \<in>  set (cols (matrix_A signs subsets))" 
  proof clarsimp 
    fix x
    let ?og_list = "(cols (matrix_A signs subsets))"
    let ?ind_list = "(find_nonzeros_from_input_vec
                     (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
    assume x_in: "x \<in> set (take_indices ?og_list ?ind_list)"
    show "x \<in> set (cols (matrix_A signs subsets))" 
      using x_in unfolding take_indices_def using in_set_member apply (auto)
      using in_set_conv_nth well_def by fastforce
  qed
  then show ?thesis
    by blast 
qed

lemma reduction_doesnt_break_things_invertibility_step1:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  shows "vec_space.rank (length signs) (reduce_mat_cols (matrix_A signs subsets) (solve_for_lhs p qs subsets (matrix_A signs subsets))) =
    (length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))"
proof - 
  let ?og_mat = "(matrix_A signs subsets)"
  let ?lhs = "(solve_for_lhs p qs subsets ?og_mat)"
  let ?new_mat = "(take_rows_from_matrix (reduce_mat_cols ?og_mat ?lhs) (rows_to_keep (reduce_mat_cols ?og_mat ?lhs)))"
  have "square_mat (matrix_A signs subsets)" using inv
    using invertible_mat_def by blast
  then have mat_size: "?og_mat \<in> carrier_mat (length signs) (length signs)" 
    using size_of_mat
    by auto 
  then have mat_size_alt: "?og_mat \<in> carrier_mat (length subsets) (length subsets)" 
    using size_of_mat same_size assms 
    by auto 
  have det_h: "det ?og_mat \<noteq> 0"
    using invertible_det[where A = "matrix_A signs subsets"] mat_size
    using inv by blast
  then have rank_h: "vec_space.rank (length signs) ?og_mat = (length signs)" 
    using vec_space.det_rank_iff  mat_size
    by auto
  then have dist_cols: "distinct (cols ?og_mat)" using mat_size vec_space.non_distinct_low_rank[where A = ?og_mat, where n = "length signs"]
    by auto
  have well_def: "(\<And>j. j \<in> set (find_nonzeros_from_input_vec
                    (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<Longrightarrow>
          j < length (cols (matrix_A signs subsets)))"
    using assms well_def_find_zeros_from_lhs_vec by auto
  have dist1: "distinct
     (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
    unfolding find_nonzeros_from_input_vec_def by auto
  have clear: "set (take_indices (cols (matrix_A signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))
    \<subseteq> set (cols (matrix_A signs subsets))"
    using assms take_cols_subsets_og_cols by auto
  then have "distinct (take_indices (cols (matrix_A signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))"
    unfolding take_indices_def
    using dist1 dist_cols well_def conjugatable_vec_space.distinct_map_nth[where ls = "cols (matrix_A signs subsets)", where inds = "(find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"]
    by auto
  then have unfold_thesis: "vec_space.rank (length signs) (mat_of_cols (dim_row ?og_mat) (take_indices (cols ?og_mat) (find_nonzeros_from_input_vec ?lhs)))
= (length (find_nonzeros_from_input_vec ?lhs))" 
    using clear inv conjugatable_vec_space.rank_invertible_subset_cols[where A= "matrix_A signs subsets", where B = "(take_indices (cols (matrix_A signs subsets))
         (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))"]
    by (simp add: len_eq mat_size take_indices_def)
  then show ?thesis apply (simp) unfolding take_cols_from_matrix_def by auto
qed

lemma rechar_take_cols: "take_cols_var A B = take_cols_from_matrix A B"
  unfolding take_cols_var_def take_cols_from_matrix_def take_indices_def by auto

lemma rows_and_cols_transpose: "rows M = cols M\<^sup>T"
  using row_transpose  by simp 

lemma take_rows_and_take_cols:  "(take_rows_from_matrix M r) = (take_cols_from_matrix M\<^sup>T r)\<^sup>T"
  unfolding take_rows_from_matrix_def take_cols_from_matrix_def
  using transpose_carrier_mat rows_and_cols_transpose apply (auto)
  by (simp add: transpose_mat_of_cols) 

lemma reduction_doesnt_break_things_invertibility:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation p qs subsets signs"
  shows "invertible_mat (get_matrix (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))"
proof - 
  let ?og_mat = "(matrix_A signs subsets)"
  let ?lhs = "(solve_for_lhs p qs subsets ?og_mat)"
  let ?step1_mat = "(reduce_mat_cols ?og_mat ?lhs)"
  let ?new_mat = "take_rows_from_matrix ?step1_mat (rows_to_keep ?step1_mat)"
  let ?ind_list = "(find_nonzeros_from_input_vec  ?lhs)"
  have "square_mat (matrix_A signs subsets)" using inv
    using invertible_mat_def by blast
  then have og_mat_size: "?og_mat \<in> carrier_mat (length signs) (length signs)" 
    using size_of_mat
    by auto 
  have "dim_col (mat_of_cols (dim_row ?og_mat) (take_indices (cols ?og_mat) ?ind_list))
      = (length (find_nonzeros_from_input_vec ?lhs))"
    by (simp add: take_indices_def) 
  then have "mat_of_cols (dim_row ?og_mat) (take_indices (cols ?og_mat) ?ind_list)
      \<in> carrier_mat (length signs) (length (find_nonzeros_from_input_vec ?lhs))"
    by (simp add: len_eq mat_of_cols_def)
  then have step1_mat_size: "?step1_mat \<in> carrier_mat (length signs) (length (find_nonzeros_from_input_vec ?lhs))"
    by (simp add: take_cols_from_matrix_def)
  then have "dim_row ?step1_mat \<ge> dim_col ?step1_mat"
    by (metis carrier_matD(1) carrier_matD(2) construct_lhs_matches_solve_for_lhs diff_zero find_nonzeros_from_input_vec_def inv length_filter_le length_upt match size_of_lhs)
  then have gt_eq_assm: "dim_col ?step1_mat\<^sup>T  \<ge> dim_row  ?step1_mat\<^sup>T"
    by simp 
  have det_h: "det ?og_mat \<noteq> 0"
    using invertible_det[where A = "matrix_A signs subsets"] og_mat_size
    using inv by blast
  then have rank_h: "vec_space.rank (length signs) ?og_mat = (length signs)" 
    using vec_space.det_rank_iff  og_mat_size
    by auto
  have rank_drop_cols: "vec_space.rank (length signs) ?step1_mat = (dim_col ?step1_mat)"
    using assms reduction_doesnt_break_things_invertibility_step1 step1_mat_size 
    by auto
  let ?step1_T = "?step1_mat\<^sup>T"
  have rank_transpose: "vec_space.rank (length signs) ?step1_mat = vec_space.rank (length (find_nonzeros_from_input_vec ?lhs)) ?step1_T"
    using transpose_rank[of ?step1_mat]
    using step1_mat_size by auto  
  have obv: "?step1_T \<in> carrier_mat (dim_row ?step1_T) (dim_col ?step1_T)" by auto
  have should_have_this:"vec_space.rank (length (find_nonzeros_from_input_vec ?lhs)) (take_cols ?step1_T (map snd (pivot_positions (gauss_jordan_single (?step1_T))))) = vec_space.rank (length (find_nonzeros_from_input_vec ?lhs)) ?step1_T"
    using obv gt_eq_assm conjugatable_vec_space.gauss_jordan_single_rank[where A = "?step1_T", where n = "dim_row ?step1_T", where nc = "dim_col ?step1_T"]
    by (simp add: take_cols_from_matrix_def take_indices_def)
  then have "vec_space.rank (length (find_nonzeros_from_input_vec ?lhs)) (take_cols ?step1_T (map snd (pivot_positions (gauss_jordan_single (?step1_T))))) = dim_col ?step1_mat"
    using rank_drop_cols rank_transpose by auto
  then have with_take_cols_from_matrix: "vec_space.rank (length (find_nonzeros_from_input_vec ?lhs)) (take_cols_from_matrix ?step1_T (map snd (pivot_positions (gauss_jordan_single (?step1_T))))) = dim_col ?step1_mat"
    using rank_transpose rechar_take_cols conjugatable_vec_space.gjs_and_take_cols_var
    apply (auto)
    by (smt conjugatable_vec_space.gjs_and_take_cols_var gt_eq_assm obv rechar_take_cols reduce_mat_cols.simps)
  have "(take_rows_from_matrix ?step1_mat (rows_to_keep ?step1_mat)) = (take_cols_from_matrix ?step1_T  (rows_to_keep ?step1_mat))\<^sup>T"
    using take_rows_and_take_cols
    by blast 
  then have rank_new_mat: "vec_space.rank (dim_row ?new_mat) ?new_mat = dim_col ?step1_mat"
    using with_take_cols_from_matrix transpose_rank apply (auto)
  proof -
    assume a1: "vec_space.rank (length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) (take_cols_from_matrix (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))\<^sup>T (map snd (pivot_positions (gauss_jordan_single (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))\<^sup>T)))) = dim_col (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))"
    have f2: "\<forall>m. vec_space.rank (dim_row (m::rat mat)) m = vec_space.rank (dim_row m\<^sup>T) m\<^sup>T"
      by (simp add: transpose_rank)
    have f3: "dim_row (mat_of_cols (dim_row (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (take_indices (cols (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (map snd (pivot_positions (gauss_jordan_single (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T))))) = length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
      using \<open>dim_col (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))) = length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> by force
    have "vec_space.rank (length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) (mat_of_cols (dim_row (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (take_indices (cols (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (map snd (pivot_positions (gauss_jordan_single (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T))))) = dim_row (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T"
      using a1 by (simp add: take_cols_from_matrix_def)
    then have "vec_space.rank (dim_row (mat_of_cols (dim_row (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (take_indices (cols (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (map snd (pivot_positions (gauss_jordan_single (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T)))))\<^sup>T) (mat_of_cols (dim_row (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (take_indices (cols (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T) (map snd (pivot_positions (gauss_jordan_single (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T)))))\<^sup>T = dim_row (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))\<^sup>T"
      using f3 f2 by presburger
    then show "vec_space.rank (dim_col (take_cols_from_matrix (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))\<^sup>T (rows_to_keep (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))))) (take_cols_from_matrix (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))\<^sup>T (rows_to_keep (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))))\<^sup>T = dim_col (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))"
      by (simp add: rows_to_keep_def take_cols_from_matrix_def)
  qed 
  have "length (pivot_positions (gauss_jordan_single (?step1_mat\<^sup>T))) \<le> (length (find_nonzeros_from_input_vec ?lhs))"
    using obv length_pivot_positions_dim_row[where A = "(gauss_jordan_single (?step1_mat\<^sup>T))"]
    by (metis carrier_matD(1) carrier_matD(2) gauss_jordan_single(2) gauss_jordan_single(3) index_transpose_mat(2) step1_mat_size) 
  then have len_lt_eq: "length (pivot_positions (gauss_jordan_single (?step1_mat\<^sup>T))) \<le> dim_col ?step1_mat"
    using step1_mat_size
    by simp 
  have len_gt_false: "length (rows_to_keep ?step1_mat) < (dim_col ?step1_mat) \<Longrightarrow> False"
  proof - 
    assume length_lt: "length (rows_to_keep ?step1_mat) < (dim_col ?step1_mat)"
    have h: "dim_row ?new_mat < (dim_col ?step1_mat)"
      by (metis Matrix.transpose_transpose index_transpose_mat(3) length_lt length_map mat_of_cols_carrier(3) take_cols_from_matrix_def take_indices_def take_rows_and_take_cols)
    then show "False" using rank_new_mat
      by (metis Matrix.transpose_transpose carrier_matI index_transpose_mat(2) nat_less_le not_less_iff_gr_or_eq transpose_rank vec_space.rank_le_nc)    
  qed
  then have len_gt_eq: "length (rows_to_keep ?step1_mat) \<ge> (dim_col ?step1_mat)"
    using not_less by blast
  have len_match: "length (rows_to_keep ?step1_mat) = (dim_col ?step1_mat)"
    using len_lt_eq len_gt_eq
    by (simp add: rows_to_keep_def) 
  have mat_match: "matrix_A (get_signs (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))
  (get_subsets (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs))))) = 
  (get_matrix (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))"
    using reduce_system_matrix_match[of p qs signs subsets]  assms
    by blast 
  have f2: "length (get_subsets (take_rows_from_matrix (mat_of_cols (dim_row (matrix_A signs subsets)) (map ((!) (cols (matrix_A signs subsets))) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))) (rows_to_keep (mat_of_cols (dim_row (matrix_A signs subsets)) (map ((!) (cols (matrix_A signs subsets))) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))), map ((!) subsets) (rows_to_keep (mat_of_cols (dim_row (matrix_A signs subsets)) (map ((!) (cols (matrix_A signs subsets))) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))), map ((!) signs) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))) = length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
    by (metis (no_types) \<open>dim_col (mat_of_cols (dim_row (matrix_A signs subsets)) (take_indices (cols (matrix_A signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))) = length (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> \<open>length (rows_to_keep (reduce_mat_cols (matrix_A signs subsets) (solve_for_lhs p qs subsets (matrix_A signs subsets)))) = dim_col (reduce_mat_cols (matrix_A signs subsets) (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> length_map reduce_mat_cols.simps reduce_system.simps reduction_step.simps reduction_subsets_def reduction_subsets_is_get_subsets take_cols_from_matrix_def take_indices_def)
  have f3: "\<forall>p ps rss nss m. map ((!) rss) (find_nonzeros_from_input_vec (solve_for_lhs p ps nss m)) = get_signs (reduce_system p (ps, m, nss, rss))"
    by (metis (no_types) reduction_signs_def reduction_signs_is_get_signs take_indices_def)
  have square_final_mat: "square_mat (get_matrix (reduce_system p (qs, ((matrix_A signs subsets), (subsets, signs)))))"
    using mat_match assms size_of_mat same_size   
    apply (auto) using f2 f3
    by (metis (no_types, lifting) Matrix.transpose_transpose fst_conv get_matrix_def index_transpose_mat(2) len_match length_map mat_of_cols_carrier(2) mat_of_cols_carrier(3) reduce_mat_cols.simps take_cols_from_matrix_def take_indices_def take_rows_and_take_cols) 
  have rank_match: "vec_space.rank (dim_row ?new_mat) ?new_mat = dim_row ?new_mat"
    using len_match rank_new_mat
    by (simp add: take_cols_from_matrix_def take_indices_def take_rows_and_take_cols) 
  have "invertible_mat ?new_mat"
    using invertible_det og_mat_size
    using vec_space.det_rank_iff square_final_mat
    by (metis dim_col_matrix_A dim_row_matrix_A fst_conv get_matrix_def mat_match rank_match reduce_system.simps reduction_step.simps size_of_mat square_mat.elims(2))
  then show ?thesis apply (simp)
    by (metis fst_conv get_matrix_def)
qed

subsection "Well def signs preserved when reducing"

lemma reduction_doesnt_break_length_signs:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes length_init : "\<forall> x\<in> set(signs). length x = length qs"
  assumes sat_eq: "satisfy_equation p qs subsets signs"
  assumes inv_mat: "invertible_mat (matrix_A signs subsets)"
  shows "\<forall>x \<in> set(reduction_signs p qs signs subsets (matrix_A signs subsets)). 
    length x = length qs"
proof clarsimp 
  fix x
  assume x_in_set: "x \<in> set (reduction_signs p qs signs subsets (matrix_A signs subsets))"
  have "List.member (reduction_signs p qs signs subsets (matrix_A signs subsets)) x"
    using x_in_set by (simp add: in_set_member)
  then have take_ind: "List.member (take_indices signs
     (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) x"
    unfolding reduction_signs_def by auto
  have find_nz_len: "\<forall>y. List.member (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) y \<longrightarrow>  y < length signs"
    using size_of_lhs sat_eq inv_mat construct_lhs_matches_solve_for_lhs[of p qs subsets signs] unfolding find_nonzeros_from_input_vec_def
    by (metis atLeastLessThan_iff filter_is_subset in_set_member set_upt subset_code(1)) 
  then have "\<exists> n < length signs. x = signs ! n"
    using take_ind
    by (metis in_set_conv_nth reduction_signs_def take_indices_lem x_in_set) 
  then show "length x = length qs" using length_init take_indices_lem
    using nth_mem by blast
qed

subsection "Distinct signs preserved when reducing"

lemma reduction_signs_are_distinct:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes sat_eq: "satisfy_equation p qs subsets signs"
  assumes inv_mat: "invertible_mat (matrix_A signs subsets)"
  assumes distinct_init: "distinct signs"
  shows "distinct (reduction_signs p qs signs subsets (matrix_A signs subsets))"
proof -
  have solve_construct: "construct_lhs_vector p qs signs =
  solve_for_lhs p qs subsets (matrix_A signs subsets)"
    using construct_lhs_matches_solve_for_lhs assms
    by simp
  have h1: "distinct (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
    unfolding find_nonzeros_from_input_vec_def 
    using distinct_filter
    using distinct_upt by blast 
  have h2: "(\<And>j. j \<in> set (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<Longrightarrow>
          j < length signs)"
  proof - 
    fix j
    assume "j \<in> set (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
    show "j < length signs" using solve_construct size_of_lhs
      by (metis \<open>j \<in> set (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))\<close> atLeastLessThan_iff filter_is_subset find_nonzeros_from_input_vec_def set_upt subset_iff)
  qed
  then show ?thesis unfolding reduction_signs_def unfolding take_indices_def
    using distinct_init h1 h2 conjugatable_vec_space.distinct_map_nth[where ls = "signs", where inds = "(find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"]
    by blast
qed

subsection "Well def subsets preserved when reducing"

lemma reduction_doesnt_break_subsets:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes length_init : "all_list_constr subsets (length qs)"
  assumes sat_eq: "satisfy_equation p qs subsets signs"
  assumes inv_mat: "invertible_mat (matrix_A signs subsets)"
  shows "all_list_constr (reduction_subsets p qs signs subsets (matrix_A signs subsets)) (length qs)"
  unfolding all_list_constr_def 
proof clarsimp
  fix x
  assume in_red_subsets: "List.member (reduction_subsets p qs signs subsets (matrix_A signs subsets)) x "
  have solve_construct: "construct_lhs_vector p qs signs =
  solve_for_lhs p qs subsets (matrix_A signs subsets)"
    using construct_lhs_matches_solve_for_lhs assms
    by simp
  have rows_to_keep_hyp: "\<forall>y. y \<in> set (rows_to_keep (reduce_mat_cols (matrix_A signs subsets) (solve_for_lhs p qs subsets (matrix_A signs subsets)))) \<longrightarrow> 
      y < length subsets" 
  proof clarsimp 
    fix y
    assume in_set: "y \<in> set (rows_to_keep
                   (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))))"
    have in_set_2: "y \<in> set (rows_to_keep
                   (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (construct_lhs_vector p qs signs))))"
      using in_set solve_construct by simp
    let ?lhs_vec = "(solve_for_lhs p qs subsets (matrix_A signs subsets))"
    have h30: "(construct_lhs_vector p qs signs) = ?lhs_vec"
      using assms construct_lhs_matches_solve_for_lhs
      by simp 
    have h3a: "\<forall>x. List.member (find_nonzeros_from_input_vec ?lhs_vec) x \<longrightarrow>x < length (signs)" 
      using h30 size_of_lhs unfolding find_nonzeros_from_input_vec_def apply (auto)
      by (metis atLeastLessThan_iff filter_is_subset member_def set_upt subset_eq) 
    have h3c: "\<forall>x. List.member (rows_to_keep (reduce_mat_cols (matrix_A signs subsets) (solve_for_lhs p qs subsets (matrix_A signs subsets)))) x \<longrightarrow> x < length (subsets)"
    proof clarsimp
      fix x
      assume x_mem: "List.member (rows_to_keep
            (take_cols_from_matrix (matrix_A signs subsets)
              (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))) x"
      obtain nn :: "rat list list \<Rightarrow> nat list \<Rightarrow> nat" where
        "\<forall>x2 x3. (\<exists>v4. v4 \<in> set x3 \<and> \<not> v4 < length x2) = (nn x2 x3 \<in> set x3 \<and> \<not> nn x2 x3 < length x2)"
        by moura
      then have f4: "nn signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<in> set (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<and> \<not> nn signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) < length signs \<or> matrix_A (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) subsets = take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))"
        using h3a nonzero reduce_system_matrix_signs_helper by auto
      then have "matrix_A (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets)))) subsets = take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))) \<and> x \<in> set (map snd (pivot_positions (gauss_jordan_single (take_cols_from_matrix (matrix_A signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (matrix_A signs subsets))))\<^sup>T)))"
        by (metis h3a in_set_member rows_to_keep_def x_mem)
      thus "x < length (subsets)" using x_mem unfolding rows_to_keep_def using pivot_positions
        using  dim_row_matrix_A h3a in_set_member nonzero reduce_system_matrix_signs_helper rows_to_keep_def rows_to_keep_lem
        apply (auto)
        by (smt (z3) \<open>M_mat (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (M_mat signs subsets)))) subsets = take_cols_from_matrix (M_mat signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (M_mat signs subsets))) \<and> x \<in> set (map snd (pivot_positions (gauss_jordan_single (take_cols_from_matrix (M_mat signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs p qs subsets (M_mat signs subsets))))\<^sup>T)))\<close> dim_row_matrix_A rows_to_keep_def rows_to_keep_lem)
    qed
    then show "y < length subsets" using in_set_member apply (auto)
      using in_set_2 solve_construct by fastforce  
  qed
  show "list_constr x (length qs)" using in_red_subsets  unfolding  reduction_subsets_def 
    using take_indices_lem[of _ subsets]  rows_to_keep_hyp
    by (metis all_list_constr_def in_set_conv_nth in_set_member length_init) 
qed

section "Overall Lemmas"

lemma combining_to_smash:  "combine_systems p (qs1, m1, (sub1, sgn1)) (qs2, m2, (sub2, sgn2))
 =  smash_systems p qs1 qs2 sub1 sub2 sgn1 sgn2 m1 m2"
  by simp

lemma getter_functions: "calculate_data p qs = (get_matrix (calculate_data p qs), (get_subsets (calculate_data p qs), get_signs (calculate_data p qs))) "
  unfolding get_matrix_def get_subsets_def get_signs_def by auto

subsection "Key properties preserved"

subsubsection "Properties preserved when combining and reducing systems"
lemma combining_sys_satisfies_properties_helper:
  fixes p:: "real poly"
  fixes qs1 :: "real poly list"
  fixes qs2 :: "real poly list"
  fixes subsets1 subsets2 :: "nat list list"
  fixes signs1 signs2 :: "rat list list" 
  fixes matrix1 matrix2:: "rat mat"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes pairwise_rel_prime1: "\<forall>q. ((List.member qs1 q) \<longrightarrow> (coprime p q))"
  assumes nontriv2: "length qs2 > 0"
  assumes pairwise_rel_prime2: "\<forall>q. ((List.member qs2 q) \<longrightarrow> (coprime p q))"
  assumes satisfies_properties_sys1: "satisfies_properties p qs1 subsets1 signs1 matrix1"
  assumes satisfies_properties_sys2: "satisfies_properties p qs2 subsets2 signs2 matrix2"
  shows  "satisfies_properties p (qs1@qs2) (get_subsets (snd ((combine_systems p (qs1,(matrix1, (subsets1, signs1))) (qs2,(matrix2, (subsets2, signs2))))))) 
  (get_signs (snd ((combine_systems p (qs1,(matrix1, (subsets1, signs1))) (qs2,(matrix2, (subsets2, signs2))))))) 
  (get_matrix (snd ((combine_systems p (qs1,(matrix1, (subsets1, signs1))) (qs2,(matrix2, (subsets2, signs2)))))))"
proof -     
  let ?subsets = "(get_subsets (snd (combine_systems p (qs1, matrix1, subsets1, signs1)
              (qs2, matrix2, subsets2, signs2))))"
  let ?signs = "(get_signs (snd (combine_systems p (qs1, matrix1, subsets1, signs1) (qs2, matrix2, subsets2, signs2))))"
  let ?matrix = "(get_matrix (snd (combine_systems p (qs1, matrix1, subsets1, signs1) (qs2, matrix2, subsets2, signs2))))"
  have h1: "all_list_constr ?subsets (length (qs1 @ qs2))"
    using well_def_step[of subsets1 qs1 subsets2 qs2] assms
    by (simp add: nontriv2 get_subsets_def satisfies_properties_def smash_systems_def) 
  have h2: "well_def_signs (length (qs1 @ qs2)) ?signs"
    using well_def_signs_step[of qs1 qs2 signs1 signs2]
    using get_signs_def nontriv1 nontriv2 satisfies_properties_def satisfies_properties_sys1 satisfies_properties_sys2 smash_systems_def by auto 
  have h3: "distinct ?signs" 
    using distinct_step[of _ signs1 _ signs2] assms
    using combine_systems.simps get_signs_def satisfies_properties_def smash_systems_def snd_conv by auto
  have h4: "satisfy_equation p (qs1 @ qs2) ?subsets ?signs" 
    using assms inductive_step[of p qs1 qs2 signs1 signs2 subsets1 subsets2]
    using get_signs_def get_subsets_def satisfies_properties_def smash_systems_def
    by auto  
  have h5: " invertible_mat ?matrix"
    using assms inductive_step[of p qs1 qs2 signs1 signs2 subsets1 subsets2]
    by (metis combining_to_smash fst_conv get_matrix_def kronecker_invertible satisfies_properties_def smash_systems_def snd_conv)
  have h6: "?matrix = matrix_A ?signs ?subsets" 
    unfolding get_matrix_def combine_systems.simps smash_systems_def get_signs_def get_subsets_def
    apply simp
    apply (subst matrix_construction_is_kronecker_product[of subsets1 _ signs1 signs2 subsets2])
    apply (metis Ball_set all_list_constr_def in_set_member list_constr_def satisfies_properties_def satisfies_properties_sys1)
    using satisfies_properties_def satisfies_properties_sys1 well_def_signs_def apply blast
    using satisfies_properties_def satisfies_properties_sys1 satisfies_properties_sys2 by auto
  have h7: "set (characterize_consistent_signs_at_roots_copr p (qs1 @ qs2))
    \<subseteq> set (?signs)"
    using subset_step[of p qs1 signs1 qs2  signs2] assms
    by (simp add: nonzero get_signs_def satisfies_properties_def smash_systems_def) 
  then show ?thesis unfolding satisfies_properties_def using h1 h2 h3 h4 h5 h6 h7 by blast
qed

lemma combining_sys_satisfies_properties:
  fixes p:: "real poly"
  fixes qs1 :: "real poly list"
  fixes qs2 :: "real poly list"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes pairwise_rel_prime1: "\<forall>q. ((List.member qs1 q) \<longrightarrow> (coprime p q))"
  assumes nontriv2: "length qs2 > 0"
  assumes pairwise_rel_prime2: "\<forall>q. ((List.member qs2 q) \<longrightarrow> (coprime p q))"
  assumes satisfies_properties_sys1: "satisfies_properties p qs1 (get_subsets (calculate_data p qs1)) (get_signs (calculate_data p qs1)) (get_matrix (calculate_data p qs1))"
  assumes satisfies_properties_sys2: "satisfies_properties p qs2 (get_subsets (calculate_data p qs2)) (get_signs (calculate_data p qs2)) (get_matrix (calculate_data p qs2))"
  shows  "satisfies_properties p (qs1@qs2) (get_subsets (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2))))) 
  (get_signs (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2))))) 
  (get_matrix (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2)))))"
  using combining_sys_satisfies_properties_helper
  by (metis getter_functions nontriv1 nontriv2 nonzero pairwise_rel_prime1 pairwise_rel_prime2 nonzero satisfies_properties_sys1 satisfies_properties_sys2) 

lemma reducing_sys_satisfies_properties:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  fixes matrix:: "rat mat"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv: "length qs > 0"
  assumes pairwise_rel_prime: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  assumes satisfies_properties_sys: "satisfies_properties p qs subsets signs matrix"
  shows  "satisfies_properties p qs (get_subsets (reduce_system p (qs,matrix,subsets,signs)))
  (get_signs (reduce_system p (qs,matrix,subsets,signs)))
  (get_matrix (reduce_system p (qs,matrix,subsets,signs)))"
proof -
  have h1: " all_list_constr (get_subsets (reduce_system p (qs, matrix, subsets, signs))) (length qs)"
    using reduction_doesnt_break_subsets assms reduction_subsets_is_get_subsets satisfies_properties_def satisfies_properties_sys by auto
  have h2: "well_def_signs (length qs) (get_signs (reduce_system p (qs, matrix, subsets, signs)))"
    using reduction_doesnt_break_length_signs[of signs qs p subsets] assms reduction_signs_is_get_signs satisfies_properties_def well_def_signs_def by auto
  have h3: "distinct (get_signs (reduce_system p (qs, matrix, subsets, signs)))"
    using reduction_signs_are_distinct[of p qs subsets signs] assms reduction_signs_is_get_signs satisfies_properties_def by auto 
  have h4: "satisfy_equation p qs (get_subsets (reduce_system p (qs, matrix, subsets, signs)))
     (get_signs (reduce_system p (qs, matrix, subsets, signs)))"
    using reduce_system_matrix_equation_preserved[of p qs signs subsets] assms satisfies_properties_def by auto
  have h5: "invertible_mat (get_matrix (reduce_system p (qs, matrix, subsets, signs)))"
    using reduction_doesnt_break_things_invertibility assms same_size satisfies_properties_def by auto 
  have h6: "get_matrix (reduce_system p (qs, matrix, subsets, signs)) =
    matrix_A (get_signs (reduce_system p (qs, matrix, subsets, signs)))
     (get_subsets (reduce_system p (qs, matrix, subsets, signs)))"
    using reduce_system_matrix_match[of p qs signs subsets] assms satisfies_properties_def by auto
  have h7: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set (get_signs (reduce_system p (qs, matrix, subsets, signs)))"
    using reduction_doesnt_break_things_signs[of p qs signs subsets] assms reduction_signs_is_get_signs satisfies_properties_def by auto
  then show ?thesis unfolding satisfies_properties_def using h1 h2 h3 h4 h5 h6 h7
    by blast
qed

subsubsection "For length 1 qs"

lemma  length_1_calculate_data_satisfies_properties:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes len1: "length qs = 1"
  assumes pairwise_rel_prime: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  shows "satisfies_properties p qs (get_subsets (calculate_data p qs)) (get_signs (calculate_data p qs)) (get_matrix (calculate_data p qs))"
proof - 
  have h1: "all_list_constr [[],[0]] (length qs)"
    using len1 unfolding all_list_constr_def list_constr_def apply (auto)
    by (metis (full_types) length_Cons less_Suc0 list.size(3) list_all_length list_all_simps(2) member_rec(1) member_rec(2) nth_Cons_0) 
  have h2: "well_def_signs (length qs) [[1],[-1]]"
    unfolding well_def_signs_def using len1 in_set_member 
    by auto
  have h3: "distinct ([[1],[-1]]::rat list list)" 
    unfolding distinct_def using in_set_member by auto
  have h4: "satisfy_equation p qs [[],[0]] [[1],[-1]]"
    using assms base_case_satisfy_equation_alt[of qs p] by auto
  have h6: "(mat_of_rows_list 2 [[1,1], [1,-1]]::rat mat) = (matrix_A ([[1],[-1]]) ([[],[0]]) :: rat mat)" 
    using mat_base_case by auto
  then have h5: "invertible_mat (mat_of_rows_list 2 [[1,1], [1,-1]]:: rat mat)" 
    using base_case_invertible_mat
    by simp
  have h7:  "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set ([[1],[-1]])"
    using assms base_case_sgas_alt[of qs p]
    by simp  
  have base_case_hyp: "satisfies_properties p qs [[],[0]] [[1],[-1]] (mat_of_rows_list 2 [[1,1], [1,-1]])"
    using h1 h2 h3 h4 h5 h6 h7
    using satisfies_properties_def by blast 
  then have key_hyp: "satisfies_properties p qs (get_subsets (reduce_system p (qs,base_case_info))) (get_signs (reduce_system p (qs,base_case_info))) (get_matrix (reduce_system p (qs,base_case_info)))"
    using reducing_sys_satisfies_properties
    by (metis base_case_info_def len1 nonzero pairwise_rel_prime nonzero zero_less_one_class.zero_less_one) 
  show ?thesis
    by (simp add: key_hyp len1) 
qed

subsubsection "For arbitrary qs"
lemma append_not_distinct_helper: "(List.member l1 m \<and> List.member l2 m) \<longrightarrow> (distinct (l1@l2) = False)"
proof - 
  have h1: "List.member l1 m \<longrightarrow> (\<exists> n. n < length l1 \<and> (nth l1 n) = m)"
    using member_def nth_find_first
    by (simp add: member_def in_set_conv_nth) 
  have h2: "\<forall>n. n < length l1 \<and> (nth l1 n) = m \<longrightarrow> (nth (l1@l2) n) = m"
  proof clarsimp 
    fix n
    assume lt: "n < length l1"
    assume nth_l1: "m = l1 ! n"
    show "(l1 @ l2) ! n = l1 ! n" 
    proof (induct l2)
      case Nil
      then show ?case
        by simp 
    next
      case (Cons a l2)
      then show ?case
        by (simp add: lt nth_append)
    qed
  qed
  have h3: "List.member l1 m \<longrightarrow> (\<exists>n.  n < length l1 \<and> (nth (l1@l2) n) = m)" 
    using h1 h2 by auto
  have h4: "List.member l2 m \<longrightarrow> (\<exists> n. (nth l2 n) = m)"
    by (meson member_def nth_find_first) 
  have h5: "\<forall>n. (nth l2 n) = m \<longrightarrow> (nth (l1@l2) (n + length l1)) = m"
  proof clarsimp 
    fix n
    assume nth_l2: "m = l2 ! n"
    show "(l1 @ l2) ! (n + length l1) = l2 ! n" 
    proof (induct l2)
      case Nil
      then show ?case
        by (metis add.commute nth_append_length_plus) 
    next
      case (Cons a l2)
      then show ?case
        by (simp add: nth_append) 
    qed
  qed
  have h6: "List.member l2 m \<longrightarrow> (\<exists>n. (nth (l1@l2) (n + length l1)) = m)" 
    using h4 h5
    by blast 
  show ?thesis using h3 h6
    by (metis distinct_append equalityI insert_disjoint(1) insert_subset member_def order_refl) 
qed

lemma  calculate_data_satisfies_properties:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  shows "(p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) )
    \<longrightarrow> satisfies_properties p qs (get_subsets (calculate_data p qs)) (get_signs (calculate_data p qs)) (get_matrix (calculate_data p qs))"
proof (induction "length qs" arbitrary: qs rule: less_induct)
  case less
  have len1_h: "length qs = 1 \<longrightarrow> ( p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) ) \<longrightarrow> satisfies_properties p qs (get_subsets (calculate_data p qs)) (get_signs (calculate_data p qs)) (get_matrix (calculate_data p qs))"
    using  length_1_calculate_data_satisfies_properties
    by blast
  let ?len = "length qs"
  let ?q1 = "take (?len div 2) qs"
  let ?left = "calculate_data p ?q1"
  let ?q2 = "drop (?len div 2) qs"
  let ?right = "calculate_data p ?q2"
  let ?comb = "combine_systems p (?q1,?left) (?q2,?right)"
  let ?red =  "reduce_system p ?comb"
  have h_q1_len: "length qs > 1 \<longrightarrow> (length ?q1 > 0)" by auto 
  have h_q2_len: "length qs > 1 \<longrightarrow> (length ?q2 > 0)" by auto
  have h_q1_copr: "(\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) \<longrightarrow> (\<forall>q. ((List.member ?q1 q) \<longrightarrow> (coprime p q)))"
  proof -
    have mem_hyp: "(\<forall>q. ((List.member ?q1 q) \<longrightarrow> (List.member qs q)))"
      by (meson in_set_member in_set_takeD)
    then show ?thesis
      by blast 
  qed
  have h_q2_copr: "(\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) \<longrightarrow> (\<forall>q. ((List.member ?q2 q) \<longrightarrow> (coprime p q)))"
  proof -
    have mem_hyp: "(\<forall>q. ((List.member ?q2 q) \<longrightarrow> (List.member qs q)))"
      by (meson in_set_dropD in_set_member)
    then show ?thesis
      by blast 
  qed
  have q1_sat_props: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) ) \<longrightarrow> satisfies_properties p ?q1 (get_subsets (calculate_data p ?q1)) (get_signs (calculate_data p ?q1)) (get_matrix (calculate_data p ?q1))"
    using less.hyps[of ?q1] h_q1_len h_q1_copr by auto
  have q2_help: "length qs > 1 \<longrightarrow> length (drop (length qs div 2) qs) < length qs"
    using h_q1_len by auto  
  then have q2_sat_props: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) ) \<longrightarrow> satisfies_properties p ?q2 (get_subsets (calculate_data p ?q2)) (get_signs (calculate_data p ?q2)) (get_matrix (calculate_data p ?q2))"
    using less.hyps[of ?q2] h_q2_len h_q2_copr
    by blast
  have put_tog: "?q1@?q2 = qs"
    using append_take_drop_id by blast 
  then have comb_sat_props: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) ) \<longrightarrow> (satisfies_properties p (qs) (get_subsets (snd ((combine_systems p (?q1,calculate_data p ?q1) (?q2,calculate_data p ?q2))))) 
  (get_signs (snd ((combine_systems p (?q1,calculate_data p ?q1) (?q2,calculate_data p ?q2))))) 
  (get_matrix (snd ((combine_systems p (?q1,calculate_data p ?q1) (?q2,calculate_data p ?q2))))))"
    using q1_sat_props q2_sat_props  combining_sys_satisfies_properties
    using h_q1_copr h_q1_len h_q2_copr h_q2_len  put_tog
    by metis
  then have comb_sat: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) ) \<longrightarrow> 
      (satisfies_properties p (qs) (get_subsets (snd ?comb)) (get_signs (snd ?comb)) (get_matrix (snd ?comb)))"
    by blast
  have red_char: "?red = (reduce_system p (qs,(get_matrix (snd ?comb)),(get_subsets (snd ?comb)),(get_signs (snd ?comb))))"
    using getter_functions
      by (smt Pair_inject combining_to_smash get_matrix_def get_signs_def get_subsets_def prod.collapse put_tog smash_systems_def)
  then have "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) )  \<longrightarrow> (satisfies_properties p qs (get_subsets ?red) (get_signs ?red) (get_matrix ?red))"
    using reducing_sys_satisfies_properties comb_sat  by presburger 
  have len_gt1: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0) \<and> (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))) ) \<longrightarrow> satisfies_properties p qs (get_subsets (calculate_data p qs)) (get_signs (calculate_data p qs)) (get_matrix (calculate_data p qs))"
    by (smt \<open>1 < length qs \<longrightarrow>  p \<noteq> 0 \<and> 0 < length qs \<and> (\<forall>q. List.member qs q \<longrightarrow> coprime p q) \<longrightarrow> satisfies_properties p qs (get_subsets (reduce_system p (combine_systems p (take (length qs div 2) qs, calculate_data p (take (length qs div 2) qs)) (drop (length qs div 2) qs, calculate_data p (drop (length qs div 2) qs))))) (get_signs (reduce_system p (combine_systems p (take (length qs div 2) qs, calculate_data p (take (length qs div 2) qs)) (drop (length qs div 2) qs, calculate_data p (drop (length qs div 2) qs))))) (get_matrix (reduce_system p (combine_systems p (take (length qs div 2) qs, calculate_data p (take (length qs div 2) qs)) (drop (length qs div 2) qs, calculate_data p (drop (length qs div 2) qs)))))\<close> calculate_data.simps neq0_conv not_less)
  then show ?case using len1_h len_gt1
    by (metis One_nat_def Suc_lessI) 
qed


subsection "Some key results on consistent sign assignments"

lemma find_consistent_signs_at_roots_len1:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes len1: "length qs = 1"
  assumes pairwise_rel_prime: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  shows "set (find_consistent_signs_at_roots p qs) = set (characterize_consistent_signs_at_roots_copr p qs)"
proof - 
  let ?signs = "[[1],[-1]]::rat list list"
  let ?subsets = "[[],[0]]::nat list list"
  have mat_help: "matrix_A [[1],[-1]] [[],[0]] = (mat_of_rows_list 2 [[1,1], [1,-1]])"
    using mat_base_case by auto
  have well_def_signs: "well_def_signs (length qs) ?signs" unfolding well_def_signs_def 
    using len1 by auto
  have distinct_signs: "distinct ?signs"
    unfolding distinct_def by auto
  have ex_q: "\<exists>(q::real poly). qs = [q]" 
    using len1    
    using length_Suc_conv[of qs 0] by auto
  then have all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(?signs)"
    using assms base_case_sgas apply (auto)
    by (meson in_mono insertE insert_absorb insert_not_empty member_rec(1)) 
  have match: "satisfy_equation p qs ?subsets ?signs"
    using ex_q base_case_satisfy_equation nonzero pairwise_rel_prime
    apply (auto)
    by (simp add: member_rec(1)) 
  have invertible_mat: "invertible_mat (matrix_A ?signs ?subsets)"
    using inverse_mat_base_case inverse_mat_base_case_2 unfolding invertible_mat_def using mat_base_case 
    by auto
  have h: "set (get_signs (reduce_system p (qs, ((matrix_A ?signs ?subsets), (?subsets, ?signs))))) = 
    set (characterize_consistent_signs_at_roots_copr p qs)" 
    using nonzero nonzero well_def_signs distinct_signs all_info match invertible_mat
      reduce_system_sign_conditions[where p = "p", where qs = "qs", where signs = "[[1],[-1]]", where subsets = "[[],[0]]"]
    by blast 
  then have  "set (snd (snd (reduce_system p (qs, ((mat_of_rows_list 2 [[1,1], [1,-1]]), ([[],[0]], [[1],[-1]])))))) = 
    set (characterize_consistent_signs_at_roots_copr p qs)"
    unfolding get_signs_def using mat_help by auto
  then have "set (snd (snd (reduce_system p (qs, base_case_info)))) = set (characterize_consistent_signs_at_roots_copr p qs)"
    unfolding base_case_info_def
    by auto
  then show ?thesis using len1
    by (simp add: find_consistent_signs_at_roots_thm)
qed


lemma smaller_sys_are_good:
  fixes p:: "real poly"
  fixes qs1 :: "real poly list"
  fixes qs2 :: "real poly list"
  fixes subsets :: "nat list list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes pairwise_rel_prime1: "\<forall>q. ((List.member qs1 q) \<longrightarrow> (coprime p q))"
  assumes nontriv2: "length qs2 > 0"
  assumes pairwise_rel_prime2: "\<forall>q. ((List.member qs2 q) \<longrightarrow> (coprime p q))"
  assumes "set(find_consistent_signs_at_roots p qs1) = set(characterize_consistent_signs_at_roots_copr p qs1)"
  assumes "set(find_consistent_signs_at_roots p qs2) = set(characterize_consistent_signs_at_roots_copr p qs2)"
  shows "set(snd(snd(reduce_system p (combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2)))))
    = set(characterize_consistent_signs_at_roots_copr p (qs1@qs2))"
proof - 
  let ?signs = "(get_signs (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2))))) "
  let ?subsets = "(get_subsets (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2))))) "
  have h0: "satisfies_properties p (qs1@qs2) ?subsets ?signs
    (get_matrix (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2)))))"
    using calculate_data_satisfies_properties combining_sys_satisfies_properties
    using nontriv1 nontriv2 nonzero pairwise_rel_prime1 pairwise_rel_prime2 nonzero
    by simp
  then have h1: "set(characterize_consistent_signs_at_roots_copr p (qs1@qs2)) \<subseteq> set ?signs"
    unfolding satisfies_properties_def
    by linarith 
  have h2: "well_def_signs (length (qs1@qs2)) ?signs"
    using calculate_data_satisfies_properties
    using h0 satisfies_properties_def by blast 
  have h3: "distinct ?signs" 
    using calculate_data_satisfies_properties
    using h0 satisfies_properties_def by blast 
  have h4: "satisfy_equation p (qs1@qs2) ?subsets ?signs"
    using calculate_data_satisfies_properties
    using h0 satisfies_properties_def by blast 
  have h5: "invertible_mat (matrix_A ?signs ?subsets) "
    using calculate_data_satisfies_properties  
    using h0 satisfies_properties_def
    by auto
  have h: "set (take_indices ?signs 
            (find_nonzeros_from_input_vec (solve_for_lhs p (qs1@qs2) ?subsets  (matrix_A ?signs ?subsets))))
        =  set(characterize_consistent_signs_at_roots_copr p (qs1@qs2))" 
    using h1 h2 h3 h4 h5 reduction_deletes_bad_sign_conds
    using nonzero nonzero reduction_signs_def by auto
  then have h: "set (characterize_consistent_signs_at_roots_copr p (qs1@qs2)) =
    set (reduction_signs p (qs1@qs2) ?signs ?subsets  (matrix_A ?signs ?subsets ))" 
    unfolding reduction_signs_def get_signs_def
    by blast  
  have help_h: "reduction_signs p (qs1@qs2) ?signs ?subsets  (matrix_A ?signs ?subsets) 
      = (take_indices ?signs (find_nonzeros_from_input_vec (solve_for_lhs p (qs1@qs2) ?subsets  (matrix_A ?signs ?subsets))))"
    unfolding reduction_signs_def by auto
  have clear_signs: "(signs_smash (get_signs (calculate_data p qs1)) (get_signs (calculate_data p qs2))) = (get_signs (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2)))))"
    by (smt combining_to_smash get_signs_def getter_functions smash_systems_def snd_conv)
  have clear_subsets: "(subsets_smash (length qs1) (get_subsets(calculate_data p qs1)) (get_subsets (calculate_data p qs2))) = (get_subsets (snd ((combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2)))))"
    by (smt Pair_inject combining_to_smash get_subsets_def prod.collapse smash_systems_def)
  have "well_def_signs (length qs1) (get_signs (calculate_data p qs1))" 
    using calculate_data_satisfies_properties
    using nontriv1 nonzero pairwise_rel_prime1 nonzero satisfies_properties_def
    by auto 
  then have well_def_signs1: "(\<And>j. j \<in> set (get_signs (calculate_data p qs1)) \<Longrightarrow> length j = (length qs1))"
    using well_def_signs_def by blast 
  have "all_list_constr (get_subsets(calculate_data p qs1))  (length qs1) "
    using calculate_data_satisfies_properties
    using nontriv1 nonzero pairwise_rel_prime1 nonzero satisfies_properties_def
    by auto 
  then have well_def_subsets1: "(\<And>l i. l \<in> set (get_subsets(calculate_data p qs1)) \<Longrightarrow> i \<in> set l \<Longrightarrow> i < (length qs1))"
    unfolding all_list_constr_def list_constr_def using in_set_member
    by (metis in_set_conv_nth list_all_length) 
  have extra_matrix_same: "matrix_A (signs_smash (get_signs (calculate_data p qs1)) (get_signs (calculate_data p qs2)))
         (subsets_smash (length qs1) (get_subsets(calculate_data p qs1)) (get_subsets (calculate_data p qs2))) 
        = kronecker_product (get_matrix (calculate_data p qs1)) (get_matrix (calculate_data p qs2))"
    using  well_def_signs1 well_def_subsets1
    using matrix_construction_is_kronecker_product
    using calculate_data_satisfies_properties nontriv1 nontriv2 nonzero pairwise_rel_prime1 pairwise_rel_prime2 nonzero satisfies_properties_def by auto 
  then have matrix_same: "matrix_A ?signs ?subsets = kronecker_product (get_matrix (calculate_data p qs1)) (get_matrix (calculate_data p qs2))"
    using clear_signs clear_subsets
    by simp
  have comb_sys_h: "snd(snd(reduce_system p (combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2)))) =
      snd(snd(reduce_system p (qs1@qs2, (matrix_A ?signs ?subsets, (?subsets, ?signs)))))"
    unfolding get_signs_def get_subsets_def using matrix_same
    by (smt combining_to_smash get_signs_def get_subsets_def getter_functions prod.collapse prod.inject smash_systems_def)   
  then have extra_h: " snd(snd(reduce_system p (qs1@qs2, (matrix_A ?signs ?subsets, (?subsets, ?signs))))) = 
      snd(snd(reduction_step (matrix_A ?signs ?subsets) ?signs ?subsets (solve_for_lhs p (qs1@qs2) ?subsets (matrix_A ?signs ?subsets)))) "
    by simp
  then have same_h: "set(snd(snd(reduce_system p (combine_systems p (qs1,calculate_data p qs1) (qs2,calculate_data p qs2))))) 
      = set (reduction_signs p (qs1@qs2) ?signs ?subsets  (matrix_A ?signs ?subsets ))"
    using comb_sys_h unfolding reduction_signs_def
    by (metis get_signs_def help_h reduction_signs_is_get_signs) 
  then show ?thesis using h
    by blast 
qed

lemma find_consistent_signs_at_roots_1:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  shows "(p \<noteq> 0 \<and> length qs > 0 \<and>
    (\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q)))) \<longrightarrow> 
    set(find_consistent_signs_at_roots p qs) = set(characterize_consistent_signs_at_roots_copr p qs)"
proof (induction "length qs" arbitrary: qs rule: less_induct)
  case less 
  then show ?case
  proof clarsimp
    assume ind_hyp: "(\<And>qsa.
        length qsa < length qs \<Longrightarrow> qsa \<noteq> [] \<and> (\<forall>q. List.member qsa q \<longrightarrow> coprime p q) \<longrightarrow>
        set (find_consistent_signs_at_roots p qsa) =
        set (characterize_consistent_signs_at_roots_copr p qsa))"
    assume nonzero: "p \<noteq> 0"  
    assume nontriv: "qs \<noteq> []"
    assume copr:" \<forall>q. List.member qs q \<longrightarrow> coprime p q"
    let ?len = "length qs"
    let ?q1 = "take ((?len) div 2) qs"
    let ?left = "calculate_data p ?q1"
    let ?q2 = "drop ((?len) div 2) qs"
    let ?right = "calculate_data p ?q2"
    have nontriv_q1: "length qs>1 \<longrightarrow> length ?q1 > 0" 
      by auto
    have qs_more_q1: "length qs>1 \<longrightarrow> length qs > length ?q1" 
      by auto
    have pairwise_rel_prime_q1: "\<forall>q. ((List.member ?q1 q) \<longrightarrow> (coprime p q))"
    proof clarsimp 
      fix q 
      assume mem: "List.member (take (length qs div 2) qs) q"
      have "List.member qs q" using mem set_take_subset[where n = "length qs div 2"]
      proof -
        show ?thesis
          by (meson \<open>List.member (take (length qs div 2) qs) q\<close> in_set_member in_set_takeD)
      qed  
      then show "coprime p q" 
        using copr by blast 
    qed
    have nontriv_q2: "length qs>1 \<longrightarrow>length ?q2 > 0" 
      by auto
    have qs_more_q2: "length qs>1 \<longrightarrow> length qs > length ?q2" 
      by auto
    have pairwise_rel_prime_q2: "\<forall>q. ((List.member ?q2 q) \<longrightarrow> (coprime p q))" 
    proof clarsimp 
      fix q 
      assume mem: "List.member (drop (length qs div 2) qs) q"
      have "List.member qs q" using mem set_take_subset[where n = "length qs div 2"]
      proof -
        show ?thesis
          by (meson \<open>List.member (drop (length qs div 2) qs) q\<close> in_set_dropD in_set_member)
      qed
      then show "coprime p q" 
        using copr by blast 
    qed
    have key_h: "set (snd (snd (if ?len \<le> Suc 0 then reduce_system p (qs, base_case_info)
                        else   Let (combine_systems p (?q1, ?left) (?q2, ?right))
                                  (reduce_system p)))) =
       set (characterize_consistent_signs_at_roots_copr p qs)" 
    proof - 
      have h_len1 : "?len = 1 \<longrightarrow> set (snd (snd (if ?len \<le> Suc 0 then reduce_system p (qs, base_case_info)
                        else   Let (combine_systems p (?q1, ?left) (?q2, ?right))
                                  (reduce_system p)))) =
       set (characterize_consistent_signs_at_roots_copr p qs)" 
        using find_consistent_signs_at_roots_len1[of p qs] copr nonzero nontriv
        by (simp add: find_consistent_signs_at_roots_thm)
      have h_len_gt1 : "?len > 1 \<longrightarrow> set (snd (snd (if ?len \<le> Suc 0 then reduce_system p (qs, base_case_info)
                        else   Let (combine_systems p (?q1, ?left) (?q2, ?right))
                                  (reduce_system p)))) =
       set (characterize_consistent_signs_at_roots_copr p qs)" 
      proof - 
        have h_imp_a: "?len > 1 \<longrightarrow> set (snd (snd (reduce_system p (combine_systems p (?q1, ?left) (?q2, ?right))))) =
              set (characterize_consistent_signs_at_roots_copr p qs)"
        proof - 
          have h1: "?len > 1 \<longrightarrow> set(snd(snd(?left))) = set (characterize_consistent_signs_at_roots_copr p ?q1)"
            using nontriv_q1 pairwise_rel_prime_q1 ind_hyp[of ?q1] qs_more_q1             by (metis find_consistent_signs_at_roots_thm less_numeral_extra(3) list.size(3))
          have h2: "?len > 1 \<longrightarrow> set(snd(snd(?right))) = set (characterize_consistent_signs_at_roots_copr p ?q2)"
            using nontriv_q2 pairwise_rel_prime_q2 ind_hyp[of ?q2] qs_more_q2
            by (metis (full_types) find_consistent_signs_at_roots_thm list.size(3) not_less_zero)
          show ?thesis using nonzero nontriv_q1 pairwise_rel_prime_q1 nontriv_q2 pairwise_rel_prime_q2 h1 h2
              smaller_sys_are_good
            by (metis append_take_drop_id find_consistent_signs_at_roots_thm)
        qed
        then have h_imp: "?len > 1 \<longrightarrow> set (snd (snd (Let (combine_systems p (?q1, ?left) (?q2, ?right))
                                  (reduce_system p)))) =
       set (characterize_consistent_signs_at_roots_copr p qs)"
          by auto
        then show ?thesis by auto 
      qed
      show ?thesis using h_len1 h_len_gt1
        by (meson \<open>qs \<noteq> []\<close> length_0_conv less_one nat_neq_iff) 
    qed
    then show "set (find_consistent_signs_at_roots p qs) = set (characterize_consistent_signs_at_roots_copr p qs)"
      by (smt One_nat_def calculate_data.simps find_consistent_signs_at_roots_thm length_0_conv nontriv)
  qed
qed

lemma find_consistent_signs_at_roots_0:
  fixes p:: "real poly"
  assumes "p \<noteq> 0"
  shows "set(find_consistent_signs_at_roots p []) =
         set(characterize_consistent_signs_at_roots_copr p [])"
proof -
  obtain a b c where abc: "reduce_system p ([1], base_case_info) = (a,b,c)"
    using prod_cases3 by blast 
  have "find_consistent_signs_at_roots p [1] = c" using abc
    by (simp add: find_consistent_signs_at_roots_thm) 
  have *: "set (find_consistent_signs_at_roots p [1]) = set (characterize_consistent_signs_at_roots_copr p [1])"
    apply (subst find_consistent_signs_at_roots_1)
    using assms apply auto
    by (simp add: member_rec(1) member_rec(2))
  have "set(characterize_consistent_signs_at_roots_copr p []) = drop 1 ` set(characterize_consistent_signs_at_roots_copr p [1])"
    unfolding characterize_consistent_signs_at_roots_copr_def consistent_sign_vec_copr_def apply simp
    by (smt drop0 drop_Suc_Cons image_cong image_image)
  thus ?thesis using abc *
    apply (auto) apply (simp add: find_consistent_signs_at_roots_thm)
    by (simp add: find_consistent_signs_at_roots_thm) 
qed

lemma find_consistent_signs_at_roots_copr:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  assumes "p \<noteq> 0"
  assumes "\<And>q. q \<in> set qs \<Longrightarrow> coprime p q"
  shows "set(find_consistent_signs_at_roots p qs) = set(characterize_consistent_signs_at_roots_copr p qs)"
  by (metis assms find_consistent_signs_at_roots_0 find_consistent_signs_at_roots_1 in_set_member length_greater_0_conv)

lemma find_consistent_signs_at_roots:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  assumes "p \<noteq> 0"
  assumes "\<And>q. q \<in> set qs \<Longrightarrow> coprime p q"
  shows "set(find_consistent_signs_at_roots p qs) = set(characterize_consistent_signs_at_roots p qs)"
  using assms find_consistent_signs_at_roots_copr csa_list_copr_rel
  by (simp add: in_set_member)

end