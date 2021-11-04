theory Renegar_Proofs
  imports "Renegar_Algorithm"
    "BKR_Proofs"
begin

(* Note that there is significant overlap between Renegar and BKR in general, so there is some
  similarity between this file and BKR_Proofs.thy
  The main difference is that the RHS vector in Renegar is different from the RHS vector in BKR 
  In BKR, all of the qs are assumed to be relatively prime to p. Renegar removes this assumption. 

  In general, the _R's on definition and lemma names in this file are to emphasize that we are 
  working with Renegar style.
*)

section "Tarski Queries Changed"

lemma construct_NofI_R_relation:
  fixes p:: "real poly"
  fixes I1:: "real poly list"
  fixes I2:: "real poly list"
  shows "construct_NofI_R p I1 I2 =
    construct_NofI (sum_list (map power2 (p # I1))) I2"
  unfolding construct_NofI_R_def construct_NofI_def
  by metis

lemma sum_list_map_power2:
  shows "sum_list (map power2 ls) \<ge> (0::real poly)"
  apply (induct ls)
  by auto

lemma sum_list_map_power2_poly:
  shows "poly (sum_list (map power2 (ls::real poly list))) x \<ge> (0::real)"
  apply (induct ls)
  by auto

lemma construct_NofI_R_prop_helper:
  fixes p:: "real poly"
  fixes I1:: "real poly list"
  fixes I2:: "real poly list"
  assumes nonzero: "p\<noteq>0"
  shows "construct_NofI_R p I1 I2 =
    rat_of_int (int (card {x. poly (sum_list (map (\<lambda>x. x^2) (p # I1))) x = 0 \<and> poly (prod_list I2) x > 0}) - 
    int (card {x. poly (sum_list (map (\<lambda>x. x^2) (p # I1))) x = 0  \<and> poly (prod_list I2) x < 0}))"
proof -
  show ?thesis unfolding construct_NofI_R_relation[of p I1 I2]
    apply (subst construct_NofI_prop[of _ I2])
     apply auto
    using assms sum_list_map_power2
    by (metis le_add_same_cancel1 power2_less_eq_zero_iff)
qed

lemma zer_iff:
  fixes p:: "real poly"
  fixes ls:: "real poly list"
  shows "poly (sum_list (map (\<lambda>x. x^2) ls)) x = 0 \<longleftrightarrow> (\<forall>i \<in> set ls. poly i x = 0)"
proof (induct ls)
  case Nil
  then show ?case by auto
next
  case (Cons a I1)
  then show ?case
    apply simp
    apply (subst add_nonneg_eq_0_iff)
    using zero_le_power2 apply blast
    using sum_list_map_power2_poly apply presburger
    by simp
qed

lemma construct_NofI_prop_R:
  fixes p:: "real poly"
  fixes I1:: "real poly list"
  fixes I2:: "real poly list"
  assumes nonzero: "p\<noteq>0"
  shows "construct_NofI_R p I1 I2 =
    rat_of_int (int (card {x. poly p x = 0 \<and> (\<forall>q \<in> set I1. poly q x = 0) \<and> poly (prod_list I2) x > 0}) - 
    int (card {x. poly p x = 0  \<and> (\<forall>q \<in> set I1. poly q x = 0) \<and> poly (prod_list I2) x < 0}))"
  unfolding construct_NofI_R_prop_helper[OF nonzero] 
  using zer_iff
  apply auto
  by (smt (verit, del_insts) Collect_cong sum_list_map_power2_poly zero_le_power2 zero_less_power2)

section "Matrix Equation"

definition map_sgas:: "rat list \<Rightarrow> rat list"
  where "map_sgas l = map (\<lambda>r. (1 - r^2)) l"

definition z_R:: "(nat list*nat list) \<Rightarrow> rat list \<Rightarrow> rat"
  where "z_R index_list sign_asg \<equiv> (prod_list (map (nth (map_sgas sign_asg)) (fst(index_list))))*(prod_list (map (nth sign_asg) (snd(index_list))))"

definition mtx_row_R:: "rat list list \<Rightarrow> (nat list * nat list) \<Rightarrow> rat list"
  where "mtx_row_R sign_list index_list \<equiv> (map ((z_R index_list)) sign_list)"

definition matrix_A_R:: "rat list list \<Rightarrow>  (nat list * nat list) list \<Rightarrow> rat mat" 
  where "matrix_A_R sign_list subset_list = 
    (mat_of_rows_list (length sign_list) (map (\<lambda>i .(mtx_row_R sign_list i)) subset_list))"

definition all_list_constr_R:: "(nat list*nat list) list \<Rightarrow> nat \<Rightarrow> bool"
  where "all_list_constr_R L n \<equiv> (\<forall>x. List.member L x \<longrightarrow> (list_constr (fst x) n \<and> list_constr (snd x) n))"

definition alt_matrix_A_R:: "rat list list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat mat"
  where "alt_matrix_A_R signs subsets = (mat (length subsets) (length signs) 
    (\<lambda>(i, j). z_R (subsets ! i) (signs ! j)))"

lemma alt_matrix_char_R: "alt_matrix_A_R signs subsets = matrix_A_R signs subsets"
proof - 
  have h0: "(\<And>i j. i < length subsets \<Longrightarrow>
            j < length signs \<Longrightarrow>
            map (\<lambda>index_list. map (z_R index_list) signs) subsets ! i ! j = z_R (subsets ! i) (signs ! j))"
  proof -
    fix i
    fix j
    assume i_lt: "i < length subsets"
    assume j_lt: "j < length signs"
    show "((map (\<lambda>index_list. map (z_R index_list) signs) subsets) ! i) ! j = z_R (subsets ! i) (signs ! j)"
    proof - 
      have h0: "(map (\<lambda>index_list. map (z_R index_list) signs) subsets) ! i =  map (z_R (subsets ! i)) signs" 
        using nth_map i_lt
        by blast
      then show ?thesis using nth_map j_lt
        by simp 
    qed
  qed
  have h: " mat (length subsets) (length signs) (\<lambda>(i, j). z_R (subsets ! i) (signs ! j)) =
    mat (length subsets) (length signs) (\<lambda>(i, y). map (\<lambda>index_list. map (z_R index_list) signs) subsets ! i ! y)"
    using h0 eq_matI[where A = "mat (length subsets) (length signs) (\<lambda>(i, j). z_R (subsets ! i) (signs ! j))",
        where B = "mat (length subsets) (length signs) (\<lambda>(i, y). map (\<lambda>index_list. map (z_R index_list) signs) subsets ! i ! y)"]
    by auto
  show ?thesis unfolding alt_matrix_A_R_def matrix_A_R_def mat_of_rows_list_def apply (auto) unfolding mtx_row_R_def
    using h  by blast
qed

lemma subsets_are_rows_R: "\<forall>i < (length subsets). row (alt_matrix_A_R signs subsets) i  = vec (length signs) (\<lambda>j. z_R (subsets ! i) (signs ! j))"
  unfolding row_def unfolding alt_matrix_A_R_def by auto

lemma signs_are_cols_R: "\<forall>i < (length signs). col (alt_matrix_A_R signs subsets) i  = vec (length subsets) (\<lambda>j. z_R (subsets ! j) (signs ! i))"
  unfolding col_def unfolding alt_matrix_A_R_def by auto

definition consistent_sign_vec::"real poly list \<Rightarrow> real \<Rightarrow> rat list"
  where "consistent_sign_vec qs x \<equiv>
    map (\<lambda> q. if (poly q x > 0) then (1::rat) else (if (poly q x = 0) then (0::rat) else (-1::rat))) qs"

definition construct_lhs_vector_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list  \<Rightarrow> rat vec"
  where "construct_lhs_vector_R p qs signs \<equiv>                                                           
 vec_of_list (map (\<lambda>w.  rat_of_int (int (length (filter (\<lambda>v. v = w) (map (consistent_sign_vec qs) (characterize_root_list_p p)))))) signs)"

(* The ith entry of LHS vector is the number of (distinct) real zeros of p where the sign vector of 
   the qs is the ith entry of signs.*)

(* Putting all of the pieces of the construction together *)
definition satisfy_equation_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat list list \<Rightarrow> bool"
  where "satisfy_equation_R p qs subset_list sign_list =
        (mult_mat_vec (matrix_A_R sign_list subset_list) (construct_lhs_vector_R p qs sign_list) = (construct_rhs_vector_R p qs subset_list))"

(* Recharacterize the LHS vector *)
lemma construct_lhs_vector_clean_R:
  assumes "p \<noteq> 0"
  assumes "i < length signs"
  shows "(construct_lhs_vector_R p qs signs) $ i =
    card {x. poly p x = 0 \<and> ((consistent_sign_vec qs x) = (nth signs i))}"
proof -
  from poly_roots_finite[OF assms(1)] have "finite {x. poly p x = 0}" .
  then have eq: "(Collect
       ((\<lambda>v. v = signs ! i) \<circ>
        consistent_sign_vec qs) \<inter>
      set (sorted_list_of_set
            {x. poly p x = 0})) =
    {x. poly p x = 0 \<and> consistent_sign_vec qs x = signs ! i}"
    by auto
  show ?thesis
    unfolding construct_lhs_vector_R_def vec_of_list_index characterize_root_list_p_def
    apply auto
    apply (subst nth_map[OF assms(2)])
    apply auto
    apply (subst distinct_length_filter)
     apply (auto) 
    using eq 
    by auto
qed

lemma construct_lhs_vector_cleaner_R:
  assumes "p \<noteq> 0"
  shows "(construct_lhs_vector_R p qs signs) =
   vec_of_list (map (\<lambda>s. rat_of_int (card {x. poly p x = 0 \<and> ((consistent_sign_vec qs x) = s)})) signs)"
  apply (rule eq_vecI)
   apply (auto simp add:  construct_lhs_vector_clean_R[OF assms] )
   apply (simp add: vec_of_list_index)
  unfolding construct_lhs_vector_R_def
  using assms construct_lhs_vector_clean_R construct_lhs_vector_def apply auto[1]
   apply (simp add: construct_lhs_vector_R_def)
  by auto

(* Show that because our consistent sign vectors consist of 1, 0's, and -1's, z returns 1, 0, or -1 
  when applied to a consistent sign vector *)
lemma z_signs_R2:
  fixes I:: "nat list"
  fixes signs:: "rat list"
  assumes lf: "list_all (\<lambda>i. i < length signs) I"
  assumes la:  "list_all (\<lambda>s. s = 1 \<or> s = 0 \<or> s = -1) signs"
  shows "(prod_list (map (nth signs) I)) = 1 \<or>
  (prod_list (map (nth signs) I)) = 0 \<or>
  (prod_list (map (nth signs) I)) = -1" using assms
proof (induct I)
  case Nil
  then show ?case by auto
next
  case (Cons a I)
  moreover have eo: "signs ! a = 1 \<or> signs ! a = 0 \<or> signs ! a = -1" 
    using assms
    by (smt (verit, del_insts) calculation(2) list_all_length list_all_simps(1)) 
  have "prod_list (map ((!) (map_sgas signs)) (a # I)) = (1 - (signs ! a)^2)*prod_list (map ((!) (map_sgas signs)) (I))"
    unfolding map_sgas_def apply (auto)
    using calculation(2) by auto 
  then show ?case using eo
    using Cons.hyps calculation(2) la by auto 
qed

lemma z_signs_R1:
  fixes I:: "nat list"
  fixes signs:: "rat list"
  assumes lf: "list_all (\<lambda>i. i < length signs) I"
  assumes la:  "list_all (\<lambda>s. s = 1 \<or> s = 0 \<or> s = -1) signs"
  shows "(prod_list (map (nth (map_sgas signs)) I)) = 1 \<or>
(prod_list (map (nth (map_sgas signs)) I)) = 0" using assms
proof (induct I)
  case Nil
  then show ?case by auto
next
  case (Cons a I)
  moreover have "signs ! a = 1 \<or> signs ! a = 0 \<or> signs ! a = -1" 
    using assms
    by (smt (verit, best) calculation(2) list_all_length list_all_simps(1)) 
  then have eo: "1 - (signs ! a)^2 = 1 \<or> 1 - (signs !a)^2 = 0"
    using cancel_comm_monoid_add_class.diff_cancel diff_zero by fastforce
  have "prod_list (map ((!) (map_sgas signs)) (a # I)) = (1 - (signs ! a)^2)*prod_list (map ((!) (map_sgas signs)) (I))"
    unfolding map_sgas_def apply (auto)
    using calculation(2) by auto 
  then show ?case using eo
    using Cons.hyps calculation(2) la by auto 
qed

lemma z_signs_R:
  fixes I:: "(nat list * nat list)"
  fixes signs:: "rat list"
  assumes lf: "list_all (\<lambda>i. i < length signs) (fst(I))"
  assumes ls: "list_all (\<lambda>i. i < length signs) (snd(I))"
  assumes la:  "list_all (\<lambda>s. s = 1 \<or> s = 0 \<or> s = -1) signs"
  shows "(z_R I signs = 1) \<or> (z_R I signs = 0) \<or> (z_R I signs = -1)" 
  using assms z_signs_R2 z_signs_R1 unfolding z_R_def apply (auto)
  by (metis (no_types, lifting) mult_cancel_left1 mult_minus1_right)

lemma z_lemma_R:
  fixes I:: "nat list * nat list" 
  fixes sign:: "rat list"
  assumes consistent: "sign \<in> set (characterize_consistent_signs_at_roots p qs)"
  assumes welldefined1: "list_constr (fst I) (length qs)"
  assumes welldefined2: "list_constr (snd I) (length qs)"
  shows "(z_R I sign = 1) \<or> (z_R I sign = 0) \<or> (z_R I sign = -1)"
proof (rule z_signs_R)
  have same: "length sign = length qs" using consistent
    using characterize_consistent_signs_at_roots_def signs_at_def by fastforce
  thus "(list_all (\<lambda>i. i < length sign) (fst I))"
    using welldefined1  
    by (auto simp add: list_constr_def characterize_consistent_signs_at_roots_def consistent_sign_vec_copr_def)
  thus "(list_all (\<lambda>i. i < length sign) (snd I))"
    using same welldefined2  
    by (auto simp add: list_constr_def characterize_consistent_signs_at_roots_def consistent_sign_vec_copr_def)
  show "list_all (\<lambda>s. s = 1 \<or> s = 0 \<or> s = - 1) sign" using consistent
    apply (auto simp add: list.pred_map  characterize_consistent_signs_at_roots_def  consistent_sign_vec_def)
    using Ball_set
    by (simp add: list_all_length signs_at_def squash_def) 
qed

(* Show that all consistent sign vectors on roots of polynomials are in characterize_consistent_signs_at_roots  *)
lemma in_set_R: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  shows "sign \<in> set (characterize_consistent_signs_at_roots p qs)" 
proof -
  have h1: "consistent_sign_vec qs x \<in>
      set (remdups (map (signs_at qs) (sorted_list_of_set {x. poly p x = 0})))" 
    unfolding consistent_sign_vec_def signs_at_def squash_def
    using root_p nonzero poly_roots_finite set_sorted_list_of_set apply (auto)
    by (smt (verit, ccfv_SIG) Collect_cong comp_def image_eqI map_eq_conv mem_Collect_eq poly_roots_finite set_sorted_list_of_set) 
  thus ?thesis unfolding characterize_consistent_signs_at_roots_def characterize_root_list_p_def using sign_fix
    by blast
qed

lemma consistent_signs_prop_R:
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  shows  "list_all (\<lambda>s. s = 1 \<or> s = 0 \<or> s = -1) sign"
  using assms unfolding consistent_sign_vec_def squash_def apply (auto)
  by (smt (z3) length_map list_all_length nth_map) 

(* The next few lemmas relate z_R to the signs of the product of subsets of polynomials of qs *)
lemma horiz_vector_helper_pos_ind_R1: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  assumes asm: "list_constr I (length qs)"
  shows "(prod_list (map (nth (map_sgas sign)) I)) = 1 \<longleftrightarrow> 
    (\<forall>p \<in> set (retrieve_polys qs I). poly p x = 0)"
  using asm
proof (induction "I")
  case Nil
  then show ?case unfolding map_sgas_def apply (auto)
    by (simp add: retrieve_polys_def)
next
  case (Cons a xa)
  then have same0: "(prod_list (map (nth (map_sgas sign)) xa)) = 1 \<longleftrightarrow> 
    (\<forall>p \<in> set (retrieve_polys qs xa). poly p x = 0)" unfolding list_constr_def by auto
  have welldef: "a < length qs" using Cons.prems assms unfolding list_constr_def by auto
  then have h: "prod_list (map ((!) (map_sgas sign)) (a#xa)) = (1 - (sign ! a)^2)*(prod_list (map ((!) (map_sgas sign)) (xa)))"
    unfolding map_sgas_def using assms apply (auto)
    by (metis (no_types, lifting) consistent_sign_vec_def length_map nth_map) 
  have "list_all (\<lambda>s. s = 1 \<or> s = 0 \<or> s = -1) sign" using sign_fix unfolding consistent_sign_vec_def squash_def
    apply (auto)
    by (smt (z3) length_map list_all_length nth_map) 
  then have eo: "(prod_list (map ((!) (map_sgas sign)) (xa))) = 0 \<or> (prod_list (map ((!) (map_sgas sign)) (xa))) = 1"
    using z_signs_R1 assms Cons.prems consistent_sign_vec_def length_map list_all_simps(1) length_map list_all_length list_constr_def
    by (smt (verit, best))
  have "(sign ! a)^2 = 1 \<or> (sign ! a)^2 = 0" using sign_fix welldef  unfolding consistent_sign_vec_def 
    by auto
  then have s1: "(prod_list (map (nth (map_sgas sign)) (a#xa))) = 1 \<longleftrightarrow> 
    ((sign ! a)^2 = 0 \<and> (prod_list (map ((!) (map_sgas sign)) (xa))) = 1)"
    using eo h
    by (metis (mono_tags, hide_lams) cancel_comm_monoid_add_class.diff_cancel diff_zero mult.left_neutral mult_zero_left)
  have "(sign ! a)^2 = 0 \<longleftrightarrow> (poly (qs ! a) x = 0)"
    using sign_fix unfolding consistent_sign_vec_def welldef apply (auto)
     apply (smt (z3) class_field.neg_1_not_0 class_field.zero_not_one nth_map welldef)
    by (smt (z3) nth_map welldef)
  then have same1:"(prod_list (map (nth (map_sgas sign)) (a#xa))) = 1 \<longleftrightarrow> 
    ((poly (qs ! a) x = 0) \<and> (prod_list (map ((!) (map_sgas sign)) (xa))) = 1)" using s1 by auto
  have "set (retrieve_polys qs (a#xa)) = {(qs ! a)} \<union> set (retrieve_polys qs xa)"
    by (metis (no_types, lifting) insert_is_Un list.simps(15) list.simps(9) retrieve_polys_def)
  then have same2:"(\<forall>p \<in> set (retrieve_polys qs (a#xa)). poly p x = 0) = ((poly (qs ! a) x = 0)
      \<and> (\<forall>p \<in> set (retrieve_polys qs (xa)). poly p x = 0))"
    by auto 
  then show ?case using same0 same1 same2 
      assms by auto
qed

lemma csv_length_same_as_qlist: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  shows "length sign = length qs" 
  using assms unfolding consistent_sign_vec_def by auto

lemma horiz_vector_helper_zer_ind_R2: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  assumes asm: "list_constr I (length qs)"
  shows "(prod_list (map (nth sign) I)) = 0 \<longleftrightarrow> 
    (poly (prod_list (retrieve_polys qs I)) x = 0)"
  using asm
proof (induction "I")
  case Nil
  then show ?case unfolding map_sgas_def apply (auto) unfolding retrieve_polys_def
    by auto next
  case (Cons a xa)
  have "poly (prod_list (retrieve_polys qs (a # xa))) x = (poly (qs ! a) x)*poly (prod_list (retrieve_polys qs (xa))) x"
    by (simp add: retrieve_polys_def)
  then show ?case using Cons.prems
    by (smt (z3) Cons.IH class_field.neg_1_not_0 class_field.zero_not_one consistent_sign_vec_def list.simps(9) list_all_simps(1) list_constr_def mult_eq_0_iff nth_map prod_list.Cons sign_fix) 
qed

lemma horiz_vector_helper_pos_ind_R2: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  assumes asm: "list_constr I (length qs)"
  shows "(prod_list (map (nth sign) I)) = 1 \<longleftrightarrow> 
    (poly (prod_list (retrieve_polys qs I)) x > 0)"
  using asm
proof (induction "I")
  case Nil
  then show ?case unfolding map_sgas_def apply (auto) unfolding retrieve_polys_def
    by auto next
  case (Cons a xa)
  then have ih: "(prod_list (map ((!) sign) xa) = 1) = (0 < poly (prod_list (retrieve_polys qs xa)) x)"
    unfolding list_constr_def by auto
  have lensame: "length sign = length qs" using sign_fix csv_length_same_as_qlist[of p x sign qs]
      nonzero root_p by auto
  have "poly (prod_list (retrieve_polys qs (a # xa))) x = (poly (qs ! a) x)*poly (prod_list (retrieve_polys qs (xa))) x"
    by (simp add: retrieve_polys_def)
  then have iff1: "(poly (prod_list (retrieve_polys qs (a#xa))) x > 0) \<longleftrightarrow> 
      (((poly (qs ! a) x) > 0 \<and> poly (prod_list (retrieve_polys qs (xa))) x > 0) \<or> 
       ((poly (qs ! a) x) < 0 \<and> poly (prod_list (retrieve_polys qs (xa))) x < 0))"
    by (metis zero_less_mult_iff)
  have prodsame: "(prod_list (map (nth sign) (a#xa))) = (sign ! a)* (prod_list (map (nth sign) (xa)))"
    using lensame Cons.prems unfolding list_constr_def by auto
  have sagt: "sign ! a = 1 \<longleftrightarrow> (poly (qs ! a) x) > 0" using assms unfolding consistent_sign_vec_def
    apply (auto)
     apply (smt (verit, best) Cons.prems list_all_simps(1) list_constr_def neg_equal_zero nth_map zero_neq_one)
    by (smt (verit, ccfv_threshold) Cons.prems list_all_simps(1) list_constr_def nth_map)
  have salt: "sign ! a = -1 \<longleftrightarrow> (poly (qs ! a) x) < 0" using assms unfolding consistent_sign_vec_def
    apply (auto)
     apply (smt (verit, ccfv_SIG) Cons.prems less_minus_one_simps(1) less_minus_one_simps(3) list_all_simps(1) list_constr_def neg_0_less_iff_less nth_map)
    by (smt (verit, best) Cons.prems list_all_simps(1) list_constr_def nth_map)  
  have h1: "((poly (qs ! a) x) > 0 \<and> poly (prod_list (retrieve_polys qs (xa))) x > 0) \<longrightarrow>
       (prod_list (map (nth sign) (a#xa))) = 1" 
    using prodsame sagt ih by auto
  have eo: "(prod_list (map ((!) sign) xa) = 1)  \<or> (prod_list (map ((!) sign) xa) = 0) \<or> 
      (prod_list (map ((!) sign) xa) = -1)"
    using Cons.prems consistent_signs_prop_R lensame list_constr_def nonzero root_p sign_fix z_signs_R2 by auto
  have d1:"(prod_list (map ((!) sign) xa) = -1) \<Longrightarrow> (0 > poly (prod_list (retrieve_polys qs xa)) x)"
  proof -
    assume "(prod_list (map ((!) sign) xa) = -1) "
    then show "(0 > poly (prod_list (retrieve_polys qs xa)) x)"
      using prodsame salt ih assms Cons.prems class_field.neg_1_not_0 equal_neg_zero horiz_vector_helper_zer_ind_R2 linorder_neqE_linordered_idom list_all_simps(1) list_constr_def
      apply (auto)
       apply (smt (verit, ccfv_threshold) class_field.neg_1_not_0 list.set_map list_all_length semidom_class.prod_list_zero_iff)
      by (smt (verit, ccfv_threshold) class_field.neg_1_not_0 list.set_map list_all_length semidom_class.prod_list_zero_iff)
  qed
  have d2: "(0 > poly (prod_list (retrieve_polys qs xa)) x) \<longrightarrow> (prod_list (map ((!) sign) xa) = -1)"
    using eo assms horiz_vector_helper_zer_ind_R2[where p = "p", where x = "x", where sign = "sign", where I ="I"]
    apply (auto)
    using ih apply force
    by (metis (full_types, lifting) Cons.prems class_field.neg_1_not_0 horiz_vector_helper_zer_ind_R2 ih imageI list.set_map list_all_simps(1) list_constr_def mem_Collect_eq neg_equal_0_iff_equal semidom_class.prod_list_zero_iff)  
  have "(prod_list (map ((!) sign) xa) = -1) = (0 > poly (prod_list (retrieve_polys qs xa)) x)"
    using d1 d2
    by blast       
  then have h2: "((poly (qs ! a) x) < 0 \<and> poly (prod_list (retrieve_polys qs (xa))) x < 0) \<longrightarrow>
      (prod_list (map (nth sign) (a#xa))) = 1"
    using prodsame salt ih by auto
  have h3: "(prod_list (map (nth sign) (a#xa))) = 1 \<longrightarrow> (((poly (qs ! a) x) > 0 \<and> poly (prod_list (retrieve_polys qs (xa))) x > 0) \<or> 
       ((poly (qs ! a) x) < 0 \<and> poly (prod_list (retrieve_polys qs (xa))) x < 0))"
    using prodsame salt ih assms horiz_vector_helper_zer_ind_R2[where p = "p", where x = "x", where sign = "sign", where I ="I"]
    by (smt (verit, ccfv_threshold) Cons.prems \<open>poly (prod_list (retrieve_polys qs (a # xa))) x = poly (qs ! a) x * poly (prod_list (retrieve_polys qs xa)) x\<close> horiz_vector_helper_zer_ind_R2 mem_Collect_eq mult_cancel_left1 mult_not_zero sagt) 
  then show ?case using h1 h2 h3 iff1 Cons.prems by auto
qed

lemma horiz_vector_helper_pos_ind_R: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes I:: "nat list * nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  assumes asm1: "list_constr (fst I) (length qs)"
  assumes asm2: "list_constr (snd I) (length qs)"
  shows "((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x > 0)) \<longleftrightarrow> (z_R I sign = 1)"
proof - 
  have len: "length sign = length qs" using sign_fix csv_length_same_as_qlist[of p x sign qs]
      nonzero root_p by auto
  have d1: "((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x > 0)) \<longrightarrow> (z_R I sign = 1)" 
    using assms horiz_vector_helper_pos_ind_R1[where p = "p", where qs = "qs", where sign = "sign", where x = "x", where I = "fst I"]
      horiz_vector_helper_pos_ind_R2[where p = "p", where qs = "qs", where sign = "sign", where x = "x", where I = "snd I"] unfolding z_R_def 
    by auto
  have d2: "(z_R I sign = 1) \<longrightarrow> ((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x > 0))"
  proof - 
    have h1: "(z_R I sign = 1) \<longrightarrow> (\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0)" 
    proof - 
      have "(prod_list (map (nth (map_sgas sign)) (fst I))) = 1 \<or> (prod_list (map (nth (map_sgas sign)) (fst I))) = 0" 
        using len consistent_signs_prop_R[where p = "p", where qs = "qs", where x = "x", where sign = "sign"] z_signs_R1[where signs = "sign", where I = "fst I"] assms 
        unfolding list_constr_def 
        by auto
      then show ?thesis
        using z_signs_R1[where signs = "sign", where I = "fst I"] horiz_vector_helper_pos_ind_R1[where sign = "sign", where I = "fst I", where p = "p", where x = "x"] assms 
        apply (auto)
        by (metis (mono_tags, hide_lams) \<open>prod_list (map ((!) (map_sgas sign)) (fst I)) = 1 \<or> prod_list (map ((!) (map_sgas sign)) (fst I)) = 0\<close> mult_zero_left z_R_def) 
    qed
    then have h2: "(z_R I sign = 1) \<longrightarrow> (poly (prod_list (retrieve_polys qs (snd I))) x > 0)" 
      unfolding z_R_def using assms horiz_vector_helper_pos_ind_R2[where p = "p", where x = "x", where sign = "sign", where qs = "qs", where I ="snd I"]
      by (metis horiz_vector_helper_pos_ind_R1 mult.left_neutral)
    show ?thesis using h1 h2 by auto
  qed
  show ?thesis using d1 d2 by blast
qed

lemma horiz_vector_helper_pos_R: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes I:: "nat list*nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  assumes welldefined1: "list_constr (fst I) (length qs)"
  assumes welldefined2: "list_constr (snd I) (length qs)"
  shows "((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x > 0)) \<longleftrightarrow> (z_R I sign = 1)"
  using horiz_vector_helper_pos_ind_R
  using  nonzero  root_p sign_fix welldefined1 welldefined2 by blast

lemma horiz_vector_helper_neg_R: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes I:: "nat list*nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec qs x"
  assumes welldefined1: "list_constr (fst I) (length qs)"
  assumes welldefined2: "list_constr (snd I) (length qs)"
  shows "((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x < 0)) \<longleftrightarrow> (z_R I sign = -1)"
proof -
  have set_hyp: "sign \<in> set (characterize_consistent_signs_at_roots p qs)" 
    using in_set_R[of p x sign qs] nonzero root_p sign_fix  by blast 
  have z_hyp: "((z_R I sign = 1) \<or> (z_R I sign = 0) \<or> (z_R I sign = -1))" 
    using welldefined1 welldefined2 set_hyp  z_lemma_R[where sign="sign", where I = "I", where p="p", where qs="qs"] by blast
  have d1: "((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x < 0)) \<Longrightarrow> (z_R I sign = -1)"
    using horiz_vector_helper_pos_R
    using nonzero root_p sign_fix welldefined1 welldefined2
    by (smt (verit, ccfv_threshold) horiz_vector_helper_pos_ind_R1 horiz_vector_helper_zer_ind_R2 mem_Collect_eq mult_eq_0_iff z_R_def z_hyp) 
  have d2: "(z_R I sign = -1) \<Longrightarrow> ((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x < 0))" 
    using horiz_vector_helper_pos_ind_R1 horiz_vector_helper_zer_ind_R2 nonzero root_p sign_fix welldefined1 welldefined2
    by (smt (verit, ccfv_threshold) class_field.neg_1_not_0 consistent_sign_vec_def consistent_signs_prop_R equal_neg_zero horiz_vector_helper_pos_ind_R2 length_map list_all_length list_constr_def mem_Collect_eq mem_Collect_eq mult_cancel_left1 mult_not_zero retrieve_polys_def z_R_def z_signs_R1 zero_neq_one)
  then show ?thesis using d1 d2
    by linarith 
qed

lemma lhs_dot_rewrite:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list*nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  shows
    "(vec_of_list (mtx_row_R signs I) \<bullet> (construct_lhs_vector_R p qs signs)) =
   sum_list (map (\<lambda>s. (z_R I s)  *  rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) signs)"
proof -
  have "p \<noteq> 0" using nonzero by auto
  from construct_lhs_vector_cleaner[OF this]
  have rhseq: "construct_lhs_vector_R p qs signs =
    vec_of_list
    (map (\<lambda>s. rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) signs)"
    using construct_lhs_vector_cleaner_R nonzero by presburger
  have "(vec_of_list (mtx_row_R signs I) \<bullet> (construct_lhs_vector_R p qs signs)) =    
    sum_list (map2 (*) (mtx_row_R signs I) (map (\<lambda>s. rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) signs))"
    unfolding rhseq 
    apply (intro vec_of_list_dot_rewrite)
    by (auto simp add: mtx_row_R_def)
  thus ?thesis unfolding mtx_row_R_def
    using map2_map_map 
    by (auto simp add: map2_map_map)
qed

(* If we have a superset of the signs, we can drop to just the consistent ones *)
lemma construct_lhs_vector_drop_consistent_R:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list*nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes welldefined1: "list_constr (fst I) (length qs)"
  assumes welldefined2: "list_constr (snd I) (length qs)"
  shows
    "(vec_of_list (mtx_row_R signs I) \<bullet> (construct_lhs_vector_R p qs signs)) =
     (vec_of_list (mtx_row_R (characterize_consistent_signs_at_roots p qs) I) \<bullet>
      (construct_lhs_vector_R p qs (characterize_consistent_signs_at_roots p qs)))"
proof - 
  have h0: "\<forall> sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec qs ` set (characterize_root_list_p p) \<and> 
    0 < rat_of_nat (card  {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = sgn}) \<longrightarrow> z_R I sgn = 0"
  proof - 
    have "\<forall> sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec qs ` set (characterize_root_list_p p) \<and> 0 < rat_of_int (card
                  {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = sgn}) \<longrightarrow> {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = sgn} \<noteq> {}" 
      by fastforce
    then show ?thesis
    proof -
      { fix iis :: "rat list"
        have ff1: "0 \<noteq> p"
          using nonzero rsquarefree_def by blast
        obtain rr :: "(real \<Rightarrow> bool) \<Rightarrow> real" where
          ff2: "\<And>p. p (rr p) \<or> Collect p = {}"
          by moura
        { assume "\<exists>is. is = iis \<and> {r. poly p r = 0 \<and> consistent_sign_vec qs r = is} \<noteq> {}"
          then have "\<exists>is. consistent_sign_vec qs (rr (\<lambda>r. poly p r = 0 \<and> consistent_sign_vec qs r = is)) = iis \<and> {r. poly p r = 0 \<and> consistent_sign_vec qs r = is} \<noteq> {}"
            using ff2
            by (metis (mono_tags, lifting))
          then have "\<exists>r. poly p r = 0 \<and> consistent_sign_vec qs r = iis"
            using ff2
            by smt
          then have "iis \<in> consistent_sign_vec qs ` set (sorted_list_of_set {r. poly p r = 0})"
            using ff1 poly_roots_finite
            by (metis (mono_tags) imageI mem_Collect_eq set_sorted_list_of_set) }
        then have "iis \<notin> set signs \<or> iis \<in> consistent_sign_vec qs ` set (characterize_root_list_p p) \<or> \<not> 0 < rat_of_int (int (card {r. poly p r = 0 \<and> consistent_sign_vec qs r = iis}))"
          by (metis (no_types) \<open>\<forall>sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec qs ` set (characterize_root_list_p p) \<and> 0 < rat_of_int (int (card {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = sgn})) \<longrightarrow> {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = sgn} \<noteq> {}\<close> characterize_root_list_p_def) }
      then show ?thesis
        by fastforce
    qed
  qed
  then have "\<forall> sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec qs ` set (characterize_root_list_p p) \<longrightarrow> ((0 = rat_of_nat (card
                  {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = sgn}) \<or> z_R I sgn = 0))"
    by auto
  then have hyp: "\<forall> s. s \<in> set signs \<and> s \<notin> consistent_sign_vec qs ` set (characterize_root_list_p p) \<longrightarrow> (z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}) = 0)"
    by auto
  then have "(\<Sum>s\<in> set(signs). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) = 
        (\<Sum>s\<in>(set (signs) \<inter> (consistent_sign_vec qs ` set (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
  proof - 
    have "set(signs) =(set (signs) \<inter> (consistent_sign_vec qs ` set (characterize_root_list_p p))) \<union>
              (set(signs)-(consistent_sign_vec qs ` set (characterize_root_list_p p)))"
      by blast
    then have sum_rewrite: "(\<Sum>s\<in> set(signs). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) =  
          (\<Sum>s\<in> (set (signs) \<inter> (consistent_sign_vec qs ` set (characterize_root_list_p p))) \<union>
              (set(signs)-(consistent_sign_vec qs ` set (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
      by auto
    then have sum_split: "(\<Sum>s\<in> (set (signs) \<inter> (consistent_sign_vec qs ` set (characterize_root_list_p p))) \<union>
              (set(signs)-(consistent_sign_vec qs ` set (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))
          = 
(\<Sum>s\<in> (set (signs) \<inter> (consistent_sign_vec qs ` set (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))
+ (\<Sum>s\<in> (set(signs)-(consistent_sign_vec qs ` set (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
      by (metis (no_types, lifting) List.finite_set sum.Int_Diff)
    have sum_zero: "(\<Sum>s\<in> (set(signs)-(consistent_sign_vec qs ` set (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) = 0"   
      using hyp
      by (simp add: hyp)      
    show ?thesis using sum_rewrite sum_split sum_zero by linarith
  qed
  then have set_eq: "set (remdups
           (map (consistent_sign_vec qs)
             (characterize_root_list_p p))) = set (signs) \<inter> (consistent_sign_vec qs ` set (characterize_root_list_p p))"
    using all_info apply (simp add: characterize_consistent_signs_at_roots_def subset_antisym)
    by (smt (z3) Int_subset_iff consistent_sign_vec_def list.set_map map_eq_conv o_apply signs_at_def squash_def subsetI subset_antisym)
  have hyp1: "(\<Sum>s\<leftarrow>signs. z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) = 
        (\<Sum>s\<in>set (signs). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
    using distinct_signs sum_list_distinct_conv_sum_set by blast
  have hyp2: "(\<Sum>s\<leftarrow>remdups
           (map (consistent_sign_vec qs)
             (characterize_root_list_p p)). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))
  = (\<Sum>s\<in> set (remdups
           (map (consistent_sign_vec qs)
             (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
    using sum_list_distinct_conv_sum_set by blast 
  have set_sum_eq: "(\<Sum>s\<in>(set (signs) \<inter> (consistent_sign_vec qs ` set (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) =
    (\<Sum>s\<in> set (remdups
           (map (consistent_sign_vec qs)
             (characterize_root_list_p p))). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
    using set_eq by auto
  then have "(\<Sum>s\<leftarrow>signs. z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) =
    (\<Sum>s\<leftarrow>remdups
           (map (consistent_sign_vec qs)
             (characterize_root_list_p p)). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
    using set_sum_eq hyp1 hyp2
    using \<open>(\<Sum>s\<in>set signs. z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) = (\<Sum>s\<in>set signs \<inter> consistent_sign_vec qs ` set (characterize_root_list_p p). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))\<close> by linarith
  then have "consistent_sign_vec qs ` set (characterize_root_list_p p) \<subseteq> set signs \<Longrightarrow>
    (\<And>p qss.
        characterize_consistent_signs_at_roots p qss =
        remdups (map (consistent_sign_vec qss) (characterize_root_list_p p))) \<Longrightarrow>
    (\<Sum>s\<leftarrow>signs. z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) =
    (\<Sum>s\<leftarrow>remdups
           (map (consistent_sign_vec qs)
             (characterize_root_list_p p)). z_R I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
    by linarith
  then show ?thesis unfolding lhs_dot_rewrite[OF nonzero]
    apply (auto intro!: sum_list_distinct_filter simp add: distinct_signs  consistent_sign_vec_def characterize_consistent_signs_at_roots_def)
    using all_info consistent_sign_vec_def characterize_consistent_signs_at_roots_def
    by (smt (z3) list.set_map map_eq_conv o_apply set_remdups signs_at_def squash_def) 
qed

lemma matrix_equation_helper_step_R:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list*nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes welldefined1: "list_constr (fst I) (length qs)"
  assumes welldefined2: "list_constr (snd I) (length qs)"
  shows "(vec_of_list (mtx_row_R signs I) \<bullet> (construct_lhs_vector_R p qs signs)) =
   rat_of_int (card {x. poly p x = 0 \<and> (\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> poly (prod_list (retrieve_polys qs (snd I))) x > 0}) -
   rat_of_int (card {x. poly p x = 0 \<and> (\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> poly (prod_list (retrieve_polys qs (snd I))) x < 0})"
proof -
  have finset: "finite (set (map (consistent_sign_vec qs)  (characterize_root_list_p p)))" by auto
  let ?gt = "(set (map (consistent_sign_vec qs)  (characterize_root_list_p p)) \<inter> {s. z_R I s = 1})"
  let ?lt = "  (set (map (consistent_sign_vec qs)  (characterize_root_list_p p)) \<inter> {s. z_R I s = -1})"  
  let ?zer = "(set (map (consistent_sign_vec qs)  (characterize_root_list_p p)) \<inter> {s. z_R I s = 0})"
  have eq: "set (map (consistent_sign_vec qs)  (characterize_root_list_p p)) = (?gt \<union> ?lt) \<union> ?zer"
  proof safe
    fix x
    assume h:"x \<in> set (map (consistent_sign_vec qs) (characterize_root_list_p p))"
        "z_R I x \<noteq> 0" "z_R I x \<noteq> - 1" 
    then have "x \<in> set (characterize_consistent_signs_at_roots p qs)"
      unfolding characterize_consistent_signs_at_roots_def
      by (smt (verit, del_insts) characterize_consistent_signs_at_roots_def characterize_root_list_p_def imageE in_set_R nonzero poly_roots_finite set_map sorted_list_of_set(1))
    thus "z_R I x = 1"
      using h welldefined1 welldefined2 z_lemma_R by blast
  qed
  have sumeq: "(\<Sum>s\<in>(?gt\<union>?lt). z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))
  = (\<Sum>s\<in>?gt. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) +
  (\<Sum>s\<in>?lt. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
    apply (rule sum.union_disjoint) by auto
      (* First, drop the signs that are irrelevant *)
  from construct_lhs_vector_drop_consistent_R[OF assms(1-5)] have
    "vec_of_list (mtx_row_R signs I) \<bullet> construct_lhs_vector_R p qs signs =
  vec_of_list (mtx_row_R (characterize_consistent_signs_at_roots p qs) I) \<bullet>
  construct_lhs_vector_R p qs (characterize_consistent_signs_at_roots p qs)" .
    (* Now we split the sum *)
  from lhs_dot_rewrite[OF assms(1)]
  moreover have "... =
  (\<Sum>s\<leftarrow>characterize_consistent_signs_at_roots p qs.
    z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))" .
  moreover have "... =
  (\<Sum>s\<in>set (map (consistent_sign_vec qs)  (characterize_root_list_p p)).
    z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))" unfolding characterize_consistent_signs_at_roots_def sum_code[symmetric]
    apply (auto)
    by (smt (verit, best) consistent_sign_vec_def list.set_map map_eq_conv o_apply signs_at_def squash_def sum.set_conv_list) 
  moreover have setc1:"... = 
  (\<Sum>s\<in>(?gt\<union>?lt). z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) +
    (\<Sum>s\<in>?zer. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) "
    apply (subst eq) 
    apply (rule  sum.union_disjoint) by auto
  ultimately have setc: "... =
  (\<Sum>s\<in>?gt. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) +
  (\<Sum>s\<in>?lt. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) +
  (\<Sum>s\<in>?zer. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))"
    using sumeq by auto
  have "\<forall>s \<in> ?zer. (z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) = 0"
    by auto
  then have obvzer: "(\<Sum>s\<in>?zer. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) = 0"
    by auto
  (* Now recharacterize lt, gt*)
  have setroots: "set (characterize_root_list_p p) = {x. poly p x = 0}" unfolding characterize_root_list_p_def
    using poly_roots_finite nonzero rsquarefree_def set_sorted_list_of_set by blast    
  have *: "\<And>s. {x. poly p x = 0 \<and> consistent_sign_vec qs x = s} =
        {x \<in>{x. poly p x = 0}. consistent_sign_vec qs x = s}"
    by auto
  have e1: "(\<Sum>s\<in>consistent_sign_vec qs ` {x. poly p x = 0} \<inter> {s. z_R I s = 1}.
       card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}) =
     (sum (\<lambda>x. if (\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x) > 0 then 1 else 0) {x. poly p x = 0})"
    unfolding * apply (rule sum_multicount_gen)
    using \<open>finite (set (map (consistent_sign_vec qs) (characterize_root_list_p p)))\<close> setroots apply auto[1]
     apply (metis List.finite_set setroots)
  proof safe
    fix x
    assume rt: "poly p x = 0"
    then have 1: "{s \<in> consistent_sign_vec qs ` {x. poly p x = 0} \<inter> {s. z_R I s = 1}. consistent_sign_vec qs x = s} =
      {s. z_R I s = 1 \<and> consistent_sign_vec qs x = s}"
      by auto
    have 2: "... = {s. (\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (0 < poly (prod_list (retrieve_polys qs (snd I))) x)  \<and> consistent_sign_vec qs x = s}"
      using horiz_vector_helper_pos_R assms welldefined1 welldefined2 rt by blast
    have 3: "... = (if (\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (0 < poly (prod_list (retrieve_polys qs (snd I))) x)  then {consistent_sign_vec qs x} else {})"
      by auto
    then have "card {s \<in> consistent_sign_vec qs ` {x. poly p x = 0} \<inter> {s. z_R I s = 1}. consistent_sign_vec qs x = s} =
         (if ((\<forall>p \<in> set (retrieve_polys qs (fst I)). poly p x = 0) \<and> 0 < poly (prod_list  (retrieve_polys qs (snd I))) x)
          then 1 else 0)" using 1 2 3 by auto
    thus " card
          {s \<in> consistent_sign_vec qs ` {x. poly p x = 0} \<inter> {s. z_R I s = 1}.
           consistent_sign_vec qs x = s} =
         (if (\<forall>p\<in>set (retrieve_polys qs (fst I)). poly p x = 0) \<and>
             0 < poly (prod_list (retrieve_polys qs (snd I))) x
          then 1 else 0)" 
      by auto
  qed

  have gtchr: "(\<Sum>s\<in>?gt. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) =
    rat_of_int (card {x. poly p x = 0 \<and> (\<forall>p\<in>set (retrieve_polys qs (fst I)). poly p x = 0) \<and> 0 < poly (prod_list (retrieve_polys qs (snd I))) x})"
    apply (auto simp add: setroots)
    apply (subst of_nat_sum[symmetric])
    apply (subst of_nat_eq_iff)
    apply (subst e1)
    apply (subst card_eq_sum)
    apply (rule sum.mono_neutral_cong_right)
       apply (metis List.finite_set setroots)
    by auto
  have e2: " (\<Sum>s\<in>consistent_sign_vec qs ` {x. poly p x = 0} \<inter> {s. z_R I s = - 1}.
       card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}) =
     (sum (\<lambda>x. if (\<forall>p\<in>set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (poly (prod_list (retrieve_polys qs (snd I))) x) < 0 then 1 else 0) {x. poly p x = 0})"
    unfolding * apply (rule sum_multicount_gen)
    using \<open>finite (set (map (consistent_sign_vec qs) (characterize_root_list_p p)))\<close> setroots apply auto[1]
     apply (metis List.finite_set setroots)
  proof safe
    fix x
    assume rt: "poly p x = 0"
    then have 1: "{s \<in> consistent_sign_vec qs ` {x. poly p x = 0} \<inter> {s. z_R I s = -1}. consistent_sign_vec qs x = s} =
      {s. z_R I s = -1 \<and> consistent_sign_vec qs x = s}"
      by auto
    have 2: "... = {s. ((\<forall>p\<in>set (retrieve_polys qs (fst I)). poly p x = 0) \<and> 0 > poly (prod_list (retrieve_polys qs (snd I))) x)  \<and> consistent_sign_vec qs x = s}"
      using horiz_vector_helper_neg_R assms rt welldefined1 welldefined2 by blast
    have 3: "... = (if (\<forall>p\<in>set (retrieve_polys qs (fst I)). poly p x = 0) \<and> (0 > poly (prod_list (retrieve_polys qs (snd I))) x)  then {consistent_sign_vec qs x} else {})"
      by auto
    thus "card {s \<in> consistent_sign_vec qs ` {x. poly p x = 0} \<inter> {s. z_R I s = -1}. consistent_sign_vec qs x = s} =
         (if (\<forall>p\<in>set (retrieve_polys qs (fst I)). poly p x = 0) \<and> 0 > poly
                  (prod_list
                    (retrieve_polys qs (snd I)))
                  x
          then 1 else 0)" using 1 2 3 by auto
  qed
  have ltchr: "(\<Sum>s\<in>?lt. z_R I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})) =
    - rat_of_int (card {x. poly p x = 0 \<and> (\<forall>p\<in>set (retrieve_polys qs (fst I)). poly p x = 0) \<and> 0 > poly (prod_list (retrieve_polys qs (snd I))) x})"
    apply (auto simp add: setroots sum_negf)
    apply (subst of_nat_sum[symmetric])
    apply (subst of_nat_eq_iff)
    apply (subst e2)
    apply (subst card_eq_sum)
    apply (rule sum.mono_neutral_cong_right)
       apply (metis List.finite_set setroots)
    by auto
  show ?thesis using gtchr ltchr obvzer setc
    using \<open>(\<Sum>s\<leftarrow>characterize_consistent_signs_at_roots p qs. z_R I s * rat_of_int (int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}))) = (\<Sum>s\<in>set (map (consistent_sign_vec qs) (characterize_root_list_p p)). z_R I s * rat_of_int (int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})))\<close> \<open>vec_of_list (mtx_row_R (characterize_consistent_signs_at_roots p qs) I) \<bullet> construct_lhs_vector_R p qs (characterize_consistent_signs_at_roots p qs) = (\<Sum>s\<leftarrow>characterize_consistent_signs_at_roots p qs. z_R I s * rat_of_int (int (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s})))\<close> \<open>vec_of_list (mtx_row_R signs I) \<bullet> construct_lhs_vector_R p qs signs = vec_of_list (mtx_row_R (characterize_consistent_signs_at_roots p qs) I) \<bullet> construct_lhs_vector_R p qs (characterize_consistent_signs_at_roots p qs)\<close> setc1 by linarith
qed  

lemma matrix_equation_main_step_R:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list*nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes welldefined1: "list_constr (fst I) (length qs)"
  assumes welldefined2: "list_constr (snd I) (length qs)"
  shows "(vec_of_list (mtx_row_R signs I) \<bullet>
          (construct_lhs_vector_R p qs signs)) =  
    construct_NofI_R p (retrieve_polys qs (fst I)) (retrieve_polys qs (snd I))"
proof -
  show ?thesis
    unfolding construct_NofI_prop_R[OF nonzero]
    using matrix_equation_helper_step_R[OF assms]
    by linarith
qed

lemma mtx_row_length_R:
  "list_all (\<lambda>r. length r = length signs) (map (mtx_row_R signs) ls)"
  apply (induction ls)
  by (auto simp add: mtx_row_R_def)

(* Shows that as long as we have a "basis" of sign assignments (see assumptions all_info, welldefined), 
  and some other mild assumptions on our inputs (given in nonzero, distinct_signs), the construction 
  will be satisfied *)
theorem matrix_equation_R:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes subsets:: "(nat list*nat list) list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes welldefined: "all_list_constr_R (subsets) (length qs)"
  shows "satisfy_equation_R p qs subsets signs"
  unfolding satisfy_equation_R_def matrix_A_R_def
    construct_lhs_vector_R_def construct_rhs_vector_R_def all_list_constr_R_def
  apply (subst mult_mat_vec_of_list)
    apply (auto simp add: mtx_row_length_R intro!: map_vec_vec_of_list_eq_intro)
  using matrix_equation_main_step_R[OF assms(1-3), unfolded construct_lhs_vector_R_def]
  using all_list_constr_R_def in_set_member welldefined by fastforce

(* Prettifying some theorems*)

lemma consistent_signs_at_roots_eq:
  assumes "p \<noteq> 0"
  shows "consistent_signs_at_roots p qs =
         set (characterize_consistent_signs_at_roots p qs)"
  unfolding consistent_signs_at_roots_def characterize_consistent_signs_at_roots_def
    characterize_root_list_p_def
  apply auto
   apply (subst set_sorted_list_of_set)
  using assms poly_roots_finite apply blast
  unfolding sgn_vec_def sgn_def signs_at_def squash_def o_def
  using roots_def apply auto[1]
    by (smt Collect_cong assms image_iff poly_roots_finite roots_def sorted_list_of_set(1))

abbreviation w_vec_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list  \<Rightarrow> rat vec"
  where "w_vec_R \<equiv> construct_lhs_vector_R"

abbreviation v_vec_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat vec"
  where "v_vec_R \<equiv> construct_rhs_vector_R"

abbreviation M_mat_R:: "rat list list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat mat"
  where "M_mat_R \<equiv> matrix_A_R"

theorem matrix_equation_pretty:
  fixes subsets:: "(nat list*nat list) list"
  assumes "p\<noteq>0"
  assumes "distinct signs"
  assumes "consistent_signs_at_roots p qs \<subseteq> set signs"
  assumes "\<And>a b i. (a, b) \<in> set ( subsets) \<Longrightarrow> (i \<in> set a \<or> i \<in> set b) \<Longrightarrow> i < length qs"
  shows "M_mat_R signs subsets *\<^sub>v w_vec_R p qs signs = v_vec_R p qs subsets"
  unfolding satisfy_equation_R_def[symmetric]
  using matrix_equation_R[of p signs qs subsets] assms 
  using consistent_signs_at_roots_eq unfolding all_list_constr_R_def list_constr_def apply (auto)
  by (metis (no_types, lifting) Ball_set in_set_member)

section "Base Case"
definition satisfies_properties_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat list list \<Rightarrow> rat mat \<Rightarrow> bool"
  where "satisfies_properties_R p qs subsets signs matrix = 
  ( all_list_constr_R subsets (length qs) \<and> well_def_signs (length qs) signs \<and> distinct signs
  \<and> satisfy_equation_R p qs subsets signs \<and>  invertible_mat matrix  \<and> matrix = matrix_A_R signs subsets
  \<and> set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)
  )"

lemma mat_base_case_R:
  shows "matrix_A_R [[1],[0],[-1]] [([], []),([0], []),([], [0])] = (mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]])"
  unfolding matrix_A_R_def mtx_row_R_def z_R_def map_sgas_def apply (auto)
  by (simp add: numeral_3_eq_3)

lemma base_case_sgas_R:
  fixes q p:: "real poly"
  assumes nonzero: "p \<noteq> 0"
  shows "set (characterize_consistent_signs_at_roots p [q]) \<subseteq> {[1],[0], [- 1]}"
  unfolding characterize_consistent_signs_at_roots_def signs_at_def  apply (auto)
  by (meson squash_def) 

lemma base_case_sgas_alt_R:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  assumes len1: "length qs = 1"
  assumes nonzero: "p \<noteq> 0"
  shows "set (characterize_consistent_signs_at_roots p qs) \<subseteq> {[1], [0], [- 1]}"
proof - 
  have ex_q: "\<exists>(q::real poly). qs = [q]" 
    using len1    
    using length_Suc_conv[of qs 0] by auto
  then show ?thesis using base_case_sgas_R nonzero 
    by auto
qed

lemma base_case_satisfy_equation_R:
  fixes q p:: "real poly"
  assumes nonzero: "p \<noteq> 0"
  shows "satisfy_equation_R p [q] [([], []),([0], []),([], [0])] [[1],[0],[-1]] "
proof - 
  have h1: "set (characterize_consistent_signs_at_roots p [q]) \<subseteq> {[1], [0],[- 1]}"
    using base_case_sgas_R assms by auto
  have h2: "all_list_constr_R [([], []),([0], []),([], [0])] (Suc 0)" unfolding all_list_constr_R_def
    by (simp add: list_constr_def member_def)
  then show ?thesis using matrix_equation_R[where p = "p", where qs = "[q]", where signs = "[[1],[0],[-1]] ", where subsets = "[([], []),([0], []),([], [0])]"]
      nonzero h1  h2 by auto
qed

lemma base_case_satisfy_equation_alt_R:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  assumes len1: "length qs = 1"
  assumes nonzero: "p \<noteq> 0"
  shows "satisfy_equation_R p qs [([], []),([0], []),([], [0])] [[1],[0],[-1]]"
proof - 
  have ex_q: "\<exists>(q::real poly). qs = [q]" 
    using len1    
    using length_Suc_conv[of qs 0] by auto
  then show ?thesis using base_case_satisfy_equation_R nonzero
    by auto
qed

lemma base_case_matrix_eq:
  fixes q p:: "real poly"
  assumes nonzero: "p \<noteq> 0"
  shows "(mult_mat_vec (mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]]) (construct_lhs_vector_R p [q] [[1],[0],[-1]]) = 
    (construct_rhs_vector_R p [q] [([], []),([0], []),([], [0])]))"                      
  using mat_base_case_R base_case_satisfy_equation_R unfolding satisfy_equation_R_def
  by (simp add: nonzero)

lemma less_three: "(n::nat) < Suc (Suc (Suc 0)) \<longleftrightarrow> n = 0 \<or> n = 1 \<or> n = 2"
  by auto

lemma inverse_mat_base_case_R:
  shows "inverts_mat (mat_of_rows_list 3  [[1/2, -1/2, 1/2], [0, 1, 0], [1/2, -1/2, -1/2]]::rat mat) (mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]]::rat mat)"
  unfolding inverts_mat_def mat_of_rows_list_def mat_eq_iff apply auto
  unfolding less_three by (auto simp add: scalar_prod_def)

lemma inverse_mat_base_case_2_R: 
  shows "inverts_mat (mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]]::rat mat) (mat_of_rows_list 3  [[1/2, -1/2, 1/2], [0, 1, 0], [1/2, -1/2, -1/2]]:: rat mat)"
  unfolding inverts_mat_def mat_of_rows_list_def mat_eq_iff apply auto
  unfolding less_three by (auto simp add: scalar_prod_def)

lemma base_case_invertible_mat_R: 
  shows "invertible_mat (matrix_A_R [[1],[0], [- 1]] [([], []),([0], []),([], [0])])"
  unfolding invertible_mat_def using inverse_mat_base_case_R inverse_mat_base_case_2_R
  apply (auto)
  apply (simp add: mat_base_case mat_of_rows_list_def)
  using mat_base_case_R by auto 

section "Inductive Step"

(***** Need some properties of smashing; smashing signs is just as it was in BKR *****)
subsection "Lemmas on smashing subsets "

definition subsets_first_component_list::"(nat list*nat list) list \<Rightarrow> nat list list"
  where "subsets_first_component_list I = map (\<lambda>I. (fst I)) I"

definition subsets_second_component_list::"(nat list*nat list) list \<Rightarrow> nat list list"
  where "subsets_second_component_list I = map (\<lambda>I. (snd I)) I"

definition smash_list_list::"('a list*'a list) list \<Rightarrow>  ('a list*'a list) list \<Rightarrow> ('a list*'a list) list"
  where "smash_list_list s1 s2 = concat (map (\<lambda>l1. map (\<lambda>l2. (fst l1 @ fst l2, snd l1 @ snd l2)) s2) s1)"

lemma smash_list_list_property_set:
  fixes l1 l2 :: "('a list*'a list) list"
  fixes a b:: "nat"
  shows "\<forall> (elem :: ('a list*'a list)). (elem \<in> (set (smash_list_list l1 l2)) \<longrightarrow> 
    (\<exists> (elem1:: ('a list*'a list)). \<exists> (elem2:: ('a list*'a list)). 
      (elem1 \<in> set(l1) \<and> elem2 \<in> set(l2) \<and> elem = (fst elem1@ fst elem2, snd elem1 @ snd elem2))))"
proof clarsimp 
  fix a b 
  assume assum: "(a, b) \<in> set (smash_list_list l1 l2)"
  show "\<exists>aa ba. (aa, ba) \<in> set l1 \<and> (\<exists>ab bb. (ab, bb) \<in> set l2 \<and> a = aa @ ab \<and> b = ba @ bb)"
    using assum unfolding smash_list_list_def 
    apply (auto) by blast 
qed


lemma subsets_smash_property_R:
  fixes subsets1 subsets2 :: "(nat list*nat list) list"
  fixes n:: "nat"
  shows "\<forall> (elem :: nat list*nat list). (List.member (subsets_smash_R n subsets1 subsets2) elem) \<longrightarrow> 
    (\<exists> (elem1::nat list*nat list). \<exists> (elem2::nat list*nat list).
      (elem1 \<in> set(subsets1) \<and> elem2 \<in> set(subsets2) \<and> elem = ((fst elem1) @ (map ((+) n) (fst elem2)), (snd elem1) @ (map ((+) n) (snd elem2)))))"
proof -
  let ?fst_component2 = "subsets_first_component_list subsets2"
  let ?snd_component2 = "subsets_second_component_list subsets2"
  let ?new_subsets = "map (\<lambda>I. ((map ((+) n)) (fst I),  (map ((+) n)) (snd I))) subsets2"
    (* a slightly unorthodox use of signs_smash, but it closes the proof *)
  have "subsets_smash_R n subsets1 subsets2 = smash_list_list subsets1 ?new_subsets" 
    unfolding subsets_smash_R_def smash_list_list_def apply (auto)
    by (simp add: comp_def) 
  then show ?thesis using smash_list_list_property_set[of subsets1 ?new_subsets] apply (auto)
    using imageE in_set_member set_map smash_list_list_property_set
    by (smt (z3) prod.exhaust_sel)
qed

(* If subsets for smaller systems are well-defined, then subsets for combined systems are, too *)
subsection "Well-defined subsets preserved when smashing"

lemma well_def_step_R: 
  fixes qs1 qs2 :: "real poly list"
  fixes subsets1 subsets2 :: "(nat list*nat list) list"
  assumes well_def_subsets1: "all_list_constr_R (subsets1) (length qs1)"
  assumes well_def_subsets2: "all_list_constr_R (subsets2) (length qs2)"
  shows "all_list_constr_R ((subsets_smash_R (length qs1) subsets1 subsets2))
     (length (qs1 @ qs2))"
proof - 
  let ?n = "(length qs1)"
  have h1: "\<forall>elem.
     List.member (subsets_smash_R ?n subsets1 subsets2) elem \<longrightarrow>
     (\<exists> (elem1::nat list*nat list). \<exists> (elem2::nat list*nat list).
      (elem1 \<in> set(subsets1) \<and> elem2 \<in> set(subsets2) \<and> elem = ((fst elem1) @ (map ((+) ?n) (fst elem2)), (snd elem1) @ (map ((+) ?n) (snd elem2)))))"
    using subsets_smash_property_R by blast
  have h2: "\<forall>elem1 elem2. (elem1 \<in> set subsets1 \<and> elem2 \<in> set subsets2) \<longrightarrow> list_constr ((fst elem1) @ map ((+) (length qs1)) (fst elem2)) (length (qs1 @ qs2))"
  proof clarsimp 
    fix elem1 b elem2 ba
    assume e1: "(elem1, b) \<in> set subsets1"
    assume e2: "(elem2, ba) \<in> set subsets2"
    have h1: "list_constr elem1  (length qs1 + length qs2) " 
    proof - 
      have h1: "list_constr elem1  (length qs1)"  using e1 well_def_subsets1
        unfolding all_list_constr_R_def
        apply (auto) 
        by (simp add: in_set_member) 
      then show ?thesis unfolding list_constr_def
        by (simp add: list.pred_mono_strong) 
    qed
    have h2: "list_constr (map ((+) (length qs1)) elem2) (length qs1 + length qs2)"
    proof - 
      have h1: "list_constr elem2  (length qs2)"  using e2 well_def_subsets2 
        unfolding all_list_constr_R_def
        by (simp add: in_set_member) 
      then show ?thesis unfolding list_constr_def
        by (simp add: list_all_length)
    qed
    show "list_constr (elem1 @ map ((+) (length qs1)) elem2) (length qs1 + length qs2)" 
      using h1 h2 list_constr_append
      by blast 
  qed
  have h3: "\<forall>elem1 elem2. (elem1 \<in> set subsets1 \<and> elem2 \<in> set subsets2) \<longrightarrow> list_constr ((snd elem1) @ map ((+) (length qs1)) (snd elem2)) (length (qs1 @ qs2))"
  proof clarsimp 
    fix elem1 b elem2 ba
    assume e1: "(b, elem1) \<in> set subsets1"
    assume e2: "(ba, elem2) \<in> set subsets2"
    have h1: "list_constr elem1  (length qs1 + length qs2) " 
    proof - 
      have h1: "list_constr elem1  (length qs1)"  using e1 well_def_subsets1
        unfolding all_list_constr_R_def
        apply (auto) 
        by (simp add: in_set_member) 
      then show ?thesis unfolding list_constr_def
        by (simp add: list.pred_mono_strong) 
    qed
    have h2: "list_constr (map ((+) (length qs1)) elem2) (length qs1 + length qs2)"
    proof - 
      have h1: "list_constr elem2  (length qs2)"  using e2 well_def_subsets2 
        unfolding all_list_constr_R_def
        by (simp add: in_set_member) 
      then show ?thesis unfolding list_constr_def
        by (simp add: list_all_length)
    qed
    show "list_constr (elem1 @ map ((+) (length qs1)) elem2) (length qs1 + length qs2)" 
      using h1 h2 list_constr_append
      by blast 
  qed
  show ?thesis using h1 h2 h3 unfolding all_list_constr_def
    by (metis all_list_constr_R_def fst_conv snd_conv) 
qed

subsection "Consistent Sign Assignments Preserved When Smashing"

lemma subset_helper_R:
  fixes p:: "real poly"
  fixes qs1 qs2 :: "real poly list"
  fixes signs1 signs2 :: "rat list list"
  shows "\<forall> x \<in> set (characterize_consistent_signs_at_roots p (qs1 @ qs2)). 
        \<exists> x1 \<in> set (characterize_consistent_signs_at_roots p qs1). 
        \<exists> x2 \<in> set (characterize_consistent_signs_at_roots p qs2).
        x = x1@x2"
proof clarsimp 
  fix x
  assume  x_in: "x \<in> set (characterize_consistent_signs_at_roots p (qs1 @ qs2))" 
  have x_in_csv: "x \<in> set(map (consistent_sign_vec (qs1 @ qs2)) (characterize_root_list_p p))"  
    using x_in unfolding characterize_consistent_signs_at_roots_def
    by (smt (z3) consistent_sign_vec_def map_eq_conv o_apply set_remdups signs_at_def squash_def) 
  have csv_hyp: "\<forall>r. consistent_sign_vec (qs1 @ qs2) r = (consistent_sign_vec qs1 r)@(consistent_sign_vec qs2 r)"
    unfolding consistent_sign_vec_def by auto
  have exr_iff: "(\<exists>r \<in> set (characterize_root_list_p p). x = consistent_sign_vec (qs1 @ qs2) r) \<longleftrightarrow> (\<exists>r \<in> set (characterize_root_list_p p). x = (consistent_sign_vec qs1 r)@(consistent_sign_vec qs2 r))"
    using csv_hyp by auto
  have exr: "x \<in> set(map (consistent_sign_vec (qs1 @ qs2)) (characterize_root_list_p p)) \<longrightarrow> (\<exists>r \<in> set (characterize_root_list_p p). x = consistent_sign_vec (qs1 @ qs2) r)"
    by auto
  have mem_list1: "\<forall> r \<in> set (characterize_root_list_p p). (consistent_sign_vec qs1 r) \<in> set(map (consistent_sign_vec qs1) (characterize_root_list_p p))"
    by simp
  have mem_list2: "\<forall> r \<in> set (characterize_root_list_p p). (consistent_sign_vec qs2 r) \<in> set(map (consistent_sign_vec qs2) (characterize_root_list_p p))"
    by simp
  then show "\<exists>x1\<in>set (characterize_consistent_signs_at_roots p qs1).
            \<exists>x2\<in>set (characterize_consistent_signs_at_roots p qs2). x = x1 @ x2"
    using x_in_csv exr mem_list1 mem_list2 characterize_consistent_signs_at_roots_def exr_iff
    using imageE image_eqI map_append set_map set_remdups signs_at_def x_in
    by auto
qed

lemma subset_step_R:  
  fixes p:: "real poly"
  fixes qs1 qs2 :: "real poly list"
  fixes signs1 signs2 :: "rat list list"
  assumes csa1: "set (characterize_consistent_signs_at_roots p qs1) \<subseteq> set (signs1)"
  assumes csa2: "set (characterize_consistent_signs_at_roots p qs2) \<subseteq> set (signs2)"  
  shows "set (characterize_consistent_signs_at_roots p
          (qs1 @ qs2))
    \<subseteq> set (signs_smash signs1 signs2)"
proof - 
  have h0: "\<forall> x \<in> set (characterize_consistent_signs_at_roots p (qs1 @ qs2)). \<exists> x1 \<in> set (characterize_consistent_signs_at_roots p qs1). \<exists> x2 \<in> set (characterize_consistent_signs_at_roots p qs2).
     (x = x1@x2)" using subset_helper_R[of p qs1 qs2]
    by blast 
  then have "\<forall>x \<in> set (characterize_consistent_signs_at_roots p (qs1 @ qs2)). 
          x \<in> set (signs_smash (characterize_consistent_signs_at_roots p qs1) 
          (characterize_consistent_signs_at_roots p qs2))"
    unfolding signs_smash_def apply (auto)
    by fastforce 
  then have "\<forall>x \<in> set (characterize_consistent_signs_at_roots p
          (qs1 @ qs2)). x \<in> set (signs_smash signs1 signs2)"
    using csa1 csa2 subset_smash_signs[of _ signs1 _ signs2] apply (auto)
    by blast 
  thus ?thesis
    by blast 
qed

subsection "Main Results"
lemma dim_row_matrix_A_R[simp]:
  shows "dim_row (matrix_A_R signs subsets) = length subsets"
  unfolding matrix_A_R_def by auto

lemma dim_col_matrix_A_R[simp]:
  shows "dim_col (matrix_A_R signs subsets) = length signs"
  unfolding matrix_A_R_def by auto

lemma length_subsets_smash_R:
  shows
    "length (subsets_smash_R n subs1 subs2) = length subs1 * length subs2"
  unfolding subsets_smash_R_def length_concat
  by (auto simp add: o_def sum_list_triv)

lemma z_append_R:
  fixes xs:: "(nat list * nat list)"
  assumes "\<And>i. i \<in> set (fst xs) \<Longrightarrow> i  < length as"
  assumes "\<And>i. i \<in> set (snd xs) \<Longrightarrow> i  < length as"
  shows "z_R ((fst xs) @ (map ((+) (length as)) (fst ys)), (snd xs) @ (map ((+) (length as)) (snd ys))) (as @ bs) = z_R xs as * z_R ys bs"
proof -
  have 1: "map ((!) (as @ bs)) (fst xs) = map ((!) as) (fst xs)"
    unfolding list_eq_iff_nth_eq
    using assms by (auto simp add:nth_append)
  have 2: "map ((!) (as @ bs) \<circ> (+) (length as)) (fst ys) = map ((!) bs) (fst ys)"
    unfolding list_eq_iff_nth_eq
    using assms by auto
  have 3: "map ((!) (as @ bs)) (snd xs) = map ((!) as) (snd xs)"
    unfolding list_eq_iff_nth_eq
    using assms by (auto simp add:nth_append)
  have 4: "map ((!) (as @ bs) \<circ> (+) (length as)) (snd ys) = map ((!) bs) (snd ys)"
    unfolding list_eq_iff_nth_eq
    using assms by auto
  show ?thesis
    unfolding z_R_def apply auto
    unfolding 1 2 3 4 apply (auto)
    by (smt (z3) assms(1) comp_apply length_map map_append map_eq_conv map_sgas_def nth_append nth_append_length_plus) 
qed

(* Shows that the matrix of a smashed system is the Kronecker product of the matrices of the two
  systems being combined *)
lemma matrix_construction_is_kronecker_product_R: 
  fixes qs1 :: "real poly list"
  fixes subs1 subs2 :: "(nat list*nat list) list"
  fixes signs1 signs2 :: "rat list list"
    (* n1 is the number of polynomials in the "1" sets *)
  assumes "\<And>l i. l \<in> set subs1 \<Longrightarrow> (i \<in> set (fst l) \<or> i \<in> set (snd l)) \<Longrightarrow> i < n1"
  assumes "\<And>j. j \<in> set signs1 \<Longrightarrow> length j = n1"
  shows "(matrix_A_R (signs_smash signs1 signs2) (subsets_smash_R n1 subs1 subs2)) =
    kronecker_product (matrix_A_R signs1 subs1) (matrix_A_R signs2 subs2)"
  unfolding mat_eq_iff dim_row_matrix_A_R dim_col_matrix_A_R
    length_subsets_smash_R length_signs_smash dim_kronecker
proof safe
  fix i j
  assume i: "i < length subs1 * length subs2"
  assume j: "j < length signs1 * length signs2"

  have ld: "i div length subs2 < length subs1"
    "j div length signs2 < length signs1"
    using i j less_mult_imp_div_less by auto
  have lm: "i mod length subs2 < length subs2"
    "j mod length signs2 < length signs2"
    using i j less_mult_imp_mod_less by auto

  have n1: "n1 = length (signs1 ! (j div length signs2))"
    using assms(2) ld(2) nth_mem by blast

  have 1: "matrix_A_R (signs_smash signs1 signs2) (subsets_smash_R n1 subs1 subs2) $$ (i, j) =
    z_R (subsets_smash_R n1 subs1 subs2 ! i) (signs_smash signs1 signs2 ! j)"
    unfolding mat_of_rows_list_def matrix_A_R_def mtx_row_R_def
    using i j by (auto simp add: length_signs_smash length_subsets_smash_R)
  have 2: " ... = z_R ((fst (subs1 ! (i div length subs2)) @ map ((+) n1) (fst(subs2 ! (i mod length subs2)))),
  (snd (subs1 ! (i div length subs2)) @ map ((+) n1) (snd (subs2 ! (i mod length subs2)))))
     (signs1 ! (j div length signs2) @ signs2 ! (j mod length signs2))"
    unfolding signs_smash_def subsets_smash_R_def
    apply (subst length_eq_concat)
    using i apply (auto simp add: mult.commute)
    apply (subst length_eq_concat)
    using j apply (auto simp add: mult.commute)
    using ld lm by auto
  have 3: "... =
  z_R (subs1 ! (i div length subs2)) (signs1 ! (j div length signs2)) *
  z_R (subs2 ! (i mod length subs2)) (signs2 ! (j mod length signs2))"
    unfolding n1
    apply (subst z_append_R)
    apply (auto simp add: n1[symmetric])
    using assms(1) ld(1) nth_mem
    apply blast
    using assms(1) ld(1) nth_mem by blast
  have 4: "kronecker_product (matrix_A_R signs1 subs1) (matrix_A_R signs2 subs2) $$ (i,j) =
    z_R (subs1 ! (i div length subs2))
     (signs1 ! (j div length signs2)) *
    z_R (subs2 ! (i mod length subs2))
     (signs2 ! (j mod length signs2))"
    unfolding kronecker_product_def matrix_A_R_def mat_of_rows_list_def mtx_row_R_def
    using i j apply (auto simp add: Let_def)
    apply (subst index_mat(1)[OF ld])
    apply (subst index_mat(1)[OF lm])
    using ld lm by auto
  show "matrix_A_R (signs_smash signs1 signs2) (subsets_smash_R n1 subs1 subs2) $$ (i, j) =
        kronecker_product (matrix_A_R signs1 subs1) (matrix_A_R signs2 subs2) $$ (i, j)"
    using 1 2 3 4 by auto 
qed

(* Given that two smaller systems satisfy some mild constraints, show that their combined system
  (after smashing the signs and subsets) satisfies the matrix equation, and that the matrix of the
  combined system is invertible. *)
lemma inductive_step_R:
  fixes p:: "real poly"
  fixes qs1 qs2 :: "real poly list"
  fixes subsets1 subsets2 :: "(nat list*nat list) list"
  fixes signs1 signs2 :: "rat list list"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes nontriv2: "length qs2 > 0"
  assumes welldefined_signs1: "well_def_signs (length qs1) signs1"
  assumes welldefined_signs2: "well_def_signs (length qs2) signs2"
  assumes distinct_signs1: "distinct signs1"
  assumes distinct_signs2: "distinct signs2"
  assumes all_info1: "set (characterize_consistent_signs_at_roots p qs1) \<subseteq> set(signs1)"
  assumes all_info2: "set (characterize_consistent_signs_at_roots p qs2) \<subseteq> set(signs2)"
  assumes welldefined_subsets1: "all_list_constr_R (subsets1) (length qs1)"
  assumes welldefined_subsets2: "all_list_constr_R (subsets2) (length qs2)"
  assumes invertibleMtx1: "invertible_mat (matrix_A_R signs1 subsets1)"
  assumes invertibleMtx2: "invertible_mat (matrix_A_R signs2 subsets2)"
  shows "satisfy_equation_R p (qs1@qs2) (subsets_smash_R (length qs1) subsets1 subsets2) (signs_smash signs1 signs2) 
        \<and> invertible_mat (matrix_A_R (signs_smash signs1 signs2) (subsets_smash_R (length qs1) subsets1 subsets2))"
proof - 
  have h1: "invertible_mat (matrix_A_R (signs_smash signs1 signs2) (subsets_smash_R (length qs1) subsets1 subsets2))"
    using matrix_construction_is_kronecker_product_R
      kronecker_invertible invertibleMtx1 invertibleMtx2
      welldefined_subsets1 welldefined_subsets2 unfolding all_list_constr_R_def list_constr_def
    using Ball_set in_set_member well_def_signs_def welldefined_signs1 in_set_conv_nth list_all_length
    apply (auto)
    by (smt (z3) Ball_set kronecker_invertible member_def)
  have h2a: "distinct (signs_smash signs1 signs2)" 
    using distinct_signs1 distinct_signs2 welldefined_signs1 welldefined_signs2 nontriv1 nontriv2 
      distinct_step by auto
  have h2c: "all_list_constr_R ((subsets_smash_R (length qs1) subsets1 subsets2)) (length (qs1@qs2))" 
    using well_def_step_R
      welldefined_subsets1 welldefined_subsets2
    by blast
  have h2d: "set (characterize_consistent_signs_at_roots p (qs1@qs2)) \<subseteq> set(signs_smash signs1 signs2)" 
    using subset_step_R all_info1 all_info2
    by simp 
  have h2: "satisfy_equation_R p (qs1@qs2) (subsets_smash_R (length qs1) subsets1 subsets2) (signs_smash signs1 signs2)"
    using matrix_equation_R[where p="p", where qs="qs1@qs2", where subsets = "subsets_smash_R (length qs1) subsets1 subsets2",
        where signs = "signs_smash signs1 signs2"] 
        h2a h2c h2d apply (auto) using nonzero by blast
  show ?thesis using h1 h2 by blast
qed

section "Reduction Step Proofs"
  (* Some definitions *)
definition get_matrix_R:: "(rat mat \<times> ((nat list*nat list) list \<times> rat list list)) \<Rightarrow> rat mat"
  where "get_matrix_R data = fst(data)"

definition get_subsets_R:: "(rat mat \<times> ((nat list*nat list) list \<times> rat list list)) \<Rightarrow>  (nat list*nat list) list"
  where "get_subsets_R data = fst(snd(data))"

definition get_signs_R:: "(rat mat \<times> ((nat list*nat list) list \<times> rat list list)) \<Rightarrow> rat list list"
  where "get_signs_R data = snd(snd(data))"

definition reduction_signs_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat mat \<Rightarrow> rat list list" 
  where "reduction_signs_R p qs signs subsets matr = 
    (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets matr)))"

definition reduction_subsets_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat mat \<Rightarrow> (nat list*nat list) list" 
  where "reduction_subsets_R p qs signs subsets matr = 
    (take_indices subsets (rows_to_keep (reduce_mat_cols matr (solve_for_lhs_R p qs subsets matr))))"

(* Some basic lemmas *)
lemma reduction_signs_is_get_signs_R: "reduction_signs_R p qs signs subsets m =  get_signs_R (reduce_system_R p (qs, (m, (subsets, signs))))"
  unfolding reduction_signs_R_def get_signs_R_def apply (simp)
  using reduction_step_R.elims snd_conv
  by metis 

lemma reduction_subsets_is_get_subsets_R: "reduction_subsets_R p qs signs subsets m =  get_subsets_R (reduce_system_R p (qs, (m, (subsets, signs))))"
  unfolding reduction_subsets_R_def get_subsets_R_def
  using reduce_system.simps reduction_step.elims fst_conv snd_conv
  by (metis reduce_system_R.simps reduction_step_R.simps) 

subsection "Showing sign conditions preserved when reducing"

lemma take_indices_lem_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes arb_list :: "('a list*'a list) list"
  fixes index_list :: "nat list" 
  fixes n:: "nat"
  assumes lest: "n < length (take_indices arb_list index_list)"
  assumes well_def: "\<forall>q.(List.member index_list q \<longrightarrow> q < length arb_list)"
  shows "\<exists>k<length arb_list.
            (take_indices arb_list index_list) ! n =  arb_list ! k"
  using lest well_def unfolding take_indices_def apply (auto)
  by (metis member_def nth_mem)

lemma size_of_mat_R:
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  shows "(matrix_A_R signs subsets) \<in> carrier_mat (length subsets) (length signs)"
  unfolding matrix_A_R_def carrier_mat_def by auto

lemma size_of_lhs_R: 
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes signs :: "rat list list" 
  shows "dim_vec (construct_lhs_vector_R p qs signs) = length signs"
  unfolding construct_lhs_vector_R_def
  by simp

lemma size_of_rhs_R: 
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list" 
  shows "dim_vec (construct_rhs_vector_R p qs subsets) = length subsets"
  unfolding construct_rhs_vector_R_def
  by simp

lemma same_size_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes invertible_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "length subsets = length signs"
  using invertible_mat unfolding invertible_mat_def
  using size_of_mat_R[of signs subsets] size_of_lhs_R[of p qs signs] size_of_rhs_R[of p qs subsets]
  by simp

lemma construct_lhs_matches_solve_for_lhs_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes match: "satisfy_equation_R p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "(construct_lhs_vector_R p qs signs) = solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)"
proof -
  have matrix_equation_hyp: "(mult_mat_vec (matrix_A_R signs subsets) (construct_lhs_vector_R p qs signs) = (construct_rhs_vector_R p qs subsets))"
    using match unfolding satisfy_equation_R_def by blast
  then have eqn_hyp: " ((matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) *\<^sub>v (mult_mat_vec (matrix_A_R signs subsets) (construct_lhs_vector_R p qs signs)) = 
      mult_mat_vec (matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) (construct_rhs_vector_R p qs subsets))"
    using invertible_mat 
    by (simp add: matrix_equation_hyp) 
  have match_hyp: "length subsets = length signs" using same_size_R invertible_mat by auto 
  then have dim_hyp1: "matrix_A_R signs subsets \<in> carrier_mat (length signs) (length signs)"
    using size_of_mat
    by auto 
  then have dim_hyp2: "matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets)) \<in> carrier_mat (length signs) (length signs)"
    using invertible_mat dim_invertible
    by blast 
  have mult_assoc_hyp: "((matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) *\<^sub>v (mult_mat_vec (matrix_A_R signs subsets) (construct_lhs_vector_R p qs signs)))
    = (((matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) * (matrix_A_R signs subsets)) *\<^sub>v  (construct_lhs_vector_R p qs signs))"
    using mult_assoc dim_hyp1 dim_hyp2 size_of_lhs_R by auto
  have cancel_helper: "(((matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) * (matrix_A_R signs subsets)) *\<^sub>v  (construct_lhs_vector_R p qs signs))
  = (1\<^sub>m (length signs)) *\<^sub>v   (construct_lhs_vector_R p qs signs)"
    using invertible_means_mult_id[where A= "matrix_A_R signs subsets"] dim_hyp1
    by (simp add: invertible_mat match_hyp) 
  then have cancel_hyp: "(((matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) * (matrix_A_R signs subsets)) *\<^sub>v  (construct_lhs_vector_R p qs signs))
  = (construct_lhs_vector_R p qs signs)"
    apply (auto)
    by (metis carrier_vec_dim_vec one_mult_mat_vec size_of_lhs_R)
  then have mult_hyp: "((matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) *\<^sub>v (mult_mat_vec (matrix_A_R signs subsets) (construct_lhs_vector_R p qs signs)))
    = (construct_lhs_vector_R p qs signs)"
    using mult_assoc_hyp cancel_hyp  
    by simp
  then have "(construct_lhs_vector_R p qs signs) =  (mult_mat_vec (matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets))) (construct_rhs_vector_R p qs subsets)) "
    using eqn_hyp
    by simp 
  then show ?thesis
    unfolding solve_for_lhs_R_def
    by (simp add: mat_inverse_same)
qed

(* Then show that dropping columns doesn't affect the consistent sign assignments *)
lemma reduction_doesnt_break_things_signs_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(reduction_signs_R p qs signs subsets (matrix_A_R signs subsets))"
proof - 
  have dim_hyp2: "matr_option (dim_row (matrix_A_R signs subsets))
     (mat_inverse (matrix_A_R signs subsets)) \<in> carrier_mat (length signs) (length signs)"
    using invertible_mat dim_invertible
    using same_size_R by fastforce 
  have "(construct_lhs_vector_R p qs signs) = solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)"
    using construct_lhs_matches_solve_for_lhs_R assms by auto
  then have "(solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) =
   vec_of_list (map rat_of_nat (map (\<lambda>s. card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}) signs))" 
    using construct_lhs_vector_cleaner_R assms
    by (metis (mono_tags, lifting) list.map_cong map_map o_apply of_int_of_nat_eq)
  then have "\<forall> n < (dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))). 
       (((solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) $ n = 0) \<longrightarrow>
       (nth signs n) \<notin> set (characterize_consistent_signs_at_roots p qs))"
  proof - 
    have h0: "\<forall> n < (dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))). 
       (((solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) $ n = 0) \<longrightarrow> 
       rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = (nth signs n)}) = 0)"
      by (metis (mono_tags, lifting) \<open>construct_lhs_vector_R p qs signs = solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)\<close> construct_lhs_vector_clean_R nonzero of_nat_0_eq_iff of_rat_of_nat_eq size_of_lhs_R)
    have h1: "\<forall> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}) = 0 \<longrightarrow> 
        (\<nexists> x. poly p x = 0 \<and> consistent_sign_vec qs x = w))"
    proof clarsimp 
      fix x
      assume card_asm: "card {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = consistent_sign_vec qs x} = 0"
      assume zero_asm: "poly p x = 0"
      have card_hyp: "{xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = consistent_sign_vec qs x} = {}"
        using card_eq_0_iff
        using card_asm nonzero poly_roots_finite
        by (metis (full_types) finite_Collect_conjI)
      have "x \<in> {xa. poly p xa = 0 \<and> consistent_sign_vec qs xa = consistent_sign_vec qs x}"
        using zero_asm by auto
      thus "False" using card_hyp
        by blast
    qed
    have h2: "\<And> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}) = 0 \<Longrightarrow>
       (\<not>List.member (characterize_consistent_signs_at_roots p qs) w))"
    proof clarsimp
      fix w
      assume card_asm: "card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w} = 0"
      assume mem_asm: "List.member (characterize_consistent_signs_at_roots p qs) w"
      have h0: "\<nexists> x. poly p x = 0 \<and> consistent_sign_vec qs x = w" using h1 card_asm
        by (simp add: h1)
      have h1: "\<exists> x. poly p x = 0 \<and> consistent_sign_vec qs x = w" using mem_asm 
        unfolding characterize_consistent_signs_at_roots_def characterize_root_list_p_def
      proof -
        have "w \<in> Collect (List.member (remdups (map (consistent_sign_vec qs) (sorted_list_of_set {r. poly p r = 0}))))"
          using characterize_consistent_signs_at_roots_def mem_asm characterize_root_list_p_def
          by (smt (verit, ccfv_SIG) consistent_sign_vec_def h0 imageE in_set_member list.set_map map_cong mem_Collect_eq nonzero o_apply poly_roots_finite set_remdups set_sorted_list_of_set signs_at_def squash_def)
        then have f1: "w \<in> set (map (consistent_sign_vec qs) (sorted_list_of_set {r. poly p r = 0}))"
          by (metis (no_types) in_set_member mem_Collect_eq set_remdups)
        have "finite {r. poly p r = 0}"
          using nonzero poly_roots_finite by blast
        then show ?thesis
          using f1 by auto
      qed
      show "False" using h0 h1 by auto
    qed
    then have h3: "\<forall> w. rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}) = 0 \<longrightarrow> 
        w \<notin> set (characterize_consistent_signs_at_roots p qs)"
      by (simp add: in_set_member)
    show ?thesis using h0 h3
      by blast 
  qed
  then have "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set (take_indices signs
             (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))"
    using all_info
      reduction_signs_set_helper_lemma[where A = "set (characterize_consistent_signs_at_roots p qs)", where B = "signs",
      where C = "(solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))"]
    using dim_hyp2 solve_for_lhs_R_def by (simp add: mat_inverse_same)
  then show ?thesis unfolding reduction_signs_R_def by auto
qed

lemma reduction_deletes_bad_sign_conds_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "set (characterize_consistent_signs_at_roots p qs) = set(reduction_signs_R p qs signs subsets (matrix_A_R signs subsets))"
proof - 
  have dim_hyp2: "matr_option (dim_row (matrix_A_R signs subsets))
       (mat_inverse (matrix_A_R signs subsets)) \<in> carrier_mat (length signs) (length signs)"
    using invertible_mat dim_invertible
    using same_size_R by fastforce 
  have supset: "set (characterize_consistent_signs_at_roots p qs) \<supseteq> set(reduction_signs_R p qs signs subsets (matrix_A_R signs subsets))" 
  proof - 
    have "(construct_lhs_vector_R p qs signs) = solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)"
      using construct_lhs_matches_solve_for_lhs_R assms by auto
    then have "(solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) =
       vec_of_list (map rat_of_nat (map (\<lambda>s. card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}) signs))" 
      using construct_lhs_vector_cleaner_R assms
      by (metis (mono_tags, lifting) list.map_cong map_map o_apply of_int_of_nat_eq)
    then have "\<forall> n < (dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))). 
           (((solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) $ n \<noteq> 0) \<longrightarrow>
           (nth signs n) \<in> set (characterize_consistent_signs_at_roots p qs))"
    proof - 
      have h0: "\<forall> n < (dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))). 
           (((solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) $ n = 0) \<longrightarrow> 
           rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = (nth signs n)}) = 0)"
        by (simp add: \<open>solve_for_lhs_R p qs subsets (M_mat_R signs subsets) = vec_of_list (map rat_of_nat (map (\<lambda>s. card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}) signs))\<close> vec_of_list_index)
      have h1: "\<forall> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}) \<noteq> 0 \<longrightarrow> 
            (\<exists> x. poly p x = 0 \<and> consistent_sign_vec qs x = w))"
      proof clarsimp 
        fix w
        assume card_asm: "0 < card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}"
        show "\<exists>x. poly p x = 0 \<and> consistent_sign_vec qs x = w"
          by (metis (mono_tags, lifting) Collect_empty_eq card_asm card_eq_0_iff gr_implies_not0)
      qed
      have h2: "\<And> w. (rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}) \<noteq> 0 \<Longrightarrow>
           (List.member (characterize_consistent_signs_at_roots p qs) w))"
      proof clarsimp 
        fix w
        assume card_asm: " 0 < card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}"
        have h0: "\<exists>x. poly p x = 0 \<and> consistent_sign_vec qs x = w"
          using card_asm
          by (simp add: h1) 
        then show "List.member (characterize_consistent_signs_at_roots p qs) w" 
          unfolding characterize_consistent_signs_at_roots_def
          using in_set_member nonzero poly_roots_finite characterize_root_list_p_def
          by (smt (verit) characterize_consistent_signs_at_roots_def in_set_R mem_Collect_eq)
      qed
      then have h3: "\<forall> w. rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec qs x = w}) \<noteq> 0 \<longrightarrow> 
            w \<in> set (characterize_consistent_signs_at_roots p qs)"
        by (simp add: in_set_member)
      show ?thesis using h0 h3
        by (metis (no_types, lifting) \<open>solve_for_lhs_R p qs subsets (matrix_A_R signs subsets) = vec_of_list (map rat_of_nat (map (\<lambda>s. card {x. poly p x = 0 \<and> consistent_sign_vec qs x = s}) signs))\<close> dim_vec_of_list length_map nth_map vec_of_list_index)
    qed
    then have "set (take_indices signs
                 (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))) \<subseteq>
              set (characterize_consistent_signs_at_roots p qs)"
      using all_info
        reduction_signs_set_helper_lemma2[where A = "set (characterize_consistent_signs_at_roots p qs)", where B = "signs",
        where C = "(solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))"]
      using distinct_signs dim_hyp2 solve_for_lhs_R_def
      by (simp add: mat_inverse_same)
    then show ?thesis unfolding reduction_signs_R_def by auto
  qed
  have subset: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(reduction_signs_R p qs signs subsets (matrix_A_R signs subsets))" 
    using reduction_doesnt_break_things_signs_R[of p qs signs subsets] assms
    by blast 
  then show ?thesis using supset subset by auto 
qed


theorem reduce_system_sign_conditions_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "set (get_signs_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs))))) = set (characterize_consistent_signs_at_roots p qs)"
  unfolding get_signs_R_def
  using reduction_deletes_bad_sign_conds_R[of p qs signs subsets] apply (auto)
  apply (simp add: all_info distinct_signs match nonzero reduction_signs_def welldefined_signs1)
  using nonzero invertible_mat snd_conv
  apply (metis reduction_signs_R_def)
  by (metis all_info distinct_signs invertible_mat match nonzero reduction_signs_R_def snd_conv welldefined_signs1)

subsection "Showing matrix equation preserved when reducing"

lemma reduce_system_matrix_equation_preserved_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs: "well_def_signs (length qs) signs"
  assumes welldefined_subsets: "all_list_constr_R (subsets) (length qs)"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  assumes invertible_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "satisfy_equation_R p qs (get_subsets_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))
  (get_signs_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))"
proof - 
  have poly_type_hyp: "p \<noteq> 0" using nonzero by auto
  have distinct_signs_hyp: "distinct (snd (snd (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs))))))" 
  proof - 
    let ?sym = "(find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
    have h1: "\<forall> i < length (take_indices signs ?sym). \<forall>j < length(take_indices signs ?sym).
      i \<noteq> j \<longrightarrow> nth (take_indices signs ?sym) i \<noteq> nth (take_indices signs ?sym) j" 
      using distinct_signs unfolding take_indices_def 
    proof clarsimp 
      fix i
      fix j
      assume "distinct signs"
      assume "i < length
                (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
      assume "j < length
                (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
      assume neq_hyp: "i \<noteq> j"
      assume "signs ! (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets 
              (matrix_A_R signs subsets)) ! i) =
           signs ! (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets 
              (matrix_A_R signs subsets)) ! j)"
      have h1: "find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets 
              (matrix_A_R signs subsets)) ! i \<noteq> find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets 
              (matrix_A_R signs subsets)) ! j"
        unfolding find_nonzeros_from_input_vec_def using neq_hyp
        by (metis \<open>i < length (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))\<close> \<open>j < length (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))\<close> distinct_conv_nth distinct_filter distinct_upt find_nonzeros_from_input_vec_def) 
      then show "False" using distinct_signs
      proof -
        have f1: "\<forall>p ns n. ((n::nat) \<in> {n \<in> set ns. p n}) = (n \<in> set ns \<and> n \<in> Collect p)"
          by simp
        then have f2: "filter (\<lambda>n. solve_for_lhs_R p qs subsets (matrix_A_R signs subsets) $ n \<noteq> 0) [0..<dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))] ! i \<in> set [0..<length signs]"
          by (metis (full_types) \<open>i < length (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))\<close> construct_lhs_matches_solve_for_lhs_R find_nonzeros_from_input_vec_def invertible_mat match nth_mem set_filter size_of_lhs_R)
        have "filter (\<lambda>n. solve_for_lhs_R p qs subsets (matrix_A_R signs subsets) $ n \<noteq> 0) [0..<dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))] ! j \<in> set [0..<length signs]"
          using f1 by (metis (full_types) \<open>j < length (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))\<close> construct_lhs_matches_solve_for_lhs_R find_nonzeros_from_input_vec_def invertible_mat match nth_mem set_filter size_of_lhs_R)
        then show ?thesis
          using f2 by (metis \<open>signs ! (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) ! i) = signs ! (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) ! j)\<close> atLeastLessThan_iff distinct_conv_nth distinct_signs find_nonzeros_from_input_vec_def h1 set_upt)
      qed
    qed
    then have "distinct (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))"
      using distinct_conv_nth by blast 
    then show ?thesis
      using get_signs_R_def reduction_signs_R_def reduction_signs_is_get_signs_R by auto 
  qed
  have all_info_hyp: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(snd (snd (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs))))))"
    using reduce_system_sign_conditions_R assms unfolding get_signs_R_def by auto
  have welldefined_hyp: "all_list_constr_R (fst (snd (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))) (length qs)"
    using welldefined_subsets rows_to_keep_lem
    unfolding all_list_constr_R_def List.member_def list_constr_def list_all_def
    apply (auto simp add: Let_def take_indices_def take_cols_from_matrix_def)
    using nth_mem
    apply (smt (z3) mat_of_cols_carrier(2) rows_to_keep_lem)
    by (smt (z3) mat_of_cols_carrier(2) nth_mem rows_to_keep_lem)
  then show ?thesis using poly_type_hyp distinct_signs_hyp all_info_hyp  welldefined_hyp
    using matrix_equation_R unfolding get_subsets_R_def get_signs_R_def
    by blast 
qed

(* Show that we are tracking the correct matrix in the algorithm *)
subsection "Showing matrix preserved"
lemma reduce_system_matrix_signs_helper_aux_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length signs"
  assumes nonzero: "p \<noteq> 0"
  shows "alt_matrix_A_R (take_indices signs S) subsets = take_cols_from_matrix (alt_matrix_A_R signs subsets) S"
proof - 
  have h0a: "dim_col (take_cols_from_matrix (alt_matrix_A_R signs subsets) S) = length (take_indices signs S)" 
    unfolding take_cols_from_matrix_def apply (auto) unfolding take_indices_def by auto
  have h0: "\<forall>i < length (take_indices signs S). (col (alt_matrix_A_R (take_indices signs S) subsets ) i = 
col (take_cols_from_matrix (alt_matrix_A_R signs subsets) S) i)" 
  proof clarsimp
    fix i
    assume asm: "i < length (take_indices signs S)"
    have i_lt: "i < length (map ((!) (cols (alt_matrix_A_R signs subsets))) S)" using asm
      apply (auto) unfolding take_indices_def by auto
    have h0: " vec (length subsets) (\<lambda>j. z_R (subsets ! j) (map ((!) signs) S ! i)) = 
      vec (length subsets) (\<lambda>j. z_R (subsets ! j) (signs ! (S ! i)))" using nth_map
      by (metis \<open>i < length (take_indices signs S)\<close> length_map take_indices_def) 
    have dim: "(map ((!) (cols (alt_matrix_A_R signs subsets))) S) ! i \<in> carrier_vec (dim_row (alt_matrix_A_R signs subsets))"
    proof - 
      have "dim_col (alt_matrix_A_R signs subsets) = length (signs)"
        by (simp add: alt_matrix_A_R_def) 
      have well_d: "S ! i < length (signs)" using well_def_h
        using i_lt in_set_member by fastforce 
      have 
        map_eq: "(map ((!) (cols (alt_matrix_A_R signs subsets))) S) ! i  = nth (cols (alt_matrix_A_R signs subsets))  (S ! i)"
        using i_lt by auto
      have "nth (cols (alt_matrix_A_R signs subsets))  (S ! i) \<in> carrier_vec (dim_row (alt_matrix_A_R signs subsets))"
        using col_dim unfolding cols_def using nth_map well_d
        by (simp add: \<open>dim_col (alt_matrix_A_R signs subsets) = length signs\<close>) 
      then show ?thesis using map_eq  by auto
    qed
    have h1: "col (take_cols_from_matrix (alt_matrix_A_R signs subsets) S) i = 
      col (mat_of_cols (dim_row (alt_matrix_A_R signs subsets)) (map ((!) (cols (alt_matrix_A_R signs subsets))) S)) i "
      by (simp add: take_cols_from_matrix_def take_indices_def)
    have h2: "col (mat_of_cols (dim_row (alt_matrix_A_R signs subsets)) (map ((!) (cols (alt_matrix_A_R signs subsets))) S)) i 
      = nth (map ((!) (cols (alt_matrix_A_R signs subsets))) S) i " 
      using dim i_lt asm col_mat_of_cols[where j = "i", where n = "(dim_row (alt_matrix_A_R signs subsets))",
          where vs = "(map ((!) (cols (alt_matrix_A_R signs subsets))) S)"]
      by blast 
    have h3: "col (take_cols_from_matrix (alt_matrix_A_R signs subsets) S) i = (col (alt_matrix_A_R signs subsets) (S !i))"
      using h1 h2 apply (auto)
      by (metis alt_matrix_char_R asm cols_nth dim_col_mat(1) in_set_member length_map mat_of_rows_list_def matrix_A_R_def nth_map nth_mem take_indices_def well_def_h)
    have "vec (length subsets) (\<lambda>j. z_R (subsets ! j) (signs ! (S ! i))) = (col (alt_matrix_A_R signs subsets) (S !i))"
      by (metis asm in_set_member length_map nth_mem signs_are_cols_R take_indices_def well_def_h)
    then have "vec (length subsets) (\<lambda>j. z_R (subsets ! j) (take_indices signs S ! i)) =
      col (take_cols_from_matrix (alt_matrix_A_R signs subsets) S) i "
      using h0 h3
      by (simp add: take_indices_def) 
    then show "col (alt_matrix_A_R (take_indices signs S) subsets) i =
         col (take_cols_from_matrix (alt_matrix_A_R signs subsets) S) i "
      using asm signs_are_cols_R[where signs = "(take_indices signs S)", where subsets = "subsets"] 
      by auto
  qed
  then show ?thesis   unfolding alt_matrix_A_R_def take_cols_from_matrix_def apply (auto) 
    using h0a mat_col_eqI
    by (metis alt_matrix_A_R_def dim_col_mat(1) dim_row_mat(1) h0 mat_of_cols_def take_cols_from_matrix_def) 
qed


lemma reduce_system_matrix_signs_helper_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length signs"
  assumes nonzero: "p \<noteq> 0"
  shows "matrix_A_R (take_indices signs S) subsets = take_cols_from_matrix (matrix_A_R signs subsets) S"
  using reduce_system_matrix_signs_helper_aux_R alt_matrix_char_R assms by auto

lemma reduce_system_matrix_subsets_helper_aux_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list* nat list) list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes inv: "length subsets \<ge> length signs"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length subsets"
  assumes nonzero: "p \<noteq> 0"
  shows "alt_matrix_A_R signs (take_indices subsets S) = take_rows_from_matrix (alt_matrix_A_R signs subsets) S"
proof - 
  have h0a: "dim_row (take_rows_from_matrix (alt_matrix_A_R signs subsets) S) = length (take_indices subsets S)" 
    unfolding take_rows_from_matrix_def apply (auto) unfolding take_indices_def by auto
  have h0: "\<forall>i < length (take_indices subsets S). (row (alt_matrix_A_R signs (take_indices subsets S) ) i = 
row (take_rows_from_matrix (alt_matrix_A_R signs subsets) S) i)" 
  proof clarsimp
    fix i
    assume asm: "i < length (take_indices subsets S)"
    have i_lt: "i < length (map ((!) (rows (alt_matrix_A_R signs subsets))) S)" using asm
      apply (auto) unfolding take_indices_def by auto
    have h0: "row (take_rows_from_matrix (alt_matrix_A_R signs subsets) S) i =
    row (mat_of_rows (dim_col (alt_matrix_A_R signs subsets)) (map ((!) (rows (alt_matrix_A_R signs subsets))) S)) i "
      unfolding take_rows_from_matrix_def take_indices_def by auto
    have dim: "(map ((!) (rows (alt_matrix_A_R signs subsets))) S) ! i \<in> carrier_vec (dim_col (alt_matrix_A_R signs subsets))"
    proof - 
      have "dim_col (alt_matrix_A_R signs subsets) = length (signs)"
        by (simp add: alt_matrix_A_R_def) 
      then have lenh: "dim_col (alt_matrix_A_R signs subsets) \<le> length (subsets)"
        using assms
        by auto 
      have well_d: "S ! i < length (subsets)" using well_def_h
        using i_lt in_set_member by fastforce 
      have 
        map_eq: "(map ((!) (rows (alt_matrix_A_R signs subsets))) S) ! i  = nth (rows (alt_matrix_A_R signs subsets))  (S ! i)"
        using i_lt by auto
      have "nth (rows (alt_matrix_A_R signs subsets))  (S ! i) \<in> carrier_vec (dim_col (alt_matrix_A_R signs subsets))"
        using col_dim unfolding rows_def using nth_map well_d
        using lenh
        by (simp add: alt_matrix_A_R_def) 
      then show ?thesis using map_eq unfolding alt_matrix_A_R_def by auto
    qed
    have h1: " row (mat_of_rows (dim_col (alt_matrix_A_R signs subsets)) (map ((!) (rows (alt_matrix_A_R signs subsets))) S)) i
      = (row  (alt_matrix_A_R signs subsets) (S ! i)) "
      using dim i_lt mat_of_rows_row[where i = "i", where n = "(dim_col (alt_matrix_A_R signs subsets))",
          where vs = "(map ((!) (rows (alt_matrix_A_R signs subsets))) S)"]
      using alt_matrix_char_R in_set_member nth_mem well_def_h
      by fastforce
    have "row (alt_matrix_A_R signs (take_indices subsets S) ) i = (row  (alt_matrix_A_R signs subsets) (S ! i))"
      using subsets_are_rows_R
    proof -
      have f1: "i < length S"
        by (metis (no_types) asm length_map take_indices_def)
      then have "List.member S (S ! i)"
        by (meson in_set_member nth_mem)
      then show ?thesis
        using f1 
        by (simp add: \<open>\<And>subsets signs. \<forall>i<length subsets. row (alt_matrix_A_R signs subsets) i = vec (length signs) (\<lambda>j. z_R (subsets ! i) (signs ! j))\<close> take_indices_def well_def_h)
    qed 
    then show "(row (alt_matrix_A_R signs (take_indices subsets S) ) i = 
      row (take_rows_from_matrix (alt_matrix_A_R signs subsets) S) i)" 
      using h0 h1 unfolding take_indices_def by auto
  qed
  then show ?thesis  unfolding alt_matrix_A_R_def take_rows_from_matrix_def apply (auto) 
    using eq_rowI
    by (metis alt_matrix_A_R_def dim_col_mat(1) dim_row_mat(1) h0 h0a mat_of_rows_def take_rows_from_matrix_def) 
qed


lemma reduce_system_matrix_subsets_helper_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  fixes S:: "nat list"
  assumes nonzero: "p \<noteq> 0"
  assumes inv: "length subsets \<ge> length signs"
  assumes well_def_h: "\<forall>x. List.member S x \<longrightarrow> x < length subsets"
  shows "matrix_A_R signs (take_indices subsets S) = take_rows_from_matrix (matrix_A_R signs subsets) S"
  using assms reduce_system_matrix_subsets_helper_aux_R alt_matrix_char_R
  by auto

lemma reduce_system_matrix_match_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  assumes inv: "invertible_mat (matrix_A_R signs subsets)"
  shows "matrix_A_R (get_signs_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))
  (get_subsets_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs))))) = 
  (get_matrix_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))"
proof -
  let ?A = "(matrix_A_R signs subsets)"
  let ?lhs_vec = "(solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))"
  let ?red_mtx = "(take_rows_from_matrix (reduce_mat_cols (matrix_A_R signs subsets) ?lhs_vec) (rows_to_keep (reduce_mat_cols (matrix_A_R signs subsets) ?lhs_vec)))"
  have h1: "matrix_A_R (get_signs_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))
  (get_subsets_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))
   = matrix_A_R (reduction_signs_R p qs signs subsets (matrix_A_R signs subsets)) (reduction_subsets_R p qs signs subsets (matrix_A_R signs subsets))"
    using reduction_signs_is_get_signs_R reduction_subsets_is_get_subsets_R by auto
  have h1_var: "matrix_A_R (get_signs_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))
  (get_subsets_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))
   = matrix_A_R (take_indices signs (find_nonzeros_from_input_vec ?lhs_vec)) (take_indices subsets (rows_to_keep (reduce_mat_cols ?A ?lhs_vec)))"
    using h1 reduction_signs_R_def reduction_subsets_R_def  by auto 
  have h2: "?red_mtx = (take_rows_from_matrix (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec)) (rows_to_keep (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec))))"
    by simp
  have h30: "(construct_lhs_vector_R p qs signs) = ?lhs_vec"
    using assms construct_lhs_matches_solve_for_lhs_R
    by simp 
  have h3a: "\<forall>x. List.member (find_nonzeros_from_input_vec ?lhs_vec) x \<longrightarrow>x < length (signs)" 
    using h30 size_of_lhs_R[of p qs signs]  
    unfolding find_nonzeros_from_input_vec_def apply (auto)
    using in_set_member by force
  have h3b_a: "\<forall>x. List.member (find_nonzeros_from_input_vec ?lhs_vec) x \<longrightarrow>x < length (subsets)" 
    using assms h30 size_of_lhs_R same_size_R unfolding find_nonzeros_from_input_vec_def apply (auto)
    by (simp add: find_nonzeros_from_input_vec_def h3a)
  have h3ba: "length
     (filter (\<lambda>i. solve_for_lhs_R p qs subsets (matrix_A_R signs subsets) $ i \<noteq> 0)
       [0..<length subsets])
    \<le> length subsets" using length_filter_le[where P = "(\<lambda>i. solve_for_lhs_R p qs subsets (matrix_A_R signs subsets) $ i \<noteq> 0)",
    where xs = "[0..<length subsets]"] length_upto by auto
  have " length subsets = dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))"
    using h30 inv size_of_lhs_R same_size_R[of signs subsets] apply (auto)
    by metis 
  then have "length
     (filter (\<lambda>i. solve_for_lhs_R p qs subsets (matrix_A_R signs subsets) $ i \<noteq> 0)
       [0..<dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))])
    \<le> length subsets" using h3ba
    by auto
  then have h3b: "length subsets \<ge> length (take_indices signs (find_nonzeros_from_input_vec ?lhs_vec))" 
    unfolding take_indices_def find_nonzeros_from_input_vec_def by auto
  have h3c: "\<forall>x. List.member (rows_to_keep (reduce_mat_cols ?A ?lhs_vec)) x \<longrightarrow> x < length (subsets)"
  proof clarsimp
    fix x
    assume x_mem: "List.member (rows_to_keep
            (take_cols_from_matrix (matrix_A_R signs subsets)
              (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))) x"
    obtain nn :: "rat list list \<Rightarrow> nat list \<Rightarrow> nat" where
      "\<forall>x2 x3. (\<exists>v4. v4 \<in> set x3 \<and> \<not> v4 < length x2) = (nn x2 x3 \<in> set x3 \<and> \<not> nn x2 x3 < length x2)"
      by moura
    then have f4: "nn signs (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) \<in> set (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) \<and> \<not> nn signs (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) < length signs \<or> matrix_A_R (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))) subsets = take_cols_from_matrix (matrix_A_R signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
      using nonzero
      using h3a reduce_system_matrix_signs_helper_R by auto 
    then have "matrix_A_R (take_indices signs (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))) subsets = take_cols_from_matrix (matrix_A_R signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) \<and> x \<in> set (map snd (pivot_positions (gauss_jordan_single (take_cols_from_matrix (matrix_A_R signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))\<^sup>T)))"
      using f4
      by (metis h3a in_set_member rows_to_keep_def x_mem)
    thus "x < length (subsets)" using x_mem unfolding rows_to_keep_def
      by (metis dim_row_matrix_A_R rows_to_keep_def rows_to_keep_lem)
  qed
  have h3: "matrix_A_R (take_indices signs (find_nonzeros_from_input_vec ?lhs_vec)) (take_indices subsets (rows_to_keep (reduce_mat_cols ?A ?lhs_vec))) = 
    (take_rows_from_matrix (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec)) (rows_to_keep (take_cols_from_matrix ?A (find_nonzeros_from_input_vec ?lhs_vec))))" 
    using inv h3a h3b h3c reduce_system_matrix_subsets_helper_R reduce_system_matrix_signs_helper_R
      assms 
    by auto
  show ?thesis using h1 h2 h3 
    by (metis fst_conv get_matrix_R_def h1_var reduce_system_R.simps reduction_step_R.simps)
qed

subsection "Showing invertibility preserved when reducing"

(* gauss_jordan_single_rank is critically helpful in this subsection *)
thm conjugatable_vec_space.gauss_jordan_single_rank

thm vec_space.full_rank_lin_indpt

(* Overall:
  Start with a matrix equation.
  Input a matrix, subsets, and signs.
  Drop columns of the matrix based on the 0's on the LHS---so extract a list of 0's. Reduce signs accordingly.
  Then find a list of rows to delete based on using rank (use the transpose result, pivot positions!),
   and delete those rows.  Reduce subsets accordingly.
  End with a reduced system! *)
lemma well_def_find_zeros_from_lhs_vec_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A_R signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  shows "(\<And>j. j \<in> set (find_nonzeros_from_input_vec
                    (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) \<Longrightarrow>
          j < length (cols (matrix_A_R signs subsets)))"
proof - 
  fix i
  fix j
  assume j_in: " j \<in> set (find_nonzeros_from_input_vec
                      (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) "
  let ?og_mat = "(matrix_A_R signs subsets)"
  let ?lhs = "(solve_for_lhs_R p qs subsets ?og_mat)"
  let ?new_mat = "(take_rows_from_matrix (reduce_mat_cols ?og_mat ?lhs) (rows_to_keep (reduce_mat_cols ?og_mat ?lhs)))"
  have "square_mat (matrix_A_R signs subsets)" using inv
    using invertible_mat_def by blast
  then have mat_size: "?og_mat \<in> carrier_mat (length signs) (length signs)" 
    using size_of_mat
    by auto 
  have "dim_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)) = (length signs)"
    using size_of_lhs_R construct_lhs_matches_solve_for_lhs_R assms
    by (metis (full_types))
  then have h: "j < (length signs)"
    using j_in unfolding find_nonzeros_from_input_vec_def
    by simp 
  then show "j <  length (cols (matrix_A_R signs subsets))" 
    using mat_size by auto
qed


lemma take_cols_subsets_og_cols_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A_R signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  shows "set (take_indices (cols (matrix_A_R signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))
    \<subseteq> set (cols (matrix_A_R signs subsets))"
proof -
  have well_def: "(\<And>j. j \<in> set (find_nonzeros_from_input_vec
                    (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) \<Longrightarrow>
          j < length (cols (matrix_A_R signs subsets)))"
    using assms well_def_find_zeros_from_lhs_vec_R by auto
  have "\<forall>x. x \<in> set (take_indices (cols (matrix_A_R signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))) 
    \<longrightarrow> x \<in>  set (cols (matrix_A_R signs subsets))" 
  proof clarsimp 
    fix x
    let ?og_list = "(cols (matrix_A_R signs subsets))"
    let ?ind_list = "(find_nonzeros_from_input_vec
                     (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
    assume x_in: "x \<in> set (take_indices ?og_list ?ind_list)"
    show "x \<in> set (cols (matrix_A_R signs subsets))" 
      using x_in unfolding take_indices_def using in_set_member apply (auto)
      using in_set_conv_nth well_def by fastforce
  qed
  then show ?thesis
    by blast 
qed


lemma reduction_doesnt_break_things_invertibility_step1_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A_R signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  shows "vec_space.rank (length signs) (reduce_mat_cols (matrix_A_R signs subsets) (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) =
    (length (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))"
proof - 
  let ?og_mat = "(matrix_A_R signs subsets)"
  let ?lhs = "(solve_for_lhs_R p qs subsets ?og_mat)"
  let ?new_mat = "(take_rows_from_matrix (reduce_mat_cols ?og_mat ?lhs) (rows_to_keep (reduce_mat_cols ?og_mat ?lhs)))"
  have "square_mat (matrix_A_R signs subsets)" using inv
    using invertible_mat_def by blast
  then have mat_size: "?og_mat \<in> carrier_mat (length signs) (length signs)" 
    using size_of_mat
    by auto 
  then have mat_size_alt: "?og_mat \<in> carrier_mat (length subsets) (length subsets)" 
    using size_of_mat same_size assms 
    by auto 
  have det_h: "det ?og_mat \<noteq> 0"
    using invertible_det[where A = "matrix_A_R signs subsets"] mat_size
    using inv by blast
  then have rank_h: "vec_space.rank (length signs) ?og_mat = (length signs)" 
    using vec_space.det_rank_iff  mat_size
    by auto
  then have dist_cols: "distinct (cols ?og_mat)" using mat_size vec_space.non_distinct_low_rank[where A = ?og_mat, where n = "length signs"]
    by auto
  have well_def: "(\<And>j. j \<in> set (find_nonzeros_from_input_vec
                    (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) \<Longrightarrow>
          j < length (cols (matrix_A_R signs subsets)))"
    using assms well_def_find_zeros_from_lhs_vec_R by auto
  have dist1: "distinct
     (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
    unfolding find_nonzeros_from_input_vec_def by auto
  have clear: "set (take_indices (cols (matrix_A_R signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))
    \<subseteq> set (cols (matrix_A_R signs subsets))"
    using assms take_cols_subsets_og_cols_R by auto
  then have "distinct (take_indices (cols (matrix_A_R signs subsets))
          (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))"
    unfolding take_indices_def
    using dist1 dist_cols well_def conjugatable_vec_space.distinct_map_nth[where ls = "cols (matrix_A_R signs subsets)", where inds = "(find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"]
    by auto
  then have unfold_thesis: "vec_space.rank (length signs) (mat_of_cols (dim_row ?og_mat) (take_indices (cols ?og_mat) (find_nonzeros_from_input_vec ?lhs)))
= (length (find_nonzeros_from_input_vec ?lhs))" 
    using clear inv conjugatable_vec_space.rank_invertible_subset_cols[where A= "matrix_A_R signs subsets", where B = "(take_indices (cols (matrix_A_R signs subsets))
         (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))"]
    by (simp add: len_eq mat_size take_indices_def)
  then show ?thesis apply (simp) unfolding take_cols_from_matrix_def by auto
qed


lemma reduction_doesnt_break_things_invertibility_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes len_eq: "length subsets = length signs"
  assumes inv: "invertible_mat (matrix_A_R signs subsets)"
  assumes nonzero: "p \<noteq> 0"
  assumes welldefined_signs1: "well_def_signs (length qs) signs"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(signs)"
  assumes match: "satisfy_equation_R p qs subsets signs"
  shows "invertible_mat (get_matrix_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))"
proof - 
  let ?og_mat = "(matrix_A_R signs subsets)"
  let ?lhs = "(solve_for_lhs_R p qs subsets ?og_mat)"
  let ?step1_mat = "(reduce_mat_cols ?og_mat ?lhs)"
  let ?new_mat = "take_rows_from_matrix ?step1_mat (rows_to_keep ?step1_mat)"
  let ?ind_list = "(find_nonzeros_from_input_vec  ?lhs)"
  have "square_mat (matrix_A_R signs subsets)" using inv
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
    by (metis carrier_matD(1) carrier_matD(2) construct_lhs_matches_solve_for_lhs_R diff_zero find_nonzeros_from_input_vec_def inv length_filter_le length_upt match size_of_lhs_R)
  then have gt_eq_assm: "dim_col ?step1_mat\<^sup>T  \<ge> dim_row  ?step1_mat\<^sup>T"
    by simp 
  have det_h: "det ?og_mat \<noteq> 0"
    using invertible_det[where A = "matrix_A_R signs subsets"] og_mat_size
    using inv by blast
  then have rank_h: "vec_space.rank (length signs) ?og_mat = (length signs)" 
    using vec_space.det_rank_iff  og_mat_size
    by auto
  have rank_drop_cols: "vec_space.rank (length signs) ?step1_mat = (dim_col ?step1_mat)"
    using assms reduction_doesnt_break_things_invertibility_step1_R step1_mat_size 
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
    by (smt (verit, ccfv_threshold) carrier_matD(2) index_transpose_mat(2) mat_of_cols_carrier(2) reduce_mat_cols.simps rows_to_keep_def step1_mat_size take_cols_from_matrix_def transpose_rank)
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
  have mat_match: "matrix_A_R (get_signs_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))
  (get_subsets_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs))))) = 
  (get_matrix_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))"
    using reduce_system_matrix_match_R[of p qs signs subsets]  assms
    by blast 
  have f2: "length (get_subsets_R (take_rows_from_matrix (mat_of_cols (dim_row (matrix_A_R signs subsets)) (map ((!) (cols (matrix_A_R signs subsets))) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))) (rows_to_keep (mat_of_cols (dim_row (matrix_A_R signs subsets)) (map ((!) (cols (matrix_A_R signs subsets))) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))))), map ((!) subsets) (rows_to_keep (mat_of_cols (dim_row (matrix_A_R signs subsets)) (map ((!) (cols (matrix_A_R signs subsets))) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))))), map ((!) signs) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))) = length (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"

    by (metis (no_types) \<open>dim_col (mat_of_cols (dim_row (matrix_A_R signs subsets)) (take_indices (cols (matrix_A_R signs subsets)) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))) = length (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))\<close> \<open>length (rows_to_keep (reduce_mat_cols (matrix_A_R signs subsets) (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))) = dim_col (reduce_mat_cols (matrix_A_R signs subsets) (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))\<close> length_map reduce_mat_cols.simps reduce_system_R.simps reduction_step_R.simps reduction_subsets_R_def reduction_subsets_is_get_subsets_R take_cols_from_matrix_def take_indices_def)
  have f3: "\<forall>p ps rss nss m. map ((!) rss) (find_nonzeros_from_input_vec (solve_for_lhs_R p ps nss m)) = get_signs_R (reduce_system_R p (ps, m, nss, rss))"
    by (metis (no_types) reduction_signs_R_def reduction_signs_is_get_signs_R take_indices_def)
  have square_final_mat: "square_mat (get_matrix_R (reduce_system_R p (qs, ((matrix_A_R signs subsets), (subsets, signs)))))"
    using mat_match assms size_of_mat_R same_size_R
    apply (auto) using f2 f3
    by (metis (no_types, lifting) Matrix.transpose_transpose fst_conv get_matrix_R_def index_transpose_mat(2) len_match length_map mat_of_cols_carrier(2) mat_of_cols_carrier(3) reduce_mat_cols.simps take_cols_from_matrix_def take_indices_def take_rows_and_take_cols) 
  have rank_match: "vec_space.rank (dim_row ?new_mat) ?new_mat = dim_row ?new_mat"
    using len_match rank_new_mat
    by (simp add: take_cols_from_matrix_def take_indices_def take_rows_and_take_cols) 
  have "invertible_mat ?new_mat"
    using invertible_det og_mat_size
    using vec_space.det_rank_iff square_final_mat
    by (metis dim_col_matrix_A_R dim_row_matrix_A_R fst_conv get_matrix_R_def mat_match rank_match reduce_system_R.simps reduction_step_R.simps size_of_mat_R square_mat.elims(2))
  then show ?thesis apply (simp)
    by (metis fst_conv get_matrix_R_def)
qed

subsection "Well def signs preserved when reducing"

lemma reduction_doesnt_break_length_signs_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes length_init : "\<forall> x\<in> set(signs). length x = length qs"
  assumes sat_eq: "satisfy_equation_R p qs subsets signs"
  assumes inv_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "\<forall>x \<in> set(reduction_signs_R p qs signs subsets (matrix_A_R signs subsets)). 
    length x = length qs"
  unfolding reduction_signs_def using take_indices_lem
  by (smt (verit) atLeastLessThan_iff construct_lhs_matches_solve_for_lhs_R filter_is_subset find_nonzeros_from_input_vec_def in_set_conv_nth in_set_member inv_mat length_init reduction_signs_R_def sat_eq set_upt size_of_lhs_R subset_code(1))

subsection "Distinct signs preserved when reducing"

lemma reduction_signs_are_distinct_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes sat_eq: "satisfy_equation_R p qs subsets signs"
  assumes inv_mat: "invertible_mat (matrix_A_R signs subsets)"
  assumes distinct_init: "distinct signs"
  shows "distinct (reduction_signs_R p qs signs subsets (matrix_A_R signs subsets))"
proof -
  have solve_construct: "construct_lhs_vector_R p qs signs =
  solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)"
    using construct_lhs_matches_solve_for_lhs_R assms
    by simp
  have h1: "distinct (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
    unfolding find_nonzeros_from_input_vec_def 
    using distinct_filter
    using distinct_upt by blast 
  have h2: "(\<And>j. j \<in> set (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))) \<Longrightarrow>
          j < length signs)"
  proof - 
    fix j
    assume "j \<in> set (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"
    show "j < length signs" using solve_construct size_of_lhs_R
      by (metis \<open>j \<in> set (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))\<close> atLeastLessThan_iff filter_is_subset find_nonzeros_from_input_vec_def set_upt subset_iff)
  qed
  then show ?thesis unfolding reduction_signs_R_def unfolding take_indices_def
    using distinct_init h1 h2 conjugatable_vec_space.distinct_map_nth[where ls = "signs", where inds = "(find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))"]
    by blast
qed

subsection "Well def subsets preserved when reducing"

lemma reduction_doesnt_break_subsets_R:  
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list* nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes length_init : "all_list_constr_R subsets (length qs)"
  assumes sat_eq: "satisfy_equation_R p qs subsets signs"
  assumes inv_mat: "invertible_mat (matrix_A_R signs subsets)"
  shows "all_list_constr_R (reduction_subsets_R p qs signs subsets (matrix_A_R signs subsets)) (length qs)"
  unfolding all_list_constr_R_def 
proof clarsimp
  fix a b
  assume in_red_subsets: "List.member (reduction_subsets_R p qs signs subsets (matrix_A_R signs subsets)) (a, b) "
  have solve_construct: "construct_lhs_vector_R p qs signs =
  solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)"
    using construct_lhs_matches_solve_for_lhs_R assms
    by simp
  have rows_to_keep_hyp: "\<forall>y. y \<in> set (rows_to_keep (reduce_mat_cols (matrix_A_R signs subsets) (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))) \<longrightarrow> 
      y < length subsets" 
  proof clarsimp 
    fix y
    assume in_set: "y \<in> set (rows_to_keep
                   (take_cols_from_matrix (matrix_A_R signs subsets) (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))))"
    have in_set_2: "y \<in> set (rows_to_keep
                   (take_cols_from_matrix (matrix_A_R signs subsets) (find_nonzeros_from_input_vec (construct_lhs_vector_R p qs signs))))"
      using in_set solve_construct by simp
    let ?lhs_vec = "(solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))"
    have h30: "(construct_lhs_vector_R p qs signs) = ?lhs_vec"
      using assms construct_lhs_matches_solve_for_lhs_R
      by simp 
    have h3a: "\<forall>x. List.member (find_nonzeros_from_input_vec ?lhs_vec) x \<longrightarrow>x < length (signs)" 
      using h30 size_of_lhs_R unfolding find_nonzeros_from_input_vec_def 
      using atLeastLessThan_iff filter_is_subset member_def set_upt subset_eq apply (auto)
      by (smt (verit, best) atLeastLessThan_iff in_set_member mem_Collect_eq set_filter set_upt)
    have h3c: "\<forall>x. List.member (rows_to_keep (reduce_mat_cols (matrix_A_R signs subsets) (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets)))) x \<longrightarrow> x < length (subsets)"
    proof clarsimp
      fix x
      assume x_mem: "List.member (rows_to_keep
            (take_cols_from_matrix (matrix_A_R signs subsets)
              (find_nonzeros_from_input_vec (solve_for_lhs_R p qs subsets (matrix_A_R signs subsets))))) x"
      show "x < length (subsets)" using x_mem unfolding rows_to_keep_def using pivot_positions
        using  dim_row_matrix_A h3a in_set_member nonzero reduce_system_matrix_signs_helper_R rows_to_keep_def rows_to_keep_lem
        apply (auto)
        by (smt (verit, best) List.member_def dim_row_matrix_A_R rows_to_keep_def rows_to_keep_lem) 
    qed
    then show "y < length subsets" using in_set_member apply (auto)
      using in_set_2 solve_construct by fastforce  
  qed
  show "list_constr a (length qs) \<and> list_constr b (length qs)" using in_red_subsets  unfolding  reduction_subsets_def 
    using take_indices_lem_R[of _ subsets]  rows_to_keep_hyp 
    using all_list_constr_R_def in_set_conv_nth in_set_member length_init
    by (metis fst_conv reduction_subsets_R_def snd_conv)
qed

section "Overall Lemmas"
lemma combining_to_smash_R:  "combine_systems_R p (qs1, m1, (sub1, sgn1)) (qs2, m2, (sub2, sgn2))
 =  smash_systems_R p qs1 qs2 sub1 sub2 sgn1 sgn2 m1 m2"
  by simp

lemma getter_functions_R: "calculate_data_R p qs = (get_matrix_R (calculate_data_R p qs), (get_subsets_R (calculate_data_R p qs), get_signs_R (calculate_data_R p qs))) "
  unfolding get_matrix_R_def get_subsets_R_def get_signs_R_def by auto

subsection "Key properties preserved"

subsubsection "Properties preserved when combining and reducing systems"
lemma combining_sys_satisfies_properties_helper_R:
  fixes p:: "real poly"
  fixes qs1 :: "real poly list"
  fixes qs2 :: "real poly list"
  fixes subsets1 subsets2 :: "(nat list * nat list) list"
  fixes signs1 signs2 :: "rat list list" 
  fixes matrix1 matrix2:: "rat mat"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes nontriv2: "length qs2 > 0"
  assumes satisfies_properties_sys1: "satisfies_properties_R p qs1 subsets1 signs1 matrix1"
  assumes satisfies_properties_sys2: "satisfies_properties_R p qs2 subsets2 signs2 matrix2"
  shows  "satisfies_properties_R p (qs1@qs2) (get_subsets_R (snd ((combine_systems_R p (qs1,(matrix1, (subsets1, signs1))) (qs2,(matrix2, (subsets2, signs2))))))) 
  (get_signs_R (snd ((combine_systems_R p (qs1,(matrix1, (subsets1, signs1))) (qs2,(matrix2, (subsets2, signs2))))))) 
  (get_matrix_R (snd ((combine_systems_R p (qs1,(matrix1, (subsets1, signs1))) (qs2,(matrix2, (subsets2, signs2)))))))"
proof -     
  let ?subsets = "(get_subsets_R (snd (combine_systems_R p (qs1, matrix1, subsets1, signs1)
              (qs2, matrix2, subsets2, signs2))))"
  let ?signs = "(get_signs_R (snd (combine_systems_R p (qs1, matrix1, subsets1, signs1) (qs2, matrix2, subsets2, signs2))))"
  let ?matrix = "(get_matrix_R (snd (combine_systems_R p (qs1, matrix1, subsets1, signs1) (qs2, matrix2, subsets2, signs2))))"
  have h1: "all_list_constr_R ?subsets (length (qs1 @ qs2))"
    using well_def_step_R[of subsets1 qs1 subsets2 qs2] assms
    by (simp add: nontriv2 get_subsets_R_def satisfies_properties_R_def smash_systems_R_def) 
  have h2: "well_def_signs (length (qs1 @ qs2)) ?signs"
    using well_def_signs_step[of qs1 qs2 signs1 signs2]
    using get_signs_R_def nontriv1 nontriv2 satisfies_properties_R_def satisfies_properties_sys1 satisfies_properties_sys2 smash_systems_R_def by auto 
  have h3: "distinct ?signs" 
    using distinct_step[of _ signs1 _ signs2] assms
    using combine_systems.simps get_signs_R_def satisfies_properties_R_def smash_systems_R_def snd_conv by auto
  have h4: "satisfy_equation_R p (qs1 @ qs2) ?subsets ?signs" 
    using assms inductive_step_R[of p qs1 qs2 signs1 signs2 subsets1 subsets2]
    using get_signs_R_def get_subsets_R_def satisfies_properties_R_def smash_systems_R_def
    by auto  
  have h5: " invertible_mat ?matrix"
    using assms inductive_step_R[of p qs1 qs2 signs1 signs2 subsets1 subsets2]
    by (metis combining_to_smash_R fst_conv get_matrix_R_def kronecker_invertible satisfies_properties_R_def smash_systems_R_def snd_conv)
  have h6: "?matrix = matrix_A_R ?signs ?subsets" 
    unfolding get_matrix_R_def combine_systems_R.simps smash_systems_R_def get_signs_R_def get_subsets_R_def
    apply simp
    apply (subst matrix_construction_is_kronecker_product_R[of subsets1 _ signs1 signs2 subsets2])
    apply (metis Ball_set all_list_constr_R_def in_set_member list_constr_def satisfies_properties_R_def satisfies_properties_sys1)
    using satisfies_properties_R_def satisfies_properties_sys1 well_def_signs_def apply blast
    using satisfies_properties_R_def satisfies_properties_sys1 satisfies_properties_sys2 by auto
  have h7: "set (characterize_consistent_signs_at_roots p (qs1 @ qs2))
    \<subseteq> set (?signs)"
    using subset_step_R[of p qs1 signs1 qs2  signs2] assms
    by (simp add: nonzero get_signs_R_def satisfies_properties_R_def smash_systems_R_def) 
  then show ?thesis unfolding satisfies_properties_R_def using h1 h2 h3 h4 h5 h6 h7 by blast
qed

lemma combining_sys_satisfies_properties_R:
  fixes p:: "real poly"
  fixes qs1 :: "real poly list"
  fixes qs2 :: "real poly list"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes nontriv2: "length qs2 > 0"
  assumes satisfies_properties_sys1: "satisfies_properties_R p qs1 (get_subsets_R (calculate_data_R p qs1)) (get_signs_R (calculate_data_R p qs1)) (get_matrix_R (calculate_data_R p qs1))"
  assumes satisfies_properties_sys2: "satisfies_properties_R p qs2 (get_subsets_R (calculate_data_R p qs2)) (get_signs_R (calculate_data_R p qs2)) (get_matrix_R (calculate_data_R p qs2))"
  shows  "satisfies_properties_R p (qs1@qs2) (get_subsets_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2))))) 
  (get_signs_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2))))) 
  (get_matrix_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2)))))"
  using combining_sys_satisfies_properties_helper_R[of p qs1 qs2]
  by (metis getter_functions_R nontriv1 nontriv2 nonzero satisfies_properties_sys1 satisfies_properties_sys2) 

lemma reducing_sys_satisfies_properties_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  fixes matrix:: "rat mat"
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv: "length qs > 0"
  assumes satisfies_properties_sys: "satisfies_properties_R p qs subsets signs matrix"
  shows  "satisfies_properties_R p qs (get_subsets_R (reduce_system_R p (qs,matrix,subsets,signs)))
  (get_signs_R (reduce_system_R p (qs,matrix,subsets,signs)))
  (get_matrix_R (reduce_system_R p (qs,matrix,subsets,signs)))"
proof -
  have h1: " all_list_constr_R (get_subsets_R (reduce_system_R p (qs, matrix, subsets, signs))) (length qs)"
    using reduction_doesnt_break_subsets_R assms reduction_subsets_is_get_subsets_R satisfies_properties_R_def satisfies_properties_sys by auto
  have h2: "well_def_signs (length qs) (get_signs_R (reduce_system_R p (qs, matrix, subsets, signs)))"
    using reduction_doesnt_break_length_signs_R[of signs qs p subsets] assms reduction_signs_is_get_signs_R satisfies_properties_R_def well_def_signs_def by auto
  have h3: "distinct (get_signs_R (reduce_system_R p (qs, matrix, subsets, signs)))"
    using reduction_signs_are_distinct_R[of p qs subsets signs] assms reduction_signs_is_get_signs_R satisfies_properties_R_def by auto 
  have h4: "satisfy_equation_R p qs (get_subsets_R (reduce_system_R p (qs, matrix, subsets, signs)))
     (get_signs_R (reduce_system_R p (qs, matrix, subsets, signs)))"
    using reduce_system_matrix_equation_preserved_R[of p qs signs subsets] assms satisfies_properties_R_def by auto
  have h5: "invertible_mat (get_matrix_R (reduce_system_R p (qs, matrix, subsets, signs)))"
    using reduction_doesnt_break_things_invertibility_R assms same_size_R satisfies_properties_R_def by auto 
  have h6: "get_matrix_R (reduce_system_R p (qs, matrix, subsets, signs)) =
    matrix_A_R (get_signs_R (reduce_system_R p (qs, matrix, subsets, signs)))
     (get_subsets_R (reduce_system_R p (qs, matrix, subsets, signs)))"
    using reduce_system_matrix_match_R[of p qs signs subsets] assms satisfies_properties_R_def by auto
  have h7: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set (get_signs_R (reduce_system_R p (qs, matrix, subsets, signs)))"
    using reduction_doesnt_break_things_signs_R[of p qs signs subsets] assms reduction_signs_is_get_signs_R satisfies_properties_R_def by auto
  then show ?thesis unfolding satisfies_properties_R_def using h1 h2 h3 h4 h5 h6 h7
    by blast
qed

subsubsection "For length 1 qs"

lemma  length_1_calculate_data_satisfies_properties_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes len1: "length qs = 1"
  shows "satisfies_properties_R p qs (get_subsets_R (calculate_data_R p qs)) (get_signs_R (calculate_data_R p qs)) (get_matrix_R (calculate_data_R p qs))"
proof - 
  have h1: "all_list_constr_R  [([], []),([0], []),([], [0])] (length qs)"
    using len1 unfolding all_list_constr_R_def list_constr_def apply (auto)
    apply (smt (verit, best) Ball_set in_set_member member_rec(1) member_rec(2) prod.inject)
    by (smt (verit, ccfv_threshold) Ball_set in_set_member member_rec(1) member_rec(2) prod.inject)
  have h2: "well_def_signs (length qs) [[1],[-1]]"
    unfolding well_def_signs_def using len1 in_set_member 
    by auto
  have h3: "distinct ([[1],[0],[-1]]::rat list list)" 
    unfolding distinct_def using in_set_member by auto
  have h4: "satisfy_equation_R p qs [([], []),([0], []),([], [0])] [[1],[0],[-1]]"
    using assms base_case_satisfy_equation_alt_R[of qs p] by auto
  have h6: "(mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]]::rat mat) = (matrix_A_R ([[1],[0],[-1]]) ([([], []),([0], []),([], [0])]) :: rat mat)" 
    using mat_base_case_R by auto
  then have h5: "invertible_mat (mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]]::rat mat)" 
    using base_case_invertible_mat_R
    by simp
  have h7:  "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set ([[1],[0],[-1]])"
    using assms base_case_sgas_alt_R[of qs p]
    by simp  
  have base_case_hyp: "satisfies_properties_R p qs [([], []),([0], []),([], [0])] [[1],[0],[-1]] (mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]]::rat mat)"
    using h1 h2 h3 h4 h5 h6 h7
    using satisfies_properties_R_def apply (auto)
    by (simp add: well_def_signs_def) 
  then have key_hyp: "satisfies_properties_R p qs (get_subsets_R (reduce_system_R p (qs,base_case_info_R))) (get_signs_R (reduce_system_R p (qs,base_case_info_R))) (get_matrix_R (reduce_system_R p (qs,base_case_info_R)))"
    using reducing_sys_satisfies_properties_R
    by (metis base_case_info_R_def len1 nonzero nonzero zero_less_one_class.zero_less_one) 
  show ?thesis
    by (simp add: key_hyp len1) 
qed

subsubsection "For arbitrary qs"

lemma  calculate_data_satisfies_properties_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  shows "(p \<noteq> 0 \<and> (length qs > 0))
    \<longrightarrow> satisfies_properties_R p qs (get_subsets_R (calculate_data_R p qs)) (get_signs_R (calculate_data_R p qs)) (get_matrix_R (calculate_data_R p qs))"
proof (induction "length qs" arbitrary: qs rule: less_induct)
  case less
  have len1_h: "length qs = 1 \<longrightarrow> ( p \<noteq> 0 \<and> (length qs > 0)) \<longrightarrow> satisfies_properties_R p qs (get_subsets_R (calculate_data_R p qs)) (get_signs_R (calculate_data_R p qs)) (get_matrix_R (calculate_data_R p qs))"
    using  length_1_calculate_data_satisfies_properties_R
    by blast
  let ?len = "length qs"
  let ?q1 = "take (?len div 2) qs"
  let ?left = "calculate_data_R p ?q1"
  let ?q2 = "drop (?len div 2) qs"
  let ?right = "calculate_data_R p ?q2"
  let ?comb = "combine_systems_R p (?q1,?left) (?q2,?right)"
  let ?red =  "reduce_system_R p ?comb"
  have h_q1_len: "length qs > 1 \<longrightarrow> (length ?q1 > 0)" by auto 
  have h_q2_len: "length qs > 1 \<longrightarrow> (length ?q2 > 0)" by auto
  have q1_sat_props: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0)) \<longrightarrow> satisfies_properties_R p ?q1 (get_subsets_R (calculate_data_R p ?q1)) (get_signs_R (calculate_data_R p ?q1)) (get_matrix_R (calculate_data_R p ?q1))"
    using less.hyps[of ?q1] h_q1_len
    by (metis div_le_dividend div_less_dividend length_take min.absorb2 one_less_numeral_iff semiring_norm(76)) 
  have q2_help: "length qs > 1 \<longrightarrow> length (drop (length qs div 2) qs) < length qs"
    using h_q1_len by auto  
  then have q2_sat_props: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0)) \<longrightarrow> satisfies_properties_R p ?q2 (get_subsets_R (calculate_data_R p ?q2)) (get_signs_R (calculate_data_R p ?q2)) (get_matrix_R (calculate_data_R p ?q2))"
    using less.hyps[of ?q2] h_q2_len
    by blast
  have put_tog: "?q1@?q2 = qs"
    using append_take_drop_id by blast 
  then have comb_sat_props: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0)) \<longrightarrow> (satisfies_properties_R p (qs) (get_subsets_R (snd ((combine_systems_R p (?q1,calculate_data_R p ?q1) (?q2,calculate_data_R p ?q2))))) 
  (get_signs_R (snd ((combine_systems_R p (?q1,calculate_data_R p ?q1) (?q2,calculate_data_R p ?q2))))) 
  (get_matrix_R (snd ((combine_systems_R p (?q1,calculate_data_R p ?q1) (?q2,calculate_data_R p ?q2))))))"
    using q1_sat_props q2_sat_props  combining_sys_satisfies_properties_R
    using h_q1_len h_q2_len  put_tog
    by metis
  then have comb_sat: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0)) \<longrightarrow> 
      (satisfies_properties_R p (qs) (get_subsets_R (snd ?comb)) (get_signs_R (snd ?comb)) (get_matrix_R (snd ?comb)))"
    by blast
  have red_char: "?red = (reduce_system_R p (qs,(get_matrix_R (snd ?comb)),(get_subsets_R (snd ?comb)),(get_signs_R (snd ?comb))))"
    using getter_functions
    by (smt (z3) combine_systems_R.simps find_consistent_signs_at_roots_R_def find_consistent_signs_at_roots_thm_R fst_conv get_matrix_R_def get_signs_R_def get_subsets_R_def prod.collapse put_tog smash_systems_R_def)
  then have "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0))  \<longrightarrow> (satisfies_properties_R p qs (get_subsets_R ?red) (get_signs_R ?red) (get_matrix_R ?red))"
    using reducing_sys_satisfies_properties_R comb_sat
    by presburger 
  then have len_gt1: "length qs > 1 \<longrightarrow> (p \<noteq> 0 \<and> (length qs > 0) ) \<longrightarrow> satisfies_properties_R p qs (get_subsets_R (calculate_data_R p qs)) (get_signs_R (calculate_data_R p qs)) (get_matrix_R (calculate_data_R p qs))"
    apply (auto)
    by (smt (z3) div_le_dividend min.absorb2)
  then show ?case using len1_h len_gt1
    by (metis One_nat_def Suc_lessI) 
qed


subsection "Some key results on consistent sign assignments"

lemma find_consistent_signs_at_roots_len1_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes len1: "length qs = 1"
  shows "set (find_consistent_signs_at_roots_R p qs) = set (characterize_consistent_signs_at_roots p qs)"
proof - 
  let ?signs = "[[1],[0],[-1]]::rat list list"
  let ?subsets = "[([], []),([0], []),([], [0])]::(nat list*nat list) list"
  let ?mat = "(mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]])"
  have mat_help: "matrix_A_R ?signs ?subsets = (mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]])"
    using mat_base_case_R by auto
  have well_def_signs: "well_def_signs (length qs) ?signs" unfolding well_def_signs_def 
    using len1 by auto
  have distinct_signs: "distinct ?signs"
    unfolding distinct_def by auto
  have ex_q: "\<exists>(q::real poly). qs = [q]" 
    using len1    
    using length_Suc_conv[of qs 0] by auto
  then have all_info: "set (characterize_consistent_signs_at_roots p qs) \<subseteq> set(?signs)"
    using assms base_case_sgas_R by auto
  have match: "satisfy_equation_R p qs ?subsets ?signs"
    using ex_q base_case_satisfy_equation_R nonzero
    by auto
  have invertible_mat: "invertible_mat (matrix_A_R ?signs ?subsets)"
    using inverse_mat_base_case_R inverse_mat_base_case_2_R unfolding invertible_mat_def using mat_base_case_R
    by auto
  have h: "set (get_signs_R (reduce_system_R p (qs, ((matrix_A_R ?signs ?subsets), (?subsets, ?signs))))) = 
    set (characterize_consistent_signs_at_roots p qs)" 
    using nonzero nonzero well_def_signs distinct_signs all_info match invertible_mat
      reduce_system_sign_conditions_R[where p = "p", where qs = "qs", where signs = ?signs, where subsets = ?subsets]
    by blast 
  then have  "set (snd (snd (reduce_system_R p (qs, (?mat, (?subsets, ?signs)))))) = 
    set (characterize_consistent_signs_at_roots p qs)"
    unfolding get_signs_R_def using mat_help by auto
  then have "set (snd (snd (reduce_system_R p (qs, base_case_info_R)))) = set (characterize_consistent_signs_at_roots p qs)"
    unfolding base_case_info_R_def
    by auto
  then show ?thesis using len1 
    by (simp add: find_consistent_signs_at_roots_thm_R)
qed

lemma smaller_sys_are_good_R:
  fixes p:: "real poly"
  fixes qs1 :: "real poly list"
  fixes qs2 :: "real poly list"
  fixes subsets :: "(nat list*nat list) list"
  fixes signs :: "rat list list" 
  assumes nonzero: "p \<noteq> 0"
  assumes nontriv1: "length qs1 > 0"
  assumes nontriv2: "length qs2 > 0"
  assumes "set(find_consistent_signs_at_roots_R p qs1) = set(characterize_consistent_signs_at_roots p qs1)"
  assumes "set(find_consistent_signs_at_roots_R p qs2) = set(characterize_consistent_signs_at_roots p qs2)"
  shows "set(snd(snd(reduce_system_R p (combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2)))))
    = set(characterize_consistent_signs_at_roots p (qs1@qs2))"
proof - 
  let ?signs = "(get_signs_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2))))) "
  let ?subsets = "(get_subsets_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2))))) "
  have h0: "satisfies_properties_R p (qs1@qs2) ?subsets ?signs
    (get_matrix_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2)))))"
    using calculate_data_satisfies_properties_R combining_sys_satisfies_properties_R
    using nontriv1 nontriv2 nonzero nonzero
    by simp
  then have h1: "set(characterize_consistent_signs_at_roots p (qs1@qs2)) \<subseteq> set ?signs"
    unfolding satisfies_properties_R_def
    by linarith 
  have h2: "well_def_signs (length (qs1@qs2)) ?signs"
    using calculate_data_satisfies_properties_R
    using h0 satisfies_properties_R_def by blast 
  have h3: "distinct ?signs" 
    using calculate_data_satisfies_properties_R
    using h0 satisfies_properties_R_def by blast 
  have h4: "satisfy_equation_R p (qs1@qs2) ?subsets ?signs"
    using calculate_data_satisfies_properties_R
    using h0 satisfies_properties_R_def by blast 
  have h5: "invertible_mat (matrix_A_R ?signs ?subsets) "
    using calculate_data_satisfies_properties_R 
    using h0 satisfies_properties_R_def
    by auto
  have h: "set (take_indices ?signs 
            (find_nonzeros_from_input_vec (solve_for_lhs_R p (qs1@qs2) ?subsets  (matrix_A_R ?signs ?subsets))))
        =  set(characterize_consistent_signs_at_roots p (qs1@qs2))" 
    using h1 h2 h3 h4 h5 reduction_deletes_bad_sign_conds_R
    using nonzero reduction_signs_R_def by auto
  then have h: "set (characterize_consistent_signs_at_roots p (qs1@qs2)) =
    set (reduction_signs_R p (qs1@qs2) ?signs ?subsets  (matrix_A_R ?signs ?subsets ))" 
    unfolding reduction_signs_R_def get_signs_R_def
    by blast  
  have help_h: "reduction_signs_R p (qs1@qs2) ?signs ?subsets  (matrix_A_R ?signs ?subsets) 
      = (take_indices ?signs (find_nonzeros_from_input_vec (solve_for_lhs_R p (qs1@qs2) ?subsets  (matrix_A_R?signs ?subsets))))"
    unfolding reduction_signs_R_def by auto
  have clear_signs: "(signs_smash (get_signs_R (calculate_data_R p qs1)) (get_signs_R (calculate_data_R p qs2))) = (get_signs_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2)))))"
    using combining_to_smash get_signs_R_def getter_functions_R smash_systems_R_def snd_conv
  proof -
    have "combine_systems_R p (qs1, calculate_data_R p qs1) (qs2, calculate_data_R p qs2) = (qs1 @ qs2, kronecker_product (get_matrix_R (calculate_data_R p qs1)) (get_matrix_R (calculate_data_R p qs2)), subsets_smash_R (length qs1) (get_subsets_R (calculate_data_R p qs1)) (get_subsets_R (calculate_data_R p qs2)), signs_smash (snd (snd (calculate_data_R p qs1))) (snd (snd (calculate_data_R p qs2))))"
      by (metis (no_types) combine_systems_R.simps get_signs_R_def getter_functions_R smash_systems_R_def)
    then show ?thesis
      by (simp add: get_signs_R_def)
  qed
  have clear_subsets: "(subsets_smash_R (length qs1) (get_subsets_R(calculate_data_R p qs1)) (get_subsets_R (calculate_data_R p qs2))) = (get_subsets_R (snd ((combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2)))))"  
    using Pair_inject combining_to_smash get_subsets_R_def prod.collapse smash_systems_R_def
    by (smt (z3) combine_systems_R.simps)
  have "well_def_signs (length qs1) (get_signs_R (calculate_data_R p qs1))" 
    using calculate_data_satisfies_properties_R
    using nontriv1 nonzero nonzero satisfies_properties_R_def
    by auto 
  then have well_def_signs1: "(\<And>j. j \<in> set (get_signs_R (calculate_data_R p qs1)) \<Longrightarrow> length j = (length qs1))"
    using well_def_signs_def by blast 
  have "all_list_constr_R (get_subsets_R(calculate_data_R p qs1))  (length qs1) "
    using calculate_data_satisfies_properties_R
    using nontriv1 nonzero nonzero satisfies_properties_R_def
    by auto 
  then have well_def_subsets1: "(\<And>l i. l \<in> set (get_subsets_R(calculate_data_R p qs1)) \<Longrightarrow> (i \<in> set (fst l) \<longrightarrow> i < (length qs1)) \<and> (i \<in> set (snd l) \<longrightarrow> i < (length qs1)))"
    unfolding all_list_constr_R_def list_constr_def 
    using in_set_member
    by (metis in_set_conv_nth list_all_length) 
  have extra_matrix_same: "matrix_A_R (signs_smash (get_signs_R (calculate_data_R p qs1)) (get_signs_R (calculate_data_R p qs2)))
         (subsets_smash_R (length qs1) (get_subsets_R(calculate_data_R p qs1)) (get_subsets_R (calculate_data_R p qs2))) 
        = kronecker_product (get_matrix_R (calculate_data_R p qs1)) (get_matrix_R (calculate_data_R p qs2))"
    using  well_def_signs1 well_def_subsets1
    using matrix_construction_is_kronecker_product_R
    using calculate_data_satisfies_properties_R nontriv1 nontriv2 nonzero  nonzero satisfies_properties_R_def 
    by fastforce
  then have matrix_same: "matrix_A_R ?signs ?subsets = kronecker_product (get_matrix_R (calculate_data_R p qs1)) (get_matrix_R (calculate_data_R p qs2))"
    using clear_signs clear_subsets
    by simp
  have comb_sys_h: "snd(snd(reduce_system_R p (combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2)))) =
      snd(snd(reduce_system_R p (qs1@qs2, (matrix_A_R ?signs ?subsets, (?subsets, ?signs)))))"
    unfolding get_signs_R_def get_subsets_R_def using matrix_same
    by (metis (full_types) clear_signs clear_subsets combine_systems_R.simps get_signs_R_def get_subsets_R_def getter_functions_R smash_systems_R_def)
  then have extra_h: " snd(snd(reduce_system_R p (qs1@qs2, (matrix_A_R ?signs ?subsets, (?subsets, ?signs))))) = 
      snd(snd(reduction_step_R (matrix_A_R ?signs ?subsets) ?signs ?subsets (solve_for_lhs_R p (qs1@qs2) ?subsets (matrix_A_R ?signs ?subsets)))) "
    by simp
  then have same_h: "set(snd(snd(reduce_system_R p (combine_systems_R p (qs1,calculate_data_R p qs1) (qs2,calculate_data_R p qs2))))) 
      = set (reduction_signs_R p (qs1@qs2) ?signs ?subsets  (matrix_A_R ?signs ?subsets ))"
    using comb_sys_h unfolding reduction_signs_R_def
    by (metis get_signs_R_def help_h reduction_signs_is_get_signs_R) 
  then show ?thesis using h
    by blast 
qed

lemma find_consistent_signs_at_roots_1_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  shows "(p \<noteq> 0 \<and> length qs > 0) \<longrightarrow> 
    set(find_consistent_signs_at_roots_R p qs) = set(characterize_consistent_signs_at_roots p qs)"
proof (induction "length qs" arbitrary: qs rule: less_induct)
  case less 
  then show ?case
  proof clarsimp
    assume ind_hyp: "(\<And>qsa.
        length qsa < length qs \<Longrightarrow> qsa \<noteq> [] \<longrightarrow>
        set (find_consistent_signs_at_roots_R p qsa) =
        set (characterize_consistent_signs_at_roots p qsa))"
    assume nonzero: "p \<noteq> 0"  
    assume nontriv: "qs \<noteq> []"
    let ?len = "length qs"
    let ?q1 = "take ((?len) div 2) qs"
    let ?left = "calculate_data_R p ?q1"
    let ?q2 = "drop ((?len) div 2) qs"
    let ?right = "calculate_data_R p ?q2"
    have nontriv_q1: "length qs>1 \<longrightarrow> length ?q1 > 0" 
      by auto
    have qs_more_q1: "length qs>1 \<longrightarrow> length qs > length ?q1" 
      by auto
    have nontriv_q2: "length qs>1 \<longrightarrow>length ?q2 > 0" 
      by auto
    have qs_more_q2: "length qs>1 \<longrightarrow> length qs > length ?q2" 
      by auto
    have key_h: "set (snd (snd (if ?len \<le> Suc 0 then reduce_system_R p (qs, base_case_info_R)
                        else   Let (combine_systems_R p (?q1, ?left) (?q2, ?right))
                                  (reduce_system_R p)))) =
       set (characterize_consistent_signs_at_roots p qs)" 
    proof - 
      have h_len1 : "?len = 1 \<longrightarrow> set (snd (snd (if ?len \<le> Suc 0 then reduce_system_R p (qs, base_case_info_R)
                        else   Let (combine_systems_R p (?q1, ?left) (?q2, ?right))
                                  (reduce_system_R p)))) =
       set (characterize_consistent_signs_at_roots p qs)" 
        using find_consistent_signs_at_roots_len1_R[of p qs] nonzero nontriv
        by (simp add: find_consistent_signs_at_roots_thm_R)
      have h_len_gt1 : "?len > 1 \<longrightarrow> set (snd (snd (if ?len \<le> Suc 0 then reduce_system_R p (qs, base_case_info_R)
                        else   Let (combine_systems_R p (?q1, ?left) (?q2, ?right))
                                  (reduce_system_R p)))) =
       set (characterize_consistent_signs_at_roots p qs)" 
      proof - 
        have h_imp_a: "?len > 1 \<longrightarrow> set (snd (snd (reduce_system_R p (combine_systems_R p (?q1, ?left) (?q2, ?right))))) =
              set (characterize_consistent_signs_at_roots p qs)"
        proof - 
          have h1: "?len > 1 \<longrightarrow> set(snd(snd(?left))) = set (characterize_consistent_signs_at_roots p ?q1)"
            using nontriv_q1 ind_hyp[of ?q1] qs_more_q1             
            by (metis find_consistent_signs_at_roots_thm_R less_numeral_extra(3) list.size(3))
          have h2: "?len > 1 \<longrightarrow> set(snd(snd(?right))) = set (characterize_consistent_signs_at_roots p ?q2)"
            using nontriv_q2 ind_hyp[of ?q2] qs_more_q2
            by (metis (full_types) find_consistent_signs_at_roots_thm_R list.size(3) not_less_zero)
          show ?thesis using nonzero nontriv_q1 nontriv_q2 h1 h2 smaller_sys_are_good_R             
            by (metis append_take_drop_id find_consistent_signs_at_roots_thm_R)
        qed
        then have h_imp: "?len > 1 \<longrightarrow> set (snd (snd (Let (combine_systems_R p (?q1, ?left) (?q2, ?right))
                                  (reduce_system_R p)))) =
       set (characterize_consistent_signs_at_roots p qs)"
          by auto
        then show ?thesis by auto 
      qed
      show ?thesis using h_len1 h_len_gt1
        by (meson \<open>qs \<noteq> []\<close> length_0_conv less_one nat_neq_iff) 
    qed
    then show "set (find_consistent_signs_at_roots_R p qs) = set (characterize_consistent_signs_at_roots p qs)"
      using One_nat_def calculate_data.simps find_consistent_signs_at_roots_thm length_0_conv nontriv
      by (smt (z3) calculate_data_R.simps find_consistent_signs_at_roots_thm_R)
  qed
qed

lemma find_consistent_signs_at_roots_0_R:
  fixes p:: "real poly"
  assumes "p \<noteq> 0"
  shows "set(find_consistent_signs_at_roots_R p []) =
         set(characterize_consistent_signs_at_roots p [])"
proof -
  obtain a b c where abc: "reduce_system_R p ([1], base_case_info_R) = (a,b,c)"
    using prod_cases3 by blast 
  have "find_consistent_signs_at_roots_R p [1] = c" using abc
    by (simp add: find_consistent_signs_at_roots_thm_R) 
  have *: "set (find_consistent_signs_at_roots_R p [1]) = set (characterize_consistent_signs_at_roots p [1])"
    apply (subst find_consistent_signs_at_roots_1_R)
    using assms by auto
  have "set(characterize_consistent_signs_at_roots p []) = drop 1 ` set(characterize_consistent_signs_at_roots p [1])"
    unfolding characterize_consistent_signs_at_roots_def consistent_sign_vec_def signs_at_def squash_def apply simp
    using drop0 drop_Suc_Cons image_cong image_image 
  proof -
    have "(\<lambda>r. []) ` set (characterize_root_list_p p) = (\<lambda>r. drop (Suc 0) [1::rat]) ` set (characterize_root_list_p p)"
      by force
    then show "(\<lambda>r. []) ` set (characterize_root_list_p p) = drop (Suc 0) ` (\<lambda>r. [1::rat]) ` set (characterize_root_list_p p)"
      by blast
  qed 
  thus ?thesis using abc *
    apply (auto) apply (simp add: find_consistent_signs_at_roots_thm_R)
    by (simp add: find_consistent_signs_at_roots_thm_R) 
qed

lemma find_consistent_signs_at_roots_R:
  fixes p:: "real poly"
  fixes qs :: "real poly list"
  assumes "p \<noteq> 0"
  shows "set(find_consistent_signs_at_roots_R p qs) = set(characterize_consistent_signs_at_roots p qs)"
  by (metis assms find_consistent_signs_at_roots_0_R find_consistent_signs_at_roots_1_R length_greater_0_conv)

end