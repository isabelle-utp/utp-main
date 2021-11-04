theory Matrix_Equation_Construction

imports "BKR_Algorithm"
begin

section "Results with Sturm's Theorem"

lemma relprime:
  fixes q::"real poly"
  assumes "coprime p q"
  assumes "p \<noteq> 0"
  assumes "q \<noteq> 0"
  shows "changes_R_smods p (pderiv p) = card {x. poly p x = 0 \<and> poly q x > 0} + card {x. poly p x = 0 \<and> poly q x < 0}"
proof -
  have 1: "{x. poly p x = 0 \<and> poly q x = 0} = {}"
    using assms(1) coprime_poly_0 by auto
  have 2: "changes_R_smods p (pderiv p) = int (card {x . poly p x = 0})" using sturm_R by auto
  have 3: "{x. poly p x = 0 \<and> poly q x > 0} \<inter> {x. poly p x = 0 \<and> poly q x < 0} = {}" by auto
  have "{x . poly p x = 0} =  {x. poly p x = 0 \<and> poly q x > 0} \<union>{x. poly p x = 0 \<and> poly q x < 0} \<union> {x. poly p x = 0 \<and> poly q x = 0}" by force
  then have "{x . poly p x = 0} = {x. poly p x = 0 \<and> poly q x > 0} \<union>{x. poly p x = 0 \<and> poly q x < 0}" using 1 by auto
  then have "(card {x . poly p x = 0}) = (card ({x. poly p x = 0 \<and> poly q x > 0} \<union>{x. poly p x = 0 \<and> poly q x < 0}))" by presburger
  then have 4: "(card {x . poly p x = 0}) =  card {x. poly p x = 0 \<and> poly q x > 0} + card {x. poly p x = 0 \<and> poly q x < 0}" using 3 by (simp add: card_Un_disjoint assms(2) poly_roots_finite)
  show ?thesis  by (simp add: "2" "4")
qed

(* This is the same proof as card_eq_sum *)
lemma card_eq_const_sum: 
  fixes k:: real
  assumes "finite A"
  shows "k*card A = sum (\<lambda>x. k) A"
proof -
  have "plus \<circ> (\<lambda>_. Suc 0) = (\<lambda>_. Suc)"
    by (simp add: fun_eq_iff)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) = Finite_Set.fold (\<lambda>_. Suc)"
    by (rule arg_cong)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) 0 A = Finite_Set.fold (\<lambda>_. Suc) 0 A"
    by (blast intro: fun_cong)
  then show ?thesis
    by (simp add: card.eq_fold sum.eq_fold)
qed

lemma restate_tarski:
  fixes q::"real poly"
  assumes "coprime p q"
  assumes "p \<noteq> 0"       
  assumes "q \<noteq> 0"
  shows "changes_R_smods p ((pderiv p) * q) = card {x. poly p x = 0 \<and> poly q x > 0} -  int(card {x. poly p x = 0 \<and> poly q x < 0})"
proof -
  have 3: "taq {x. poly p x=0} q \<equiv> \<Sum>y\<in>{x. poly p x=0}. sign (poly q y)" by (simp add: taq_def)
  have 4: "{x. poly p x=0} =  {x. poly p x = 0 \<and> poly q x > 0} \<union> {x. poly p x = 0 \<and> poly q x < 0} \<union> {x. poly p x = 0 \<and> poly q x = 0}" by force
  then have 5: "{x. poly p x=0} =  {x. poly p x = 0 \<and> poly q x > 0} \<union> {x. poly p x = 0 \<and> poly q x < 0}" using assms(1) coprime_poly_0 by auto
  then have 6: "\<Sum>y\<in>{x. poly p x=0}. sign (poly q y) \<equiv> \<Sum>y\<in>{x. poly p x = 0 \<and> poly q x > 0} \<union> {x. poly p x = 0 \<and> poly q x < 0}. sign (poly q y)" by presburger
  then have 12: "taq {x. poly p x=0} q \<equiv> \<Sum>y\<in>{x. poly p x = 0 \<and> poly q x > 0} \<union> {x. poly p x = 0 \<and> poly q x < 0}. sign (poly q y)" using 3 by linarith
  have 7: "{x. poly p x = 0 \<and> poly q x > 0} \<inter> {x. poly p x = 0 \<and> poly q x < 0} = {}" by auto
  then have 8: "\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x > 0} \<union> {x. poly p x = 0 \<and> poly q x < 0}. sign (poly q y) \<equiv> (\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x > 0}.sign (poly q y)) + (\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x < 0}.sign(poly q y))" by (simp add: assms(2) poly_roots_finite sum.union_disjoint)
  then have 13: "taq {x. poly p x=0} q \<equiv> (\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x > 0}.sign (poly q y)) + (\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x < 0}.sign(poly q y))" using 12 by linarith
  then have 9: "taq {x. poly p x = 0} q \<equiv> (\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x > 0}.1) + (\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x < 0}.(-1))" by simp
  have 10: "(\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x > 0}.1) =  card {x. poly p x = 0 \<and> poly q x > 0}" using card_eq_sum by auto
  have 11: " (\<Sum>y\<in>{x. poly p x = 0 \<and> poly q x < 0}.(-1)) = -1*card {x. poly p x = 0 \<and> poly q x < 0}" using card_eq_const_sum by simp
  have 14: "taq {x. poly p x = 0} q \<equiv> card {x. poly p x = 0 \<and> poly q x > 0} + -1*card {x. poly p x = 0 \<and> poly q x < 0}" using 9 10 11 by simp
  have 1: "changes_R_smods p (pderiv p * q) = taq {x. poly p x=0} q" using sturm_tarski_R by simp
  then have 15: "changes_R_smods p (pderiv p * q) = card {x. poly p x = 0 \<and> poly q x > 0} + (-1*card {x. poly p x = 0 \<and> poly q x < 0})" using 14 by linarith
  have 16: "(-1*card {x. poly p x = 0 \<and> poly q x < 0}) = - card {x. poly p x = 0 \<and> poly q x < 0}" by auto
  then show ?thesis using 15 by linarith
qed

lemma restate_tarski2:
  fixes q::"real poly"
  assumes "p \<noteq> 0"
  shows "changes_R_smods p ((pderiv p) * q) =
        int(card {x. poly p x = 0 \<and> poly q x > 0}) -
        int(card {x. poly p x = 0 \<and> poly q x < 0})"
  unfolding sturm_tarski_R[symmetric] taq_def
proof -
  let ?all = "{x. poly p x=0}"
  let ?lt = "{x. poly p x=0 \<and> poly q x < 0}"
  let ?gt = "{x. poly p x=0 \<and> poly q x > 0}"
  let ?eq = "{x. poly p x=0 \<and> poly q x = 0}"
  have eq: "?all = ?lt \<union> ?gt \<union> ?eq" by force
  from poly_roots_finite[OF assms] have fin: "finite ?all" .
  show  "(\<Sum>x | poly p x = 0. sign (poly q x)) = int (card ?gt) - int (card ?lt)"
    unfolding eq
    apply (subst sum_Un)
      apply (auto simp add:fin)
    apply (subst sum_Un)
    by (auto simp add:fin)
qed

lemma coprime_set_prod:
  fixes I:: "real poly set"
  shows "finite I \<Longrightarrow> ((\<forall> q \<in> I. (coprime p q)) \<longrightarrow> (coprime p (\<Prod> I)))"
proof (induct rule: finite_induct)
  case empty
  then show ?case
    by simp 
next
  case (insert x F)
  then show ?case using coprime_mult_right_iff
    by simp
qed

lemma finite_nonzero_set_prod:
  fixes I:: "real poly set"
  shows  nonzero_hyp: "finite I \<Longrightarrow> ((\<forall> q \<in> I. q \<noteq> 0) \<longrightarrow> \<Prod> I \<noteq> 0)"
proof (induct rule: finite_induct)
  case empty
  then show ?case
    by simp 
next
  case (insert x F)
  have h: "\<Prod> (insert x F) = x * (\<Prod> F)"
    by (simp add: insert.hyps(1) insert.hyps(2)) 
  have h_xin: "x \<in> insert x F"
    by simp 
  have hq: "(\<forall> q \<in> (insert x F). q \<noteq> 0) \<longrightarrow> x \<noteq> 0" using h_xin
    by blast 
  show ?case using h hq
    using insert.hyps(3) by auto
qed

section "Setting up the construction: Definitions"

definition characterize_root_list_p:: "real poly \<Rightarrow> real list"
  where "characterize_root_list_p p \<equiv> sorted_list_of_set({x. poly p x = 0}::real set)"

(************** Renegar's N(I); towards defining the RHS of the matrix equation **************)

lemma construct_NofI_prop:
  fixes p:: "real poly"
  fixes I:: "real poly list"
  assumes nonzero: "p\<noteq>0"
  shows "construct_NofI p I =
    rat_of_int (int (card {x. poly p x = 0 \<and> poly (prod_list I) x > 0}) - 
    int (card {x. poly p x = 0 \<and> poly (prod_list I) x < 0}))"
  unfolding construct_NofI_def
  using assms restate_tarski2 nonzero rsquarefree_def
  by (simp add: rsquarefree_def)

definition construct_s_vector:: "real poly \<Rightarrow> real poly list list \<Rightarrow> rat vec"
  where "construct_s_vector p Is = vec_of_list (map (\<lambda> I.(construct_NofI p I)) Is)"

(* Consistent sign assignments *)
definition squash::"'a::linordered_field \<Rightarrow> rat"
  where "squash x = (if x > 0 then 1
                    else if x < 0 then -1
                    else 0)"

definition signs_at::"real poly list \<Rightarrow> real \<Rightarrow> rat list"
  where "signs_at qs x \<equiv>
    map (squash \<circ> (\<lambda>q. poly q x)) qs"

definition characterize_consistent_signs_at_roots:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list"
  where "characterize_consistent_signs_at_roots p qs =
  (remdups (map (signs_at qs) (characterize_root_list_p p)))"

(* An alternate version designed to be used when every polynomial in qs is relatively prime to p*)
definition consistent_sign_vec_copr::"real poly list \<Rightarrow> real \<Rightarrow> rat list"
  where "consistent_sign_vec_copr qs x \<equiv>
    map (\<lambda> q. if (poly q x > 0) then (1::rat) else (-1::rat)) qs"

definition characterize_consistent_signs_at_roots_copr:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list"
  where "characterize_consistent_signs_at_roots_copr p qss =
  (remdups (map (consistent_sign_vec_copr qss) (characterize_root_list_p p)))"

lemma csa_list_copr_rel:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  assumes nonzero: "p\<noteq>0"
  assumes pairwise_rel_prime: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  shows "characterize_consistent_signs_at_roots p qs = characterize_consistent_signs_at_roots_copr p qs"
proof - 
  have "\<forall>q \<in> set(qs). \<forall> x \<in> set (characterize_root_list_p p).  poly q x \<noteq> 0"
    using pairwise_rel_prime
    using coprime_poly_0 in_set_member nonzero poly_roots_finite characterize_root_list_p_def by fastforce 
  then have h: "\<forall>q \<in> set(qs). \<forall> x \<in> set (characterize_root_list_p p). squash (poly q x) = (if (poly q x > 0) then (1::rat) else (-1::rat))"
    by (simp add: squash_def)
  have "map (\<lambda>r. map (\<lambda>p. if 0 < poly p r then 1 else - 1) qs) (characterize_root_list_p p) = map (\<lambda>r. map (squash \<circ> (\<lambda>p. poly p r)) qs) (characterize_root_list_p p)"
    by (simp add: h)
  thus ?thesis unfolding characterize_consistent_signs_at_roots_def characterize_consistent_signs_at_roots_copr_def
      signs_at_def consistent_sign_vec_copr_def
    by presburger
qed

(************** Towards defining Renegar's polynomial function and the LHS of the matrix equation **************)

definition list_constr:: "nat list \<Rightarrow> nat \<Rightarrow> bool"
  where "list_constr L n \<equiv> list_all (\<lambda>x. x < n) L"

definition all_list_constr:: "nat list list \<Rightarrow> nat \<Rightarrow> bool"
  where "all_list_constr L n \<equiv> (\<forall>x. List.member L x \<longrightarrow> list_constr x n)"

(* The first input is the subset; the second input is the consistent sign assignment.
  We want to map over the first list and pull out all of the elements in the second list with
  corresponding positions, and then multiply those together.
*)
definition z:: "nat list \<Rightarrow> rat list \<Rightarrow> rat"
  where "z index_list sign_asg \<equiv> (prod_list (map (nth sign_asg) index_list))"

definition mtx_row:: "rat list list \<Rightarrow> nat list \<Rightarrow> rat list"
  where "mtx_row sign_list index_list \<equiv> (map ( (z index_list)) sign_list)"

definition matrix_A:: "rat list list \<Rightarrow> nat list list \<Rightarrow> rat mat" 
  where "matrix_A sign_list subset_list = 
    (mat_of_rows_list (length sign_list) (map (\<lambda>i .(mtx_row sign_list i)) subset_list))"

definition alt_matrix_A:: "rat list list \<Rightarrow> nat list list \<Rightarrow> rat mat"
  where "alt_matrix_A signs subsets = (mat (length subsets) (length signs) 
    (\<lambda>(i, j). z (subsets ! i) (signs ! j)))"

lemma alt_matrix_char: "alt_matrix_A signs subsets = matrix_A signs subsets"
proof - 
  have h0: "(\<And>i j. i < length subsets \<Longrightarrow>
            j < length signs \<Longrightarrow>
            map (\<lambda>index_list. map (z index_list) signs) subsets ! i ! j = z (subsets ! i) (signs ! j))"
  proof -
    fix i
    fix j
    assume i_lt: "i < length subsets"
    assume j_lt: "j < length signs"
    show "((map (\<lambda>index_list. map (z index_list) signs) subsets) ! i) ! j = z (subsets ! i) (signs ! j)"
    proof - 
      have h0: "(map (\<lambda>index_list. map (z index_list) signs) subsets) ! i =  map (z (subsets ! i)) signs" 
        using nth_map i_lt
        by blast
      then show ?thesis using nth_map j_lt
        by simp 
    qed
  qed
  have h: " mat (length subsets) (length signs) (\<lambda>(i, j). z (subsets ! i) (signs ! j)) =
    mat (length subsets) (length signs) (\<lambda>(i, y). map (\<lambda>index_list. map (z index_list) signs) subsets ! i ! y)"
    using h0 eq_matI[where A = "mat (length subsets) (length signs) (\<lambda>(i, j). z (subsets ! i) (signs ! j))",
        where B = "mat (length subsets) (length signs) (\<lambda>(i, y). map (\<lambda>index_list. map (z index_list) signs) subsets ! i ! y)"]
    by auto
  show ?thesis unfolding alt_matrix_A_def matrix_A_def mat_of_rows_list_def apply (auto) unfolding mtx_row_def
    using h   by blast
qed

lemma subsets_are_rows: "\<forall>i < (length subsets). row (alt_matrix_A signs subsets) i  = vec (length signs) (\<lambda>j. z (subsets ! i) (signs ! j))"
  unfolding row_def unfolding alt_matrix_A_def by auto

lemma signs_are_cols: "\<forall>i < (length signs). col (alt_matrix_A signs subsets) i  = vec (length subsets) (\<lambda>j. z (subsets ! j) (signs ! i))"
  unfolding col_def unfolding alt_matrix_A_def by auto

(* ith entry of LHS vector is the number of (distinct) real zeros of p where the sign vector of the qs  is the ith entry of signs.*)
definition construct_lhs_vector:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list  \<Rightarrow> rat vec"
  where "construct_lhs_vector p qs signs \<equiv>
  vec_of_list (map (\<lambda>w.  rat_of_int (int (length (filter (\<lambda>v. v = w) (map (consistent_sign_vec_copr qs) (characterize_root_list_p p)))))) signs)"

(* Putting all of the pieces of the construction together *)
definition satisfy_equation:: "real poly \<Rightarrow> real poly list \<Rightarrow> nat list list \<Rightarrow> rat list list \<Rightarrow> bool"
  where "satisfy_equation p qs subset_list sign_list =
        (mult_mat_vec (matrix_A sign_list subset_list) (construct_lhs_vector p qs sign_list) = (construct_rhs_vector p qs subset_list))"

section "Setting up the construction: Proofs"

(* Some matrix lemmas  *)
lemma row_mat_of_rows_list:
  assumes "list_all (\<lambda>r. length r = nc) rs"
  assumes "i < length rs"
  shows "row (mat_of_rows_list nc rs) i = vec_of_list (nth rs i)"
  by (smt assms(1) assms(2) dim_col_mat(1) dim_vec_of_list eq_vecI index_row(2) index_vec list_all_length mat_of_rows_list_def row_mat split_conv vec_of_list_index)


lemma mult_mat_vec_of_list:
  assumes "length ls = nc"
  assumes "list_all (\<lambda>r. length r = nc) rs"
  shows "mat_of_rows_list nc rs *\<^sub>v vec_of_list ls =
    vec_of_list (map (\<lambda>r. vec_of_list r \<bullet> vec_of_list ls) rs)"
  unfolding mult_mat_vec_def
  using row_mat_of_rows_list assms 
  apply auto
  by (smt dim_row_mat(1) dim_vec dim_vec_of_list eq_vecI index_map_vec(1) index_map_vec(2) index_vec list_all_length mat_of_rows_list_def row_mat_of_rows_list vec_of_list_index)

lemma mtx_row_length:
  "list_all (\<lambda>r. length r = length signs) (map (mtx_row signs) ls)"
  apply (induction ls)
  by (auto simp add: mtx_row_def)

thm construct_lhs_vector_def
thm  poly_roots_finite

(* Recharacterize the LHS vector *)
lemma construct_lhs_vector_clean:
  assumes "p \<noteq> 0"
  assumes "i < length signs"
  shows "(construct_lhs_vector p qs signs) $ i =
    card {x. poly p x = 0 \<and> ((consistent_sign_vec_copr qs x) = (nth signs i))}"
proof -
  from poly_roots_finite[OF assms(1)] have "finite {x. poly p x = 0}" .
  then have eq: "(Collect
       ((\<lambda>v. v = signs ! i) \<circ>
        consistent_sign_vec_copr qs) \<inter>
      set (sorted_list_of_set
            {x. poly p x = 0})) =
    {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = signs ! i}"
    by auto
  show ?thesis
    unfolding construct_lhs_vector_def vec_of_list_index characterize_root_list_p_def
    apply auto
    apply (subst nth_map[OF assms(2)])
    apply auto
    apply (subst distinct_length_filter)
    using eq by auto
qed

lemma construct_lhs_vector_cleaner:
  assumes "p \<noteq> 0"
  shows "(construct_lhs_vector p qs signs) =
   vec_of_list (map (\<lambda>s. rat_of_int (card {x. poly p x = 0 \<and> ((consistent_sign_vec_copr qs x) = s)})) signs)"
  apply (rule eq_vecI)
  apply (auto simp add:  construct_lhs_vector_clean[OF assms] )
  apply (simp add: vec_of_list_index)
  unfolding construct_lhs_vector_def
  using assms construct_lhs_vector_clean construct_lhs_vector_def apply auto[1]
  by simp

(* Show that because our consistent sign vectors consist of 1 and -1's, z returns 1 or -1 
  when applied to a consistent sign vector *)
lemma z_signs:
  assumes "list_all (\<lambda>i. i < length signs) I"
  assumes "list_all (\<lambda>s. s = 1 \<or> s = -1) signs"
  shows "(z I signs = 1) \<or> (z I signs = -1)" using assms
proof (induction I)
  case Nil
  then show ?case
    by (auto simp add:z_def)
next
  case (Cons a I)
  moreover have "signs ! a = 1 \<or> signs ! a = -1"
    by (metis (mono_tags, lifting) add_Suc_right calculation(2) calculation(3) gr0_conv_Suc list.size(4) list_all_length nth_Cons_0)
  ultimately show ?case
    by (auto simp add:z_def)
qed

lemma z_lemma:
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  assumes consistent: "sign \<in> set (characterize_consistent_signs_at_roots_copr p qs)"
  assumes welldefined: "list_constr I (length qs)"
  shows "(z I sign = 1) \<or> (z I sign = -1)"
proof (rule z_signs)
  have "length sign = length qs" using consistent
    by (auto simp add: characterize_consistent_signs_at_roots_copr_def consistent_sign_vec_copr_def)
  thus "list_all (\<lambda>i. i < length sign) I"
    using welldefined
    by (auto simp add: list_constr_def characterize_consistent_signs_at_roots_copr_def consistent_sign_vec_copr_def)
  show "list_all (\<lambda>s. s = 1 \<or> s = - 1) sign" using consistent
    apply (auto simp add: list.pred_map  characterize_consistent_signs_at_roots_copr_def  consistent_sign_vec_copr_def)
    using Ball_set
    by force
qed

(* Show that all consistent sign vectors on roots of polynomials are in characterize_consistent_signs_at_roots_copr  *)
lemma in_set: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec_copr qs x"
  assumes welldefined: "list_constr I (length qs)"
  shows "sign \<in> set (characterize_consistent_signs_at_roots_copr p qs)" 
proof -
  have h1: "consistent_sign_vec_copr qs x \<in>
      set (remdups (map (consistent_sign_vec_copr qs) (sorted_list_of_set {x. poly p x = 0})))" 
    using root_p apply auto apply (subst set_sorted_list_of_set)
    using nonzero poly_roots_finite rsquarefree_def apply blast by auto
  thus ?thesis unfolding characterize_consistent_signs_at_roots_copr_def characterize_root_list_p_def using sign_fix
    by blast
qed

(* Since all of the polynomials in qs are relatively prime to p, products of subsets of these
    polynomials are also relatively prime to p  *)
lemma nonzero_product: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  assumes pairwise_rel_prime_1: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  fixes I:: "nat list" 
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes welldefined: "list_constr I (length qs)"
  shows "(poly (prod_list (retrieve_polys qs I)) x > 0) \<or> (poly (prod_list (retrieve_polys qs I)) x < 0)"
proof -
  have "\<And>x. x \<in> set (retrieve_polys qs I) \<Longrightarrow> coprime p x"
    unfolding retrieve_polys_def
    by (smt in_set_conv_nth in_set_member length_map list_all_length list_constr_def nth_map pairwise_rel_prime_1 welldefined)
  then have coprimeh: "coprime p (prod_list (retrieve_polys qs I))"
    using prod_list_coprime_right by auto
  thus ?thesis using root_p
    using coprime_poly_0 linorder_neqE_linordered_idom by blast 
qed

(* The next few lemmas relate z to the signs of the product of subsets of polynomials of qs *)
lemma horiz_vector_helper_pos_ind: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  assumes pairwise_rel_prime_1: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec_copr qs x"
  shows "(list_constr I (length qs)) \<longrightarrow> (poly (prod_list (retrieve_polys qs I)) x > 0) \<longleftrightarrow> (z I sign = 1)"
proof (induct I)
  case Nil
  then show ?case
    by (simp add: retrieve_polys_def z_def) 
next
  case (Cons a I) 
  have welldef: "list_constr (a#I) (length qs) \<longrightarrow> (list_constr I (length qs))" 
    unfolding list_constr_def list_all_def by auto
  have set_hyp: "list_constr I (length qs) \<longrightarrow> sign \<in> set (characterize_consistent_signs_at_roots_copr p qs)" 
    using in_set using nonzero root_p sign_fix by blast 
  have z_hyp: "list_constr I (length qs) \<longrightarrow> ((z I sign = 1) \<or> (z I sign = -1))" 
    using set_hyp z_lemma[where sign="sign", where I = "I", where p="p", where qs="qs"] by blast
  have sign_hyp: "sign = map (\<lambda> q. if (poly q x > 0) then 1 else -1) qs" 
    using sign_fix unfolding consistent_sign_vec_copr_def by blast
  have ind_hyp_1: "list_constr (a#I) (length qs) \<longrightarrow> 
    ((0 < poly (prod_list (retrieve_polys qs I)) x) = (z I sign = 1))"
    using welldef Cons.hyps by auto
  have ind_hyp_2: "list_constr (a#I) (length qs) \<longrightarrow> 
    ((0 > poly (prod_list (retrieve_polys qs I)) x) = (z I sign = -1))"
    using welldef z_hyp Cons.hyps nonzero_product
    using pairwise_rel_prime_1 nonzero root_p by auto 
  have h1: "prod_list (retrieve_polys qs (a # I)) = (nth qs a)*(prod_list (retrieve_polys qs I))"
    by (simp add: retrieve_polys_def)
  have h2: "(z (a # I) sign) = (nth sign a)*(z I sign)"
    by (metis (mono_tags, hide_lams) list.simps(9) prod_list.Cons z_def)
  have h3help: "list_constr (a#I) (length qs) \<longrightarrow> a < length qs" unfolding list_constr_def
    by simp 
  then have h3: "list_constr (a#I) (length qs) \<longrightarrow> 
    ((nth sign a) = (if (poly (nth qs a) x > 0) then 1 else -1))" 
    using nth_map sign_hyp by auto
  have h2: "(0 < poly ((nth qs a)*(prod_list (retrieve_polys qs I))) x) \<longleftrightarrow> 
    ((0 < poly (nth qs a) x \<and> (0 < poly (prod_list (retrieve_polys qs I)) x)) \<or>
   (0 > poly (nth qs a) x \<and> (0 > poly (prod_list (retrieve_polys qs I)) x)))"
    by (simp add: zero_less_mult_iff)
  have final_hyp_a: "list_constr (a#I) (length qs) \<longrightarrow> (((0 < poly (nth qs a) x \<and> (0 < poly (prod_list (retrieve_polys qs I)) x)) 
    \<or> (0 > poly (nth qs a) x \<and> (0 > poly (prod_list (retrieve_polys qs I)) x))) = 
    ((nth sign a)*(z I sign) = 1))" 
  proof -
    have extra_hyp_a: "list_constr (a#I) (length qs) \<longrightarrow> (0 < poly (nth qs a) x = ((nth sign a) = 1))" using h3
      by simp 
    have extra_hyp_b: "list_constr (a#I) (length qs) \<longrightarrow>  (0 > poly (nth qs a) x = ((nth sign a) = -1))" 
      using h3 apply (auto) using coprime_poly_0 h3help in_set_member nth_mem pairwise_rel_prime_1 root_p by fastforce 
    have ind_hyp_1: "list_constr (a#I) (length qs) \<longrightarrow> (((0 < poly (nth qs a) x \<and> (z I sign = 1)) \<or> 
    (0 > poly (nth qs a) x \<and> (z I sign = -1)))
      = ((nth sign a)*(z I sign) = 1))" using extra_hyp_a extra_hyp_b
      using zmult_eq_1_iff
      by (simp add: h3)   
    then show ?thesis
      using ind_hyp_1 ind_hyp_2 by (simp add: Cons.hyps welldef)
  qed
  then show ?case 
    using h1 z_def by (simp add: zero_less_mult_iff)  
qed

lemma horiz_vector_helper_pos: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  assumes pairwise_rel_prime_1: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec_copr qs x"
  assumes welldefined: "list_constr I (length qs)"
  shows "(poly (prod_list (retrieve_polys qs I)) x > 0) \<longleftrightarrow> (z I sign = 1)"
  using horiz_vector_helper_pos_ind
  using pairwise_rel_prime_1 nonzero  root_p sign_fix welldefined by blast 

lemma horiz_vector_helper_neg: 
  fixes p:: "real poly"
  assumes nonzero: "p\<noteq>0"
  fixes qs:: "real poly list"
  assumes pairwise_rel_prime_1: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  fixes I:: "nat list" 
  fixes sign:: "rat list"
  fixes x:: "real"
  assumes root_p: "x \<in> {x. poly p x = 0}"
  assumes sign_fix: "sign = consistent_sign_vec_copr qs x"
  assumes welldefined: "list_constr I (length qs)"
  shows "(poly (prod_list (retrieve_polys qs I)) x < 0) \<longleftrightarrow> (z I sign = -1)"
proof - 
  have set_hyp: "list_constr I (length qs) \<longrightarrow> sign \<in> set (characterize_consistent_signs_at_roots_copr p qs)" 
    using in_set using nonzero root_p sign_fix by blast 
  have z_hyp: "list_constr I (length qs) \<longrightarrow> ((z I sign = 1) \<or> (z I sign = -1))" 
    using set_hyp  z_lemma[where sign="sign", where I = "I", where p="p", where qs="qs"] by blast
  have poly_hyp: "(poly (prod_list (retrieve_polys qs I)) x > 0) \<or> (poly (prod_list (retrieve_polys qs I)) x < 0)"
    using nonzero_product
    using pairwise_rel_prime_1 nonzero root_p
    using welldefined by blast
  have pos_hyp: "(poly (prod_list (retrieve_polys qs I)) x > 0) \<longleftrightarrow> (z I sign = 1)" using horiz_vector_helper_pos
    using pairwise_rel_prime_1 nonzero root_p sign_fix welldefined by blast
  show ?thesis using z_hyp poly_hyp pos_hyp apply (auto)
    using welldefined by blast
qed

(* Recharacterize the dot product *)
lemma vec_of_list_dot_rewrite:
  assumes "length xs = length ys"
  shows "vec_of_list xs \<bullet> vec_of_list ys =
    sum_list (map2 (*) xs ys)"
  using assms
proof (induction xs arbitrary:ys)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case apply auto
    by (smt (verit, best) Suc_length_conv list.simps(9) old.prod.case scalar_prod_vCons sum_list.Cons vec_of_list_Cons zip_Cons_Cons)
qed

lemma lhs_dot_rewrite:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  shows
    "(vec_of_list (mtx_row signs I) \<bullet> (construct_lhs_vector p qs signs)) =
   sum_list (map (\<lambda>s. (z I s)  *  rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) signs)"
proof -
  have "p \<noteq> 0" using nonzero by auto
  from construct_lhs_vector_cleaner[OF this]
  have rhseq: "construct_lhs_vector p qs signs =
    vec_of_list
    (map (\<lambda>s. rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) signs)" by auto
  have "(vec_of_list (mtx_row signs I) \<bullet> (construct_lhs_vector p qs signs)) =    
    sum_list (map2 (*) (mtx_row signs I) (map (\<lambda>s. rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) signs))"
    unfolding rhseq
    apply (intro vec_of_list_dot_rewrite)
    by (auto simp add: mtx_row_def)
  thus ?thesis unfolding mtx_row_def
    using map2_map_map 
    by (auto simp add: map2_map_map)
qed

lemma sum_list_distinct_filter:
  fixes f:: "'a \<Rightarrow> int"
  assumes "distinct xs" "distinct ys"
  assumes "set ys \<subseteq> set xs"
  assumes "\<And>x. x \<in> set xs - set ys \<Longrightarrow> f x = 0"
  shows "sum_list (map f xs) = sum_list (map f ys)"
  by (metis List.finite_set assms(1) assms(2) assms(3) assms(4) sum.mono_neutral_cong_left sum_list_distinct_conv_sum_set)

(* If we have a superset of the signs, we can drop to just the consistent ones *)
lemma construct_lhs_vector_drop_consistent:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes welldefined: "list_constr I (length qs)"
  shows
    "(vec_of_list (mtx_row signs I) \<bullet> (construct_lhs_vector p qs signs)) =
     (vec_of_list (mtx_row (characterize_consistent_signs_at_roots_copr p qs) I) \<bullet>
      (construct_lhs_vector p qs (characterize_consistent_signs_at_roots_copr p qs)))"
proof - 
  have h0: "\<forall> sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec_copr qs ` set (characterize_root_list_p p) \<and> 0 < rat_of_nat (card
                  {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = sgn}) \<longrightarrow> z I sgn = 0"
  proof - 
    have "\<forall> sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec_copr qs ` set (characterize_root_list_p p) \<and> 0 < rat_of_int (card
                  {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = sgn}) \<longrightarrow> {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = sgn} \<noteq> {}" 
      by fastforce
    then show ?thesis
    proof -
      { fix iis :: "rat list"
        have ff1: "0 \<noteq> p"
          using nonzero rsquarefree_def by blast
        obtain rr :: "(real \<Rightarrow> bool) \<Rightarrow> real" where
          ff2: "\<And>p. p (rr p) \<or> Collect p = {}"
          by moura
        { assume "\<exists>is. is = iis \<and> {r. poly p r = 0 \<and> consistent_sign_vec_copr qs r = is} \<noteq> {}"
          then have "\<exists>is. consistent_sign_vec_copr qs (rr (\<lambda>r. poly p r = 0 \<and> consistent_sign_vec_copr qs r = is)) = iis \<and> {r. poly p r = 0 \<and> consistent_sign_vec_copr qs r = is} \<noteq> {}"
            using ff2
            by (metis (mono_tags, lifting))
          then have "\<exists>r. poly p r = 0 \<and> consistent_sign_vec_copr qs r = iis"
            using ff2 by smt
          then have "iis \<in> consistent_sign_vec_copr qs ` set (sorted_list_of_set {r. poly p r = 0})"
            using ff1 poly_roots_finite by fastforce }
        then have "iis \<notin> set signs \<or> iis \<in> consistent_sign_vec_copr qs ` set (characterize_root_list_p p) \<or> \<not> 0 < rat_of_int (int (card {r. poly p r = 0 \<and> consistent_sign_vec_copr qs r = iis}))"
          by (metis (no_types) \<open>\<forall>sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec_copr qs ` set (characterize_root_list_p p) \<and> 0 < rat_of_int (int (card {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = sgn})) \<longrightarrow> {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = sgn} \<noteq> {}\<close> characterize_root_list_p_def) }
      then show ?thesis
        by fastforce
    qed
  qed
  then have "\<forall> sgn. sgn \<in> set signs \<and> sgn \<notin> consistent_sign_vec_copr qs ` set (characterize_root_list_p p) \<longrightarrow> ((0 = rat_of_nat (card
                  {xa. poly p xa = 0 \<and> consistent_sign_vec_copr qs xa = sgn}) \<or> z I sgn = 0))"
    by auto
  then have hyp: "\<forall> s. s \<in> set signs \<and> s \<notin> consistent_sign_vec_copr qs ` set (characterize_root_list_p p) \<longrightarrow> (z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}) = 0)"
    by auto
  then have "(\<Sum>s\<in> set(signs). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) = 
        (\<Sum>s\<in>(set (signs) \<inter> (consistent_sign_vec_copr qs ` set (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
  proof - 
    have "set(signs) =(set (signs) \<inter> (consistent_sign_vec_copr qs ` set (characterize_root_list_p p))) \<union>
              (set(signs)-(consistent_sign_vec_copr qs ` set (characterize_root_list_p p)))"
      by blast
    then have sum_rewrite: "(\<Sum>s\<in> set(signs). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) =  
          (\<Sum>s\<in> (set (signs) \<inter> (consistent_sign_vec_copr qs ` set (characterize_root_list_p p))) \<union>
              (set(signs)-(consistent_sign_vec_copr qs ` set (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
      by auto
    then have sum_split: "(\<Sum>s\<in> (set (signs) \<inter> (consistent_sign_vec_copr qs ` set (characterize_root_list_p p))) \<union>
              (set(signs)-(consistent_sign_vec_copr qs ` set (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))
          = 
(\<Sum>s\<in> (set (signs) \<inter> (consistent_sign_vec_copr qs ` set (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))
+ (\<Sum>s\<in> (set(signs)-(consistent_sign_vec_copr qs ` set (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
      by (metis (no_types, lifting) List.finite_set sum.Int_Diff)
    have sum_zero: "(\<Sum>s\<in> (set(signs)-(consistent_sign_vec_copr qs ` set (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) = 0"   
      using hyp
      by (simp add: hyp)      
    show ?thesis using sum_rewrite sum_split sum_zero by linarith
  qed
  then have set_eq: "set (remdups
           (map (consistent_sign_vec_copr qs)
             (characterize_root_list_p p))) = set (signs) \<inter> (consistent_sign_vec_copr qs ` set (characterize_root_list_p p))"
    using all_info
    by (simp add: characterize_consistent_signs_at_roots_copr_def subset_antisym)
  have hyp1: "(\<Sum>s\<leftarrow>signs. z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) = 
        (\<Sum>s\<in>set (signs). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
    using distinct_signs sum_list_distinct_conv_sum_set by blast
  have hyp2: "(\<Sum>s\<leftarrow>remdups
           (map (consistent_sign_vec_copr qs)
             (characterize_root_list_p p)). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))
  = (\<Sum>s\<in> set (remdups
           (map (consistent_sign_vec_copr qs)
             (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
    using sum_list_distinct_conv_sum_set by blast 
  have set_sum_eq: "(\<Sum>s\<in>(set (signs) \<inter> (consistent_sign_vec_copr qs ` set (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) =
    (\<Sum>s\<in> set (remdups
           (map (consistent_sign_vec_copr qs)
             (characterize_root_list_p p))). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
    using set_eq by auto
  then have "(\<Sum>s\<leftarrow>signs. z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) =
    (\<Sum>s\<leftarrow>remdups
           (map (consistent_sign_vec_copr qs)
             (characterize_root_list_p p)). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
    using set_sum_eq hyp1 hyp2
    using \<open>(\<Sum>s\<in>set signs. z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) = (\<Sum>s\<in>set signs \<inter> consistent_sign_vec_copr qs ` set (characterize_root_list_p p). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))\<close> by linarith
  then have "consistent_sign_vec_copr qs ` set (characterize_root_list_p p) \<subseteq> set signs \<Longrightarrow>
    (\<And>p qss.
        characterize_consistent_signs_at_roots_copr p qss =
        remdups (map (consistent_sign_vec_copr qss) (characterize_root_list_p p))) \<Longrightarrow>
    (\<Sum>s\<leftarrow>signs. z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) =
    (\<Sum>s\<leftarrow>remdups
           (map (consistent_sign_vec_copr qs)
             (characterize_root_list_p p)). z I s * rat_of_nat (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
    by linarith
  then show ?thesis  unfolding lhs_dot_rewrite[OF nonzero]
    apply (auto intro!: sum_list_distinct_filter simp add: distinct_signs  characterize_consistent_signs_at_roots_copr_def)
    using all_info characterize_consistent_signs_at_roots_copr_def by auto[1]
qed

(* Both matrix_equation_helper_step and matrix_equation_main_step relate the matrix construction 
   to the Tarski queries, i.e. relate the product of a row of the matrix and the LHS vector to a 
   Tarski query on the RHS *)
lemma matrix_equation_helper_step:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes welldefined: "list_constr I (length qs)"
  assumes pairwise_rel_prime_1: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  shows "(vec_of_list (mtx_row signs I) \<bullet> (construct_lhs_vector p qs signs)) =
   rat_of_int (card {x. poly p x = 0 \<and> poly (prod_list (retrieve_polys qs I)) x > 0}) -
   rat_of_int (card {x. poly p x = 0 \<and> poly (prod_list (retrieve_polys qs I)) x < 0})"
proof -
  have "finite (set (map (consistent_sign_vec_copr qs)  (characterize_root_list_p p)))" by auto
  let ?gt = "(set (map (consistent_sign_vec_copr qs)  (characterize_root_list_p p)) \<inter> {s. z I s = 1})"
  let ?lt = "  (set (map (consistent_sign_vec_copr qs)  (characterize_root_list_p p)) \<inter> {s. z I s = -1})"  
  have eq: "set (map (consistent_sign_vec_copr qs)  (characterize_root_list_p p)) = ?gt \<union> ?lt"
    apply auto
    by (metis characterize_root_list_p_def horiz_vector_helper_neg horiz_vector_helper_pos_ind nonzero nonzero_product pairwise_rel_prime_1 poly_roots_finite sorted_list_of_set(1) welldefined)
      (* First, drop the signs that are irrelevant *)
  from construct_lhs_vector_drop_consistent[OF assms(1-4)] have
    "vec_of_list (mtx_row signs I) \<bullet> construct_lhs_vector p qs signs =
  vec_of_list (mtx_row (characterize_consistent_signs_at_roots_copr p qs) I) \<bullet>
  construct_lhs_vector p qs (characterize_consistent_signs_at_roots_copr p qs)" .
    (* Now we split the sum *)
  from lhs_dot_rewrite[OF assms(1)]
  moreover have "... =
  (\<Sum>s\<leftarrow>characterize_consistent_signs_at_roots_copr p qs.
    z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))" .
  moreover have "... =
  (\<Sum>s\<in>set (map (consistent_sign_vec_copr qs)  (characterize_root_list_p p)).
    z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))" unfolding characterize_consistent_signs_at_roots_copr_def sum_code[symmetric]
    by (auto)
  ultimately have "... =
  (\<Sum>s\<in>?gt. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) +
  (\<Sum>s\<in>?lt. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))"
    apply (subst eq)
    apply (rule sum.union_disjoint)
    by auto
      (* Now recharacterize lt, gt*)
  have setroots: "set (characterize_root_list_p p) = {x. poly p x = 0}" unfolding characterize_root_list_p_def
    using poly_roots_finite nonzero rsquarefree_def set_sorted_list_of_set by blast    
  have *: "\<And>s. {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s} =
        {x \<in>{x. poly p x = 0}. consistent_sign_vec_copr qs x = s}"
    by auto
  have lem_e1: "\<And>x. x \<in> {x. poly p x = 0} \<Longrightarrow>
       card
        {s \<in> consistent_sign_vec_copr  qs ` {x. poly p x = 0} \<inter> {s. z I s = 1}.
         consistent_sign_vec_copr qs x = s} =
       (if 0 < poly (prod_list (retrieve_polys qs I)) x then 1 else 0)"
  proof -
    fix x
    assume rt: "x \<in> {x. poly p x = 0}"
    then have 1: "{s \<in> consistent_sign_vec_copr qs ` {x. poly p x = 0} \<inter> {s. z I s = 1}. consistent_sign_vec_copr qs x = s} =
      {s. z I s = 1 \<and> consistent_sign_vec_copr qs x = s}"
      by auto
    from horiz_vector_helper_pos[OF assms(1) assms(5) rt]
    have 2: "... = {s. (0 < poly (prod_list (retrieve_polys qs I)) x)  \<and> consistent_sign_vec_copr qs x = s}"
      using welldefined by blast
    have 3: "... = (if (0 < poly (prod_list (retrieve_polys qs I)) x)  then {consistent_sign_vec_copr qs x} else {})"
      by auto
    thus "card {s \<in> consistent_sign_vec_copr qs ` {x. poly p x = 0} \<inter> {s. z I s = 1}. consistent_sign_vec_copr qs x = s} =
         (if 0 < poly (prod_list (retrieve_polys qs I)) x then 1 else 0) " using 1 2 3 by auto
  qed
  have e1: "(\<Sum>s\<in>consistent_sign_vec_copr qs ` {x. poly p x = 0} \<inter> {s. z I s = 1}.
       card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}) =
     (sum (\<lambda>x. if (poly (prod_list (retrieve_polys qs I)) x) > 0 then 1 else 0) {x. poly p x = 0})"
    unfolding * apply (rule sum_multicount_gen)
    using \<open>finite (set (map (consistent_sign_vec_copr qs) (characterize_root_list_p p)))\<close> setroots apply auto[1]
    apply (metis List.finite_set setroots)
    using lem_e1 by auto
  have gtchr: "(\<Sum>s\<in>?gt. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) =
    rat_of_int (card {x. poly p x = 0 \<and> 0 < poly (prod_list (retrieve_polys qs I)) x})"
    apply (auto simp add: setroots)
    apply (subst of_nat_sum[symmetric])
    apply (subst of_nat_eq_iff)
    apply (subst e1)
    apply (subst card_eq_sum)
    apply (rule sum.mono_neutral_cong_right)
    apply (metis List.finite_set setroots)
    by auto
  have lem_e2: "\<And>x. x \<in> {x. poly p x = 0} \<Longrightarrow>
       card
        {s \<in> consistent_sign_vec_copr  qs ` {x. poly p x = 0} \<inter> {s. z I s = -1}.
         consistent_sign_vec_copr qs x = s} =
       (if poly (prod_list (retrieve_polys qs I)) x < 0 then 1 else 0)"
  proof -
    fix x
    assume rt: "x \<in> {x. poly p x = 0}"
    then have 1: "{s \<in> consistent_sign_vec_copr qs ` {x. poly p x = 0} \<inter> {s. z I s = -1}. consistent_sign_vec_copr qs x = s} =
      {s. z I s = -1 \<and> consistent_sign_vec_copr qs x = s}"
      by auto
    from horiz_vector_helper_neg[OF assms(1) assms(5) rt]
    have 2: "... = {s. (0 > poly (prod_list (retrieve_polys qs I)) x)  \<and> consistent_sign_vec_copr qs x = s}"
      using welldefined by blast
    have 3: "... = (if (0 > poly (prod_list (retrieve_polys qs I)) x)  then {consistent_sign_vec_copr qs x} else {})"
      by auto
    thus "card {s \<in> consistent_sign_vec_copr qs ` {x. poly p x = 0} \<inter> {s. z I s = -1}. consistent_sign_vec_copr qs x = s} =
       (if poly (prod_list (retrieve_polys qs I)) x < 0 then 1 else 0)" using 1 2 3 by auto
  qed
  have e2: " (\<Sum>s\<in>consistent_sign_vec_copr qs ` {x. poly p x = 0} \<inter> {s. z I s = - 1}.
       card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}) =
     (sum (\<lambda>x. if (poly (prod_list (retrieve_polys qs I)) x) < 0 then 1 else 0) {x. poly p x = 0})"
    unfolding * apply (rule sum_multicount_gen)
    using \<open>finite (set (map (consistent_sign_vec_copr qs) (characterize_root_list_p p)))\<close> setroots apply auto[1]
     apply (metis List.finite_set setroots)
    using lem_e2 by auto
  have ltchr: "(\<Sum>s\<in>?lt. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) =
    - rat_of_int (card {x. poly p x = 0 \<and> 0 > poly (prod_list (retrieve_polys qs I)) x})"
    apply (auto simp add: setroots sum_negf)
    apply (subst of_nat_sum[symmetric])
    apply (subst of_nat_eq_iff)
    apply (subst e2)
    apply (subst card_eq_sum)
    apply (rule sum.mono_neutral_cong_right)
       apply (metis List.finite_set setroots)
    by auto
  show ?thesis using gtchr ltchr
    using \<open>(\<Sum>s\<in>set (map (consistent_sign_vec_copr qs) (characterize_root_list_p p)). z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) = (\<Sum>s\<in>set (map (consistent_sign_vec_copr qs) (characterize_root_list_p p)) \<inter> {s. z I s = 1}. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) + (\<Sum>s\<in>set (map (consistent_sign_vec_copr qs) (characterize_root_list_p p)) \<inter> {s. z I s = - 1}. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))\<close> \<open>(\<Sum>s\<leftarrow>characterize_consistent_signs_at_roots_copr p qs. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s})) = (\<Sum>s\<in>set (map (consistent_sign_vec_copr qs) (characterize_root_list_p p)). z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))\<close> \<open>vec_of_list (mtx_row (characterize_consistent_signs_at_roots_copr p qs) I) \<bullet> construct_lhs_vector p qs (characterize_consistent_signs_at_roots_copr p qs) = (\<Sum>s\<leftarrow>characterize_consistent_signs_at_roots_copr p qs. z I s * rat_of_int (card {x. poly p x = 0 \<and> consistent_sign_vec_copr qs x = s}))\<close> \<open>vec_of_list (mtx_row signs I) \<bullet> construct_lhs_vector p qs signs = vec_of_list (mtx_row (characterize_consistent_signs_at_roots_copr p qs) I) \<bullet> construct_lhs_vector p qs (characterize_consistent_signs_at_roots_copr p qs)\<close>
    by linarith
qed

(* A clean restatement of the helper lemma *)
lemma matrix_equation_main_step:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes I:: "nat list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes welldefined: "list_constr I (length qs)"
  assumes pairwise_rel_prime_1: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  shows "(vec_of_list (mtx_row signs I) \<bullet> (construct_lhs_vector p qs signs)) =  
    construct_NofI p (retrieve_polys qs I)"
    unfolding construct_NofI_prop[OF nonzero]
    using matrix_equation_helper_step[OF assms]
    by linarith

lemma map_vec_vec_of_list_eq_intro:
  assumes "map f xs = map g ys"
  shows "map_vec f (vec_of_list xs) = map_vec g (vec_of_list ys)"
  by (metis assms vec_of_list_map)

(* Shows that as long as we have a "basis" of sign assignments (see assumptions all_info, welldefined), 
  and some other mild assumptions on our inputs (given in nonzero, distinct_signs, pairwise_rel_prime),
  the construction will be satisfied *)
theorem matrix_equation:
  fixes p:: "real poly"
  fixes qs:: "real poly list"
  fixes subsets:: "nat list list" 
  fixes signs:: "rat list list"
  assumes nonzero: "p\<noteq>0"
  assumes distinct_signs: "distinct signs"
  assumes all_info: "set (characterize_consistent_signs_at_roots_copr p qs) \<subseteq> set(signs)"
  assumes pairwise_rel_prime: "\<forall>q. ((List.member qs q) \<longrightarrow> (coprime p q))"
  assumes welldefined: "all_list_constr (subsets) (length qs)"
  shows "satisfy_equation p qs subsets signs"
  unfolding satisfy_equation_def matrix_A_def
    construct_lhs_vector_def construct_rhs_vector_def all_list_constr_def
  apply (subst mult_mat_vec_of_list)
    apply (auto simp add: mtx_row_length intro!: map_vec_vec_of_list_eq_intro)
  using matrix_equation_main_step[OF assms(1-3) _ assms(4), unfolded construct_lhs_vector_def]
  using all_list_constr_def in_set_member welldefined by fastforce

(* Prettifying some theorems*)
definition roots:: "real poly \<Rightarrow> real set"
  where "roots p = {x. poly p x = 0}"

definition sgn::"'a::linordered_field \<Rightarrow> rat"
  where "sgn x = (if x > 0 then 1
                  else if x < 0 then -1
                  else 0)"

definition sgn_vec::"real poly list \<Rightarrow> real \<Rightarrow> rat list"
  where "sgn_vec qs x \<equiv>  map (sgn \<circ> (\<lambda>q. poly q x)) qs"

definition consistent_signs_at_roots:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list set"
  where "consistent_signs_at_roots p qs =
    (sgn_vec qs) ` (roots p)"

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

abbreviation w_vec:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list  \<Rightarrow> rat vec"
  where "w_vec \<equiv> construct_lhs_vector"

abbreviation v_vec:: "real poly \<Rightarrow> real poly list \<Rightarrow> nat list list \<Rightarrow> rat vec"
  where "v_vec \<equiv> construct_rhs_vector"

abbreviation M_mat:: "rat list list \<Rightarrow> nat list list \<Rightarrow> rat mat"
  where "M_mat \<equiv> matrix_A"

theorem matrix_equation_pretty:
  assumes "p\<noteq>0"
  assumes "\<And>q. q \<in> set qs \<Longrightarrow> coprime p q"
  assumes "distinct signs"
  assumes "consistent_signs_at_roots p qs \<subseteq> set signs"
  assumes "\<And>l i. l \<in> set subsets \<Longrightarrow> i \<in> set l \<Longrightarrow> i < length qs"
  shows "M_mat signs subsets *\<^sub>v w_vec p qs signs = v_vec p qs subsets"
  unfolding satisfy_equation_def[symmetric]
  apply (rule matrix_equation[OF assms(1) assms(3)])
  apply (metis assms(1) assms(2) assms(4) consistent_signs_at_roots_eq csa_list_copr_rel member_def)
  apply (simp add: assms(2) in_set_member)
  using Ball_set all_list_constr_def assms(5) list_constr_def member_def by fastforce

end