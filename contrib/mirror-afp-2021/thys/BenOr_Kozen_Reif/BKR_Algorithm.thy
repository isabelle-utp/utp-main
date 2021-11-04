theory BKR_Algorithm
  imports
    "More_Matrix"
    "Sturm_Tarski.Sturm_Tarski"
begin

section "Setup"

definition retrieve_polys:: "real poly list \<Rightarrow> nat list \<Rightarrow> real poly list"
  where "retrieve_polys qss index_list = (map (nth qss) index_list)"

definition construct_NofI:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat"
  where "construct_NofI p I =  rat_of_int (changes_R_smods p ((pderiv p)*(prod_list I)))"

definition construct_rhs_vector:: "real poly \<Rightarrow> real poly list \<Rightarrow> nat list list \<Rightarrow> rat vec"
  where "construct_rhs_vector p qs Is = vec_of_list (map (\<lambda> I.(construct_NofI p (retrieve_polys qs I))) Is)"

section "Base Case"

definition base_case_info:: "(rat mat \<times> (nat list list \<times> rat list list))"
  where "base_case_info =
    ((mat_of_rows_list 2 [[1,1], [1,-1]]), ([[],[0]], [[1],[-1]]))"

(* When p, q are coprime, this will actually be an int vec, which is why taking the floor is okay *)
definition base_case_solve_for_lhs:: "real poly \<Rightarrow> real poly \<Rightarrow> rat vec"
  where "base_case_solve_for_lhs p q = (mult_mat_vec (mat_of_rows_list 2 [[1/2, 1/2], [1/2, -1/2]])  (construct_rhs_vector p [q] [[], [0]]))"

thm "gauss_jordan_compute_inverse"

primrec matr_option:: "nat \<Rightarrow> 'a::{one, zero} mat option \<Rightarrow> 'a mat"
  where "matr_option dimen None = 1\<^sub>m dimen"
  | "matr_option dimen (Some c) = c" 

(* For smooth code export, we want to use a computable notion of matrix equality *)
definition mat_equal:: "'a:: field mat \<Rightarrow> 'a :: field mat \<Rightarrow> bool"
  where "mat_equal A B = (dim_row A = dim_row B \<and> dim_col A = dim_col B \<and> (mat_to_list A) = (mat_to_list B))"

definition mat_inverse_var :: "'a :: field mat \<Rightarrow> 'a mat option" where 
  "mat_inverse_var A = (if dim_row A = dim_col A then
    let one = 1\<^sub>m (dim_row A) in
    (case gauss_jordan A one of
      (B, C) \<Rightarrow> if (mat_equal B one) then Some C else None) else None)"

(* Now solve for LHS in general. 
  Because mat_inverse returns an option type, we pattern match on this. 
  Notice that when we call this function in the algorithm, the matrix we pass will always be invertible,
  given how the construction works. *)
definition solve_for_lhs:: "real poly \<Rightarrow> real poly list \<Rightarrow> nat list list \<Rightarrow> rat mat \<Rightarrow> rat vec"
  where "solve_for_lhs p qs subsets matr =
     mult_mat_vec (matr_option (dim_row matr) (mat_inverse_var matr))  (construct_rhs_vector p qs subsets)"

section "Smashing" 

definition subsets_smash::"nat \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow> nat list list"
  where "subsets_smash n s1 s2 = concat (map (\<lambda>l1. map (\<lambda> l2. l1 @ (map ((+) n) l2)) s2) s1)"

definition signs_smash::"'a list list \<Rightarrow>  'a list list \<Rightarrow> 'a list list"
  where "signs_smash s1 s2 = concat (map (\<lambda>l1. map (\<lambda> l2. l1 @ l2) s2) s1)"

definition smash_systems:: "real poly \<Rightarrow> real poly list \<Rightarrow> real poly list \<Rightarrow> nat list list \<Rightarrow> nat list list \<Rightarrow>
  rat list list \<Rightarrow> rat list list \<Rightarrow> rat mat \<Rightarrow> rat mat \<Rightarrow> 
  real poly list \<times> (rat mat \<times> (nat list list \<times> rat list list))"
  where "smash_systems p qs1 qs2 subsets1 subsets2 signs1 signs2 mat1 mat2 =
    (qs1@qs2, (kronecker_product mat1 mat2, (subsets_smash (length qs1) subsets1 subsets2, signs_smash signs1 signs2)))"

fun combine_systems:: "real poly \<Rightarrow> (real poly list \<times> (rat mat \<times> (nat list list \<times> rat list list))) \<Rightarrow> (real poly list \<times> (rat mat \<times> (nat list list \<times> rat list list)))
  \<Rightarrow> (real poly list \<times> (rat mat \<times> (nat list list \<times> rat list list)))"
  where "combine_systems p (qs1, m1, sub1, sgn1) (qs2, m2, sub2, sgn2) = 
    (smash_systems p qs1 qs2 sub1 sub2 sgn1 sgn2 m1 m2)"

(* Overall:
  Start with a matrix equation.
  Input a matrix, subsets, and signs.
  Drop columns of the matrix based on the 0's on the LHS---so extract a list of 0's. Reduce signs accordingly.
  Then find a list of rows to delete based on using rank (use the transpose result, pivot positions!),
   and delete those rows.  Reduce subsets accordingly.
  End with a reduced system! *)
section "Reduction"
definition find_nonzeros_from_input_vec:: "rat vec \<Rightarrow> nat list"
  where "find_nonzeros_from_input_vec lhs_vec = filter (\<lambda>i. lhs_vec $ i \<noteq> 0) [0..< dim_vec lhs_vec]"

definition take_indices:: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list"
  where "take_indices subsets indices = map ((!) subsets) indices"

definition take_cols_from_matrix:: "'a mat \<Rightarrow> nat list \<Rightarrow> 'a mat"
  where "take_cols_from_matrix matr indices_to_keep = 
    mat_of_cols (dim_row matr) ((take_indices (cols matr) indices_to_keep):: 'a vec list)"

definition take_rows_from_matrix:: "'a mat \<Rightarrow> nat list \<Rightarrow> 'a mat"
  where "take_rows_from_matrix matr indices_to_keep = 
    mat_of_rows (dim_col matr) ((take_indices (rows matr) indices_to_keep):: 'a vec list)"

fun reduce_mat_cols:: "'a mat \<Rightarrow> rat vec \<Rightarrow> 'a mat"
  where "reduce_mat_cols A lhs_vec = take_cols_from_matrix A (find_nonzeros_from_input_vec lhs_vec)"

(* Find which rows to drop. *)
definition rows_to_keep:: "('a::field) mat \<Rightarrow> nat list" where
  "rows_to_keep A = map snd (pivot_positions (gauss_jordan_single (A\<^sup>T)))"

fun reduction_step:: "rat mat \<Rightarrow> rat list list \<Rightarrow> nat list list \<Rightarrow> rat vec \<Rightarrow> rat mat \<times> (nat list list \<times> rat list list)"
  where "reduction_step A signs subsets lhs_vec = 
    (let reduce_cols_A = (reduce_mat_cols A lhs_vec);
         rows_keep = rows_to_keep reduce_cols_A in
    (take_rows_from_matrix  reduce_cols_A rows_keep,
      (take_indices subsets rows_keep,
      take_indices signs (find_nonzeros_from_input_vec lhs_vec))))"

fun reduce_system:: "real poly \<Rightarrow> (real poly list \<times> (rat mat \<times> (nat list list \<times> rat list list))) \<Rightarrow> (rat mat \<times> (nat list list \<times> rat list list))"
  where "reduce_system p (qs,m,subs,signs) =
    reduction_step m signs subs (solve_for_lhs p qs subs m)" 

section "Overall algorithm "
  (* 
    Find the matrix, subsets, signs for an input p and qs.
    The "rat mat" in the output is the matrix. The "nat list list" is the list of subsets. 
    The "rat list list" is the list of signs.

    We will want to call this when p is nonzero and when every q in qs is pairwise coprime to p.
    Properties of this algorithm are proved in BKR_Proofs.thy. 
  *)
fun calculate_data:: "real poly \<Rightarrow> real poly list \<Rightarrow>  (rat mat \<times> (nat list list \<times> rat list list))"
  where
    "calculate_data p qs = 
  ( let len = length qs in
    if len = 0 then
      (\<lambda>(a,b,c).(a,b,map (drop 1) c)) (reduce_system p ([1],base_case_info))
    else if len \<le> 1 then reduce_system p (qs,base_case_info)
    else
    (let q1 = take (len div 2) qs; left = calculate_data p q1;
         q2 = drop (len div 2) qs; right = calculate_data p q2;
         comb = combine_systems p (q1,left) (q2,right) in
         reduce_system p comb
    )
  )"

(* Extract the list of consistent sign assignments *)
definition find_consistent_signs_at_roots:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list"
  where [code]:
    "find_consistent_signs_at_roots p qs =
  ( let (M,S,\<Sigma>) = calculate_data p qs in \<Sigma> )"

lemma find_consistent_signs_at_roots_thm:
  shows "find_consistent_signs_at_roots p qs = snd (snd (calculate_data p qs))"
  by (simp add: case_prod_beta find_consistent_signs_at_roots_def)

end