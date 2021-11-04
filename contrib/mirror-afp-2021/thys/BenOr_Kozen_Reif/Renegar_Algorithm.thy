theory Renegar_Algorithm
  imports  BKR_Algorithm
begin

(* There is significant overlap between Renegar's algorithm and BKR's.  
  However, the RHS vector is constructed differently in Renegar. The base case is also different.
  In general, the _R's on definition and lemma names in this file are to emphasize that we are 
  working with Renegar style.
*)

definition construct_NofI_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> real poly list \<Rightarrow> rat"
  where "construct_NofI_R p I1 I2 = (
    let new_p = sum_list (map (\<lambda>x. x^2) (p # I1)) in
    rat_of_int (changes_R_smods new_p ((pderiv new_p)*(prod_list I2))))"

(* Renegar's RHS vector will have type (nat list * nat list) list.
   Note the change from BKR, where the RHS vector had type nat list list*)
definition construct_rhs_vector_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> (nat list * nat list) list \<Rightarrow> rat vec"
  where "construct_rhs_vector_R p qs Is =
  vec_of_list (map (\<lambda>(I1,I2).
    (construct_NofI_R p (retrieve_polys qs I1) (retrieve_polys qs I2))) Is)"

section "Base Case"

(* Renegar's matrix is 3x3 instead of 2x2 *)
definition base_case_info_R:: "(rat mat \<times> ((nat list * nat list) list \<times> rat list list))"
  where "base_case_info_R =
    ((mat_of_rows_list 3 [[1,1,1], [0,1,0], [1,0,-1]]),([([], []),([0], []),([], [0])], [[1],[0],[-1]]))"

(* When p, q are coprime, this will actually be an int vec, which is why taking the floor is okay *)
definition base_case_solve_for_lhs:: "real poly \<Rightarrow> real poly \<Rightarrow> rat vec"
  where "base_case_solve_for_lhs p q = (mult_mat_vec (mat_of_rows_list 3 [[1/2, -1/2, 1/2], [0, 1, 0], [1/2, -1/2, -1/2]])  (construct_rhs_vector_R p [q] [([], []),([0], []),([], [0])]))"

(* Solve for LHS in general: mat_inverse returns an option type, and we pattern match on this. 
  Notice that when we call this function in the algorithm, the matrix we pass will always be invertible,
  given how the construction works. *)
definition solve_for_lhs_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> (nat list * nat list) list \<Rightarrow> rat mat \<Rightarrow> rat vec"
  where "solve_for_lhs_R p qs subsets matr =
     mult_mat_vec (matr_option (dim_row matr) (mat_inverse_var matr))  (construct_rhs_vector_R p qs subsets)"

section "Smashing" 

definition subsets_smash_R::"nat \<Rightarrow> (nat list*nat list) list \<Rightarrow> (nat list*nat list) list \<Rightarrow> (nat list*nat list) list"
  where "subsets_smash_R n s1 s2 = concat (map (\<lambda>l1. map (\<lambda> l2. (((fst l1) @ (map ((+) n) (fst l2))), (snd l1) @ (map ((+) n) (snd l2)))) s2) s1)"

definition smash_systems_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> real poly list \<Rightarrow> (nat list * nat list) list \<Rightarrow> (nat list * nat list) list \<Rightarrow>
  rat list list \<Rightarrow> rat list list \<Rightarrow> rat mat \<Rightarrow> rat mat \<Rightarrow> 
  real poly list \<times> (rat mat \<times> ((nat list * nat list) list \<times> rat list list))"
  where "smash_systems_R p qs1 qs2 subsets1 subsets2 signs1 signs2 mat1 mat2 =
    (qs1@qs2, (kronecker_product mat1 mat2, (subsets_smash_R (length qs1) subsets1 subsets2, signs_smash signs1 signs2)))"

fun combine_systems_R:: "real poly \<Rightarrow> (real poly list \<times> (rat mat \<times> ((nat list * nat list) list \<times> rat list list))) \<Rightarrow> (real poly list \<times> (rat mat \<times> ((nat list * nat list) list \<times> rat list list)))
  \<Rightarrow> (real poly list \<times> (rat mat \<times> ((nat list * nat list) list \<times> rat list list)))"
  where "combine_systems_R p (qs1, m1, sub1, sgn1) (qs2, m2, sub2, sgn2) = 
    (smash_systems_R p qs1 qs2 sub1 sub2 sgn1 sgn2 m1 m2)"

(* Overall:
  Start with a matrix equation.
  Input a matrix, subsets, and signs.
  Drop columns of the matrix based on the 0's on the LHS---so extract a list of 0's. Reduce signs accordingly.
  Then find a list of rows to delete based on using rank (use the transpose result, pivot positions!),
   and delete those rows.  Reduce subsets accordingly.
  End with a reduced system! *)
section "Reduction"

fun reduction_step_R:: "rat mat \<Rightarrow> rat list list \<Rightarrow> (nat list*nat list) list \<Rightarrow> rat vec \<Rightarrow> rat mat \<times> ((nat list*nat list) list \<times> rat list list)"
  where "reduction_step_R A signs subsets lhs_vec = 
    (let reduce_cols_A = (reduce_mat_cols A lhs_vec);
         rows_keep = rows_to_keep reduce_cols_A in
    (take_rows_from_matrix  reduce_cols_A rows_keep,
      (take_indices subsets rows_keep,
      take_indices signs (find_nonzeros_from_input_vec lhs_vec))))"

fun reduce_system_R:: "real poly \<Rightarrow> (real poly list \<times> (rat mat \<times> ((nat list*nat list) list \<times> rat list list))) \<Rightarrow> (rat mat \<times> ((nat list*nat list) list \<times> rat list list))"
  where "reduce_system_R p (qs,m,subs,signs) =
    reduction_step_R m signs subs (solve_for_lhs_R p qs subs m)" 

section "Overall algorithm "
(* Find matrix, subsets, signs.
   The "rat mat" in the output is the matrix. The "(nat list*nat list) list" is the list of subsets. 
   The "rat list list" is the list of signs.
*)
fun calculate_data_R:: "real poly \<Rightarrow> real poly list \<Rightarrow>  (rat mat \<times> ((nat list*nat list) list \<times> rat list list))"
  where
  "calculate_data_R p qs = 
  ( let len = length qs in
    if len = 0 then
      (\<lambda>(a,b,c).(a,b,map (drop 1) c)) (reduce_system_R p ([1],base_case_info_R))
    else if len \<le> 1 then reduce_system_R p (qs,base_case_info_R)
    else
    (let q1 = take (len div 2) qs; left = calculate_data_R p q1;
         q2 = drop (len div 2) qs; right = calculate_data_R p q2;
         comb = combine_systems_R p (q1,left) (q2,right) in
         reduce_system_R p comb
    )
  )"

(* Extract the list of consistent sign assignments *)
definition find_consistent_signs_at_roots_R:: "real poly \<Rightarrow> real poly list \<Rightarrow> rat list list"
  where [code]:
  "find_consistent_signs_at_roots_R p qs =
  ( let (M,S,\<Sigma>) = calculate_data_R p qs in \<Sigma> )"

lemma find_consistent_signs_at_roots_thm_R:
  shows "find_consistent_signs_at_roots_R p qs = snd (snd (calculate_data_R p qs))"
  by (simp add: case_prod_beta find_consistent_signs_at_roots_R_def)

end