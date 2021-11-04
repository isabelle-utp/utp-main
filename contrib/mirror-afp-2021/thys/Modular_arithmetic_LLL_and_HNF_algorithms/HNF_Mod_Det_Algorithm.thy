
section \<open>Formalization of an efficient Hermite normal form algorithm\<close>

text \<open>We formalize a version of the Hermite normal form algorithm based on reductions modulo
the determinant. This avoids the growth of the intermediate coefficients.\<close>

subsection \<open>Implementation of the algorithm using generic modulo operation\<close>

text \<open>Exception on generic modulo: currently in Hermite-reduce-above, ordinary div/mod is used,
  since that is our choice for the complete set of residues.\<close>

theory HNF_Mod_Det_Algorithm
  imports
    Jordan_Normal_Form.Gauss_Jordan_IArray_Impl
    Show.Show_Instances
    Jordan_Normal_Form.Determinant_Impl
    Jordan_Normal_Form.Show_Matrix
    LLL_Basis_Reduction.LLL_Certification   
    Smith_Normal_Form.SNF_Algorithm_Euclidean_Domain
    Smith_Normal_Form.SNF_Missing_Lemmas
    Uniqueness_Hermite_JNF
    Matrix_Change_Row
begin

subsubsection \<open>Echelon form algorithm\<close>

fun make_first_column_positive :: "int mat \<Rightarrow> int mat" where
  "make_first_column_positive A = (
       Matrix.mat (dim_row A) (dim_col A) \<comment> \<open> Create a matrix of the same dimensions \<close>
          (\<lambda>(i,j). if A $$(i,0) < 0 then - A $$(i,j) else A $$(i,j)
            )
  )"


locale mod_operation =
  fixes generic_mod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "gmod" 70)
    and generic_div :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "gdiv" 70)
begin

text \<open>Version for reducing all elements\<close>

fun reduce :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat" where
  "reduce a b D A = (let Aaj = A$$(a,0); Abj = A $$ (b,0)     
  in
  if Aaj = 0 then A else
  case euclid_ext2 Aaj Abj of (p,q,u,v,d) \<Rightarrow> \<comment> \<open> p*Aaj + q * Abj = d, u = - Abj/d, v = Aaj/d \<close>
       Matrix.mat (dim_row A) (dim_col A) \<comment> \<open> Create a matrix of the same dimensions \<close>
          (\<lambda>(i,k). if i = a then let r = (p*A$$(a,k) + q*A$$(b,k)) in
                              if k = 0 then if D dvd r then D else r else r gmod D \<comment> \<open> Row a is multiplied by p and added row b multiplied by q, modulo D\<close>
                   else if i = b then let r = u * A$$(a,k) + v * A$$(b,k) in
                               if k = 0 then r else r gmod D \<comment> \<open> Row b is multiplied by v and added row a multiplied by u, modulo D\<close>
                   else A$$(i,k)  \<comment> \<open> All the other rows remain unchanged\<close>
            )
  )"

text \<open>Version for reducing, with abs-checking\<close>

fun reduce_abs :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat" where
  "reduce_abs a b D A = (let Aaj = A$$(a,0); Abj = A $$ (b,0)     
  in
  if Aaj = 0 then A else
  case euclid_ext2 Aaj Abj of (p,q,u,v,d) \<Rightarrow> \<comment> \<open> p*Aaj + q * Abj = d, u = - Abj/d, v = Aaj/d \<close>
       Matrix.mat (dim_row A) (dim_col A) \<comment> \<open> Create a matrix of the same dimensions \<close>
          (\<lambda>(i,k). if i = a then let r = (p*A$$(a,k) + q*A$$(b,k)) in
                            if abs r > D then if k = 0 \<and> D dvd r then D else r gmod D else r 
                   else if i = b then let r = u * A$$(a,k) + v * A$$(b,k) in
                              if abs r > D then r gmod D else r
                   else A$$(i,k)  \<comment> \<open> All the other rows remain unchanged\<close>
            )
  )"

definition reduce_impl :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat" where
  "reduce_impl a b D A = (let 
    row_a = Matrix.row A a; 
    Aaj = row_a $v 0     
  in
  if Aaj = 0 then A else let 
    row_b = Matrix.row A b;
    Abj = row_b $v 0 in
  case euclid_ext2 Aaj Abj of (p,q,u,v,d) \<Rightarrow> 
    let row_a' = (\<lambda> k ak. let r = (p * ak + q * row_b $v k) in
              if k = 0 then if D dvd r then D else r else r gmod D);
        row_b' = (\<lambda> k bk. let r = u * row_a $v k + v * bk in
                               if k = 0 then r else r gmod D)
     in change_row a row_a' (change_row b row_b' A)
  )"

definition reduce_abs_impl :: "nat \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat" where
  "reduce_abs_impl a b D A = (let 
    row_a = Matrix.row A a; 
    Aaj = row_a $v 0     
  in
  if Aaj = 0 then A else let 
    row_b = Matrix.row A b;
    Abj = row_b $v 0 in
  case euclid_ext2 Aaj Abj of (p,q,u,v,d) \<Rightarrow> 
    let row_a' = (\<lambda> k ak. let r = (p * ak + q * row_b $v k) in
              if abs r > D then if k = 0 \<and> D dvd r then D else r gmod D else r);
        row_b' = (\<lambda> k bk. let r = u * row_a $v k + v * bk in
                                if abs r > D then r gmod D else r)
     in change_row a row_a' (change_row b row_b' A)
  )"

lemma reduce_impl: "a < nr \<Longrightarrow> b < nr \<Longrightarrow> 0 < nc \<Longrightarrow> a \<noteq> b \<Longrightarrow> A \<in> carrier_mat nr nc
  \<Longrightarrow> reduce_impl a b D A = reduce a b D A" 
  unfolding reduce_impl_def reduce.simps Let_def
  apply (intro if_cong[OF _ refl], force)
  apply (intro prod.case_cong refl, force)
  apply (intro eq_matI, auto)
  done


lemma reduce_abs_impl: "a < nr \<Longrightarrow> b < nr \<Longrightarrow> 0 < nc \<Longrightarrow> a \<noteq> b \<Longrightarrow> A \<in> carrier_mat nr nc
  \<Longrightarrow> reduce_abs_impl a b D A = reduce_abs a b D A" 
  unfolding reduce_abs_impl_def reduce_abs.simps Let_def
  apply (intro if_cong[OF _ refl], force)
  apply (intro prod.case_cong refl, force)
  apply (intro eq_matI, auto)
  done
  

(* This functions reduce the elements below the position (a,0), given a list of positions 
   of non-zero positions as input*)
fun reduce_below :: "nat \<Rightarrow> nat list \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat"
where "reduce_below a [] D A = A"
  | "reduce_below a (x # xs) D A = reduce_below a xs D (reduce a x D A)"

fun reduce_below_impl :: "nat \<Rightarrow> nat list \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat"
where "reduce_below_impl a [] D A = A"
  | "reduce_below_impl a (x # xs) D A = reduce_below_impl a xs D (reduce_impl a x D A)"

lemma reduce_impl_carrier[simp,intro]: "A \<in> carrier_mat m n \<Longrightarrow> reduce_impl a b D A \<in> carrier_mat m n" 
  unfolding reduce_impl_def Let_def by (auto split: prod.splits)

lemma reduce_below_impl: "a < nr \<Longrightarrow> 0 < nc \<Longrightarrow> (\<And> b. b \<in> set bs \<Longrightarrow> b < nr) \<Longrightarrow> a \<notin> set bs 
  \<Longrightarrow> A \<in> carrier_mat nr nc \<Longrightarrow> reduce_below_impl a bs D A = reduce_below a bs D A" 
proof (induct bs arbitrary: A)
  case (Cons b bs A)
  show ?case by (simp del: reduce.simps, 
      subst reduce_impl[of _ nr _ nc], 
      (insert Cons, auto simp del: reduce.simps)[5],
      rule Cons(1), insert Cons(2-), auto simp: Let_def split: prod.splits)
qed simp



fun reduce_below_abs :: "nat \<Rightarrow> nat list \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat"
where "reduce_below_abs a [] D A = A"
  | "reduce_below_abs a (x # xs) D A = reduce_below_abs a xs D (reduce_abs a x D A)"

fun reduce_below_abs_impl :: "nat \<Rightarrow> nat list \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat"
where "reduce_below_abs_impl a [] D A = A"
  | "reduce_below_abs_impl a (x # xs) D A = reduce_below_abs_impl a xs D (reduce_abs_impl a x D A)"

lemma reduce_abs_impl_carrier[simp,intro]: "A \<in> carrier_mat m n \<Longrightarrow> reduce_abs_impl a b D A \<in> carrier_mat m n" 
  unfolding reduce_abs_impl_def Let_def by (auto split: prod.splits)

lemma reduce_abs_below_impl: "a < nr \<Longrightarrow> 0 < nc \<Longrightarrow> (\<And> b. b \<in> set bs \<Longrightarrow> b < nr) \<Longrightarrow> a \<notin> set bs 
  \<Longrightarrow> A \<in> carrier_mat nr nc \<Longrightarrow> reduce_below_abs_impl a bs D A = reduce_below_abs a bs D A" 
proof (induct bs arbitrary: A)
  case (Cons b bs A)
  show ?case by (simp del: reduce_abs.simps, 
      subst reduce_abs_impl[of _ nr _ nc], 
      (insert Cons, auto simp del: reduce_abs.simps)[5],
      rule Cons(1), insert Cons(2-), auto simp: Let_def split: prod.splits)
qed simp

text \<open>This function outputs a matrix in echelon form via reductions modulo the determinant\<close>


function FindPreHNF :: "bool \<Rightarrow> int \<Rightarrow> int mat \<Rightarrow> int mat"
  where "FindPreHNF abs_flag D A = 
  (let m = dim_row A; n = dim_col A in 
  if m < 2 \<or> n = 0 then A else \<comment> \<open> No operations are carried out if m = 1 \<close>
  let non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A];
         A' = (if A$$(0,0) \<noteq> 0 then A
              else let i = non_zero_positions ! 0  \<comment> \<open> Select the first non-zero position below the first element\<close>
                   in swaprows 0 i A  
              );
        Reduce = (if abs_flag then reduce_below_abs else reduce_below)
    in
      if n < 2 then Reduce 0 non_zero_positions D A'  \<comment> \<open> If n = 1, then we have to reduce the column \<close>   
    else 
      let         
        (A_UL,A_UR,A_DL,A_DR) = split_block (Reduce 0 non_zero_positions D (make_first_column_positive A')) 1 1; 
        sub_PreHNF = FindPreHNF abs_flag D A_DR in       
        four_block_mat A_UL A_UR A_DL sub_PreHNF)"                 
  by auto termination 
proof (relation "Wellfounded.measure (\<lambda>(abs_flag,D,A). dim_col A)")
  show "wf (Wellfounded.measure (\<lambda>(abs_flag,D, A). dim_col A))" by auto
  fix abs_flag D A m n nz A' R xd A'_UL y A'_UR ya A'_DL A'_DR
  assume m: "m = dim_row A" and n:"n = dim_col A"
    and m2: "\<not> (m < 2 \<or> n = 0)" and nz_def: "nz = filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A] "
    and A'_def: "A' = (if A $$ (0, 0) \<noteq> 0 then A else let i = nz ! 0 in swaprows 0 i A)"
    and R_def: "R = (if abs_flag then reduce_below_abs else reduce_below)"
    and n2: "\<not> n < 2" and "xd = split_block (R 0 nz D (make_first_column_positive A')) 1 1"
    and "(A'_UL, y) = xd" and "(A'_UR, ya) = y" and "(A'_DL, A'_DR) = ya" 
  hence A'_split: "(A'_UL, A'_UR, A'_DL, A'_DR) 
        = split_block (R 0 nz D (make_first_column_positive A')) 1 1" by force
  have dr_mk1: "dim_row (make_first_column_positive A) = dim_row A" for A by auto
  have dr_mk2: "dim_col (make_first_column_positive A) = dim_col A" for A by auto  
  have r1: "reduce_below a xs D A \<in> carrier_mat m n" if "A \<in> carrier_mat m n" for A a xs
    using that by (induct a xs D A rule: reduce_below.induct, auto simp add: Let_def euclid_ext2_def) 
  hence R: "(reduce_below 0 nz D (make_first_column_positive A')) \<in> carrier_mat m n"
    using A'_def m n 
    by (metis carrier_matI index_mat_swaprows(2,3) dr_mk1 dr_mk2)
  have "reduce_below_abs a xs D A \<in> carrier_mat m n" if "A \<in> carrier_mat m n" for A a xs
    using that by (induct a xs D A rule: reduce_below_abs.induct, auto simp add: Let_def euclid_ext2_def) 
  hence R2: "(reduce_below_abs 0 nz D (make_first_column_positive A')) \<in> carrier_mat m n"
    using A'_def m n 
    by (metis carrier_matI index_mat_swaprows(2,3) dr_mk1 dr_mk2)
 
  have "A'_DR \<in> carrier_mat (m-1) (n-1)"
    by (cases abs_flag; rule split_block(4)[OF A'_split[symmetric]],insert m2 n2 m n R_def R R2, auto)
  thus "((abs_flag, D, A'_DR),abs_flag, D, A) \<in> Wellfounded.measure (\<lambda>(abs_flag,D, A). dim_col A)" using n2 m2 n m by auto
qed

lemma FindPreHNF_code: "FindPreHNF abs_flag D A = 
  (let m = dim_row A; n = dim_col A in 
  if m < 2 \<or> n = 0 then A else 
  let non_zero_positions = filter (\<lambda>i. A $$ (i,0) \<noteq> 0) [1..<dim_row A];
         A' = (if A$$(0,0) \<noteq> 0 then A
              else let i = non_zero_positions ! 0 in swaprows 0 i A  
              );
         Reduce_impl = (if abs_flag then reduce_below_abs_impl else reduce_below_impl)
    in
      if n < 2 then Reduce_impl 0 non_zero_positions D A'   
    else 
      let         
        (A_UL,A_UR,A_DL,A_DR) = split_block (Reduce_impl 0 non_zero_positions D (make_first_column_positive A')) 1 1; 
        sub_PreHNF = FindPreHNF abs_flag D A_DR in       
        four_block_mat A_UL A_UR A_DL sub_PreHNF)"  (is "?lhs = ?rhs")
proof -
  let ?f = "\<lambda>R. (if dim_row A < 2 \<or> dim_col A = 0 then A else if dim_col A < 2
          then R 0 (filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A]) D
  (if A $$ (0, 0) \<noteq> 0 then A else swaprows 0 (filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A] ! 0) A)
  else case split_block (R 0 (filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A]) D
    (make_first_column_positive (if A $$ (0, 0) \<noteq> 0 then A else 
      swaprows 0 (filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A] ! 0) A))) 1 1 of
  (A_UL, A_UR, A_DL, A_DR) \<Rightarrow> four_block_mat A_UL A_UR A_DL (FindPreHNF abs_flag D A_DR))"
  have M_carrier: "make_first_column_positive (if A $$ (0, 0) \<noteq> 0 then A 
    else swaprows 0 (filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A] ! 0) A) 
    \<in> carrier_mat (dim_row A) (dim_col A)"
    by (smt (z3) index_mat_swaprows(2) index_mat_swaprows(3) make_first_column_positive.simps mat_carrier)
  have *: "0 \<notin> set (filter (\<lambda>i. A $$ (i, 0) \<noteq> 0) [1..<dim_row A])" by simp
  have "?lhs = ?f (if abs_flag then reduce_below_abs else reduce_below)"
    unfolding FindPreHNF.simps[of abs_flag D A] Let_def by presburger
  also have "... = ?rhs"
  proof (cases abs_flag)
    case True
    have "?f (if abs_flag then reduce_below_abs else reduce_below) = ?f reduce_below_abs" 
      using True by presburger
    also have "... = ?f reduce_below_abs_impl" 
      by ((intro if_cong refl prod.case_cong arg_cong[of _ _ "\<lambda> x. split_block x 1 1"];
       (subst reduce_abs_below_impl[where nr = "dim_row A" and nc = "dim_col A"])), (auto)[9])
       (insert M_carrier *, blast+)
    also have "... = ?f (if abs_flag then reduce_below_abs_impl else reduce_below_impl)" 
      using True by presburger
    finally show ?thesis using True unfolding FindPreHNF.simps[of abs_flag D A] Let_def by blast
  next
    case False
    have "?f (if abs_flag then reduce_below_abs else reduce_below) = ?f reduce_below" 
      using False by presburger
    also have "... = ?f reduce_below_impl" 
      by ((intro if_cong refl prod.case_cong arg_cong[of _ _ "\<lambda> x. split_block x 1 1"];
       (subst reduce_below_impl[where nr = "dim_row A" and nc = "dim_col A"])), (auto)[9])
       (insert M_carrier *, blast+)
    also have "... = ?f (if abs_flag then reduce_below_abs_impl else reduce_below_impl)" 
      using False by presburger
    finally show ?thesis using False unfolding FindPreHNF.simps[of abs_flag D A] Let_def by blast
  qed
  finally show ?thesis by blast
qed
end

declare mod_operation.FindPreHNF_code[code]
declare mod_operation.reduce_below_impl.simps[code]
declare mod_operation.reduce_impl_def[code]
declare mod_operation.reduce_below_abs_impl.simps[code]
declare mod_operation.reduce_abs_impl_def[code]

subsubsection \<open>From echelon form to Hermite normal form\<close>

text \<open>From here on, we define functions to transform a matrix in echelon form into its Hermite
normal form. Essentially, we are defining the functions that are available in the AFP entry Hermite
(which uses HOL Analysis + mod-type) in the JNF matrix representation.\<close>

(*Find the first nonzero element of row l (A is upper triangular)*)
definition find_fst_non0_in_row :: "nat \<Rightarrow> int mat \<Rightarrow> nat option" where
  "find_fst_non0_in_row l A = (let is = [l ..< dim_col A];
    Ais = filter (\<lambda>j. A $$ (l, j) \<noteq> 0) is
    in case Ais of [] \<Rightarrow> None | _ \<Rightarrow> Some (Ais!0))"

primrec Hermite_reduce_above
where "Hermite_reduce_above (A::int mat) 0 i j = A"
    | "Hermite_reduce_above A (Suc n) i j = (let
    Aij = A $$ (i,j);
    Anj = A $$ (n,j)
    in 
    Hermite_reduce_above (addrow (- (Anj div Aij)) n i A) n i j)"

definition Hermite_of_row_i :: "int mat \<Rightarrow> nat \<Rightarrow> int mat" 
  where "Hermite_of_row_i A i = (
  case find_fst_non0_in_row i A of None \<Rightarrow> A | Some j \<Rightarrow> 
    let Aij = A $$(i,j) in
    if Aij < 0 then Hermite_reduce_above (multrow i (-1) A) i i j
    else Hermite_reduce_above A i i j)"


primrec Hermite_of_list_of_rows 
  where
 "Hermite_of_list_of_rows A [] = A" | 
 "Hermite_of_list_of_rows A (a#xs) = Hermite_of_list_of_rows (Hermite_of_row_i A a) xs"

text \<open>We combine the previous functions to assemble the algorithm\<close>

definition (in mod_operation) "Hermite_mod_det abs_flag A = 
  (let m = dim_row A; n = dim_col A; 
   D = abs(det_int A); 
   A' = A @\<^sub>r D \<cdot>\<^sub>m 1\<^sub>m n;
   E = FindPreHNF abs_flag D A';
   H = Hermite_of_list_of_rows E [0..<m+n]
  in mat_of_rows n (map (Matrix.row H) [0..<m]))"

subsubsection \<open>Some examples of execution\<close>

declare mod_operation.Hermite_mod_det_def[code]

value "let B = mat_of_rows_list 4 ([[0,3,1,4],[7,1,0,0],[8,0,19,16],[2,0,0,3::int]]) in
  show (mod_operation.Hermite_mod_det (mod) True B)"

(*
sage: import sage.matrix.matrix_integer_dense_hnf as matrix_integer_dense_hnf
sage: A = matrix(ZZ, [[0,3,1,4],[7,1,0,0],[8,0,19,16],[2,0,0,3]])
sage: A
[ 0  3  1  4]
[ 7  1  0  0]
[ 8  0 19 16]
[ 2  0  0  3]
sage:  H, U = matrix_integer_dense_hnf.hnf_with_transformation(A); H
[   1    0    0  672]
[   0    1    0  660]
[   0    0    1  706]
[   0    0    0 1341]
sage: 
*)


value "let B = mat_of_rows_list 7 ([
[  1,  17, -41,  -1,   1,   0,  0],
[  0,  -1,   2,   0,  -6,   2,   1],
[  9,   2,   1,   1,  -2,   2,  -5],
[ -1,  -3,  -1,   0,  -9,   0,   0],
[  9,  -1,  -9,   0,   0,   0,   1],
[  1,  -1,   1,   0,   1,  -8,   0],
[  1,  -1,   0,  -2,  -1,  -1,   0::int]]) in 
  show (mod_operation.Hermite_mod_det (mod) True B)"

(*
sage: import sage.matrix.matrix_integer_dense_hnf as matrix_integer_dense_hnf
sage: A = random_matrix(ZZ,7,7); A
[  1  17 -41  -1   1   0   0]
[  0  -1   2   0  -6   2   1]
[  9   2   1   1  -2   2  -5]
[ -1  -3  -1   0  -9   0   0]
[  9  -1  -9   0   0   0   1]
[  1  -1   1   0   1  -8   0]
[  1  -1   0  -2  -1  -1   0]
sage: H, U = matrix_integer_dense_hnf.hnf_with_transformation(A); H
[     1      0      0      0      0      1 191934]
[     0      1      0      0      0      0 435767]
[     0      0      1      0      0      1 331950]
[     0      0      0      1      0      0 185641]
[     0      0      0      0      1      0  38022]
[     0      0      0      0      0      2 477471]
[     0      0      0      0      0      0 565304]
*)

end