(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>A general algorithm to transform a matrix into its Smith normal form\<close>

theory SNF_Algorithm
  imports    
    Smith_Normal_Form_JNF
begin

text \<open>This theory presents an executable algorithm to transform a matrix
to its Smith normal form.\<close>

subsection \<open>Previous definitions and lemmas\<close>

definition "is_SNF A R = (case R of (P,S,Q) \<Rightarrow> 
  P \<in> carrier_mat (dim_row A) (dim_row A) \<and>
  Q \<in> carrier_mat (dim_col A) (dim_col A) 
  \<and> invertible_mat P \<and> invertible_mat Q 
  \<and> Smith_normal_form_mat S \<and> S = P * A * Q)"


lemma is_SNF_intro: 
  assumes "P \<in> carrier_mat (dim_row A) (dim_row A)"
  and "Q \<in> carrier_mat (dim_col A) (dim_col A) "
  and "invertible_mat P" and "invertible_mat Q" 
  and "Smith_normal_form_mat S" and "S = P * A * Q"
shows "is_SNF A (P,S,Q)" using assms unfolding is_SNF_def by auto


(*With the following lemmas, we show that for the case 1xn only column operations are needed
  and the algorithm just needs to return two matrices.*)

lemma Smith_1xn_two_matrices:
  fixes A :: "'a::comm_ring_1 mat"
  assumes A: "A \<in> carrier_mat 1 n" 
  and PSQ: "(P,S,Q) = (Smith_1xn A)"
  and is_SNF: "is_SNF A (Smith_1xn A)"
shows "\<exists>Smith_1xn'. is_SNF A (1\<^sub>m 1, (Smith_1xn' A))"
proof -
  let ?Q = "P$$(0,0) \<cdot>\<^sub>m Q"
  have P00_dvd_1: "P $$ (0, 0) dvd 1"
    by (metis (mono_tags, lifting) assms carrier_matD(1) determinant_one_element 
        invertible_iff_is_unit_JNF is_SNF_def prod.simps(2))
  have "is_SNF A (1\<^sub>m 1,S,?Q)"
  proof (rule is_SNF_intro)
    show "invertible_mat (P $$ (0, 0) \<cdot>\<^sub>m Q)"
      by (rule invertible_mat_smult_mat, insert P00_dvd_1 assms, auto simp add: is_SNF_def)
    show "S = 1\<^sub>m 1 * A * (P $$ (0, 0) \<cdot>\<^sub>m Q)" 
      by (smt A PSQ is_SNF carrier_matD(2) index_mult_mat(2) index_one_mat(2) left_mult_one_mat
          mult_smult_assoc_mat mult_smult_distrib smult_mat_mat_one_element is_SNF_def split_conv)      
  qed (insert assms, auto simp add: is_SNF_def)
  thus ?thesis by auto
qed

lemma Smith_1xn_two_matrices_all:
  assumes is_SNF: "\<forall>(A::'a::comm_ring_1 mat) \<in> carrier_mat 1 n. is_SNF A (Smith_1xn A)"
  shows "\<exists>Smith_1xn'. \<forall>(A::'a::comm_ring_1 mat) \<in> carrier_mat 1 n. is_SNF A (1\<^sub>m 1, (Smith_1xn' A))"
proof -
  let ?Smith_1xn' = "\<lambda>A. let (P,S,Q) = (Smith_1xn A) in (S, P $$ (0, 0) \<cdot>\<^sub>m Q)"
  show ?thesis by (rule exI[of _ ?Smith_1xn']) (smt Smith_1xn_two_matrices assms carrier_matD 
        carrier_matI case_prodE determinant_one_element index_smult_mat(2,3) invertible_iff_is_unit_JNF
        invertible_mat_smult_mat smult_mat_mat_one_element left_mult_one_mat is_SNF_def 
        mult_smult_assoc_mat mult_smult_distrib prod.simps(2))
qed

subsection \<open>Previous operations\<close>
(*Reduce column, parameterized by a div operation*)
context 
assumes "SORT_CONSTRAINT('a::comm_ring_1)"
begin

definition is_div_op :: "('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow>bool"
  where "is_div_op div_op = (\<forall>a b. b dvd a \<longrightarrow> div_op a b * b = a)"

(* With SOME, we can get a (non-executable) div operation:*)
lemma div_op_SOME: "is_div_op (\<lambda>a b. (SOME k. k * b = a))"
proof (unfold is_div_op_def, rule+)
  fix a b::'a assume dvd: "b dvd a" 
  show "(SOME k. k * b = a) * b = a" by (rule someI_ex, insert dvd dvd_def) (metis dvdE mult.commute)
qed

fun reduce_column_aux :: "('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> nat list \<Rightarrow> 'a mat \<Rightarrow> ('a mat \<times> 'a mat) \<Rightarrow> ('a mat \<times> 'a mat)"
  where "reduce_column_aux div_op [] H (P,K) = (P,K)" 
  | "reduce_column_aux div_op (i#xs) H (P,K) = (
    \<comment> \<open>Reduce the i-th row\<close>
    let k = div_op (H$$(i,0)) (H $$ (0, 0));
        P' = addrow_mat (dim_row H) (-k) i 0;
        K' = addrow (-k) i 0 K
  in reduce_column_aux div_op xs H (P'*P,K')    
  )"

definition "reduce_column div_op H = reduce_column_aux div_op [2..<dim_row H] H (1\<^sub>m (dim_row H),H)"


lemma reduce_column_aux:
  assumes H: "H \<in> carrier_mat m n" 
    and P_init: "P_init \<in> carrier_mat m m"
    and K_init: "K_init \<in> carrier_mat m n"
  and P_init_H_K_init: "P_init * H = K_init"
  and PK_H: "(P,K) = reduce_column_aux div_op xs H (P_init,K_init)"
  and m: "0 < m"
  and inv_P: "invertible_mat P_init"
  and xs: "0 \<notin> set xs"
shows "P \<in> carrier_mat m m \<and> K \<in> carrier_mat m n \<and> P * H = K \<and> invertible_mat P"
  using assms
  unfolding reduce_column_def
proof (induct div_op xs H "(P_init,K_init)" arbitrary: P_init K_init rule: reduce_column_aux.induct)
  case (1 div_op H P K)
  then show ?case by simp
next
  case (2 div_op i xs H P_init K_init)  
  show ?case
  proof (rule "2.hyps")
      let ?x = "div_op (H $$ (i, 0)) (H $$ (0, 0))"
      let ?xa = "addrow_mat (dim_row H) (- ?x) i 0"
      let ?xb = "addrow (- ?x) i 0 K_init"
      show "(P, K) = reduce_column_aux div_op xs H (?xa * P_init, ?xb)" 
        using "2.prems" by (auto simp add: Let_def)
      show "?xa * P_init \<in> carrier_mat m m" using "2"(2) "2"(3) by auto
      show "0 \<notin> set xs" using "2.prems" by auto
      have "?xa * K_init = ?xb" 
        by (rule addrow_mat[symmetric], insert "2.prems", auto)                  
      thus "?xa * P_init * H = ?xb"
        by (metis (no_types, lifting) "2"(5) "2.prems"(1) "2.prems"(2) addrow_mat_carrier 
            assoc_mult_mat carrier_matD(1))
      show "invertible_mat (?xa * P_init)" 
      proof (rule invertible_mult_JNF)
        show xa: "?xa \<in> carrier_mat m m" using "2"(2) by auto        
        have "Determinant.det ?xa = 1" by (rule det_addrow_mat, insert "2.prems", auto)
        thus "invertible_mat ?xa" unfolding invertible_iff_is_unit_JNF[OF xa] by simp     
      qed (auto simp add: "2.prems")
    qed(auto simp add: "2.prems")
  qed


lemma reduce_column_aux_preserves:
  assumes H: "H \<in> carrier_mat m n" 
    and P_init: "P_init \<in> carrier_mat m m"
    and K_init: "K_init \<in> carrier_mat m n"
  and P_init_H_K_init: "P_init * H = K_init"
  and PK_H: "(P,K) = reduce_column_aux div_op xs H (P_init,K_init)"
  and m: "0 < m"
  and inv_P: "invertible_mat P_init"
  and xs: "0 \<notin> set xs"  and i: "i \<notin> set xs" and im: "i<m"
shows "Matrix.row K i = Matrix.row K_init i"
  using PK_H inv_P H P_init K_init m xs i
  unfolding reduce_column_def
proof (induct div_op xs H "(P_init,K_init)" arbitrary: P_init K_init K rule: reduce_column_aux.induct)
  case (1 div_op H P K)
  then show ?case by auto
next
  case (2 div_op x xs H P_init K_init)
  thm "2.prems"
  "2.hyps"
      let ?x = "div_op (H $$ (x, 0)) (H $$ (0, 0))"
      let ?xa = "addrow_mat (dim_row H) (- ?x) x 0"
      let ?xb = "addrow (- ?x) x 0 K_init"
      have IH: "Matrix.row K i = Matrix.row ?xb i"
      proof (rule "2.hyps")
        show "(P, K) = reduce_column_aux div_op xs H (?xa * P_init, ?xb)" 
          using "2.prems" by (auto simp add: Let_def)
        show "?xa * P_init \<in> carrier_mat m m"
          using "2"(4) "2"(5) by auto    
        have "?xa * K_init = ?xb" 
          by (rule addrow_mat[symmetric], insert "2.prems", auto)
        show "invertible_mat (?xa * P_init)" 
        proof (rule invertible_mult_JNF)
          show xa: "?xa \<in> carrier_mat m m" using "2.prems" by auto        
          have "Determinant.det ?xa = 1" by (rule det_addrow_mat, insert "2.prems", auto)
          thus "invertible_mat ?xa" unfolding invertible_iff_is_unit_JNF[OF xa] by simp     
        qed (auto simp add: "2.prems")
        show "i \<notin> set xs" using "2"(9) by auto
        show "0 \<notin> set xs" using "2"(8) by auto
      qed(auto simp add: "2.prems")
      also have "... = Matrix.row K_init i"
        by (rule eq_vecI, auto, insert "2" "2.prems" im, auto)    
      finally show ?case .    
qed

lemma reduce_column_aux_index':
  assumes H: "H \<in> carrier_mat m n" 
    and P_init: "P_init \<in> carrier_mat m m"
    and K_init: "K_init \<in> carrier_mat m n"
  and P_init_H_K_init: "P_init * H = K_init"
  and PK_H: "(P,K) = reduce_column_aux div_op xs H (P_init,K_init)"
  and m: "0 < m"
  and inv_P: "invertible_mat P_init"
  and xs: "0 \<notin> set xs"  
  and "\<forall>x\<in>set xs. x<m"
  and "distinct xs"
shows "(\<forall>i\<in>set xs. Matrix.row K i = 
    Matrix.row (addrow (-(div_op (H $$ (i, 0)) (H $$ (0, 0)))) i 0 K_init) i)"
  using assms
  unfolding reduce_column_def
proof (induct div_op xs H "(P_init,K_init)" arbitrary: P_init K_init K rule: reduce_column_aux.induct)
  case (1 div_op H P K)
  then show ?case by simp
next
  case (2 div_op i xs H P_init K_init)
  let ?x = "div_op (H $$ (i, 0)) (H $$ (0, 0)) "
  let ?xa = "addrow_mat (dim_row H) ?x i 0"
  thm "2.prems"
  thm "2.hyps"
  let ?xb = "addrow (- ?x) i 0 K_init"
  let ?xa = "addrow_mat (dim_row H) (- ?x) i 0"
  have "reduce_column_aux div_op (i#xs) H (P_init,K_init) 
    = reduce_column_aux div_op xs H (?xa*P_init,?xb)"
    by (auto simp add: Let_def)
  hence PK: "(P,K) = reduce_column_aux div_op xs H (?xa*P_init,?xb)" using "2.prems" by simp
      have xa_P_init:  "?xa * P_init \<in> carrier_mat m m" using "2"(2) "2"(3) by auto
      have zero_notin_xs: "0 \<notin> set xs" using "2.prems" by auto
      have "?xa * K_init = ?xb" 
        by (rule addrow_mat[symmetric], insert "2.prems", auto)                  
      hence rw: "?xa * P_init * H = ?xb"
        by (metis (no_types, lifting) "2"(5) "2.prems"(1) "2.prems"(2) addrow_mat_carrier 
            assoc_mult_mat carrier_matD(1))
      have inv_xa_P_init: "invertible_mat (?xa * P_init)" 
      proof (rule invertible_mult_JNF)
        show xa: "?xa \<in> carrier_mat m m" using "2"(2) by auto        
        have "Determinant.det ?xa = 1" by (rule det_addrow_mat, insert "2.prems", auto)
        thus "invertible_mat ?xa" unfolding invertible_iff_is_unit_JNF[OF xa] by simp     
      qed (auto simp add: "2.prems")
      have i1: "i\<noteq>0" using "2.prems"(8) by auto
      have i2: "i<m" by (simp add: "2.prems"(9))
      have i3: "i\<notin>set xs" using 2 by auto
      have d: "distinct xs" using 2 by auto
      have "\<forall>i\<in>set xs. Matrix.row K i = Matrix.row (addrow (- (div_op (H $$ (i, 0)) (H $$ (0, 0)))) 
            i 0 ?xb) i"
    by (rule "2.hyps", insert xa_P_init zero_notin_xs rw inv_xa_P_init d, 
        auto simp add: "2.prems" Let_def)  
  moreover have "Matrix.row (addrow (- (div_op (H $$ (j, 0)) (H $$ (0, 0)))) j 0 ?xb) j 
  = Matrix.row (addrow (- (div_op (H $$ (j, 0)) (H $$ (0, 0)))) j 0 K_init) j" 
    (is "Matrix.row ?lhs j= Matrix.row ?rhs j")
    if j: "j \<in> set xs" for j 
  proof (rule eq_vecI)
    fix ia assume ia: "ia<dim_vec(Matrix.row ?rhs j)"
    let ?k = "div_op (H $$ (j, 0)) (H $$ (0, 0))"
    let ?L = "(addrow (- (div_op (H $$ (i, 0)) (H $$ (0, 0)))) i 0 K_init)"
    have "Matrix.row ?lhs j $v ia = ?lhs $$ (j,ia)"
      by (metis (no_types, lifting) Matrix.row_def ia index_mat_addrow(5) index_row(2) index_vec)
    also have "... = (-?k) * ?L$$(0,ia) + ?L$$(j,ia)"      
      by (smt "2.prems"(1) "2.prems"(9) carrier_matD(1) ia index_mat_addrow(1,5) index_row(2) 
          insert_iff list.set(2) mult_carrier_mat rw that xa_P_init)
    also have "... = ?rhs $$ (j,ia)" using "2"(10) "2"(4) i1 i3 ia j by auto
    also have "... = Matrix.row ?rhs j $v ia" using 2 ia j by auto
    finally show "Matrix.row ?lhs j $v ia = Matrix.row ?rhs j $v ia" .
  qed (auto)
  ultimately have "\<forall>j\<in>set xs. Matrix.row K j = 
    Matrix.row (addrow (- (div_op (H $$ (j, 0)) (H $$ (0, 0)))) j 0 K_init) j" by auto
  moreover have "Matrix.row K i = Matrix.row ?xb i" 
     by (rule reduce_column_aux_preserves[OF _ xa_P_init _ rw PK _ inv_xa_P_init zero_notin_xs 
            i3 i2],insert "2.prems", auto)
   ultimately show ?case by auto
 qed

corollary reduce_column_aux_index:
  assumes H: "H \<in> carrier_mat m n" 
    and P_init: "P_init \<in> carrier_mat m m"
    and K_init: "K_init \<in> carrier_mat m n"
  and P_init_H_K_init: "P_init * H = K_init"
  and PK_H: "(P,K) = reduce_column_aux div_op xs H (P_init,K_init)"
  and m: "0 < m"
  and inv_P: "invertible_mat P_init"
  and xs: "0 \<notin> set xs"  
  and "\<forall>x\<in>set xs. x<m"
  and "distinct xs"
  and "i\<in>set xs"
shows "Matrix.row K i = 
    Matrix.row (addrow (-(div_op (H $$ (i, 0)) (H $$ (0, 0)))) i 0 K_init) i"
  using reduce_column_aux_index' assms by simp


corollary reduce_column_aux_works:
  assumes H: "H \<in> carrier_mat m n"           
  and PK_H: "(P,K) = reduce_column_aux div_op xs H (1\<^sub>m (dim_row H), H)"
  and m: "0 < m"
  and xs: "0 \<notin> set xs"  
  and xm: "\<forall>x \<in> set xs. x<m"
  and d_xs: "distinct xs"
  and i: "i \<in> set xs"
  and dvd: "H $$ (0, 0) dvd H $$ (i, 0)"
  and j0: "\<forall>j\<in>{1..<n}. H$$(0,j) = 0"
  and j1n: "j\<in>{1..<n}"
  and n: "0<n"
  and id: "is_div_op div_op"
shows "K $$ (i,0) = 0" and "K$$(i,j) = H $$ (i,j)" 
proof -
  let ?k = "div_op (H $$ (i, 0)) (H $$ (0, 0))"
  let ?L = "addrow (-?k) i 0 H"
  have kH00_eq_Hi0: "?k * H $$ (0, 0) = H $$ (i, 0)" 
    using id dvd unfolding is_div_op_def by simp
  have *: "Matrix.row K i = Matrix.row ?L i"
    by (rule reduce_column_aux_index[OF H _ _ _ PK_H], insert assms, auto)
  also have " ... $v 0 = ?L $$ (i,0)" by (rule index_row, insert xm i H n, auto)
  also have "... = (- ?k) * H$$(0,0) + H$$(i,0)" by (rule index_mat_addrow, insert i xm H n, auto)
  also have "... = 0" using kH00_eq_Hi0 by auto
  finally show "K $$ (i, 0) = 0"
    by (metis H Matrix.row_def * n carrier_matD(2) dim_vec index_mat_addrow(5) index_vec)
  have "Matrix.row ?L i $v j = ?L $$ (i,j)" by (rule index_row, insert xm i H n j1n, auto)
  also have "... = (- ?k) * H$$(0,j) + H$$(i,j)" by (rule index_mat_addrow, insert xm i H j1n, auto)
  also have "... = H$$(i,j)" using j1n j0 by auto
  finally show "K$$(i,j) = H $$ (i,j)" by (metis H * Matrix.row_def atLeastLessThan_iff 
        carrier_matD(2) dim_vec index_mat_addrow(5) index_vec j1n)
qed

lemma reduce_column:
  assumes H: "H \<in> carrier_mat m n"           
  and PK_H: "(P,K) = reduce_column div_op H"
  and m: "0 < m"
shows "P \<in> carrier_mat m m \<and> K \<in> carrier_mat m n \<and> P * H = K \<and> invertible_mat P"
  by (rule reduce_column_aux[OF _ _ _ _ PK_H[unfolded reduce_column_def]], insert assms, auto)

lemma reduce_column_preserves:
  assumes H: "H \<in> carrier_mat m n"           
  and PK_H: "(P,K) = reduce_column div_op H"
  and m: "0 < m"
  and "i\<in>{0,1}"
  and "i<m"
shows "Matrix.row K i = Matrix.row H i"
  by (rule reduce_column_aux_preserves[OF _ _ _ _ PK_H[unfolded reduce_column_def]], 
      insert assms, auto)

lemma reduce_column_preserves2:
  assumes H: "H \<in> carrier_mat m n"           
  and PK_H: "(P,K) = reduce_column div_op H"
  and m: "0 < m" and i: "i\<in>{0,1}" and im: "i<m" and j: "j<n"
shows "K $$ (i,j) = H $$ (i,j)"
  using reduce_column_preserves[OF H PK_H m i im]
  by (metis H Matrix.row_def j carrier_matD(2) dim_vec index_vec)
  

corollary reduce_column_works:
  assumes H: "H \<in> carrier_mat m n"           
  and PK_H: "(P,K) = reduce_column div_op H"
  and m: "0 < m"
  and dvd: "H $$ (0, 0) dvd H $$ (i, 0)"
  and j0: "\<forall>j\<in>{1..<n}. H $$ (0, j) = 0"
  and j1n: "j\<in>{1..<n}"
  and n: "0<n"
  and "i\<in>{2..<m}"
  and id: "is_div_op div_op"
shows "K $$ (i,0) = 0" and "K$$(i,j) = H $$ (i,j)" 
    by (rule reduce_column_aux_works[OF H PK_H[unfolded reduce_column_def]], insert assms, auto)+

end


subsection \<open>The implementation\<close>

text \<open>We define a locale where we implement the algorithm. It has three fixed operations:
\begin{enumerate}
\item an operation to transform any $1 \times 2$ matrix into its Smith normal form
\item an operation to transform any $2 \times 2$ matrix into its Smith normal form
\item an operation that provides a witness for division (this operation always exists over a 
      commutative ring with unit, but maybe we cannot provide a computable algorithm).
\end{enumerate}

Since we are working in a commutative ring, we can easily get an operation for $2 \times 1$ matrices
via the $1 \times 2$ operation.
\<close>
locale Smith_Impl =   
  fixes Smith_1x2 :: "('a::comm_ring_1) mat \<Rightarrow> ('a mat \<times> 'a mat)"
    and Smith_2x2 :: "'a mat \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat)"
    and div_op :: "'a\<Rightarrow>'a\<Rightarrow>'a"
  assumes SNF_1x2_works: "\<forall>(A::'a mat) \<in> carrier_mat 1 2. is_SNF A (1\<^sub>m 1, (Smith_1x2 A))" 
    and SNF_2x2_works: "\<forall>(A::'a mat) \<in> carrier_mat 2 2. is_SNF A (Smith_2x2 A)"
    and id: "is_div_op div_op"
begin

text \<open>From a $2 \times 2$ matrix (the $B$), we construct the identity matrix of size $n$ with 
the elements of $B$ placed to modify the first element of a matrix and the element in position 
$(k,k)$\<close>

definition "make_mat n k (B::'a mat) = (Matrix.mat n n (\<lambda>(i,j). if i = 0 \<and> j = 0 then B$$(0,0) else
    if i = 0 \<and> j = k then B$$(0,1) else if i=k \<and> j = 0 
      then B$$(1,0) else if i=k \<and> j=k then B$$(1,1) 
      else if i=j then 1 else 0))"

lemma make_mat_carrier[simp]:
  shows "make_mat n k B \<in> carrier_mat n n"
  unfolding make_mat_def by auto

lemma upper_triangular_mat_delete_make_mat:
  shows "upper_triangular (mat_delete (make_mat n k B) 0 0)"
proof -
  {  let ?M = "make_mat n k B"
  fix i j
  assume "i < dim_row ?M - Suc 0" and ji: "j < i"
  hence i_n1: "i < n - 1" by (simp add: make_mat_def)
  hence Suc_i: "Suc i < n" by linarith
  hence Suc_j: "Suc j < n" using ji by auto
  have i1: "insert_index 0 i = Suc i" by (rule insert_index, auto)
  have j1: "insert_index 0 j = Suc j" by (rule insert_index, auto)
  have "mat_delete ?M 0 0 $$ (i, j) = ?M $$ (insert_index 0 i, insert_index 0 j)"
    by (rule mat_delete_index[symmetric, OF _ _ _ i_n1], insert Suc_i Suc_j, auto)   
  also have "... = ?M $$ (Suc i, Suc j)" unfolding i1 j1 by simp
  also have "... = 0" unfolding make_mat_def unfolding index_mat[OF Suc_i Suc_j] using ji by auto
  finally have "mat_delete ?M 0 0 $$ (i, j) = 0" .
  }
  thus ?thesis  unfolding upper_triangular_def by auto
qed

lemma upper_triangular_mat_delete_make_mat2:
  assumes kn: "k<n"
  shows "upper_triangular (mat_delete (mat_delete (make_mat n k B) 0 k) (k - 1) 0)"
proof -
  {  let ?M = "local.make_mat n k B"
  let ?MD = "mat_delete ?M 0 k"
  fix i j assume i: "i < dim_row ?M - 2" and ji: "j < i"  
  have insert_in: "insert_index 0 i < n" and insert_Sucin: "insert_index 0 (Suc i) < n"
    using i make_mat_def by auto
  have insert_k_Sucj: "insert_index k (Suc j) < n"
    using insert_in insert_index_def ji by auto
  have insert_j: "insert_index 0 j = Suc j" by simp  
  have "mat_delete ?MD (k - 1) 0 $$ (i, j) = ?MD $$ (insert_index (k-1) i, insert_index 0 j)" 
  proof (rule mat_delete_index[symmetric])
    show "i < n-2" using i by (simp add: make_mat_def)  
    thus "?MD \<in> carrier_mat (Suc (n - 2)) (Suc (n - 2))"
      by (metis Suc_diff_Suc card_num_simps(30) make_mat_carrier mat_delete_carrier 
          nat_diff_split_asm not_less0 not_less_eq numerals(2))
    show "k - 1 < Suc (n - 2)" using kn by auto  
    show "0 < Suc (n - 2)" by blast
    show "j < n - 2" using ji i by (simp add: make_mat_def)  
  qed
  also have "... = ?MD $$ (insert_index (k-1) i, Suc j)" unfolding insert_j by auto
  also have "... = 0"
  proof (cases "i < (k-1)")
    case True
    hence "insert_index (k-1) i = i" by auto
    hence "?MD $$ (insert_index (k-1) i, Suc j) = ?MD $$ (i, Suc j)" by auto
    also have "... = ?M $$ (insert_index 0 i, insert_index k (Suc j))" 
    proof (rule mat_delete_index[symmetric])
      show "?M \<in> carrier_mat (Suc (n-1)) (Suc (n-1))" using assms by auto
      show "0 < Suc (n - 1)" 
        by blast
      show "k < Suc (n - 1)"using kn by simp
      show "i < n - 1" using i using True assms by linarith
      thus "Suc j < n - 1" using ji less_trans_Suc by blast
    qed
    also have "... = 0" unfolding make_mat_def index_mat[OF insert_in insert_k_Sucj]
      using True ji by auto
    finally show ?thesis .
    next
      case False
      hence "insert_index (k-1) i = Suc i" by auto
      hence "?MD $$ (insert_index (k-1) i, Suc j) = ?MD $$ (Suc i, Suc j)" by auto
    also have "... = ?M $$ (insert_index 0 (Suc i), insert_index k (Suc j))" 
    proof (rule mat_delete_index[symmetric])
      show "?M \<in> carrier_mat (Suc (n-1)) (Suc (n-1))" using assms by auto
      thus "Suc i < n - 1" using i using False assms
        by (metis One_nat_def Suc_diff_Suc carrier_matD(1) diff_Suc_1 diff_Suc_eq_diff_pred 
            diff_is_0_eq' linorder_not_less nat.distinct(1) numeral_2_eq_2)
      show "0 < Suc (n - 1)" 
        by blast
      show "k < Suc (n - 1)"using kn by simp
      show "Suc j < n - 1" using ji less_trans_Suc
        using \<open>Suc i < n - 1\<close> by linarith
    qed
    also have "... = 0" unfolding make_mat_def index_mat[OF insert_Sucin insert_k_Sucj]
      using False ji by (auto, smt insert_index_def less_SucI nat.inject nat_neq_iff)
    finally show ?thesis .    
  qed  
  finally have "mat_delete ?MD (k - 1) 0 $$ (i, j) = 0" .
}
  thus ?thesis unfolding upper_triangular_def by auto
qed

corollary det_mat_delete_make_mat:
  assumes kn: "k<n"
  shows "Determinant.det (mat_delete (mat_delete (make_mat n k B) 0 k) (k - 1) 0) = 1"
proof -
  let ?M = "make_mat n k B"
  let ?MD = "mat_delete ?M 0 k"
  let ?MDMD = "mat_delete ?MD (k - 1) 0"
  have eq1: "?MDMD $$ (i,i) = 1" if i: "i<n-2" for i
  proof -
    have i1: "insert_index 0 (insert_index (k-1) i) < n" using i insert_index_def by auto
    have i2: "insert_index k (insert_index 0 i) < n" using i insert_index_def by auto
    have "?MDMD $$ (i, i) = ?MD $$ (insert_index (k-1) i, insert_index 0 i)"
    proof (rule mat_delete_index[symmetric, OF _ _ _ i i])
      show "mat_delete (local.make_mat n k B) 0 k \<in> carrier_mat (Suc (n-2)) (Suc (n-2))"
        by (metis (mono_tags, hide_lams) Suc_diff_Suc card_num_simps(30) i make_mat_carrier 
            mat_delete_carrier nat_diff_split_asm not_less0 not_less_eq numerals(2))    
      show "k - 1 < Suc (n - 2)" using kn by auto
      show "0 < Suc (n - 2)" using kn by auto
    qed
    also have "... = ?M $$ (insert_index 0 (insert_index (k-1) i), insert_index k (insert_index 0 i))"
    proof (rule mat_delete_index[symmetric])
      show "make_mat n k B \<in> carrier_mat (Suc (n-1)) (Suc (n-1))" using i by auto    
      show "insert_index (k - 1) i < n - 1" using kn i
        by (metis diff_Suc_eq_diff_pred diff_commute insert_index_def nat_neq_iff not_less0 
            numeral_2_eq_2 zero_less_diff)
      show "insert_index 0 i < n - 1" using i by auto
    qed (insert kn, auto)
    also have "... = 1" unfolding make_mat_def index_mat[OF i1 i2] 
      by (auto, metis One_nat_def diff_Suc_1 insert_index_exclude) 
         (metis One_nat_def diff_Suc_eq_diff_pred insert_index_def zero_less_diff)+
    finally show ?thesis .
  qed
  have "Determinant.det ?MDMD = prod_list (diag_mat ?MDMD)"
    by (meson assms det_upper_triangular make_mat_carrier mat_delete_carrier 
        upper_triangular_mat_delete_make_mat2)
  also have "... = 1" 
  proof (rule prod_list_neutral)
    fix x assume x: "x \<in> set (diag_mat ?MDMD)"
    from this obtain i where index: "x = ?MDMD $$ (i,i)" and i: "i<dim_row ?MDMD"
      unfolding diag_mat_def by auto
    have "?MDMD $$ (i,i) = 1" by (rule eq1, insert i, auto simp add: make_mat_def)  
    thus "x=1" using index by blast
  qed
  finally show ?thesis .
qed

lemma swaprows_make_mat:
  assumes B: "B \<in> carrier_mat 2 2" and k0: "k\<noteq>0" and k: "k<n"
  shows "swaprows k 0 (make_mat n k B) = make_mat n k (swaprows 1 0 B)" (is "?lhs = ?rhs")
proof (cases "n=0")
  case True
  then show ?thesis
    using make_mat_def by auto
next
  case False
  show ?thesis
   proof (rule eq_matI)
    show "dim_row ?lhs = dim_row ?rhs" and "dim_col ?lhs = dim_col ?rhs"
      by (simp add: make_mat_def)+
  next
    let ?M="(make_mat n k B)"
    fix i j assume i: "i < dim_row ?rhs" and j: "j < dim_col ?rhs"
    hence i2: "i < dim_row ?lhs" and j2: "j < dim_col ?lhs" by (auto simp add: make_mat_def)
    then have i3: "i < dim_row ?M" and j3: "j < dim_col ?M" by auto
    then have i4: "i<n" and j4: "j<n" by (metis carrier_matD(1,2) make_mat_carrier)+
    have lhs: "?lhs $$ (i,j) = 
        (if k = i then ?M $$ (0, j) else if 0 = i then ?M $$ (k, j) else ?M $$ (i, j))"
      by (rule index_mat_swaprows, insert i3 j3, auto)
    also have "... = ?rhs $$ (i,j)" using B i4 j4 False k0 k 
      unfolding make_mat_def index_mat[OF i4 j4] by auto
    finally show "?lhs $$ (i, j) = ?rhs $$ (i, j)" .
  qed
qed


lemma cofactor_make_mat_00:
  assumes k: "k<n" and k0: "k\<noteq>0"
  shows "cofactor (make_mat n k B) 0 0 = B $$ (1,1)"
proof -
  let ?M = "make_mat n k B"
  let ?MD = "mat_delete ?M 0 0"
  have MD_rows: "dim_row ?MD = n-1" by (simp add: make_mat_def)
  have 1: "?MD $$ (i, i) = 1" if i: "i < n - 1" and ik: "Suc i \<noteq> k" for i
  proof -
    have Suc_i: "Suc i < n" using i by linarith
    have "?MD $$ (i, i) = ?M $$ (insert_index 0 i, insert_index 0 i)"
      by (rule mat_delete_index[symmetric, OF _ _ _ i], insert Suc_i, auto)
    also have "... = ?M $$ (Suc i, Suc i)" by simp
    also have "... = 1" unfolding make_mat_def index_mat[OF Suc_i Suc_i] using ik by auto
    finally show ?thesis .
  qed
  have 2: "?MD $$ (i, i) = B$$(1,1)" if i: "i < n - 1" and ik: "Suc i = k" for i
  proof -
    have Suc_i: "Suc i < n" using i by linarith
    have "?MD $$ (i, i) = ?M $$ (insert_index 0 i, insert_index 0 i)"
      by (rule mat_delete_index[symmetric, OF _ _ _ i], insert Suc_i, auto)   
    also have "... = ?M $$ (Suc i, Suc i)" by simp
    also have "... = B$$(1,1)" unfolding make_mat_def index_mat[OF Suc_i Suc_i] using ik by auto
    finally show ?thesis .
  qed
  have set_rw: "insert (k-1) ({0..<dim_row ?MD}-{k-1}) = {0..<dim_row ?MD}" 
    using k k0 MD_rows by auto
  have up: "upper_triangular ?MD" by (rule upper_triangular_mat_delete_make_mat)
  have "Determinant.cofactor (local.make_mat n k B) 0 0 
    = Determinant.det (mat_delete (make_mat n k B) 0 0)" unfolding cofactor_def by auto
  also have "... = prod_list (diag_mat ?MD)" using up
    using det_upper_triangular make_mat_carrier mat_delete_carrier by blast
  also have "... = (\<Prod>i = 0..<dim_row ?MD. ?MD $$ (i, i))" unfolding prod_list_diag_prod by simp
  also have "... = (\<Prod>i \<in> insert (k-1) ({0..<dim_row ?MD}-{k-1}). ?MD $$ (i, i))" 
    using set_rw by simp
  also have "... = ?MD $$ (k-1, k-1) * (\<Prod>i \<in> {0..<dim_row ?MD} - {k-1}. ?MD $$ (i, i))"
    by (metis (no_types, lifting) Diff_iff finite_atLeastLessThan finite_insert prod.insert set_rw singletonI)
  also have "... = B$$(1,1)"
    by (smt "1" "2" DiffD1 DiffD2 Groups.mult_ac(2) MD_rows add_diff_cancel_left' add_diff_inverse_nat 
        k0 atLeastLessThan_iff class_cring.finprod_all1 insertI1 less_one more_arith_simps(5) 
        plus_1_eq_Suc set_rw)
  finally show ?thesis .
qed



lemma cofactor_make_mat_0k:  
  assumes kn: "k<n" and k0: "k\<noteq>0" and n0: "1<n"
  shows "cofactor (make_mat n k B) 0 k = - B $$ (1,0)"
proof -
  let ?M = "make_mat n k B"
  let ?MD = "mat_delete ?M 0 k"
  have n0: "0<n-1" using n0 by auto
  have MD_carrier: "?MD \<in> carrier_mat (n-1) (n-1)"
    using make_mat_carrier mat_delete_carrier by blast
  have MD_k1: "?MD $$ (k-1, 0) = B $$ (1,0)"
  proof -
    have n0': "0 < n" using n0 by auto
    have insert_i: "insert_index 0 (k-1) = k" using k0 by auto
    have insert_k: "insert_index k 0 = 0" using k0 by auto
    have "?MD $$ (k-1, 0) = ?M $$ (insert_index 0 (k-1), insert_index k 0)"
      by (rule mat_delete_index[symmetric, OF _ _ _ _ n0], insert k0 kn, auto)
    also have "... = ?M $$ (k, 0)" unfolding insert_i insert_k by simp
    also have "... = B $$ (1,0)" using k0 unfolding make_mat_def index_mat[OF kn n0'] by auto
    finally show ?thesis .
  qed  
  have MD0: "?MD $$ (i, 0) = 0" if i: "i<n-1" and ik: "Suc i\<noteq>k" for i
  proof -
    have i2: "Suc i < n" using i by auto
    have n0': "0<n" using n0 by auto
    have insert_i: "insert_index 0 i = Suc i" by simp
    have insert_k: "insert_index k 0 = 0" using k0 by auto
    have "?MD $$ (i, 0) = ?M $$ (insert_index 0 i, insert_index k 0)"
      by (rule mat_delete_index[symmetric, OF _ _ _ i], insert i n0 kn, auto)
    also have "... = ?M $$ (Suc i, 0)" unfolding insert_i insert_k by simp
    also have "... = 0" using ik unfolding make_mat_def index_mat[OF i2 n0'] by auto
    finally show ?thesis .
  qed
  have det_cofactor: "Determinant.cofactor ?MD (k-1) 0 = (-1) ^ (k - 1)"
    unfolding cofactor_def using det_mat_delete_make_mat[OF kn] by auto
  have sum0: "(\<Sum>i\<in>{0..<n - 1}-{k-1}. ?MD $$ (i, 0) * Determinant.cofactor ?MD i 0) = 0"
    by (rule sum.neutral, insert MD0, fastforce)
  have "Determinant.det ?MD = (\<Sum>i<n - 1. ?MD $$ (i, 0) * Determinant.cofactor ?MD i 0)" 
    by (rule laplace_expansion_column[OF MD_carrier n0])
  also have "... = ?MD $$ (k-1, 0) * Determinant.cofactor ?MD (k-1) 0 
      + (\<Sum>i\<in>{0..<n - 1}-{k-1}. ?MD $$ (i, 0) * Determinant.cofactor ?MD i 0)"  
    by (metis (no_types, lifting) Suc_less_eq add_diff_inverse_nat atLeast0LessThan finite_atLeastLessThan 
        k0 kn lessThan_iff less_one n0 nat_diff_split_asm plus_1_eq_Suc rel_simps(70) sum.remove)
  also have "... = ?MD $$ (k-1, 0) * Determinant.cofactor ?MD (k-1) 0" unfolding sum0 by simp
  also have "... = ?MD $$ (k-1, 0) * (-1) ^ (k - 1)" unfolding det_cofactor by auto
  also have "... = (-1) ^ (k - 1) * B $$ (1,0)" using MD_k1 by auto
  finally show ?thesis unfolding cofactor_def
    by (metis (no_types, lifting) arithmetic_simps(49) k0 left_minus_one_mult_self 
        more_arith_simps(11) mult_minus1 power_eq_if) 
qed


lemma invertible_make_mat:
  assumes inv_B: "invertible_mat B" and B: "B \<in> carrier_mat 2 2" 
    and kn: "k<n" and k0: "k\<noteq>0"
  shows "invertible_mat (make_mat n k B)"
proof -
  let ?M = "(make_mat n k B)"
  have M_carrier: "?M \<in> carrier_mat n n" by auto
  show ?thesis
  proof (cases "n=0")
    case True
    thus ?thesis using M_carrier using invertible_mat_zero by blast
  next
    case False note n_not_0 = False
    show ?thesis
    proof (cases "n=1")
      case True
      then show ?thesis using M_carrier using invertible_mat_zero assms by auto
    next
      case False    
      hence n: "0<n" using n_not_0 by auto
      hence n1: "1<n" using False n_not_0 by auto
      have M00: "?M $$ (0,0) = B $$ (0,0)" by (simp add: make_mat_def n)
      have M0k: "?M $$ (0,k) = B $$ (0,1)" by (simp add: k0 kn make_mat_def n)
      have sum0: "(\<Sum>j\<in>({0..<n}-{0} - {k}). ?M $$ (0, j) * Determinant.cofactor ?M 0 j) = 0"
      proof (rule sum.neutral, rule ballI)
        fix x assume x: "x \<in> {0..<n} - {0} - {k}"
        have "make_mat n k B $$ (0,x) = 0" unfolding make_mat_def using x by auto
        thus "local.make_mat n k B $$ (0, x) * Determinant.cofactor (local.make_mat n k B) 0 x = 0" 
          by simp
      qed
      have cofactor_M_00: "Determinant.cofactor ?M 0 0 = B$$(1,1)"
        by (rule cofactor_make_mat_00[OF kn k0])
      have cofactor_M_0k: "Determinant.cofactor ?M 0 k = - B $$ (1,0)"
        by (rule cofactor_make_mat_0k[OF kn k0 n1])
      have "Determinant.det ?M = (\<Sum>j<n. ?M $$ (0, j) * Determinant.cofactor ?M 0 j)" 
        using laplace_expansion_row[OF M_carrier n] by auto
      also have "... = (\<Sum>j\<in>{0..<n}. ?M $$ (0, j) * Determinant.cofactor ?M 0 j)" 
        by (rule sum.cong, auto)
      also have "... = ?M $$ (0, 0) * Determinant.cofactor ?M 0 0 
        + ?M $$ (0, k) * Determinant.cofactor ?M 0 k 
        + (\<Sum>j\<in>({0..<n}-{0} - {k}). ?M $$ (0, j) * Determinant.cofactor ?M 0 j)" 
        by (metis (no_types, lifting) add_cancel_right_right kn k0 atLeast0LessThan 
            atLeast1_lessThan_eq_remove0 finite_atLeastLessThan insert_Diff_single insert_iff 
            lessThan_iff n sum.atLeast_Suc_lessThan sum.remove sum0)
      also have "... = ?M $$ (0, 0) * Determinant.cofactor ?M 0 0 
        + ?M $$ (0, k) * Determinant.cofactor ?M 0 k" using sum0 by auto
      also have "... = ?M $$ (0, 0) * B $$ (1,1) - ?M $$ (0, k)* B $$ (1,0)" 
        unfolding cofactor_M_00 cofactor_M_0k by auto
      also have "... =  B $$ (0, 0) * B $$ (1,1) - B $$ (0, 1)* B $$ (1,0)" 
        unfolding M00 M0k by auto
      also have "... = Determinant.det B" unfolding det_2[OF B] by auto
      finally have "Determinant.det ?M = Determinant.det B" .
      thus ?thesis unfolding cofactor_def 
        using invertible_iff_is_unit_JNF by (metis B M_carrier inv_B)  
    qed
  qed
qed

lemma make_mat_index:
  assumes i: "i<n" and j: "j<n"
  shows "make_mat n k B $$ (i,j) = (if i = 0 \<and> j = 0 then B$$(0,0) else
    if i = 0 \<and> j = k then B$$(0,1) else if i=k \<and> j = 0 
      then B$$(1,0) else if i=k \<and> j=k then B$$(1,1) 
      else if i=j then 1 else 0)"
  unfolding make_mat_def index_mat[OF i j] by simp

lemma make_mat_works:
  assumes A: "A\<in>carrier_mat m n" and Suc_i_less_n: "Suc i < n"
    and Q_step_def: "Q_step = (make_mat n (Suc i) (snd (Smith_1x2 
        (Matrix.mat 1 2 (\<lambda>(a,b). if b = 0 then A $$ (0,0) else A $$(0,Suc i))))))"
  shows "A $$ (0,0) * Q_step $$ (0,(Suc i)) + A $$ (0, Suc i) * Q_step $$ (Suc i, Suc i) = 0"
proof -
  have n0: "0<n" using Suc_i_less_n by simp
  let ?A ="(Matrix.mat 1 2 (\<lambda>(a, b). if b = 0 then A $$ (0, 0) else A $$ (0, Suc i)))"
  let ?S = "fst (Smith_1x2 ?A)"
  let ?Q = "snd (Smith_1x2 ?A)"
  have 1: "(make_mat n (Suc i) ?Q) $$ (0,Suc i) = ?Q $$ (0,1)"
    unfolding make_mat_index[OF n0 Suc_i_less_n] by auto
  have 2: "(make_mat n (Suc i) ?Q) $$ (Suc i, Suc i) = ?Q $$ (1,1)"
    unfolding make_mat_index[OF Suc_i_less_n Suc_i_less_n] by auto
  have is_SNF_A': "is_SNF ?A (1\<^sub>m 1, Smith_1x2 ?A)" using SNF_1x2_works by auto 
  have SNF_S: "Smith_normal_form_mat ?S" and S: "?S = 1\<^sub>m 1 * ?A * ?Q" 
    and Q: "?Q \<in> carrier_mat 2 2"
    using is_SNF_A' unfolding is_SNF_def by auto
  have "?S $$(0,1) = (?A * ?Q) $$(0,1)" unfolding S by auto
  also have "... =  Matrix.row ?A 0 \<bullet> col ?Q 1" by (rule index_mult_mat, insert Q, auto)
  also have "... = (\<Sum>ia = 0..<dim_vec (col ?Q 1). Matrix.row ?A 0 $v ia * col ?Q 1 $v ia)"
    unfolding scalar_prod_def by auto
  also have "... = (\<Sum>ia \<in> {0,1}. Matrix.row ?A 0 $v ia * col ?Q 1 $v ia)"
    by (rule sum.cong, insert Q, auto)
  also have "... = Matrix.row ?A 0 $v 0 * col ?Q 1 $v 0 + Matrix.row ?A 0 $v 1 * col ?Q 1 $v 1"
    using sum_two_elements by auto
  also have "... = A $$ (0,0) * ?Q $$ (0,1) + A $$ (0,Suc i) * ?Q $$ (1,1)"    
    by (smt One_nat_def Q carrier_matD(1) carrier_matD(2) dim_col_mat(1) dim_row_mat(1) index_col 
        index_mat(1) index_row(1) lessI numeral_2_eq_2 pos2 prod.simps(2) rel_simps(93))
  finally have "?S $$(0,1) = A $$ (0,0) * ?Q $$ (0,1) + A $$ (0,Suc i) * ?Q $$ (1,1)" by simp
  moreover have "?S $$(0,1) = 0" using SNF_S unfolding Smith_normal_form_mat_def isDiagonal_mat_def
    by (metis (no_types, lifting) Q S card_num_simps(30) carrier_matD(2) index_mult_mat(2) 
        index_mult_mat(3) index_one_mat(2) lessI n_not_Suc_n numeral_2_eq_2)
  ultimately show ?thesis using 1 2 unfolding Q_step_def by auto
qed

subsubsection \<open>Case $1 \times n$\<close>

fun Smith_1xn_aux :: "nat \<Rightarrow> 'a mat \<Rightarrow> ('a mat \<times> 'a mat) \<Rightarrow> ('a mat \<times> 'a mat)"
  where 
    "Smith_1xn_aux 0 A (S,Q) = (S,Q)" |
    "Smith_1xn_aux (Suc i) A (S,Q) = (let 
       A_step_1x2 = (Matrix.mat 1 2 (\<lambda>(a,b). if b = 0 then S $$ (0,0) else S $$(0,Suc i)));
       (S_step_1x2, Q_step_1x2) = Smith_1x2 A_step_1x2;
      Q_step = make_mat (dim_col A) (Suc i) Q_step_1x2; 
      S' = S * Q_step
      in Smith_1xn_aux i A (S',Q*Q_step))"

definition "Smith_1xn A = (if dim_col A = 0 then (A,1\<^sub>m (dim_col A)) 
  else Smith_1xn_aux (dim_col A - 1) A (A,1\<^sub>m (dim_col A)))"

lemma Smith_1xn_aux_Q_carrier:
  assumes r: "(S',Q') = (Smith_1xn_aux i A (S,Q))"
  assumes A: "A \<in> carrier_mat 1 n" and Q: "Q \<in> carrier_mat n n"
  shows "Q' \<in> carrier_mat n n"
  using A r Q 
proof (induct i A "(S,Q)" arbitrary: S Q rule: Smith_1xn_aux.induct)
  case (1 A S Q)
  then show ?case by auto
next
  case (2 i A S Q)
  note A = "2.prems"(1)
  note S'Q' = "2.prems"(2)
  note Q = "2.prems"(3)  
  let ?A_step_1x2 = "(Matrix.mat 1 2 (\<lambda>(a,b). if b = 0 then S $$ (0,0) else S $$(0,Suc i)))"
  let ?S_step_1x2 = "fst (Smith_1x2 ?A_step_1x2)"
  let ?Q_step_1x2 = "snd (Smith_1x2 ?A_step_1x2)"
  let ?Q_step = "make_mat (dim_col A) (Suc i) ?Q_step_1x2"
  have rw: "A * (Q * ?Q_step) = A * Q * ?Q_step"
    by (smt A Q assoc_mult_mat carrier_matD(2) make_mat_carrier)  
  have Smith_rw: "Smith_1xn_aux (Suc i) A (S, Q) = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)"
    by (auto, metis (no_types, lifting) old.prod.exhaust snd_conv split_conv)
  show ?case 
  proof (rule "2.hyps"[of ?A_step_1x2 "(?S_step_1x2, ?Q_step_1x2)" ?S_step_1x2 ?Q_step_1x2])
    show "S * ?Q_step = S * ?Q_step" ..   
    show "A \<in> carrier_mat 1 n" using A by auto
    show "(S', Q') = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)" using "2.prems" Smith_rw by auto
    show "Q * ?Q_step \<in> carrier_mat n n" using A Q by auto  
  qed (auto)
qed


lemma Smith_1xn_aux_invertible_Q:
  assumes r: "(S',Q') = (Smith_1xn_aux i A (S,Q))"
  assumes A: "A \<in> carrier_mat 1 n" and Q: "Q \<in> carrier_mat n n"
    and i: "i<n" and inv_Q: "invertible_mat Q"
  shows "invertible_mat Q'"
  using r A Q inv_Q i
proof (induct i A "(S,Q)" arbitrary: S Q rule: Smith_1xn_aux.induct)
  case (1 A S Q)
  then show ?case by auto
next
  case (2 i A S Q)
  let ?A_step_1x2 = "(Matrix.mat 1 2 (\<lambda>(a,b). if b = 0 then S $$ (0,0) else S $$(0,Suc i)))"
  let ?S_step_1x2 = "fst (Smith_1x2 ?A_step_1x2)"
  let ?Q_step_1x2 = "snd (Smith_1x2 ?A_step_1x2)"
  let ?Q_step = "make_mat (dim_col A) (Suc i) ?Q_step_1x2"
   have Smith_rw: "Smith_1xn_aux (Suc i) A (S, Q) = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)"
     by (auto, metis (no_types, lifting) old.prod.exhaust snd_conv split_conv)
   have i_col: "Suc i < dim_col A"
     using  "2.prems" Suc_lessD by blast
   have i_n: "i<n" by (simp add: "2.prems" Suc_lessD)
  show ?case 
  proof (rule "2.hyps"[of ?A_step_1x2 "(?S_step_1x2, ?Q_step_1x2)" ?S_step_1x2 ?Q_step_1x2])
    show "A \<in> carrier_mat 1 n" using "2.prems" by auto
    show "Q * ?Q_step \<in> carrier_mat n n" using "2.prems" by auto  
    show "S * ?Q_step = S * ?Q_step" ..
    show "(S', Q') = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)" using "2.prems" Smith_rw by auto
    show "invertible_mat (Q * ?Q_step)"
    proof (rule invertible_mult_JNF)
      show "Q \<in> carrier_mat n n" using "2.prems" by auto
      show "?Q_step \<in> carrier_mat n n"  using "2.prems" by auto
      show "invertible_mat Q" using "2.prems" by auto
      show "invertible_mat ?Q_step" 
        by (rule invertible_make_mat[OF _ _ i_col], insert SNF_1x2_works, unfold is_SNF_def, auto)
           (metis (no_types, lifting) case_prodE mat_carrier snd_conv)+        
    qed
  qed (auto simp add: i_n)
qed

lemma Smith_1xn_aux_S'_AQ':
  assumes r: "(S',Q') = (Smith_1xn_aux i A (S,Q))"
  assumes A: "A \<in> carrier_mat 1 n" and S: "S \<in> carrier_mat 1 n" and Q: "Q \<in> carrier_mat n n"
    and S_AQ: "S = A*Q" and i: "i<n"
  shows "S' = A * Q'"
  using A S r Q S_AQ 
proof (induct i A "(S,Q)" arbitrary: S Q rule: Smith_1xn_aux.induct)
  case (1 A S Q)
  then show ?case by auto
next
 case (2 i A S Q)
  let ?A_step_1x2 = "(Matrix.mat 1 2 (\<lambda>(a,b). if b = 0 then S $$ (0,0) else S $$(0,Suc i)))"
  let ?S_step_1x2 = "fst (Smith_1x2 ?A_step_1x2)"
  let ?Q_step_1x2 = "snd (Smith_1x2 ?A_step_1x2)"
  let ?Q_step = "make_mat (dim_col A) (Suc i) ?Q_step_1x2"
  have rw: "A * (Q * ?Q_step) = A * Q * ?Q_step"
    by (smt "2.prems" assoc_mult_mat carrier_matD(2) make_mat_carrier)  
   have Smith_rw: "Smith_1xn_aux (Suc i) A (S, Q) = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)"
    by (auto, metis (no_types, lifting) old.prod.exhaust snd_conv split_conv)
  show ?case 
  proof (rule "2.hyps"[of ?A_step_1x2 "(?S_step_1x2, ?Q_step_1x2)" ?S_step_1x2 ?Q_step_1x2])
   show "A \<in> carrier_mat 1 n" using "2.prems" by auto
    show "Q * ?Q_step \<in> carrier_mat n n" using "2.prems" by auto  
    show "S * ?Q_step = S * ?Q_step" ..
    show "(S', Q') = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)" using "2.prems" Smith_rw by auto
    show " S * ?Q_step = A * (Q * ?Q_step)" using "2.prems" rw by auto
    show "S * ?Q_step \<in> carrier_mat 1 n"
      using "2.prems" by (smt carrier_matD(2) make_mat_carrier mult_carrier_mat)
  qed (auto)
qed


lemma Smith_1xn_aux_S'_works:
  assumes r: "(S',Q') = (Smith_1xn_aux i A (S,Q))"
  assumes A: "A \<in> carrier_mat 1 n" and S: "S \<in> carrier_mat 1 n" and Q: "Q \<in> carrier_mat n n"
    and S_AQ: "S = A*Q" and i: "i<n" and j0: "0<j" and jn: "j<n"
  and all_j_zero: "\<forall>j\<in>{i+1..<n}. S $$(0,j) = 0"
  shows "S' $$ (0,j) = 0"
  using A S r Q i S_AQ all_j_zero j0 jn
proof (induct i A "(S,Q)" arbitrary: S Q rule: Smith_1xn_aux.induct)
  case (1 A S Q)
  then show ?case using j0 jn by auto
next
 case (2 i A S Q)
  let ?A_step_1x2 = "(Matrix.mat 1 2 (\<lambda>(a,b). if b = 0 then S $$ (0,0) else S $$(0,Suc i)))"
  let ?S_step_1x2 = "fst (Smith_1x2 ?A_step_1x2)"
  let ?Q_step_1x2 = "snd (Smith_1x2 ?A_step_1x2)"
  let ?Q_step = "make_mat (dim_col A) (Suc i) ?Q_step_1x2"
  have i_less_n: "i<n" by (simp add: "2"(6) Suc_lessD)
  have rw: "A * (Q * ?Q_step) = A * Q * ?Q_step"
    by (smt "2.prems" assoc_mult_mat carrier_matD(2) make_mat_carrier)  
   have Smith_rw: "Smith_1xn_aux (Suc i) A (S, Q) = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)"
     by (auto, metis (no_types, lifting) old.prod.exhaust snd_conv split_conv)
   have S'_AQ': "S' = A*Q'"
     by (rule Smith_1xn_aux_S'_AQ', insert "2.prems", auto)  
  show ?case 
  proof (rule "2.hyps"[of ?A_step_1x2 "(?S_step_1x2, ?Q_step_1x2)" ?S_step_1x2 ?Q_step_1x2])
   show "A \<in> carrier_mat 1 n" using "2.prems" by auto
    show Q_Q_step_carrier: "Q * ?Q_step \<in> carrier_mat n n" using "2.prems" by auto  
    show "S * ?Q_step = S * ?Q_step" ..
    show "(S', Q') = Smith_1xn_aux i A (S * ?Q_step, Q * ?Q_step)" using "2.prems" Smith_rw by auto
    show "S * ?Q_step = A * (Q * ?Q_step)" using "2.prems" rw by auto
    show "S * ?Q_step \<in> carrier_mat 1 n"      
      using "2.prems" by (smt carrier_matD(2) make_mat_carrier mult_carrier_mat)  
    show "\<forall>j\<in>{i + 1..<n}. (S * ?Q_step) $$ (0, j) = 0"
    proof (rule ballI)
      fix j assume j: "j\<in>{i + 1..<n}" 
      have "(S * ?Q_step) $$ (0, j) = Matrix.row S 0 \<bullet> col ?Q_step j" 
        by (rule index_mult_mat, insert j "2.prems", auto simp add: make_mat_def)
      also have "... = 0"
      proof (cases "j=Suc i")
        case True
        (*In this case, the element is transformed into a zero thanks to the SNF operation.*)
        let ?f = "\<lambda>x. Matrix.row S 0 $v x * col ?Q_step j $v x"
        let ?set = "{0..<dim_vec (col ?Q_step j)}"
        have set_rw: "?set = insert 0 (insert j (?set - {0} - {j}))"
          using "2.prems" True make_mat_def by auto
        have sum0: "(\<Sum>x \<in> ?set - {0} - {j}. ?f x) = 0"
        proof (rule sum.neutral, rule ballI)
          fix x assume x: "x \<in> ?set - {0} - {j}"
          show "?f x = 0" using "2"(6) "2.prems" True make_mat_def x by auto
        qed
        have "Matrix.row S 0 \<bullet> col ?Q_step j  = (\<Sum>x = 0..<dim_vec (col ?Q_step j). ?f x)"
          unfolding scalar_prod_def by simp
        also have "... = (\<Sum>x \<in> insert 0 (insert j (?set - {0} - {j})). ?f x)" using set_rw by auto
        also have "... = ?f 0 + (\<Sum>x \<in> insert j (?set - {0} - {j}). ?f x)" by (simp add: True)
        also have "... = ?f 0 + ?f j + (\<Sum>x \<in> ?set - {0} - {j}. ?f x)"
          by (simp add: set_rw sum.insert_remove)
        also have "... = ?f 0 + ?f j" using sum0 by auto
        also have "... = S $$ (0,0) * ?Q_step $$ (0, Suc i) + S $$ (0,Suc i) * ?Q_step $$ (Suc i, Suc i)"
          using "2.prems" True make_mat_def by auto
        also have "... = 0" by (rule make_mat_works, insert "2.prems", auto)
        finally show ?thesis .
      next
        (*In this case, the zeroes are preserved. Each multiplication is zero.*)
        case False note j_not_Suc_i = False
        show ?thesis
          unfolding scalar_prod_def
        proof (rule sum.neutral, rule ballI)
          fix x assume x: "x\<in>{0..<dim_vec (col ?Q_step j)}"
          have xn: "x<n" using "2"(2) make_mat_def x by auto
          have jn2: "j<dim_col A" using "2"(2) j by auto
          have xn2: "x<dim_col A" using "2.prems"(1) xn by blast
          have "Matrix.row S 0 $v x = S $$ (0,x)" using "2.prems" make_mat_def x by auto
          moreover have "col ?Q_step j $v x = ?Q_step $$ (x,j)" using Q_Q_step_carrier j x by auto
          ultimately have eq: "Matrix.row S 0 $v x * col ?Q_step j $v x = S $$ (0,x) * ?Q_step $$ (x,j)" by auto
          have S_0x: "S $$ (0,x) = 0" if "Suc i + 1 \<le> x" using "2.prems" xn that by auto
          moreover have "?Q_step $$ (x,j) = 0" if "x\<le>Suc i" 
            using that j j_not_Suc_i unfolding make_mat_def index_mat[OF xn2 jn2] by auto 
          ultimately show "Matrix.row S 0 $v x * (col ?Q_step j) $v x = 0" using eq by force
        qed
      qed
      finally show "(S * ?Q_step) $$ (0, j) = 0" .
    qed
  qed (auto simp add: "2.prems" i_less_n)
qed

lemma Smith_1xn_works:
  assumes A: "A \<in> carrier_mat 1 n"
  and SQ: "(S,Q) = Smith_1xn A"
shows "is_SNF A (1\<^sub>m 1, S,Q)"
proof (cases "n=0")
  case True
  thus ?thesis using assms
    unfolding is_SNF_def
    by (auto simp add: Smith_1xn_def)
next
  case False 
  hence n0: "0<n" by auto
  show ?thesis
  proof (rule is_SNF_intro) 
    have SQ_eq: "(S,Q) = local.Smith_1xn_aux (dim_col A - 1) A (A,1\<^sub>m (dim_col A))"
      using SQ unfolding Smith_1xn_def by simp
    have col: "dim_col A - 1 < dim_col A" using n0 A by auto
    show "1\<^sub>m 1 \<in> carrier_mat (dim_row A) (dim_row A)" using A by auto
    show Q: "Q \<in> carrier_mat (dim_col A) (dim_col A)" 
      by (rule Smith_1xn_aux_Q_carrier[OF SQ_eq], insert A, auto)
    show "invertible_mat (1\<^sub>m 1)" by simp
    show "invertible_mat Q" by (rule Smith_1xn_aux_invertible_Q[OF SQ_eq], insert A n0, auto)
    have S_AQ: "S = A * Q"
      by (rule Smith_1xn_aux_S'_AQ'[OF SQ_eq], insert A n0, auto)
    thus "S = 1\<^sub>m 1 * A * Q" using A by auto
    have S: "S \<in> carrier_mat 1 n" using S_AQ A Q by auto  
    show "Smith_normal_form_mat S"
    proof (rule Smith_normal_form_mat_intro)
      show "\<forall>a. a + 1 < min (dim_row S) (dim_col S) \<longrightarrow> S $$ (a, a) dvd S $$ (a + 1, a + 1)"
        using S by auto
      have "S $$ (0, j) = 0" if j0: "0 < j" and jn: "j < n" for j
        by (rule Smith_1xn_aux_S'_works[OF SQ_eq], insert A n0 j0 jn, auto)  
      thus "isDiagonal_mat S" unfolding isDiagonal_mat_def using S by simp   
    qed
  qed
qed

subsubsection \<open>Case $n \times 1$\<close>

(*The case n x 1 can be obtained from the case 1 x n taking inverses appropriately. Thus, I get
  rid of the Smith_2x1 operation, since it seems to be useless.*)

definition "Smith_nx1 A = 
  (let (S,P) = (Smith_1xn_aux (dim_row A - 1) (transpose_mat A) (transpose_mat A,1\<^sub>m (dim_row A))) 
  in (transpose_mat P, transpose_mat S))"


lemma Smith_nx1_works:
  assumes A: "A \<in> carrier_mat n 1"
  and SQ: "(P,S) = Smith_nx1 A"
shows "is_SNF A (P, S,1\<^sub>m 1)"
proof (cases "n=0")
  case True
  thus ?thesis using assms
    unfolding is_SNF_def
    by (auto simp add: Smith_nx1_def)
next
  case False
  hence n0: "0<n" by auto
  show ?thesis
  proof (rule is_SNF_intro) 
    have SQ_eq: "(S\<^sup>T, P\<^sup>T) = (Smith_1xn_aux (dim_row A - 1) A\<^sup>T (A\<^sup>T,1\<^sub>m (dim_row A)))"
      using SQ[unfolded Smith_nx1_def] unfolding Let_def split_beta by auto
    have "is_SNF (A\<^sup>T) (1\<^sub>m 1, S\<^sup>T,P\<^sup>T)" 
      by (rule Smith_1xn_works[unfolded Smith_1xn_def, OF _ _], insert SQ_eq A, auto)
    have Pt: "P\<^sup>T \<in> carrier_mat (dim_col (A\<^sup>T)) (dim_col (A\<^sup>T))"
      by (rule Smith_1xn_aux_Q_carrier[OF SQ_eq], insert A n0, auto)
    thus P: "P \<in> carrier_mat (dim_row A) (dim_row A)" by auto
    show "1\<^sub>m 1 \<in> carrier_mat (dim_col A) (dim_col A)" using A by simp
    have "invertible_mat (P\<^sup>T)"
      by (rule Smith_1xn_aux_invertible_Q[OF SQ_eq], insert A n0, auto)
    thus "invertible_mat P" by (metis det_transpose P Pt invertible_iff_is_unit_JNF)
    show "invertible_mat (1\<^sub>m 1)" by simp
    have "S\<^sup>T = A\<^sup>T * P\<^sup>T" 
      by (rule Smith_1xn_aux_S'_AQ'[OF SQ_eq], insert A n0, auto)
    hence "S = P * A" by (metis A transpose_mult transpose_transpose P carrier_matD(1))
    thus "S = P * A * 1\<^sub>m 1" using P A by auto
    hence S: "S \<in> carrier_mat n 1" using P A by auto
    have "is_SNF (A\<^sup>T) (1\<^sub>m 1, S\<^sup>T,P\<^sup>T)" 
      by (rule Smith_1xn_works[unfolded Smith_1xn_def, OF _ _], insert SQ_eq A, auto)  
    hence "Smith_normal_form_mat (S\<^sup>T)" unfolding is_SNF_def by auto
    thus "Smith_normal_form_mat S" unfolding Smith_normal_form_mat_def isDiagonal_mat_def by auto
  qed
qed

subsubsection \<open>Case $2 \times n$\<close>

function Smith_2xn :: "'a mat \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat)"
  where 
    "Smith_2xn A = (
  if dim_col A = 0 then (1\<^sub>m (dim_row A),A,1\<^sub>m 0) else
  if dim_col A = 1 then let (P,S) = Smith_nx1 A in (P,S, 1\<^sub>m (dim_col A)) else
  if dim_col A = 2 then Smith_2x2 A 
  else
      let A1 = mat_of_cols (dim_row A) [col A 0];
          A2 = mat_of_cols (dim_row A) [col A i. i \<leftarrow> [1..<dim_col A]];
          (P1,D1,Q1) = Smith_2xn A2;
          C = (P1*A1) @\<^sub>c (P1*A2*Q1);
          D = mat_of_cols (dim_row A) [col C 0, col C 1];
          E = mat_of_cols (dim_row A) [col C i. i \<leftarrow> [2..<dim_col A]];
          (P2,D2,Q2) = Smith_2x2 D;
          H = (P2*D*Q2) @\<^sub>c (P2 * E);
          k = (div_op (H $$ (0,2)) (H $$ (0,0)));
          H2 = addcol (-k) 2 0 H;
          (_,_,_,H2_DR) = split_block H2 1 1;
          (H_1xn,Q3) = Smith_1xn H2_DR;
          S = four_block_mat (Matrix.mat 1 1 (\<lambda>(a,b). H$$(0,0))) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m 1 1) H_1xn;
          Q1' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_col A - 1) 1) Q1;
          Q2' = four_block_mat Q2 (0\<^sub>m 2 (dim_col A - 2)) (0\<^sub>m (dim_col A - 2) 2) (1\<^sub>m (dim_col A - 2));
          Q_div_k = addrow_mat (dim_col A) (-k) 0 2;
          Q3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_col A - 1) 1) Q3
      in (P2 * P1,S,Q1' * Q2' * Q_div_k * Q3'))"
  by pat_completeness auto
(*Termination is guaranteed since the algorithm is recursively applied to a 
  submatrix with less columns*)
termination apply (relation "measure (\<lambda>A. dim_col A)") by auto

lemma Smith_2xn_0:
  assumes A: "A \<in> carrier_mat 2 0"
  shows "is_SNF A (Smith_2xn A)"
proof -
  have "Smith_2xn A = (1\<^sub>m (dim_row A),A,1\<^sub>m 0)"
    using A by auto
  moreover have "is_SNF A ..." by (rule is_SNF_intro, insert A, auto)
  ultimately show ?thesis by simp
qed

lemma Smith_2xn_1:
  assumes A: "A \<in> carrier_mat 2 1"
  shows "is_SNF A (Smith_2xn A)"
proof -
  obtain P S where PS: "Smith_nx1 A = (P,S)" using prod.exhaust by blast
  have *: "is_SNF A (P, S,1\<^sub>m 1)" by (rule Smith_nx1_works[OF A PS[symmetric]])
  moreover have "Smith_2xn A = (P,S, 1\<^sub>m (dim_col A))"
    using A PS by auto
  moreover have "is_SNF A ..." using * A by auto
  ultimately show ?thesis by simp
qed

lemma Smith_2xn_2:
  assumes A: "A \<in> carrier_mat 2 2"
  shows "is_SNF A (Smith_2xn A)"
proof -
  have "Smith_2xn A = Smith_2x2 A" using A by auto
  from this show ?thesis using SNF_2x2_works using A by auto
qed

lemma is_SNF_Smith_2xn_n_ge_2: 
  assumes A: "A \<in> carrier_mat 2 n" and n: "n>2"
  shows "is_SNF A (Smith_2xn A)"
  using A n id
proof (induct A arbitrary: n rule: Smith_2xn.induct)
  case (1 A)
  note A = "1.prems"(1)
  note n_ge_2 = "1.prems"(2)
  have dim_col_A_g2: "dim_col A > 2" using n_ge_2 A by auto
  define A1 where "A1 = mat_of_cols (dim_row A) [col A 0]"
  define A2 where "A2 = mat_of_cols (dim_row A) [col A i. i \<leftarrow> [1..<dim_col A]]"
  obtain P1 D1 Q1 where P1D1Q1: "(P1,D1,Q1) = Smith_2xn A2" by (metis prod_cases3)
  define C where "C = (P1*A1) @\<^sub>c (P1*A2*Q1)"
  define D where "D = mat_of_cols (dim_row A) [col C 0, col C 1]"
  define E where "E = mat_of_cols (dim_row A) [col C i. i \<leftarrow> [2..<dim_col A]]"
  obtain P2 D2 Q2 where P2D2Q2: "(P2,D2,Q2) = Smith_2x2 D" by (metis prod_cases3)
  define H where "H = (P2*D*Q2) @\<^sub>c (P2 * E)"
  define k where "k = div_op (H $$ (0,2)) (H $$ (0,0))"
  define H2 where "H2 = addcol (-k) 2 0 H"
  obtain H2_UL H2_UR H2_DL H2_DR 
    where split_H2: "(H2_UL, H2_UR, H2_DL, H2_DR) = (split_block H2 1 1)" by (metis prod_cases4)
  obtain H_1xn Q3 where H_1xn_Q3: "(H_1xn,Q3) = Smith_1xn H2_DR" by (metis surj_pair)
  define S where "S = four_block_mat (Matrix.mat 1 1 (\<lambda>(a,b). H$$(0,0))) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m 1 1) H_1xn"
  define Q1' where "Q1' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_col A - 1) 1) Q1"
  define Q2' where "Q2' = four_block_mat Q2 (0\<^sub>m 2 (dim_col A - 2)) (0\<^sub>m (dim_col A - 2) 2) (1\<^sub>m (dim_col A - 2))"
  define Q_div_k where "Q_div_k = addrow_mat (dim_col A) (-k) 0 2"
  define Q3' where "Q3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_col A - 1) 1) Q3"
  have Smith_2xn_rw: "Smith_2xn A = (P2 * P1, S, Q1' * Q2' * Q_div_k * Q3')"
  proof (rule prod3_intro)
    have P1_def: "fst (Smith_2xn A2) = P1" and Q1_def: "snd (snd (Smith_2xn A2)) = Q1"
    and P2_def: "fst (Smith_2x2 D) = P2" and Q2_def: "snd (snd (Smith_2x2 D)) = Q2"
    and H_1xn_def: "fst (Smith_1xn H2_DR) = H_1xn" and Q3_def: "snd (Smith_1xn H2_DR) = Q3"     
    and H2_DR_def: "snd (snd (snd (split_block H2 1 1))) = H2_DR"
      using P2D2Q2 P1D1Q1 H_1xn_Q3 split_H2 fstI sndI by metis+
    note aux= P1_def Q1_def Q1'_def Q2'_def Q_div_k_def Q3'_def S_def A1_def[symmetric]
      C_def[symmetric] P2_def Q2_def Q3_def D_def[symmetric] E_def[symmetric] H_def[symmetric]
      k_def[symmetric] H2_def[symmetric] H2_DR_def H_1xn_def A2_def[symmetric]
  show "fst (Smith_2xn A) = P2 * P1" 
    using dim_col_A_g2 unfolding Smith_2xn.simps[of A] Let_def split_beta
    by (insert P1D1Q1 P2D2Q2 D_def C_def, unfold aux, auto simp del: Smith_2xn.simps)
  show "fst (snd (Smith_2xn A)) = S"
    using dim_col_A_g2 unfolding Smith_2xn.simps[of A] Let_def split_beta
    by (insert P1D1Q1 P2D2Q2, unfold aux, auto simp del: Smith_2xn.simps)
  show "snd (snd (Smith_2xn A)) = Q1' * Q2' * Q_div_k * Q3'" 
    using dim_col_A_g2 unfolding Smith_2xn.simps[of A] Let_def split_beta
    by (insert P1D1Q1 P2D2Q2, unfold aux, auto simp del: Smith_2xn.simps)  
  qed
  show ?case
  proof (unfold Smith_2xn_rw, rule is_SNF_intro)    
    have is_SNF_A2: "is_SNF A2 (Smith_2xn A2)" 
    proof (cases "2<dim_col A2")
      case True
      show ?thesis 
        by (rule "1.hyps", insert True A dim_col_A_g2 id, auto simp add: A2_def)
    next
      case False
      hence "dim_col A2 = 2" using n_ge_2 A unfolding A2_def by auto
      hence A2: "A2\<in>carrier_mat 2 2" unfolding A2_def using A by auto
      hence *: "Smith_2xn A2 =  Smith_2x2 A2" by auto
      show ?thesis unfolding * using SNF_2x2_works A2 by auto
    qed
    have A1[simp]: "A1 \<in> carrier_mat (dim_row A) 1" unfolding A1_def by auto
    have A2[simp]: "A2 \<in> carrier_mat (dim_row A) (dim_col A - 1)" unfolding A2_def by auto    
    have P1[simp]: "P1 \<in> carrier_mat (dim_row A) (dim_row A)" 
      and inv_P1: "invertible_mat P1" 
      and Q1: "Q1 \<in> carrier_mat (dim_col A2) (dim_col A2)" and inv_Q1: "invertible_mat Q1"
      and SNF_P1A2Q1: "Smith_normal_form_mat (P1*A2*Q1)"
      using is_SNF_A2 P1D1Q1 A2 unfolding is_SNF_def by fastforce+ 
    have D[simp]: "D \<in> carrier_mat 2 2" unfolding D_def
      by (metis "1"(2) One_nat_def Suc_eq_plus1 carrier_matD(1) list.size(3) 
          list.size(4) mat_of_cols_carrier(1) numerals(2))
    have is_SNF_D: "is_SNF D (Smith_2x2 D)" using SNF_2x2_works D by auto
    hence P2[simp]: "P2 \<in> carrier_mat (dim_row A) (dim_row A)" and inv_P2: "invertible_mat P2"
      and Q2[simp]: "Q2 \<in> carrier_mat (dim_col D) (dim_col D)" and inv_Q2: "invertible_mat Q2"
      using P2D2Q2 D_def unfolding is_SNF_def by force+ 
    show P2_P1: "P2 * P1 \<in> carrier_mat (dim_row A) (dim_row A)" by (rule mult_carrier_mat[OF P2 P1])
    show "invertible_mat (P2 * P1)" by (rule invertible_mult_JNF[OF P2 P1 inv_P2 inv_P1])
    have Q1': "Q1' \<in> carrier_mat (dim_col A) (dim_col A)" using Q1 unfolding Q1'_def
      by (auto, smt A2 One_nat_def add_diff_inverse_nat carrier_matD(1) carrier_matD(2) carrier_matI 
          dim_col_A_g2 gr_implies_not0 index_mat_four_block(2) index_mat_four_block(3) 
          index_one_mat(2) index_one_mat(3) less_Suc0)
    have Q2': "Q2' \<in> carrier_mat (dim_col A) (dim_col A)" using Q2 unfolding Q2'_def
      by (smt D One_nat_def Suc_lessD add_diff_inverse_nat carrier_matD(1) carrier_matD(2) 
          carrier_matI dim_col_A_g2 gr_implies_not0 index_mat_four_block(2) index_mat_four_block(3)
          index_one_mat(2) index_one_mat(3) less_2_cases numeral_2_eq_2 semiring_norm(138))
   have H2[simp]: "H2 \<in> carrier_mat (dim_row A) (dim_col A)" using A P2 D unfolding H2_def H_def
     by (smt E_def Q2 Q2' Q2'_def append_cols_def arithmetic_simps(50) carrier_matD(1) carrier_matD(2) 
         carrier_mat_triv index_mat_addcol(4) index_mat_addcol(5) index_mat_four_block(2) 
         index_mat_four_block(3) index_mult_mat(2) index_mult_mat(3) index_one_mat(2) index_zero_mat(2) 
         index_zero_mat(3) length_map length_upt mat_of_cols_carrier(3))
   have H'[simp]: "H2_DR \<in> carrier_mat 1 (n - 1)"
     by (rule split_block(4)[OF split_H2[symmetric]], insert H2 A n_ge_2, auto)
   have is_SNF_H': "is_SNF H2_DR (1\<^sub>m 1, H_1xn, Q3)"
     by (rule Smith_1xn_works[OF H' H_1xn_Q3])
   from this have Q3: "Q3 \<in> carrier_mat (dim_col H2_DR) (dim_col H2_DR)" and inv_Q3: "invertible_mat Q3" 
     unfolding is_SNF_def by auto
   have Q3': "Q3' \<in> carrier_mat (dim_col A) (dim_col A)"
     by (metis A A2 H' Q1 Q1' Q1'_def Q3 Q3'_def carrier_matD(1) carrier_matD(2) carrier_matI 
         index_mat_four_block(2) index_mat_four_block(3))   
   have Q_div_k[simp]: "Q_div_k \<in> carrier_mat (dim_col A) (dim_col A)" unfolding Q_div_k_def by auto
   have inv_Q_div_k: "invertible_mat Q_div_k"
     by (metis Q_div_k Q_div_k_def det_addrow_mat det_one invertible_iff_is_unit_JNF 
         invertible_mat_one nat.simps(3) numerals(2) one_carrier_mat)
   show "Q1' * Q2' * Q_div_k * Q3' \<in> carrier_mat (dim_col A) (dim_col A)"
     using Q1' Q2' Q_div_k Q3' by auto
   have inv_Q1': "invertible_mat Q1'"
   proof -
     have "invertible_mat (four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (n - 1)) (0\<^sub>m (n - 1) 1) Q1)"
       by (rule invertible_mat_four_block_mat_lower_right, insert Q1 inv_Q1 A2 "1.prems", auto)
     thus ?thesis unfolding Q1'_def using A by auto
   qed
   have inv_Q2': "invertible_mat Q2'"
     by (unfold Q2'_def, rule invertible_mat_four_block_mat_lower_right_id, 
         insert Q2 n_ge_2 inv_Q2 A D, auto)
   have inv_Q3': "invertible_mat Q3'"
   proof -
     have "invertible_mat (four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (n - 1)) (0\<^sub>m (n - 1) 1) Q3)"
       by (rule invertible_mat_four_block_mat_lower_right, insert Q3 H' inv_Q3 "1.prems", auto)
     thus ?thesis unfolding Q3'_def using A by auto
   qed
   show "invertible_mat (Q1' * Q2' * Q_div_k * Q3')"
     using inv_Q1' inv_Q2' inv_Q_div_k inv_Q3'
     by (meson Q1' Q2' Q3' Q_div_k invertible_mult_JNF mult_carrier_mat)
   have A_A1_A2: "A = A1 @\<^sub>c A2" unfolding A1_def A2_def append_cols_def 
   proof (rule eq_matI, auto)
     fix i assume i: "i < dim_row A" show 1: "A $$ (i, 0) = mat_of_cols (dim_row A) [col A 0] $$ (i, 0)"       
       by (metis dim_col_A_g2 gr_zeroI i index_col mat_of_cols_Cons_index_0 not_less0)
     let ?xs = "(map (col A) [Suc 0..<dim_col A])"
     fix j
     assume j1: "j < Suc (dim_col A - Suc 0)"
       and j2: "0 < j" 
     have "mat_of_cols (dim_row A) ?xs $$ (i, j - Suc 0) = ?xs ! (j - Suc 0) $v i"
       by (rule mat_of_cols_index, insert j1 j2 i, auto)
     also have "... = A $$ (i,j)" using dim_col_A_g2 i j1 j2 by auto
     finally show "A $$ (i, j) = mat_of_cols (dim_row A) ?xs $$ (i, j - Suc 0)" ..         
     next
       show "dim_col A = Suc (dim_col A - Suc 0)" using n_ge_2 A by auto
   qed
   have C_P1_A_Q1': "C = P1 * A * Q1'"
   proof -
     have aux: "P1 * (A1 @\<^sub>c A2) = ((P1 * A1) @\<^sub>c (P1 * A2))" 
       by (rule append_cols_mult_left, insert A1 A2 P1, auto)
     have "P1 * A * Q1' = P1 * (A1 @\<^sub>c A2) * Q1'" using A_A1_A2 by simp     
     also have "... = ((P1 * A1) @\<^sub>c (P1 * A2)) * Q1'" unfolding aux ..
     also have "... = (P1 * A1) @\<^sub>c ((P1 * A2) * Q1)"
       by (rule append_cols_mult_right_id, insert P1 A1 A2 Q1'_def Q1, auto)
     finally show ?thesis unfolding C_def by auto
   qed
   have E_ij_0: "E $$ (i,j) = 0" if i: "i<dim_row E" and j: "j<dim_col E" and ij: "(i,j) \<noteq> (1,0)" 
      for i j
   proof -
     let ?ws = "(map (col C) [2..<dim_col A])"
     have "E $$ (i,j) = ?ws ! j $v i " 
       by (unfold E_def, rule mat_of_cols_index, insert i j A E_def, auto)
     also have "... = (col C (j+2)) $v i" using E_def j by auto
     also have "... = C $$ (i,j+2)" 
       by (metis C_P1_A_Q1' P1 Q1' E_def carrier_matD(1) carrier_matD(2) index_col index_mult_mat(2)
           index_mult_mat(3) length_map length_upt less_diff_conv mat_of_cols_carrier(2)
           mat_of_cols_carrier(3) i j)
     also have "... = (if j + 2 < dim_col (P1*A1) then (P1*A1) $$ (i, j + 2) 
        else (P1 * A2 * Q1) $$ (i, (j+2) - 1))" 
       unfolding C_def 
       by (rule append_cols_nth, insert i j P1 A1 A2 Q1 A, auto simp add: E_def)    
     also have "... = (P1 * A2 * Q1) $$ (i, j+1)"
       by (metis A1 One_nat_def add.assoc add_diff_cancel_right' add_is_0 arith_special(3) 
           carrier_matD(2) index_mult_mat(3) less_Suc0 zero_neq_numeral)
     also have "... = 0" using SNF_P1A2Q1 unfolding Smith_normal_form_mat_def isDiagonal_mat_def
       by (metis (no_types, lifting) A A2 P1 Q1 Suc_diff_Suc Suc_mono E_def add_Suc_right 
           add_lessD1 arith_extra_simps(6) carrier_matD(1) carrier_matD(2) dim_col_A_g2 
           gr_implies_not0 index_mult_mat(2) index_mult_mat(3) length_map length_upt less_Suc_eq 
           mat_of_cols_carrier(2) mat_of_cols_carrier(3) numeral_2_eq_2 plus_1_eq_Suc i j ij)
     finally show ?thesis .
   qed
   have C_D_E: "C = D @\<^sub>c E"
   proof (rule eq_matI)
     have "C $$ (i, j) = mat_of_cols (dim_row A) [col C 0, col C 1] $$ (i, j)" 
       if  i: "i < dim_row A" and j: "j < 2" for i j
     proof -
       let ?ws = "[col C 0, col C 1]"
       have "mat_of_cols (dim_row A) [col C 0, col C 1] $$ (i, j) = ?ws ! j $v i"
         by (rule mat_of_cols_index, insert i j, auto)       
       also have "... = C $$ (i, j)" using j index_col 
         by (auto, smt A C_P1_A_Q1' P1 Q1' Suc_lessD carrier_matD i index_col index_mult_mat(2,3) 
             less_2_cases n_ge_2 nth_Cons_0 nth_Cons_Suc numeral_2_eq_2)
       finally show ?thesis by simp
     qed
     moreover have "C $$ (i, j) = mat_of_cols (dim_row A) (map (col C) [2..<dim_col A]) $$ (i, j - 2)"
       if i: "i < dim_row A" and j1: "j < dim_col A" and j2: "j \<ge> 2" for i j
     proof -
       let ?ws = "(map (col C) [2..<dim_col A])"
       have "mat_of_cols (dim_row A) ?ws $$ (i, j - 2) = ?ws ! (j-2) $v i"
         by (rule mat_of_cols_index, insert i j1 j2, auto)       
       also have "... = C $$ (i,j)"
         by (metis C_P1_A_Q1' P1 Q1' add_diff_inverse_nat carrier_matD(1) carrier_matD(2) dim_col_A_g2 
             i index_col index_mult_mat(2) index_mult_mat(3) less_diff_iff less_imp_le_nat 
             linorder_not_less nth_map_upt j1 j2)
       finally show ?thesis by auto
     qed
     ultimately show "\<And>i j. i < dim_row (D @\<^sub>c E) \<Longrightarrow> j < dim_col (D @\<^sub>c E) \<Longrightarrow> C $$ (i, j) = (D @\<^sub>c E) $$ (i, j)" 
       unfolding D_def E_def append_cols_def by (auto simp add: numerals)
     show "dim_row C = dim_row (D @\<^sub>c E)" using P1 A unfolding C_def D_def E_def append_cols_def by auto
     show "dim_col C = dim_col (D @\<^sub>c E)" using A1 Q1 A2 A n_ge_2 
       unfolding C_def D_def E_def append_cols_def by auto
   qed
   have E[simp]: "E\<in>carrier_mat 2 (n-2)" unfolding E_def using A by auto 
   have H[simp]: "H \<in> carrier_mat (dim_row A) (dim_col A)" unfolding H_def append_cols_def using A
     by (smt E Groups.add_ac(1) One_nat_def P2_P1 Q2 Q2' Q2'_def carrier_matD index_mat_four_block
          plus_1_eq_Suc index_mult_mat index_one_mat index_zero_mat numeral_2_eq_2 carrier_matI)
   have H_P2_P1_A_Q1'_Q2': "H = P2 * P1 * A * Q1' * Q2'"
   proof -
     have aux: "(P2 * D @\<^sub>c P2 * E) = P2 * (D @\<^sub>c E)"
       by (rule append_cols_mult_left[symmetric], insert D E P2 A, auto simp add: D_def E_def)
     have "H = P2 * D * Q2 @\<^sub>c P2 * E" using H_def by auto
     also have "... = (P2 * D @\<^sub>c P2 * E) * Q2'" by (rule append_cols_mult_right_id2[symmetric],
           insert Q2 D Q2'_def, auto simp add: D_def E_def)
     also have "... = (P2 * (D @\<^sub>c E)) * Q2'" using aux by auto
     also have "... = P2 * C * Q2'" unfolding C_D_E by auto
     also have "... = P2 * P1 * A * Q1' * Q2'" unfolding C_P1_A_Q1'
       by (smt P1 P2 Q1' P2_P1 assoc_mult_mat carrier_mat_triv index_mult_mat(2))
     finally show ?thesis .
   qed
   have H2_H_Q_div_k: "H2 = H * Q_div_k" unfolding H2_def Q_div_k_def
     by (metis H_P2_P1_A_Q1'_Q2' Q2' addcol_mat carrier_matD(2) dim_col_A_g2 gr_implies_not0 
         mat_carrier times_mat_def zero_order(5))
   hence H2_P2_P1_A_Q1'_Q2'_Q_div_k: "H2 = P2 * P1 * A * Q1' * Q2' * Q_div_k"
     unfolding H_P2_P1_A_Q1'_Q2' by simp
   have H2_as_four_block_mat: "H2 = four_block_mat H2_UL H2_UR H2_DL H2_DR" 
     by (rule split_block[OF split_H2[symmetric], of _ "n-1"], insert H2 A n_ge_2, auto)
   have H2_UL: "H2_UL \<in> carrier_mat 1 1"
     by (rule split_block[OF split_H2[symmetric], of _ "n-1"], insert H2 A n_ge_2, auto)
   have H2_UR: "H2_UR \<in> carrier_mat 1 (dim_col A - 1)"
     by (rule split_block(2)[OF split_H2[symmetric]], insert H2 A n_ge_2, auto)
   have H2_DL: "H2_DL \<in> carrier_mat 1 1"
     by (rule split_block[OF split_H2[symmetric], of _ "n-1"], insert H2 A n_ge_2, auto)
   have H2_DR: "H2_DR \<in> carrier_mat 1 (dim_col A - 1)"
     by (rule split_block[OF split_H2[symmetric]], insert H2 A n_ge_2, auto)
   have H2_UR_00: "H2_UR $$ (0,0) = 0"
   proof -
     have "H2_UR $$ (0,0) = H2 $$ (0,1)"
       by (smt A H2_H_Q_div_k H2_UL H2_as_four_block_mat H2_def H_P2_P1_A_Q1'_Q2' 
           Num.numeral_nat(7) P2_P1 Q2' add_diff_cancel_left' carrier_matD dim_col_A_g2 index_mat_addcol
           index_mat_four_block index_mult_mat less_trans_Suc plus_1_eq_Suc pos2 semiring_norm(138) 
           zero_less_one_class.zero_less_one)
     also have "... = H $$ (0,1)"
       unfolding H2_def by (rule index_mat_addcol, insert H A n_ge_2, auto) 
     also have "... = (P2 * D * Q2) $$ (0,1)"
       by (smt C_D_E C_P1_A_Q1' D H2_H_Q_div_k H2_UL H2_as_four_block_mat H_P2_P1_A_Q1'_Q2' H_def Q1' 
           Q2 add_lessD1 append_cols_def carrier_matD(1) carrier_matD(2) dim_col_A_g2 
           index_mat_four_block index_mult_mat(2) index_mult_mat(3) lessI numerals(2) plus_1_eq_Suc zero_less_Suc)
     also have "... = 0" using is_SNF_D P2D2Q2 D 
       unfolding is_SNF_def Smith_normal_form_mat_def isDiagonal_mat_def by auto
     finally show "H2_UR $$ (0,0) = 0" .
   qed
   have H2_UR_0j: "H2_UR $$ (0,j) = 0" if j_ge_1: "j > 1" and j: "j<n-1" for j
   proof -
    have col_E_0: "col E (j - 1) = 0\<^sub>v 2"
      by (rule eq_vecI, unfold col_def, insert E E_ij_0 j j_ge_1 n_ge_2, auto) 
        (metis E Suc_diff_Suc Suc_lessD Suc_less_eq Suc_pred carrier_matD index_vec numerals(2), insert E, blast)
    have "H2_UR $$ (0,j) = H2 $$ (0,j+1)"
      by (metis (no_types, lifting) A H2_P2_P1_A_Q1'_Q2'_Q_div_k H2_UL H2_as_four_block_mat H2_def 
          H_P2_P1_A_Q1'_Q2' P2_P1 Q2' add_diff_cancel_right' carrier_matD index_mat_addcol(5) 
          index_mat_four_block index_mult_mat(2,3) less_diff_conv less_numeral_extra(1) not_add_less2 pos2 j)
    also have "... = H $$ (0,j+1)" unfolding H2_def
      by (metis A H2_P2_P1_A_Q1'_Q2'_Q_div_k H2_def H_P2_P1_A_Q1'_Q2' One_nat_def P2_P1 Q_div_k_def 
          add_right_cancel carrier_matD(1) carrier_matD(2) index_mat_addcol(3) index_mat_addcol(5) 
          index_mat_addrow_mat(3) index_mult_mat(2) index_mult_mat(3) less_diff_conv less_not_refl2 
          numerals(2) plus_1_eq_Suc pos2 j j_ge_1)
    also have "... = (if j+1 < dim_col (P2 * D * Q2) 
      then (P2 * D * Q2) $$ (0, j+1) else (P2*E) $$ (0, (j+1) - 2))"
      by (unfold H_def, rule append_cols_nth, insert E P2 A Q2 D j, auto simp add: E_def)
    also have "... = (P2*E) $$ (0, j - 1)" 
      by (metis (no_types, lifting) D One_nat_def Q2 add_Suc_right add_lessD1 arithmetic_simps(50) 
          carrier_matD(2) diff_Suc_Suc index_mult_mat(3) not_less_eq numeral_2_eq_2 j_ge_1)
    also have "... = Matrix.row P2 0 \<bullet> col E (j - 1)" 
      by (rule index_mult_mat, insert P2 j_ge_1 A j, auto simp add: E_def)
    also have "... = 0" unfolding col_E_0 by (simp add: scalar_prod_def)
    finally show ?thesis .
  qed
  have H00_dvd_D01: "H$$(0,0) dvd D$$(0,1)"
  proof -
    have "H$$(0,0) = (P2*D*Q2) $$ (0,0)" unfolding H_def using append_cols_nth D E
      by (smt A C_D_E C_P1_A_Q1' D H2_DR H2_H_Q_div_k H2_UL H2_as_four_block_mat H_P2_P1_A_Q1'_Q2' 
          One_nat_def P1 Q1' Q2 Suc_lessD append_cols_def carrier_matD dim_col_A_g2 
          index_mat_four_block index_mult_mat numerals(2) plus_1_eq_Suc zero_less_Suc)
    also have "... dvd D$$(0,1)" by (rule S00_dvd_all_A[OF D _ _ inv_P2 inv_Q2],
          insert is_SNF_D P2D2Q2 P2 Q2 D, unfold is_SNF_def, auto)
    finally show ?thesis .    
  qed
  have D01_dvd_H02: "D$$(0,1) dvd H$$(0,2)" and D01_dvd_H12: "D$$(0,1) dvd H$$(1,2)"
  proof -
    have "D$$(0,1) = C$$(0,1)" unfolding C_D_E
      by (smt A C_D_E C_P1_A_Q1' D One_nat_def P1 Q1' append_cols_def carrier_matD(1) carrier_matD(2) 
          dim_col_A_g2 index_mat_four_block(1) index_mat_four_block(2) index_mat_four_block(3) 
          index_mult_mat(2) index_mult_mat(3) lessI less_trans_Suc numerals(2) pos2)
      also have "... = (P1*A2*Q1) $$ (0,0)" using C_def
        by (smt "1"(2) A1 A_A1_A2 P1 Q1 add_diff_cancel_left' append_cols_def card_num_simps(30) 
            carrier_matD dim_col_A_g2 index_mat_four_block index_mult_mat less_numeral_extra(4) 
            less_trans_Suc plus_1_eq_Suc pos2)
      also have "... dvd (P1*A2*Q1) $$ (1,1)"
        by (smt "1"(2) A2 One_nat_def P1 Q1 S00_dvd_all_A SNF_P1A2Q1 carrier_matD(1) carrier_matD(2) dim_col_A_g2 
            dvd_elements_mult_matrix_left_right inv_P1 inv_Q1 lessI less_diff_conv numeral_2_eq_2 plus_1_eq_Suc)
      also have "... = C $$ (1,2)" unfolding C_def
        by (smt "1"(2) A1 A_A1_A2 One_nat_def P1 Q1 append_cols_def carrier_matD(1) carrier_matD(2) diff_Suc_1 
            dim_col_A_g2 index_mat_four_block index_mult_mat lessI not_numeral_less_one numeral_2_eq_2)
      also have "... = E $$ (1,0)" unfolding C_D_E
        by (smt "1"(3) A C_D_E C_P1_A_Q1' D One_nat_def append_cols_def carrier_matD less_irrefl_nat
            P1 Q1' diff_Suc_1 diff_Suc_Suc index_mat_four_block index_mult_mat lessI  numerals(2))
      finally have *: "D$$(0,1) dvd E $$(1,0)" by auto
      also have "... dvd (P2*E)$$ (0,0)" 
        by (smt "1"(3) A E E_ij_0 P2 carrier_matD(1) carrier_matD(2) dvd_0_right 
            dvd_elements_mult_matrix_left dvd_refl pos2 zero_less_diff) 
      also have "... = H$$(0,2)" unfolding H_def
        by (smt "1"(3) A C_D_E C_P1_A_Q1' D Groups.add_ac(1) H2_DR H2_H_Q_div_k H2_UL H2_as_four_block_mat 
            H_P2_P1_A_Q1'_Q2' One_nat_def P1 Q1' Q2 add_diff_cancel_left' append_cols_def carrier_matD
             index_mat_four_block index_mult_mat less_irrefl_nat numerals(2) plus_1_eq_Suc pos2)
      finally show "D $$ (0, 1) dvd H $$ (0, 2)" .
      have "E $$(1,0) dvd (P2*E)$$ (1,0)"
        by (smt "1"(3) A E E_ij_0 P2 carrier_matD(1) carrier_matD(2) dvd_0_right 
            dvd_elements_mult_matrix_left dvd_refl rel_simps(49) semiring_norm(76) zero_less_diff)
      also have "... = H $$(1,2)" unfolding H_def
        by (smt A C_D_E C_P1_A_Q1' D H2_DR H2_H_Q_div_k H2_UL H2_as_four_block_mat H_P2_P1_A_Q1'_Q2' 
            One_nat_def P1 Q1' Q2 add_diff_cancel_left' append_cols_def carrier_matD diff_Suc_eq_diff_pred 
            index_mat_four_block index_mult_mat lessI less_irrefl_nat n_ge_2 numerals(2) plus_1_eq_Suc)
      finally show "D$$(0,1) dvd H$$(1,2)" using * by auto
    qed
    have kH00_eq_H02: "k * H $$ (0, 0) = H $$ (0, 2)" 
      using id D01_dvd_H02 H00_dvd_D01 unfolding k_def is_div_op_def by auto
    have H2_UR_01: "H2_UR $$ (0,1) = 0"
    proof -
      have "H2_UR $$ (0,1) = H2 $$ (0,2)"
        by (metis (no_types, lifting) A H2_P2_P1_A_Q1'_Q2'_Q_div_k H2_UL H2_as_four_block_mat One_nat_def 
            P2_P1 Q_div_k_def carrier_matD diff_Suc_1 dim_col_A_g2 index_mat_addrow_mat(3) 
            index_mat_four_block index_mult_mat(2,3) numeral_2_eq_2 pos2 rel_simps(50) rel_simps(68))
      also have "... = (-k) * H $$ (0, 0) + H $$ (0, 2)" 
        by (unfold H2_def, rule index_mat_addcol[of _ ], insert H A n_ge_2, auto)
      also have "... = 0" using kH00_eq_H02 by auto
      finally show ?thesis .
    qed   
   have H2_UR_0: "H2_UR = (0\<^sub>m 1 (n - 1))"
     by (rule eq_matI, insert H2_UR_0j H2_UR_01 H2_UR_00 H2_UR A nat_neq_iff, auto)
   have H2_UL_H: "H2_UL $$ (0,0) = H $$ (0,0)"
   proof -
     have "H2_UL $$ (0,0) = H2 $$ (0,0)"
       by (metis (no_types, lifting) Pair_inject index_mat(1) split_H2 split_block_def 
           zero_less_one_class.zero_less_one)
     also have "... = H $$ (0,0)" 
       unfolding H2_def by (rule index_mat_addcol, insert H A n_ge_2, auto) 
     finally show ?thesis .
   qed
   have H2_DL_H_10: "H2_DL $$ (0,0) = H$$(1,0)"
   proof -
     have "H2_DL $$ (0,0) = H2 $$ (1,0)"
       by (smt H2_DL One_nat_def Pair_inject add.right_neutral add_Suc_right carrier_matD(1) 
           dim_row_mat(1) index_mat(1) rel_simps(68) split_H2 split_block_def split_conv)
     also have "... = H$$(1,0)" unfolding H2_def by (rule index_mat_addcol, insert H A n_ge_2, auto) 
     finally show ?thesis .
   qed
   have H_10: "H $$(1,0) = 0"
   proof -
     have "H $$(1,0) = (P2 * D * Q2) $$ (1,0)" unfolding H_def
       by (smt A C_D_E C_P1_A_Q1' D E One_nat_def P1 P2_P1 Q2 Q2' Q2'_def Suc_lessD append_cols_def 
           carrier_matD dim_col_A_g2 index_mat_four_block index_mult_mat index_one_mat 
           index_zero_mat lessI numerals(2))
     also have "... = 0" using is_SNF_D P2D2Q2 D 
       unfolding is_SNF_def Smith_normal_form_mat_def isDiagonal_mat_def by auto
     finally show ?thesis .
   qed
   have S_H2_Q3': "S = H2 * Q3'" 
     and S_as_four_block_mat: "S = four_block_mat (H2_UL) (0\<^sub>m 1 (n - 1)) (H2_DL) (H2_DR * Q3)"
   proof -
     have "H2 * Q3' = four_block_mat (H2_UL * 1\<^sub>m 1 + H2_UR * 0\<^sub>m (dim_col A - 1) 1) 
     (H2_UL * 0\<^sub>m 1 (dim_col A - 1) + H2_UR * Q3)
     (H2_DL * 1\<^sub>m 1 + H2_DR * 0\<^sub>m (dim_col A - 1) 1) (H2_DL * 0\<^sub>m 1 (dim_col A - 1) + H2_DR * Q3)"
       unfolding H2_as_four_block_mat Q3'_def 
       by (rule mult_four_block_mat[OF H2_UL H2_UR H2_DL H2_DR], insert Q3 A H', auto)
     also have "... = four_block_mat (H2_UL) (0\<^sub>m 1 (n - 1)) (H2_DL) (H2_DR * Q3)"
       by (rule cong_four_block_mat, insert H2_UR_0 H2_UL H2_UR H2_DL H2_DR Q3, auto)
     also have *: "... = S" unfolding S_def 
     proof (rule cong_four_block_mat)
       show "H2_UL = Matrix.mat 1 1 (\<lambda>(a, b). H $$ (0, 0))" 
         by (rule eq_matI, insert H2_UL H2_UL_H, auto)
       show "H2_DR * Q3 = H_1xn" using is_SNF_H' unfolding is_SNF_def by auto
       show "0\<^sub>m 1 (n - 1) = 0\<^sub>m 1 (dim_col A - 1)" using A by auto
       show "H2_DL = 0\<^sub>m 1 1" using H2_DL H2_DL_H_10 H_10 by auto
     qed
     finally show "S = H2 * Q3'" 
       and "S = four_block_mat (H2_UL) (0\<^sub>m 1 (n - 1)) (H2_DL) (H2_DR * Q3)"
       using * by auto
   qed
   thus "S = P2 * P1 * A * (Q1' * Q2' * Q_div_k * Q3')" unfolding H2_P2_P1_A_Q1'_Q2'_Q_div_k     
     by (smt Q1' Q2' Q2'_def Q3' Q3'_def Q_div_k assoc_mult_mat 
         carrier_matD carrier_mat_triv index_mult_mat)
   show "Smith_normal_form_mat S"
   proof (rule Smith_normal_form_mat_intro)
     have Sij_0: "S$$(i,j) = 0" if ij: "i \<noteq> j" and i: "i < dim_row S" and j: "j < dim_col S" for i j
     proof (cases "i=1 \<and> j=0")
       case True
       have "S$$(1,0) = 0" using S_as_four_block_mat
         by (metis (no_types, lifting) H2_DL_H_10 H2_UL H_10 One_nat_def True carrier_matD diff_Suc_1 
             index_mat_four_block rel_simps(71) that(2) that(3) zero_less_one_class.zero_less_one)
       then show ?thesis using True by auto
      next
        case False note not_10 = False
        show ?thesis
        proof (cases "i=0")
          case True
          hence j0: "j>0" using ij by auto
          then show ?thesis using S_as_four_block_mat
            by (smt "1"(2) H2_DR H2_H_Q_div_k H2_UL H_P2_P1_A_Q1'_Q2' Num.numeral_nat(7) P2_P1 Q3 S_H2_Q3'
                Suc_pred True carrier_matD index_mat_four_block index_mult_mat index_zero_mat(1)
                not_less_eq plus_1_eq_Suc pos2 that(3) zero_less_one_class.zero_less_one)
        next
          case False
          have SNF_H_1xn: "Smith_normal_form_mat H_1xn" using is_SNF_H' unfolding is_SNF_def by auto 
          have i1: "i=1" using False ij i H2_DR H2_UL S_as_four_block_mat by auto
          hence j1: "j>1" using ij not_10 by auto thm is_SNF_H'
          have "S$$(i,j) = (if i < dim_row H2_UL then if j < dim_col H2_UL then H2_UL $$ (i, j) 
            else (0\<^sub>m 1 (n - 1)) $$ (i, j - dim_col H2_UL)
            else if j < dim_col H2_UL then H2_DL $$ (i - dim_row H2_UL, j) 
            else (H2_DR * Q3) $$ (i - dim_row H2_UL, j - dim_col H2_UL))"
            unfolding S_as_four_block_mat 
            by (rule index_mat_four_block, insert i j H2_UL H2_DR Q3 S_H2_Q3' H2 Q3' A, auto)
          also have "... = (H2_DR * Q3) $$ (0, j - 1)" using H2_UL i1 not_10 by auto
          also have "... = H_1xn $$ (0,j-1)"
            using S_def calculation i1 j not_10 i by auto           
          also have "... = 0" using SNF_H_1xn j1 i j
            unfolding Smith_normal_form_mat_def isDiagonal_mat_def
            by (simp add: S_def i1)
          finally show ?thesis .
        qed
      qed
      thus "isDiagonal_mat S" unfolding isDiagonal_mat_def by auto
      have "S$$(0,0) dvd S$$(1,1)"
      proof -       
        have dvd_all: "\<forall>i j. i < 2 \<and> j < n \<longrightarrow> H2_UL$$(0,0) dvd (H2 * Q3') $$ (i, j)"
        proof (rule dvd_elements_mult_matrix_right)
          show H2': "H2 \<in> carrier_mat 2 n" using H2 A by auto
          show "Q3' \<in> carrier_mat n n" using Q3' A by auto
          have "H2_UL $$ (0, 0) dvd H2 $$ (i, j)" if i: "i < 2" and j: "j < n"  for i j
          proof (cases "i=0")
            case True
            then show ?thesis
              by (metis (no_types, lifting) A H2_H_Q_div_k H2_UL H2_UR_0 H2_as_four_block_mat 
                  H_P2_P1_A_Q1'_Q2' P2_P1 Q3 Q_div_k S_as_four_block_mat Sij_0 carrier_matD 
                  dvd_0_right dvd_refl index_mat_four_block index_mult_mat(2,3) j less_one pos2)
          next
            case False
            hence i1: "i=1" using i by auto
            have H2_10_0: "H2 $$ (1,0) = 0"
              by (metis (no_types, lifting) H2_H_Q_div_k H2_def H_10 H_P2_P1_A_Q1'_Q2' One_nat_def 
                  Q2' H2' basic_trans_rules(19) carrier_matD dim_col_A_g2 index_mat_addcol(3)
                  index_mult_mat(2,3) lessI numeral_2_eq_2 rel_simps(76))            
            moreover have H2_UL00_dvd_H211:"H2_UL $$ (0, 0) dvd H2 $$ (1, 1)"
            proof - 
              have "H2_UL $$ (0, 0) = H $$ (0, 0)" by (simp add: H2_UL_H)
              also have "... = (P2*D*Q2) $$ (0,0)" unfolding H_def using append_cols_nth D E
                by (smt A C_D_E C_P1_A_Q1' D H2_DR H2_H_Q_div_k H2_UL H2_as_four_block_mat 
                    H_P2_P1_A_Q1'_Q2' One_nat_def P1 Q1' Q2 Suc_lessD append_cols_def carrier_matD 
                    dim_col_A_g2 index_mat_four_block index_mult_mat numerals(2) plus_1_eq_Suc zero_less_Suc)
              also have "... dvd (P2*D*Q2) $$ (1,1)" 
                using is_SNF_D P2D2Q2 unfolding is_SNF_def Smith_normal_form_mat_def by auto 
                (metis D Q2 carrier_matD index_mult_mat(1) index_mult_mat(2) lessI numerals(2) pos2)
              also have "... = H $$ (1,1)" unfolding H_def using append_cols_nth D E
                by (smt A C_D_E C_P1_A_Q1' H2_DR H2_H_Q_div_k H2_UL H2_as_four_block_mat H_P2_P1_A_Q1'_Q2' 
                    One_nat_def P1 Q1' Q2 append_cols_def carrier_matD(1) carrier_matD(2) dim_col_A_g2 
                    index_mat_four_block index_mult_mat(2) index_mult_mat(3) lessI less_trans_Suc 
                    numerals(2) plus_1_eq_Suc pos2)
              also have "... = H2 $$ (1, 1)" 
                by (metis A H2_def H_P2_P1_A_Q1'_Q2' One_nat_def P2_P1 Q2' carrier_matD dim_col_A_g2 i i1 
                    index_mat_addcol(3) index_mult_mat(2) index_mult_mat(3) less_trans_Suc nat_neq_iff pos2)
              finally show ?thesis .
            qed
            moreover have H2_UL00_dvd_H212: "H2_UL $$ (0, 0) dvd H2 $$ (1, 2)"
            proof -            
              have "H2_UL $$ (0, 0) = H $$ (0, 0)" by (simp add: H2_UL_H)
              also have "... dvd H $$ (1,2)" using D01_dvd_H12 H00_dvd_D01 dvd_trans by blast
              also have "... = (-k) * H $$ (1,0) + H $$ (1,2)"
                using H_10 by auto
              also have "... = H2 $$ (1,2)" 
                unfolding H2_def by (rule index_mat_addcol[symmetric], insert H A n_ge_2, auto)
              finally show ?thesis .
            qed
            moreover have "H2 $$ (1, j) = 0" if j1: "j>2" and j: "j<n"
            proof -
              let ?f = "(\<lambda>(i, j). \<Sum>ia = 0..<dim_vec (col E j). Matrix.row P2 i $v ia * col E j $v ia)"
              have "H2 $$ (1, j) = H $$ (1,j)" unfolding H2_def using j j1 n_ge_2 
                by (metis (mono_tags, lifting) "1"(2) H2' H_10 H_P2_P1_A_Q1'_Q2' Q2' arithmetic_simps(49) 
                    carrier_matD i i1 index_mat_addcol(1) index_mult_mat semiring_norm(64) H2_H_Q_div_k)
              also have "... = (P2*E)$$ (1,j-2)" unfolding H_def
                by (smt A C_D_E C_P1_A_Q1' D H2' H2_H_Q_div_k H_P2_P1_A_Q1'_Q2' P1 Q1' Q2 append_cols_def 
                    basic_trans_rules(19) carrier_matD index_mat_four_block index_mult_mat(2) 
                    index_mult_mat(3) j less_one nat_neq_iff not_less_less_Suc_eq numerals(2) j1)
              also have "... =  Matrix.mat (dim_row P2) (dim_col E) ?f $$ (1, j - 2)"
                unfolding times_mat_def scalar_prod_def by simp 
              also have "... = ?f (1,j-2)" by (rule index_mat, insert P2 E E_def n_ge_2 j j1 A, auto)              
              also have "... = (\<Sum>ia = 0..<2. Matrix.row P2 1 $v ia * col E (j-2) $v ia)" 
                using E A E_def j j1 by auto
              also have "... = (\<Sum>ia \<in> {0,1}. Matrix.row P2 1 $v ia * col E (j-2) $v ia)" 
                by (rule sum.cong, auto)
              also have "... = Matrix.row P2 1 $v 0 * col E (j - 2) $v 0 
                    + Matrix.row P2 1 $v 1 * col E (j - 2) $v 1" 
                by (simp add: sum_two_elements[OF zero_neq_one])
              also have "... = 0" using E_ij_0 E_def E A
                by (auto, smt D Q2 Q2' Q2'_def Suc_lessD add_cancel_right_right add_diff_inverse_nat 
                    arith_extra_simps(19) carrier_matD i i1 index_col index_mat_four_block(3) 
                    index_one_mat(3) less_2_cases nat_add_left_cancel_less numeral_2_eq_2 
                    semiring_norm(138) semiring_norm(160) j j1 zero_less_diff)                
              finally show ?thesis .
            qed
            ultimately show ?thesis using i1 False
              by (metis One_nat_def dvd_0_right less_2_cases nat_neq_iff j)
          qed                      
          thus "\<forall>i j. i < 2 \<and> j < n \<longrightarrow> H2_UL $$ (0, 0) dvd H2 $$ (i, j)" by auto
        qed
        have "S$$(0,0) = H2_UL $$ (0,0)" using H2_UL S_as_four_block_mat by auto
        also have "... dvd (H2*Q3') $$ (1,1)" using dvd_all n_ge_2 by auto
        also have "... = S $$ (1,1)" using S_H2_Q3' by auto
        finally show ?thesis .       
      qed
      thus "\<forall>a. a + 1 < min (dim_row S) (dim_col S) \<longrightarrow> S $$ (a, a) dvd S $$ (a + 1, a + 1)"
        by (metis "1"(2) H2_H_Q_div_k H_P2_P1_A_Q1'_Q2' One_nat_def P2_P1 S_H2_Q3' Suc_eq_plus1
            index_mult_mat(2) less_Suc_eq less_one min_less_iff_conj numeral_2_eq_2 carrier_matD(1))
    qed
  qed
qed


lemma is_SNF_Smith_2xn: 
  assumes A: "A \<in> carrier_mat 2 n"
  shows "is_SNF A (Smith_2xn A)"
proof (cases "n>2")
  case True
  then show ?thesis using is_SNF_Smith_2xn_n_ge_2[OF A] by simp
next
  case False
  hence "n=0 \<or> n=1 \<or> n=2" by auto
  then show ?thesis using Smith_2xn_0 Smith_2xn_1 Smith_2xn_2 A by blast
qed

subsubsection \<open>Case $n \times 2$\<close>

definition "Smith_nx2 A = (let (P,S,Q) = Smith_2xn A\<^sup>T in
   (Q\<^sup>T, S\<^sup>T, P\<^sup>T))"

lemma is_SNF_Smith_nx2: 
  assumes A: "A \<in> carrier_mat n 2"
  shows "is_SNF A (Smith_nx2 A)"
proof -
  obtain P S Q where PSQ: "(P,S,Q) = Smith_2xn A\<^sup>T" by (metis prod_cases3)
  hence rw: "Smith_nx2 A = (Q\<^sup>T, S\<^sup>T, P\<^sup>T)" unfolding Smith_nx2_def by (metis split_conv)
  have "is_SNF A\<^sup>T (Smith_2xn A\<^sup>T)" by (rule is_SNF_Smith_2xn, insert id A, auto)
  hence is_SNF_PSQ: "is_SNF A\<^sup>T (P,S,Q)" using PSQ by auto
  show ?thesis
  proof (unfold rw, rule is_SNF_intro)
    show Qt: "Q\<^sup>T \<in> carrier_mat (dim_row A) (dim_row A)"
      and Pt: "P\<^sup>T \<in> carrier_mat (dim_col A) (dim_col A)"
      and "invertible_mat Q\<^sup>T" and "invertible_mat P\<^sup>T"
      using is_SNF_PSQ invertible_mat_transpose unfolding is_SNF_def by auto
    have "Smith_normal_form_mat S" and PATQ: "S =  P * A\<^sup>T * Q"
      using is_SNF_PSQ invertible_mat_transpose unfolding is_SNF_def by auto
    thus "Smith_normal_form_mat S\<^sup>T" unfolding Smith_normal_form_mat_def isDiagonal_mat_def by auto
    show "S\<^sup>T = Q\<^sup>T * A * P\<^sup>T" using PATQ
      by (smt Matrix.transpose_mult Matrix.transpose_transpose Pt Qt assoc_mult_mat
          carrier_mat_triv index_mult_mat(2))
  qed
qed

subsubsection \<open>Case $m \times n$\<close>

(*This is necessary to avoid a loop with domintros*)
declare Smith_2xn.simps[simp del]

function (domintros) Smith_mxn :: "'a mat \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat)"
  where
    "Smith_mxn A = (
  if dim_row A = 0 \<or> dim_col A = 0 then (1\<^sub>m (dim_row A),A,1\<^sub>m (dim_col A))
  else if dim_row A = 1 then (1\<^sub>m 1, Smith_1xn A) 
  else if dim_row A = 2 then Smith_2xn A
  else if dim_col A = 1 then let (P,S) = Smith_nx1 A in (P,S,1\<^sub>m 1)
  else if dim_col A = 2 then Smith_nx2 A
  else
  let A1 = mat_of_row (Matrix.row A 0);
      A2 = mat_of_rows (dim_col A) [Matrix.row A i. i \<leftarrow> [1..<dim_row A]];
      (P1,D1,Q1) = Smith_mxn A2;
      C = (A1*Q1) @\<^sub>r (P1*A2*Q1);
      D = mat_of_rows (dim_col A) [Matrix.row C 0, Matrix.row C 1];
      E = mat_of_rows (dim_col A) [Matrix.row C i. i \<leftarrow> [2..<dim_row A]];
      (P2,F,Q2) = Smith_2xn D;
      H = (P2*D*Q2) @\<^sub>r (E*Q2);
      (P_H2, H2) = reduce_column div_op H;
      (H2_UL, H2_UR, H2_DL, H2_DR) = split_block H2 1 1;
      (P3,S',Q3) = Smith_mxn H2_DR;
      S = four_block_mat (Matrix.mat 1 1 (\<lambda>(a, b). H $$ (0, 0))) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_row A - 1) 1) S';
      P1' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_row A - 1)) (0\<^sub>m (dim_row A - 1) 1) P1;
      P2' = four_block_mat P2 (0\<^sub>m 2 (dim_row A - 2)) (0\<^sub>m (dim_row A - 2) 2) (1\<^sub>m (dim_row A - 2));
      P3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_row A - 1)) (0\<^sub>m (dim_row A - 1) 1) P3;
      Q3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_col A - 1) 1) Q3
  in (P3' * P_H2 * P2' * P1',S, Q1 * Q2 * Q3')
)"
  by pat_completeness fast
(*Termination is guaranteed since the algorithm is recursively applied to a 
  submatrix with less rows*)


(*Now I introduce it again*)
declare Smith_2xn.simps[simp]

lemma Smith_mxn_dom_nm_less_2: 
  assumes A: "A \<in> carrier_mat m n" and mn: "n\<le>2 \<or> m\<le>2"
  shows "Smith_mxn_dom A"
  by (rule Smith_mxn.domintros, insert assms, auto) (*Takes a while*)

lemma Smith_mxn_pinduct_carrier_less_2: 
  assumes A: "A \<in> carrier_mat m n" and mn: "n\<le>2 \<or> m\<le>2"
  shows "fst (Smith_mxn A) \<in> carrier_mat m m 
  \<and> fst (snd (Smith_mxn A)) \<in> carrier_mat m n
  \<and> snd (snd (Smith_mxn A)) \<in> carrier_mat n n"
proof -
  have A_dom: "Smith_mxn_dom A" using Smith_mxn_dom_nm_less_2[OF assms] by simp
  show ?thesis
proof (cases "dim_row A = 0 \<or> dim_col A = 0")
  case True
  have "Smith_mxn A = (1\<^sub>m (dim_row A),A,1\<^sub>m (dim_col A))"
    using Smith_mxn.psimps[OF A_dom] True by auto
  thus ?thesis using A by auto        
next
  case False note 1 = False
  show ?thesis
  proof (cases "dim_row A = 1")
    case True
    have "Smith_mxn A = (1\<^sub>m 1, Smith_1xn A)"
      using Smith_mxn.psimps[OF A_dom] True 1 by auto
    then show ?thesis using Smith_1xn_works unfolding is_SNF_def
      by (smt Smith_1xn_aux_Q_carrier Smith_1xn_aux_S'_AQ' Smith_1xn_def True assms(1) carrier_matD 
          carrier_matI diff_less fst_conv index_mult_mat not_gr0 one_carrier_mat prod.collapse 
          right_mult_one_mat' snd_conv zero_less_one_class.zero_less_one)
  next
    case False note 2 = False
    then show ?thesis 
    proof (cases "dim_row A = 2")
      case True
      hence A': "A \<in> carrier_mat 2 n" using A by auto
      have "Smith_mxn A = Smith_2xn A" using Smith_mxn.psimps[OF A_dom] True 1 2 by auto
      then show ?thesis using is_SNF_Smith_2xn[OF A'] A unfolding is_SNF_def
        by (metis (mono_tags, lifting) carrier_matD carrier_mat_triv case_prod_beta index_mult_mat(2,3))
    next
      case False note 3 = False
      show ?thesis 
      proof (cases "dim_col A = 1")
        case True
        hence A': "A \<in> carrier_mat m 1" using A by auto
        have "Smith_mxn A = (let (P,S) = Smith_nx1 A in (P,S,1\<^sub>m 1))" 
          using Smith_mxn.psimps[OF A_dom] True 1 2 3 by auto
        then show ?thesis using Smith_nx1_works[OF A'] A unfolding is_SNF_def
          by (metis (mono_tags, lifting) carrier_matD carrier_mat_triv case_prod_unfold 
              index_mult_mat(2,3) surjective_pairing)
      next
        case False
        hence "dim_col A = 2" using 1 2 3 mn A by auto
        hence A': "A \<in> carrier_mat m 2" using A by auto
        hence "Smith_mxn A = Smith_nx2 A" 
          using Smith_mxn.psimps[OF A_dom] 1 2 3 False by auto
        then show ?thesis using is_SNF_Smith_nx2[OF A'] A unfolding is_SNF_def by force
      qed
    qed  
  qed
qed
qed

lemma Smith_mxn_pinduct_carrier_ge_2: "\<lbrakk>Smith_mxn_dom A; A \<in> carrier_mat m n; m>2; n>2\<rbrakk> \<Longrightarrow> 
    fst (Smith_mxn A) \<in> carrier_mat m m 
  \<and> fst (snd (Smith_mxn A)) \<in> carrier_mat m n
  \<and> snd (snd (Smith_mxn A)) \<in> carrier_mat n n"
proof (induct arbitrary: m n rule: Smith_mxn.pinduct)
  case (1 A)
  note A_dom = 1(1)
  note A = "1.prems"(1)
  note m = "1.prems"(2)
  note n = "1.prems"(3)  
  define A1 where "A1 = mat_of_row (Matrix.row A 0)"
  define A2 where "A2 = mat_of_rows (dim_col A) [Matrix.row A i. i \<leftarrow> [1..<dim_row A]]"
  obtain P1 D1 Q1 where P1D1Q1: "(P1,D1,Q1) = Smith_mxn A2" by (metis prod_cases3)
  define C where "C = (A1*Q1) @\<^sub>r (P1*A2*Q1)"
  define D where "D = mat_of_rows (dim_col A) [Matrix.row C 0, Matrix.row C 1]"
  define E where "E = mat_of_rows (dim_col A) [Matrix.row C i. i \<leftarrow> [2..<dim_row A]]"
  obtain P2 F Q2 where P2FQ2: "(P2,F,Q2) = Smith_2xn D" by (metis prod_cases3)
  define H where "H = (P2*D*Q2) @\<^sub>r (E*Q2)"
  obtain P_H2 H2 where P_H2H2: "(P_H2, H2) = reduce_column div_op H" by (metis surj_pair)
  obtain H2_UL H2_UR H2_DL H2_DR where split_H2: "(H2_UL, H2_UR, H2_DL, H2_DR) = split_block H2 1 1"
    by (metis split_block_def)
  obtain P3 S' Q3 where P3S'Q3: "(P3,S',Q3) = Smith_mxn H2_DR" by (metis prod_cases3)
  define S where "S = four_block_mat (Matrix.mat 1 1 (\<lambda>(a, b). H $$ (0, 0))) (0\<^sub>m 1 (dim_col A - 1))
    (0\<^sub>m (dim_row A - 1) 1) S'"
  define P1' where "P1' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_row A - 1)) (0\<^sub>m (dim_row A - 1) 1) P1"
  define P2' where "P2' = four_block_mat P2 (0\<^sub>m 2 (dim_row A - 2)) (0\<^sub>m (dim_row A - 2) 2) (1\<^sub>m (dim_row A - 2))"
  define P3' where "P3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_row A - 1)) (0\<^sub>m (dim_row A - 1) 1) P3"
  define Q3' where "Q3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_col A - 1) 1) Q3"
  have A1: "A1 \<in> carrier_mat 1 n" unfolding A1_def using A by auto
  have A2: "A2 \<in> carrier_mat (m-1) n" unfolding A2_def using A by auto
  have "fst (Smith_mxn A2) \<in> carrier_mat (m-1) (m-1)
  \<and> fst (snd (Smith_mxn A2)) \<in> carrier_mat (m-1) n
  \<and> snd (snd (Smith_mxn A2)) \<in> carrier_mat n n"
  proof (cases "2 < m - 1")
    case True
    show ?thesis by (rule "1.hyps"(2), insert A m n A2_def A1_def True id, auto)    
  next
    case False
    hence "m=3" using m by auto
    hence A2': "A2 \<in> carrier_mat 2 n" using A2 by auto
    have A2_dom: "Smith_mxn_dom A2" by (rule Smith_mxn.domintros, insert A2', auto)    
    have "dim_row A2 = 2" using A2 A2' by fast
    hence "Smith_mxn A2 = Smith_2xn A2" 
      using n unfolding Smith_mxn.psimps[OF A2_dom] by auto
    then show ?thesis using is_SNF_Smith_2xn[OF A2'] m A2 unfolding is_SNF_def split_beta
      by (metis carrier_matD carrier_matI index_mult_mat(2,3))
  qed
  hence P1: "P1 \<in> carrier_mat (m-1) (m-1)" 
    and D1: "D1 \<in> carrier_mat (m-1) n" 
    and Q1: "Q1 \<in> carrier_mat n n" using P1D1Q1 by (metis fst_conv snd_conv)+
  have "C \<in> carrier_mat (1 + (m-1)) n" unfolding C_def 
    by (rule carrier_append_rows, insert P1 D1 Q1 A1, auto)
  hence C: "C \<in> carrier_mat m n" using m by simp
  have D: "D \<in> carrier_mat 2 n" unfolding D_def using C A by auto
  have E: "E \<in> carrier_mat (m-2) n" unfolding E_def using A by auto
  have P2: "P2 \<in> carrier_mat 2 2" and Q2: "Q2 \<in> carrier_mat n n" 
    using is_SNF_Smith_2xn[OF D] P2FQ2 D unfolding is_SNF_def by auto
  have "H \<in> carrier_mat (2 + (m-2)) n" unfolding H_def 
    by (rule carrier_append_rows, insert P2 D Q2 E, auto)
  hence H: "H \<in> carrier_mat m n" using m by auto
  have H2: "H2 \<in> carrier_mat m n" using m H P_H2H2 reduce_column by blast
  have H2_DR: "H2_DR \<in> carrier_mat (m - 1) (n - 1)"
    by (rule split_block(4)[OF split_H2[symmetric]], insert H2 m n, auto)
  have "fst (Smith_mxn H2_DR) \<in> carrier_mat (m-1) (m-1)
  \<and> fst (snd (Smith_mxn H2_DR)) \<in> carrier_mat (m-1) (n-1)
  \<and> snd (snd (Smith_mxn H2_DR)) \<in> carrier_mat (n-1) (n-1)"
  proof (cases "2<m-1 \<and> 2<n-1")
    case True
    show ?thesis
    proof (rule "1.hyps"(3)[OF _ _ _ _ _ A1_def A2_def P1D1Q1 _ _ C_def])
      show "(P2,F,Q2) = Smith_2xn D" using P2FQ2 by auto
    qed (insert A P1D1Q1 D_def E_def P2FQ2 P_H2H2 P3S'Q3 H_def split_H2 H2_DR True id, auto)
  next
    case False note m_eq_3_or_n_eq_3 = False
    show ?thesis 
    proof (cases "(2 < m - 1)")
      case True
      hence n3: "n=3" using m_eq_3_or_n_eq_3 n m by auto
      have H2_DR_dom: "Smith_mxn_dom H2_DR"
        by (rule Smith_mxn.domintros, insert H2_DR n3, auto)
      have H2_DR': "H2_DR \<in> carrier_mat (m-1) 2" using H2_DR n3 by auto
      hence "dim_col H2_DR = 2" by simp
      hence "Smith_mxn H2_DR = Smith_nx2 H2_DR" 
        using n H2_DR' True unfolding Smith_mxn.psimps[OF H2_DR_dom] by auto
      then show ?thesis using is_SNF_Smith_nx2[OF H2_DR'] m H2_DR unfolding is_SNF_def by auto
    next
      case False
      hence m3: "m=3" using m_eq_3_or_n_eq_3 n m by auto
      have H2_DR_dom: "Smith_mxn_dom H2_DR"
        by (rule Smith_mxn.domintros, insert H2_DR m3, auto)
      have H2_DR': "H2_DR \<in> carrier_mat 2 (n-1)" using H2_DR m3 by auto
      hence "dim_row H2_DR = 2" by simp
      hence "Smith_mxn H2_DR = Smith_2xn H2_DR" 
        using n H2_DR' unfolding Smith_mxn.psimps[OF H2_DR_dom] by auto
      then show ?thesis using is_SNF_Smith_2xn[OF H2_DR'] m H2_DR unfolding is_SNF_def by force
    qed
  qed
  hence P3: "P3 \<in> carrier_mat (m-1) (m-1)"
  and S': "S'\<in> carrier_mat (m-1) (n-1)"
  and Q3: "Q3 \<in> carrier_mat (n-1) (n-1)" using P3S'Q3 by (metis fst_conv snd_conv)+
  have Smith_final: "Smith_mxn A = (P3' * P_H2 * P2' * P1', S, Q1 * Q2 * Q3')"
  proof -
    have P1_def: "P1 = fst (Smith_mxn A2)" and D1_def: "D1 = fst (snd (Smith_mxn A2))" 
      and Q1_def: "Q1 = snd (snd (Smith_mxn A2))" using P1D1Q1 by (metis fstI sndI)+
    have P2_def: "P2 = fst (Smith_2xn D)" and F_def: "F = fst (snd (Smith_2xn D))" 
      and Q2_def: "Q2 = snd (snd (Smith_2xn D))" using P2FQ2 by (metis fstI sndI)+
    have P_H2_def: "P_H2 = fst (reduce_column div_op H)" 
      and H2_def: "H2 = snd (reduce_column div_op H)" 
      using P_H2H2 by (metis fstI sndI)+
    have H2_UL_def: "H2_UL = fst (split_block H2 1 1)" 
      and H2_UR_def: "H2_UR = fst (snd (split_block H2 1 1))" 
      and H2_DL_def: "H2_DL = fst (snd (snd (split_block H2 1 1)))" 
      and H2_DR_def: "H2_DR = snd (snd (snd (split_block H2 1 1)))"
      using split_H2 by (metis fstI sndI)+
    have P3_def: "P3 = fst (Smith_mxn H2_DR)"
      and S'_def: "S' = fst (snd (Smith_mxn H2_DR))" 
      and Q3_def: "Q3 = (snd (snd (Smith_mxn H2_DR)))" using P3S'Q3 by (metis fstI sndI)+
    note aux = Smith_mxn.psimps[OF A_dom] Let_def split_beta
     A1_def[symmetric] A2_def[symmetric] P1_def[symmetric] D1_def[symmetric] Q1_def[symmetric]
     C_def[symmetric] D_def[symmetric] E_def[symmetric] P2_def[symmetric] Q2_def[symmetric]
     F_def[symmetric] H_def[symmetric] P_H2_def[symmetric] H2_def[symmetric] H2_UL_def[symmetric]
     H2_DL_def[symmetric] H2_UR_def[symmetric] H2_DR_def[symmetric] P3_def[symmetric] S'_def[symmetric]
     Q3_def[symmetric] P1'_def[symmetric] P2'_def[symmetric] P3'_def[symmetric] Q1_def[symmetric]
     Q2_def[symmetric] Q3'_def[symmetric] S_def[symmetric]
    show ?thesis by (rule prod3_intro, unfold aux, insert "1.prems", auto)
  qed
  have P1': "P1' \<in> carrier_mat m m" unfolding P1'_def using P1 m by auto
  moreover have P2': "P2' \<in> carrier_mat m m" unfolding P2'_def using P2 m A by auto
  moreover have P3': "P3' \<in> carrier_mat m m" unfolding P3'_def using P3 m by auto
  moreover have P_H2: "P_H2 \<in> carrier_mat m m" using reduce_column[OF H P_H2H2] m by simp
  moreover have "S \<in> carrier_mat m n" unfolding S_def using H A S'
    by (auto, smt C One_nat_def Suc_pred \<open>C \<in> carrier_mat (1 + (m - 1)) n\<close> carrier_matD carrier_matI 
        dim_col_mat(1) dim_row_mat(1) index_mat_four_block n neq0_conv plus_1_eq_Suc zero_order(3))
  moreover have "Q3' \<in> carrier_mat n n" unfolding Q3'_def using Q3 n by auto
  ultimately show ?case using Smith_final Q1 Q2 by auto
qed


corollary Smith_mxn_pinduct_carrier: "\<lbrakk>Smith_mxn_dom A; A \<in> carrier_mat m n\<rbrakk> \<Longrightarrow> 
    fst (Smith_mxn A) \<in> carrier_mat m m 
  \<and> fst (snd (Smith_mxn A)) \<in> carrier_mat m n
  \<and> snd (snd (Smith_mxn A)) \<in> carrier_mat n n"
  using Smith_mxn_pinduct_carrier_ge_2 Smith_mxn_pinduct_carrier_less_2
  by (meson linorder_not_le)


termination proof (relation "measure (\<lambda>A. dim_row A)")
  fix A A1 A2 xb P1 y D1 Q1 C D E xf P2 yb Q2 F yc H xj P_H2 H2 xl xm ye xn yf xo yg
  assume 1: "\<not> (dim_row A = 0 \<or> dim_col A = 0)" and 2: "dim_row A \<noteq> 1"
    and 3: "dim_row A \<noteq> 2" and 4: "dim_col A \<noteq> 1" and 5: "dim_col A \<noteq> 2"
    and 6: "A1 = mat_of_row (Matrix.row A 0)"
    and xa_def: "A2 = mat_of_rows (dim_col A) (map (Matrix.row A) [1..<dim_row A])"
    and xb_def: "xb = Smith_mxn A2" and P1_y_xb: "(P1, y) = xb "
    and D1_Q1_y: "(D1, Q1) = y " and C_def: "C = A1 * Q1 @\<^sub>r P1* A2 * Q1 "
    and D_def: "D = mat_of_rows (dim_col A) [Matrix.row C 0, Matrix.row C 1] "
    and E_def: "E = mat_of_rows (dim_col A) (map (Matrix.row C) [2..<dim_row A]) "
    and xf: "xf = Smith_2xn D" and P2_yb_xf: "(P2, yb) = xf" and F_Q2_yb: "(F, Q2) = yb "
    and H_def: "H = P2 * D * Q2 @\<^sub>r E * Q2 " and xj: "xj = reduce_column div_op H "
    and P_H2_H2: "(P_H2, H2) = xj" and b4: "xl = split_block H2 1 1 "
    and b1: "(xm, ye) = xl" and b2: "(xn, yf) = ye" and b3: "(xo, yg) = yf" 
    and A2_dom: "Smith_mxn_dom A2" 
  let ?m = "dim_row A"
  let ?n = "dim_col A"
  have m: "2< ?m" and n: "2 < ?n" using 1 2 3 4 5 6 by auto  
  have A1: "A1 \<in> carrier_mat 1 (dim_col A)" using 6 by auto
  have A2: "A2 \<in> carrier_mat (dim_row A - 1) (dim_col A)" using xa_def by auto
  have "fst (Smith_mxn A2) \<in> carrier_mat (?m-1) (?m-1) 
        \<and> fst (snd (Smith_mxn A2)) \<in> carrier_mat (?m-1) ?n
        \<and> snd (snd (Smith_mxn A2)) \<in> carrier_mat ?n ?n" 
    by (rule Smith_mxn_pinduct_carrier[OF A2_dom A2])
  hence P1: "P1\<in> carrier_mat (?m-1) (?m-1)"and D1: "D1 \<in> carrier_mat (?m-1) ?n"
    and Q1: "Q1 \<in> carrier_mat ?n ?n" using P1_y_xb D1_Q1_y xa_def xb_def by (metis fstI sndI)+
  have C: "C \<in> carrier_mat ?m ?n" unfolding C_def using A1 Q1 P1 A2 Q1 
    by (smt 1 Suc_pred card_num_simps(30) carrier_append_rows mult_carrier_mat neq0_conv plus_1_eq_Suc)
  have D: "D \<in> carrier_mat 2 ?n" unfolding D_def using C by auto
  have E: "E \<in> carrier_mat (?m-2) ?n" unfolding E_def using C m by auto
  have P2FQ2: "(P2,F,Q2) = Smith_2xn D" using F_Q2_yb P2_yb_xf xf by blast
  have P2: "P2\<in>carrier_mat 2 2" and F: "F \<in> carrier_mat 2 ?n" and Q2: "Q2 \<in> carrier_mat ?n ?n"
    using is_SNF_Smith_2xn[OF D] D P2FQ2 unfolding is_SNF_def by auto
  have "H \<in> carrier_mat (2 + (?m-2)) ?n" 
    by (unfold H_def, rule carrier_append_rows, insert D Q2 P2 E, auto)
  hence H: "H \<in> carrier_mat ?m ?n" using m by auto
  have H2: "H2 \<in> carrier_mat (dim_row H) (dim_col H)" 
    and P_H2: "P_H2 \<in> carrier_mat (dim_row A) (dim_row A)"
    using reduce_column[OF H xj[unfolded P_H2_H2[symmetric]]] m H by auto    
  have "dim_row yg < dim_row H2"      
    by (rule split_block4_decreases_dim_row, insert b1 b2 b3 b4 m n H H2, auto)
  also have "... = dim_row A" using H2 H by auto
  finally show "(yg, A) \<in> measure dim_row" unfolding in_measure .
qed (auto)


lemma is_SNF_Smith_mxn_less_2: 
  assumes A: "A \<in> carrier_mat m n" and mn: "n\<le>2 \<or> m\<le>2"
  shows "is_SNF A (Smith_mxn A)"
proof -
  show ?thesis
  proof (cases "dim_row A = 0 \<or> dim_col A = 0")
    case True
    have "Smith_mxn A = (1\<^sub>m (dim_row A),A,1\<^sub>m (dim_col A))"
      using Smith_mxn.simps True by auto
    thus ?thesis using A True unfolding is_SNF_def by auto
  next
    case False note 1 = False
    show ?thesis
    proof (cases "dim_row A = 1")
      case True
      have "Smith_mxn A = (1\<^sub>m 1, Smith_1xn A)"
        using Smith_mxn.simps True 1 by auto
      then show ?thesis using Smith_1xn_works by (metis True carrier_mat_triv surj_pair)
    next
      case False note 2 = False
      then show ?thesis 
      proof (cases "dim_row A = 2")
        case True
        hence A': "A \<in> carrier_mat 2 n" using A by auto
        have "Smith_mxn A = Smith_2xn A" using Smith_mxn.simps True 1 2 by auto
        then show ?thesis using is_SNF_Smith_2xn[OF A'] A by auto
      next
        case False note 3 = False
        show ?thesis 
        proof (cases "dim_col A = 1")
          case True
          hence A': "A \<in> carrier_mat m 1" using A by auto
          have "Smith_mxn A = (let (P,S) = Smith_nx1 A in (P,S,1\<^sub>m 1))" 
            using Smith_mxn.simps True 1 2 3 by auto
          then show ?thesis using Smith_nx1_works[OF A'] A by (auto simp add: case_prod_beta)          
        next
          case False
          hence "dim_col A = 2" using 1 2 3 mn A by auto
          hence A': "A \<in> carrier_mat m 2" using A by auto
          hence "Smith_mxn A = Smith_nx2 A" 
            using Smith_mxn.simps 1 2 3 False by auto
          then show ?thesis using is_SNF_Smith_nx2[OF A'] A by force
        qed
      qed  
    qed
  qed
qed


lemma is_SNF_Smith_mxn_ge_2: 
  assumes A: "A \<in> carrier_mat m n" and m: "m>2" and n: "n>2"
  shows "is_SNF A (Smith_mxn A)"
  using A m n
proof (induct A arbitrary: m n rule: Smith_mxn.induct)
  case (1 A)
  note A = "1.prems"(1)
  note m = "1.prems"(2)
  note n = "1.prems"(3)  
  have A_dim_not0:  "\<not> (dim_row A = 0 \<or> dim_col A = 0)" and A_dim_row_not1: "dim_row A \<noteq> 1"
    and A_dim_row_not2: "dim_row A \<noteq> 2" and A_dim_col_not1: "dim_col A \<noteq> 1"
    and A_dim_col_not2: "dim_col A \<noteq> 2"
    using A m n by auto
  note A_dim_intro = A_dim_not0 A_dim_row_not1 A_dim_row_not2 A_dim_col_not1 A_dim_col_not2
  define A1 where "A1 = mat_of_row (Matrix.row A 0)"
  define A2 where "A2 = mat_of_rows (dim_col A) [Matrix.row A i. i \<leftarrow> [1..<dim_row A]]"
  obtain P1 D1 Q1 where P1D1Q1: "(P1,D1,Q1) = Smith_mxn A2" by (metis prod_cases3)
  define C where "C = (A1*Q1) @\<^sub>r (P1*A2*Q1)"
  define D where "D = mat_of_rows (dim_col A) [Matrix.row C 0, Matrix.row C 1]"
  define E where "E = mat_of_rows (dim_col A) [Matrix.row C i. i \<leftarrow> [2..<dim_row A]]"
  obtain P2 F Q2 where P2FQ2: "(P2,F,Q2) = Smith_2xn D" by (metis prod_cases3)
  define H where "H = (P2*D*Q2) @\<^sub>r (E*Q2)"
  obtain P_H2 H2 where P_H2H2: "(P_H2, H2) = reduce_column div_op H" by (metis surj_pair)
  obtain H2_UL H2_UR H2_DL H2_DR where split_H2: "(H2_UL, H2_UR, H2_DL, H2_DR) = split_block H2 1 1"
    by (metis split_block_def)
  obtain P3 S' Q3 where P3S'Q3: "(P3,S',Q3) = Smith_mxn H2_DR" by (metis prod_cases3)
  define S where "S = four_block_mat (Matrix.mat 1 1 (\<lambda>(a, b). H $$ (0, 0))) (0\<^sub>m 1 (dim_col A - 1))
    (0\<^sub>m (dim_row A - 1) 1) S'"
  define P1' where "P1' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_row A - 1)) (0\<^sub>m (dim_row A - 1) 1) P1"
  define P2' where "P2' = four_block_mat P2 (0\<^sub>m 2 (dim_row A - 2)) (0\<^sub>m (dim_row A - 2) 2) (1\<^sub>m (dim_row A - 2))"
  define P3' where "P3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_row A - 1)) (0\<^sub>m (dim_row A - 1) 1) P3"
  define Q3' where "Q3' = four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_col A - 1) 1) Q3"
  have Smith_final: "Smith_mxn A = (P3' * P_H2 * P2' * P1', S, Q1 * Q2 * Q3')"
  proof -
    have P1_def: "P1 = fst (Smith_mxn A2)" and D1_def: "D1 = fst (snd (Smith_mxn A2))" 
      and Q1_def: "Q1 = snd (snd (Smith_mxn A2))" using P1D1Q1 by (metis fstI sndI)+
    have P2_def: "P2 = fst (Smith_2xn D)" and F_def: "F = fst (snd (Smith_2xn D))" 
      and Q2_def: "Q2 = snd (snd (Smith_2xn D))" using P2FQ2 by (metis fstI sndI)+
    have P_H2_def: "P_H2 = fst (reduce_column div_op H)"
      and H2_def: "H2 = snd (reduce_column div_op H)" 
      using P_H2H2 by (metis fstI sndI)+
    have H2_UL_def: "H2_UL = fst (split_block H2 1 1)" 
      and H2_UR_def: "H2_UR = fst (snd (split_block H2 1 1))" 
      and H2_DL_def: "H2_DL = fst (snd (snd (split_block H2 1 1)))" 
      and H2_DR_def: "H2_DR = snd (snd (snd (split_block H2 1 1)))"
      using split_H2 by (metis fstI sndI)+
    have P3_def: "P3 = fst (Smith_mxn H2_DR)" and S'_def: "S' = fst (snd (Smith_mxn H2_DR))" 
      and Q3_def: "Q3 = (snd (snd (Smith_mxn H2_DR)))" using P3S'Q3 by (metis fstI sndI)+
    note aux = Smith_mxn.simps[of A] Let_def split_beta
      A1_def[symmetric] A2_def[symmetric] P1_def[symmetric] D1_def[symmetric] Q1_def[symmetric]
      C_def[symmetric] D_def[symmetric] E_def[symmetric] P2_def[symmetric] Q2_def[symmetric]
      F_def[symmetric] H_def[symmetric] P_H2_def[symmetric] H2_def[symmetric] H2_UL_def[symmetric]
      H2_DL_def[symmetric] H2_UR_def[symmetric] H2_DR_def[symmetric] P3_def[symmetric] S'_def[symmetric]
      Q3_def[symmetric] P1'_def[symmetric] P2'_def[symmetric] P3'_def[symmetric] Q1_def[symmetric]
      Q2_def[symmetric] Q3'_def[symmetric] S_def[symmetric]
    show ?thesis by (rule prod3_intro, unfold aux, insert "1.prems", auto)
  qed
  show ?case
  proof (unfold Smith_final, rule is_SNF_intro)
    have A1[simp]: "A1 \<in> carrier_mat 1 n" unfolding A1_def using A by auto
    have A2[simp]: "A2 \<in> carrier_mat (m-1) n" unfolding A2_def using A by auto
    have is_SNF_A2: "is_SNF A2 (Smith_mxn A2)"
    proof (cases "n \<le> 2 \<or> m - 1 \<le> 2")
      case True
      then show ?thesis using is_SNF_Smith_mxn_less_2[OF A2] by simp
    next
      case False
      hence n1: "2<n" and m1: "2<m-1" by auto
      show ?thesis by (rule "1.hyps"(1)[OF A_dim_intro A1_def A2_def A2 m1 n1])        
    qed
    have P1[simp]: "P1 \<in> carrier_mat (m-1) (m-1)" 
      and inv_P1: "invertible_mat P1" 
      and Q1: "Q1 \<in> carrier_mat n n" and inv_Q1: "invertible_mat Q1"
      and SNF_P1A2Q1: "Smith_normal_form_mat (P1*A2*Q1)"
      using is_SNF_A2 P1D1Q1 A2 A n m unfolding is_SNF_def by auto
    have C[simp]: "C \<in> carrier_mat m n" unfolding C_def  using P1 Q1 A1 A2 m
      by (smt "1"(3) A_dim_not0 Suc_pred card_num_simps(30) carrier_append_rows carrier_matD 
          carrier_mat_triv index_mult_mat(2,3) neq0_conv plus_1_eq_Suc)
    have D[simp]: "D \<in> carrier_mat 2 n" unfolding D_def using A m by auto  
    have is_SNF_D: "is_SNF D (Smith_2xn D)" by (rule is_SNF_Smith_2xn[OF D])
    hence P2[simp]: "P2 \<in> carrier_mat 2 2" and inv_P2: "invertible_mat P2"
      and Q2[simp]: "Q2 \<in> carrier_mat n n" and inv_Q2: "invertible_mat Q2"
      and F[simp]: "F \<in> carrier_mat 2 n" and F_P2DQ2: "F = P2*D*Q2"
      and SNF_F: "Smith_normal_form_mat F"
      using P2FQ2 D_def A unfolding is_SNF_def by auto
    have E[simp]: "E \<in> carrier_mat (m-2) n" unfolding E_def using A by auto
    have H_aux: "H \<in> carrier_mat (2 + (m-2)) n" unfolding H_def 
      by (rule carrier_append_rows, insert P2 D Q2 E F_P2DQ2 F A m n mult_carrier_mat, force)    
    hence H[simp]: "H \<in> carrier_mat m n" using m by auto
    have H2[simp]: "H2 \<in> carrier_mat m n" using m H P_H2H2 A reduce_column by blast
    have H2_DR[simp]: "H2_DR \<in> carrier_mat (m - 1) (n - 1)"
      by (rule split_block(4)[OF split_H2[symmetric]], insert H2 m n A H, auto, insert H2, blast+)    
    have P1'[simp]: "P1' \<in> carrier_mat m m" unfolding P1'_def using P1 m by auto
    have P2'[simp]: "P2' \<in> carrier_mat m m" unfolding P2'_def using P2 m A m 
      by (metis (no_types, lifting) H H_aux carrier_matD carrier_mat_triv 
          index_mat_four_block(2,3) index_one_mat(2,3))
    have is_SNF_H2_DR: "is_SNF H2_DR (Smith_mxn H2_DR)"
    proof (cases "2 < m - 1 \<and> 2 < n - 1")
      case True
      hence m1: "2<m-1" and n1: "2<n-1" by simp+
      show ?thesis
        by (rule "1.hyps"(2)[OF A_dim_intro A1_def A2_def P1D1Q1 _ _ C_def D_def E_def P2FQ2 _ _ H_def
              P_H2H2 _ split_H2 _ _ _ H2_DR m1 n1], auto)
    next
      case False
      hence "m-1\<le>2 \<or> n-1\<le>2" by auto
      then show ?thesis using H2_DR is_SNF_Smith_mxn_less_2 by blast
    qed
    hence P3[simp]: "P3 \<in> carrier_mat (m-1) (m-1)" and inv_P3: "invertible_mat P3"
      and Q3[simp]: "Q3 \<in> carrier_mat (n-1) (n-1)" and inv_Q3: "invertible_mat Q3"
      and S'[simp]: "S' \<in> carrier_mat (m-1) (n-1)" and S'_P3H2_DRQ3: "S' = P3 * H2_DR * Q3"
      and SNF_S': "Smith_normal_form_mat S'"
      using A m n H2_DR P3S'Q3 unfolding is_SNF_def by auto
    have P3'[simp]: "P3' \<in> carrier_mat m m" unfolding P3'_def using P3 m by auto
    have P_H2[simp]: "P_H2 \<in> carrier_mat m m" using reduce_column[OF H P_H2H2] m by simp
    have S[simp]: "S \<in> carrier_mat m n" unfolding S_def using H A S'
      by (smt A_dim_intro(1) One_nat_def Suc_pred carrier_matD carrier_matI dim_col_mat(1)
          dim_row_mat(1) index_mat_four_block(2,3) nat_neq_iff not_less_zero plus_1_eq_Suc)
    have Q3'[simp]: "Q3' \<in> carrier_mat n n" unfolding Q3'_def using Q3 n by auto
        (*The following two goals could have been resolved with Smith_mxn_pinduct_carrier, but we need the 
  dimensions of each matrix anyway*)
    show P_final_carrier: "P3' * P_H2 * P2' * P1' \<in> carrier_mat (dim_row A) (dim_row A)" 
      using P3' P_H2 P2' P1' A by (metis carrier_matD carrier_matI index_mult_mat(2,3))
    show Q_final_carrier: "Q1 * Q2 * Q3' \<in> carrier_mat (dim_col A) (dim_col A)"
      using Q1 Q2 Q3' A by (metis carrier_matD carrier_matI index_mult_mat(2,3))
    have inv_P1': "invertible_mat P1'" unfolding P1'_def
      by (rule invertible_mat_four_block_mat_lower_right[OF _ inv_P1], insert A P1, auto)
    have inv_P2': "invertible_mat P2'" unfolding P2'_def
      by (rule invertible_mat_four_block_mat_lower_right_id[OF _ _ _ _ _ inv_P2], insert A m, auto)
    have inv_P3': "invertible_mat P3'" unfolding P3'_def
      by (rule invertible_mat_four_block_mat_lower_right[OF _ inv_P3], insert A P3, auto)
    have inv_P_H2: "invertible_mat P_H2" using reduce_column[OF H P_H2H2] m by simp
    show "invertible_mat (P3' * P_H2 * P2' * P1')" using inv_P1' inv_P2' inv_P3' inv_P_H2
      by (meson P1' P2' P3' P_H2 invertible_mult_JNF mult_carrier_mat)
    have inv_Q3': "invertible_mat Q3'" unfolding Q3'_def
      by (rule invertible_mat_four_block_mat_lower_right[OF _ inv_Q3], insert A Q3, auto)    
    show "invertible_mat (Q1 * Q2 * Q3')" using inv_Q1 inv_Q2 inv_Q3'    
      by (meson Q1 Q2 Q3' invertible_mult_JNF mult_carrier_mat)  
    have A_A1_A2: "A = A1 @\<^sub>r A2" unfolding append_cols_def 
    proof (rule eq_matI)
      have A1_A2': "A1 @\<^sub>r A2 \<in> carrier_mat (1+(m-1)) n" by (rule carrier_append_rows[OF A1 A2])
      hence A1_A2: "A1 @\<^sub>r A2 \<in> carrier_mat m n" using m by simp
      thus "dim_row A = dim_row (A1 @\<^sub>r A2)" and "dim_col A = dim_col (A1 @\<^sub>r A2)" using A by auto
      fix i j assume i: "i < dim_row (A1 @\<^sub>r A2)" and j: "j < dim_col (A1 @\<^sub>r A2)"
      show "A $$ (i, j) = (A1 @\<^sub>r A2) $$ (i, j)"
      proof (cases "i=0")
        case True
        have "(A1 @\<^sub>r A2) $$ (i, j) = (A1 @\<^sub>r A2) $$ (0, j)" using True by simp
        also have "... = four_block_mat A1 (0\<^sub>m (dim_row A1) 0) A2 (0\<^sub>m (dim_row A2) 0) $$ (0,j)"
          unfolding append_rows_def ..
        also have "... = A1 $$ (0,j)" using A1 A1_A2 j by auto
        also have "... = A $$ (0,j)" unfolding A1_def using A1_A2 A i j by auto
        finally show ?thesis using True by simp
      next
        case False
        let ?xs = "(map (Matrix.row A) [1..<dim_row A])"
        have "(A1 @\<^sub>r A2) $$ (i, j) = four_block_mat A1 (0\<^sub>m (dim_row A1) 0) A2 (0\<^sub>m (dim_row A2) 0) $$ (i,j)"
          unfolding append_rows_def ..
        also have "... = A2 $$ (i-1,j)" using A1 A1_A2' A2 False i j by auto
        also have "... = mat_of_rows (dim_col A) ?xs $$ (i - 1, j)" by (simp add: A2_def)
        also have "... = ?xs ! (i-1) $v j" by (rule mat_of_rows_index, insert i False A j m A1_A2, auto)
        also have "... = A $$ (i,j)" using False A A1_A2 i j by auto
        finally show ?thesis ..
      qed    
    qed
    have C_eq: "C = P1' * A * Q1"
    proof -
      have aux: "(A1 @\<^sub>r A2) * Q1 = ((A1 * Q1) @\<^sub>r (A2*Q1))"
        by (rule append_rows_mult_right, insert A1 A2 Q1, auto)
      have "P1' * A * Q1 = P1' * (A1 @\<^sub>r A2) * Q1" using A_A1_A2 by simp
      also have "... =  P1' * ((A1 @\<^sub>r A2) * Q1)" using A A_A1_A2 P1' Q1 assoc_mult_mat by blast
      also have "... = P1' * ((A1 * Q1) @\<^sub>r (A2*Q1))" by (simp add: aux)
      also have "... = (A1 * Q1) @\<^sub>r (P1 * (A2 * Q1))" 
        by (rule append_rows_mult_left_id, insert A1 Q1 A2 P1 P1'_def A, auto)
      also have "... = (A1 * Q1) @\<^sub>r (P1 * A2 * Q1)" using A2 P1 Q1 by auto
      finally show ?thesis unfolding C_def ..
    qed
    have C_D_E: "C = D @\<^sub>r E"
    proof -
      let ?xs = "[Matrix.row C 0, Matrix.row C 1]"
      let ?ys = "(map (Matrix.row C) [0..<2])" 
      have xs_ys: "?xs = ?ys" by (simp add: upt_conv_Cons)
      have D_rw: "D = mat_of_rows (dim_col C) (map (Matrix.row C) [0..<2])" 
        unfolding D_def xs_ys using A C by (metis carrier_matD(2))
      have d1: "dim_col A = dim_col C" using A C by blast
      have d2: "dim_row A = dim_row C" using A C by blast
      show ?thesis unfolding D_rw E_def d1 d2 by (rule append_rows_split, insert m C A d2, auto)
    qed
    have H_eq: "H = P2' * P1' * A * Q1 * Q2"
    proof -
      have aux: "((P2 * D) @\<^sub>r E) = P2' * (D @\<^sub>r E)" 
        by (rule append_rows_mult_left_id2[symmetric, OF D E _ P2], insert P2'_def A, auto)
      have "H = P2 * D * Q2 @\<^sub>r E * Q2" by (simp add: H_def)
      also have "... = (P2 * D @\<^sub>r E) * Q2" 
        by (rule append_rows_mult_right[symmetric, OF mult_carrier_mat[OF P2 D] E Q2])
      also have "... = P2' * (D @\<^sub>r E) * Q2" by (simp add: aux)
      also have "... =  P2' * C * Q2" unfolding C_D_E by simp
      also have "... = P2' * (P1' * A * Q1) * Q2" unfolding C_eq by simp
      also have "... = P2' * P1' * A * Q1 * Q2"
        by (smt A P1' P2' Q1 \<open>P2' * C * Q2 = P2' * (P1' * A * Q1) * Q2\<close> assoc_mult_mat mult_carrier_mat)
      finally show ?thesis .    
    qed
    have P_H2_H_H2: "P_H2 * H = H2" using reduce_column[OF H P_H2H2] m by auto
    hence H2_eq: "H2 = P_H2 * P2' * P1' * A * Q1 * Q2" unfolding H_eq
      by (smt P1' P1'_def P2' P2'_def P_H2 P_final_carrier Q1 Q2 Q_final_carrier assoc_mult_mat 
          carrier_matD carrier_mat_triv index_mult_mat(2,3))        
    have H2_as_four_block_mat: "H2 = four_block_mat H2_UL H2_UR H2_DL H2_DR" 
      using split_H2 by (metis (no_types, lifting) H2 P1' P1'_def Q3' Q3'_def carrier_matD 
          index_mat_four_block(2) index_one_mat(2) split_block(5))
    have H2_UL: "H2_UL \<in> carrier_mat 1 1" 
      by (rule split_block(1)[OF split_H2[symmetric], of "m-1" "n-1"], insert H2 A m n, auto, insert H2, blast+)
    have H2_UR: "H2_UR \<in> carrier_mat 1 (n-1)"
      by (rule split_block(2)[OF split_H2[symmetric], of "m-1"], insert H2 A m n, auto, insert H2, blast+)
    have H2_DL: "H2_DL \<in> carrier_mat (m-1) 1"
      by (rule split_block(3)[OF split_H2[symmetric], of _ "n-1"], insert H2 A m n, auto, insert H2, blast+)
    have H2_DR: "H2_DR \<in> carrier_mat (m-1) (n-1)"
      by (rule split_block(4)[OF split_H2[symmetric], of _ "n-1"], insert H2 A m n, auto, insert H2, blast+)
    have H_ij_F_ij: "H$$(i,j) = F $$(i,j)" if i: "i<2" and j: "j<n" for i j
    proof -
      have "H$$(i,j) = (if i < dim_row (P2*D*Q2) then (P2*D*Q2) $$ (i, j) else (E*Q2) $$ (i - 2, j))"      
      proof (unfold H_def, rule append_rows_nth)
        show "P2 * D * Q2 \<in> carrier_mat 2 n" using F F_P2DQ2 by blast
        show "E * Q2 \<in> carrier_mat (m-2) n" using E Q2 using mult_carrier_mat by blast
      qed (insert m j i, auto)
      also have "... = F $$ (i, j)" using F F_P2DQ2 i by auto
      finally show ?thesis .
    qed
    have isDiagonal_F: "isDiagonal_mat F" 
      using is_SNF_D P2FQ2 unfolding is_SNF_def Smith_normal_form_mat_def by auto
    have H_0j_0: "H $$ (0,j) = 0" if j: "j\<in>{1..<n}" for j
    proof -   
      have "H $$ (0,j) = F $$ (0, j)" using H_ij_F_ij j by auto
      also have "... = 0" using isDiagonal_F unfolding isDiagonal_mat_def using F j by auto
      finally show ?thesis .    
    qed
    have H2_0j: "H2 $$ (0,j) = H $$ (0,j)" if j: "j<n" for j
      by (rule reduce_column_preserves2[OF H P_H2H2 _ _ _ j], insert m, auto)
    have H2_UR_0: "H2_UR = (0\<^sub>m 1 (n-1))"
    proof (rule eq_matI)
      show "dim_row H2_UR = dim_row (0\<^sub>m 1 (n - 1))" and "dim_col H2_UR = dim_col (0\<^sub>m 1 (n - 1))"
        using H2_UR by auto
      fix i j assume i: "i < dim_row (0\<^sub>m 1 (n - 1))" and j: "j < dim_col (0\<^sub>m 1 (n - 1))"
      have i0: "i=0" using i by auto
      have 1: "0 < dim_row H2_UL + dim_row H2_DR" using i H2_UL H2_DR by auto
      have 2: "j+1 < dim_col H2_UL + dim_col H2_DR" using j H2_UL H2_DR by auto
      have "H2_UR $$ (i, j) = H2 $$ (0,j+1)"
        unfolding i0 H2_as_four_block_mat using index_mat_four_block(1)[OF 1 2] H2_UL by auto
      also have "... = H $$ (0,j+1)" by (rule H2_0j, insert j, auto)
      also have "... = 0" using H_0j_0 j by auto
      finally show "H2_UR $$ (i, j) = 0\<^sub>m 1 (n - 1) $$ (i, j)" using i j by auto
    qed
    have H2_UL00_H00: "H2_UL $$ (0,0) = H $$ (0,0)"
      using H2_UL H2_as_four_block_mat H2_0j n by fastforce
    have F00_dvd_Dij: "F$$(0,0) dvd D$$(i,j)" if i: "i<2" and j: "j<n" for i j
      by (rule S00_dvd_all_A[OF D P2 Q2 inv_P2 inv_Q2 F_P2DQ2 SNF_F i j])
        (*
    Scheme of the proof:
    - D $$ (1,0) dvd all elements of E
    - F$$(0,0) divides all elements of D, in particular divides D$$(1,0)
    - Hence, F$$(0,0) divides all elements of E.
    - Hence, F$$(0,0) divides all elements of E * Q2
  *)
    have D10_dvd_Eij: "D$$(1,0) dvd E$$(i,j)" if i: "i<m-2" and j: "j<n" for i j
    proof -
      have "D$$(1,0) = C$$(1,0)"
        by (smt C C_D_E F F_P2DQ2 H H_def One_nat_def Suc_lessD add_diff_cancel_right' append_rows_def
            arith_special(3) carrier_matD index_mat_four_block index_mult_mat(2) lessI m n plus_1_eq_Suc)
      also have "... = (P1*A2*Q1) $$ (0,0)"
        by (smt "1"(3) A1 A2 A_A1_A2 A_dim_not0 P1 Q1 Suc_eq_plus1 Suc_lessD add_diff_cancel_right' 
            append_rows_def arith_special(3) card_num_simps(30) carrier_matD index_mat_four_block 
            index_mult_mat(2,3) less_not_refl2 local.C_def m neq0_conv)
      also have " ... dvd (P1*A2*Q1) $$ (i+1,j)"
        by (rule SNF_first_divides_all[OF SNF_P1A2Q1 _ _ j], insert P1 A2 Q1 i A, auto)
      also have "... = C $$ (i+2,j)" unfolding C_def using append_rows_nth
        by (smt A A1 A2 A_A1_A2 P1 Q1 Suc_lessD add_Suc_right add_diff_cancel_left' append_rows_def
            arith_special(3) carrier_matD index_mat_four_block index_mult_mat(2,3) j less_diff_conv 
            not_add_less2 plus_1_eq_Suc that(1))
      also have "... = E$$(i,j)"
        by (smt C C_D_E D add_diff_cancel_right' append_rows_def carrier_matD index_mat_four_block j i
            less_diff_conv not_add_less2)
      finally show ?thesis .   
    qed
    have F00_H00: "F $$ (0,0) = H $$ (0,0)" using H_ij_F_ij n by auto
    have F00_dvd_Eij: "F$$(0,0) dvd E$$(i,j)" if i: "i<m-2" and j: "j<n" for i j
      by (metis (no_types, lifting) A A_dim_not0 D10_dvd_Eij F00_dvd_Dij arith_special(3) carrier_matD(2) 
          dvd_trans j lessI neq0_conv plus_1_eq_Suc i)
    have F00_dvd_EQ2ij: "F$$(0,0) dvd (E*Q2) $$ (i,j)" if i: "i<m-2" and j: "j<n" for i j
      using dvd_elements_mult_matrix_right[OF E Q2]  F00_dvd_Eij i j by auto
    have H00_dvd_all: "H $$ (0, 0) dvd H $$ (i, j)" if i: "i<m" and j: "j<n" for i j
    proof (cases "i<2")
      case True
      then show ?thesis by (metis F F00_H00 H_ij_F_ij SNF_F SNF_first_divides_all j)
    next
      case False
      have "F $$ (0,0) dvd (E*Q2) $$ (i-2,j)" by (rule F00_dvd_EQ2ij, insert False i j, auto)
      moreover have "H $$ (i, j) = (E*Q2) $$ (i-2,j)"
        by (smt C C_D_E D F F_P2DQ2 False H_def append_rows_def carrier_matD i 
            index_mat_four_block index_mult_mat(2) j)
      ultimately show ?thesis using F00_H00 by simp
    qed    
    have H_00_dvd_H_i0: "H $$ (0, 0) dvd H $$ (i, 0)" if i: "i<m" for i
      using H00_dvd_all[OF i] n by auto
    have H2_DL_0: "H2_DL = (0\<^sub>m (m - 1) 1)"
    proof (rule eq_matI)
      show "dim_row (H2_DL) = dim_row (0\<^sub>m (m - 1) 1)"
        and "dim_col (H2_DL) = dim_col (0\<^sub>m (m - 1) 1)" using P3 H2_DL A by auto
      fix i j assume i: "i < dim_row (0\<^sub>m (m - 1) 1)" and j: "j < dim_col (0\<^sub>m (m - 1) 1)"
      have j0: "j=0" using j by auto
      have "(H2_DL) $$ (i, j) = H2 $$ (i+1,0)"
        using H2_UR H2_UR_0 n j0 H2 H2_UL H2_as_four_block_mat i by auto
      also have "... = 0"
      proof (cases "i=0")
        case True
        have "H2 $$ (1,0) = H $$ (1,0)" by (rule reduce_column_preserves2[OF H P_H2H2], insert m n, auto)
        also have "... = F $$ (1,0)" by (rule H_ij_F_ij, insert n, auto)
        also have "... = 0" using isDiagonal_F F n unfolding isDiagonal_mat_def by auto
        finally show ?thesis by (simp add: True)
      next
        case False
        show ?thesis
        proof (rule reduce_column_works(1)[OF H P_H2H2])      
          show "H $$ (0, 0) dvd H $$ (i + 1, 0)" using H_00_dvd_H_i0 False i by simp
          show "\<forall>j\<in>{1..<n}. H $$ (0, j) = 0" using H_0j_0 by auto
          show "i + 1 \<in> {2..<m}" using i False by auto
        qed (insert m n id, auto)
      qed
      finally show "(H2_DL) $$ (i, j) = 0\<^sub>m (m - 1) 1 $$ (i, j)" using i j j0 by auto
    qed
    have "P3'*H2 = four_block_mat H2_UL H2_UR (P3 * H2_DL) (P3 * H2_DR)"
    proof -
      have "P3'*H2 = four_block_mat 
    (1\<^sub>m 1 * H2_UL + 0\<^sub>m 1 (dim_row A - 1) * H2_DL) (1\<^sub>m 1 * H2_UR + 0\<^sub>m 1 (dim_row A - 1) * H2_DR) 
    (0\<^sub>m (dim_row A - 1) 1 * H2_UL + P3 * H2_DL) (0\<^sub>m (dim_row A - 1) 1 * H2_UR + P3 * H2_DR)"
        unfolding P3'_def H2_as_four_block_mat 
        by (rule mult_four_block_mat[OF _ _ _ P3 H2_UL H2_UR H2_DL H2_DR], insert A, auto)
      also have "... = four_block_mat H2_UL H2_UR (P3 * H2_DL) (P3 * H2_DR)"
        by (rule cong_four_block_mat, insert H2_UL A m H2_DL H2_DR H2_UR P3, auto) 
      finally show ?thesis .
    qed
    hence P3'_H2_as_four_block_mat: "P3'*H2 = four_block_mat H2_UL (0\<^sub>m 1 (n-1)) (0\<^sub>m (m - 1) 1) (P3 * H2_DR)"
      unfolding H2_UR_0 H2_DL_0 using P3 by auto
    also have "... * Q3' = S" (is "?lhs = ?rhs")
    proof -
      have "?lhs = four_block_mat H2_UL (0\<^sub>m 1 (n-1)) (0\<^sub>m (m - 1) 1) (P3 * H2_DR) 
    * four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (n - 1)) (0\<^sub>m (n - 1) 1) Q3" unfolding Q3'_def using A by auto
      also have "... = 
    four_block_mat (H2_UL * 1\<^sub>m 1 + (0\<^sub>m 1 (n-1)) * 0\<^sub>m (n - 1) 1) (H2_UL * 0\<^sub>m 1 (n - 1) + (0\<^sub>m 1 (n-1)) * Q3)
     (0\<^sub>m (m - 1) 1 * 1\<^sub>m 1 + P3 * H2_DR * 0\<^sub>m (n - 1) 1) (0\<^sub>m (m - 1) 1 * 0\<^sub>m 1 (n - 1) + P3 * H2_DR * Q3)"
        by (rule mult_four_block_mat[OF H2_UL], insert P3 H2_DR Q3, auto)
      also have "... = four_block_mat H2_UL (0\<^sub>m 1 (n - 1)) (0\<^sub>m (m - 1) 1) (P3 * H2_DR * Q3)"
        by (rule cong_four_block_mat, insert H2_UL A m H2_DL H2_DR H2_UR P3 Q3, auto)
      also have "... = four_block_mat (Matrix.mat 1 1 (\<lambda>(a, b). H $$ (0, 0))) 
      (0\<^sub>m 1 (dim_col A - 1)) (0\<^sub>m (dim_row A - 1) 1) S'"
        by (rule cong_four_block_mat, insert A S'_P3H2_DRQ3 H2_UL00_H00 H2_UL, auto)    
      finally show ?thesis unfolding S_def by simp
    qed
    finally have P3'_H2_Q3'_S: "P3'*H2*Q3' = S" .
    have S_as_four_block_mat: "S = four_block_mat H2_UL (0\<^sub>m 1 (n - 1)) (0\<^sub>m (m - 1) 1) S'"
      unfolding S_def by (rule cong_four_block_mat, insert A S'_P3H2_DRQ3 H2_UL00_H00 H2_UL, auto)    
    show "S = P3' * P_H2 * P2' * P1' * A * (Q1 * Q2 * Q3')" using P3'_H2_Q3'_S unfolding H2_eq
      by (smt P1 P1'_def P2' P2'_def P3 P3'_def P_H2 Q1 Q2 Q3' Q3'_def S Q_final_carrier P_final_carrier
          assoc_mult_mat carrier_matD carrier_mat_triv index_mat_four_block(2,3) index_mult_mat(2,3))
    have H00_dvd_all_H2: "H $$ (0, 0) dvd H2 $$ (i, j)" if i: "i<m" and j: "j<n" for i j
      using  dvd_elements_mult_matrix_left[OF H P_H2] H00_dvd_all i j P_H2_H_H2 by blast
    hence H00_dvd_all_S: "H $$ (0, 0) dvd S $$ (i, j)" if i: "i<m" and j: "j<n" for i j
      using dvd_elements_mult_matrix_left_right[OF H2 P3' Q3'] P3'_H2_Q3'_S i j by auto
    show "Smith_normal_form_mat S"
    proof (rule Smith_normal_form_mat_intro)    
      show "isDiagonal_mat S"
      proof (unfold isDiagonal_mat_def, rule+)
        fix i j assume  "i \<noteq> j \<and> i < dim_row S \<and> j < dim_col S"
        hence ij: "i \<noteq> j" and i: "i < dim_row S" and j: "j < dim_col S" by auto
        have i2: "i < dim_row H2_UL + dim_row S'" and j2: "j < dim_col H2_UL + dim_col S'"
          using S_as_four_block_mat i j by auto
        have "S $$ (i,j) = (if i < dim_row H2_UL then if j < dim_col H2_UL then H2_UL $$ (i, j) 
      else (0\<^sub>m 1 (n - 1)) $$ (i, j - dim_col H2_UL) else if j < dim_col H2_UL 
      then (0\<^sub>m (m - 1) 1) $$ (i - dim_row H2_UL, j) else S' $$ (i - dim_row H2_UL, j - dim_col H2_UL))"
          by (unfold S_as_four_block_mat, rule index_mat_four_block(1)[OF i2 j2])
        also have "... = 0" (is "?lhs = 0")
        proof (cases "i = 0 \<or> j = 0")
          case True
          then show ?thesis unfolding S_def using ij i j S H2_UL by fastforce      
        next
          case False
          have diag_S': "isDiagonal_mat S'" using SNF_S' unfolding Smith_normal_form_mat_def by simp
          have i_not_0: "i\<noteq>0" and j_not_0: "j\<noteq>0" using False by auto
          hence "?lhs = S' $$ (i - dim_row H2_UL, j - dim_col H2_UL)" using i j ij H2_UL by auto
          also have "... = 0" using diag_S' S' H2_UL i_not_0 j_not_0 ij unfolding isDiagonal_mat_def
            by (smt S_as_four_block_mat add_diff_inverse_nat add_less_cancel_left carrier_matD i 
                index_mat_four_block(2,3) j less_one)
          finally show ?thesis .
        qed
        finally show "S $$ (i, j) = 0" .
      qed
      show "\<forall>a. a + 1 < min (dim_row S) (dim_col S) \<longrightarrow> S $$ (a, a) dvd S $$ (a + 1, a + 1)"
      proof safe
        fix i assume i: "i + 1 < min (dim_row S) (dim_col S)"
        show "S $$ (i, i) dvd S $$ (i + 1, i + 1)"
        proof (cases "i=0")
          case True
          have "S $$ (0, 0) = H $$ (0,0)" using H2_UL H2_UL00_H00 S_as_four_block_mat by auto
          also have "... dvd S $$ (1,1)" using H00_dvd_all_S i m n by auto
          finally show ?thesis using True by simp
        next
          case False
          have "S $$ (i, i)= S' $$ (i-1, i-1)" using False S_def i by auto
          also have "... dvd S' $$ (i, i)" using SNF_S' i S' S unfolding Smith_normal_form_mat_def
            by (smt False H2_UL S_as_four_block_mat add.commute add_diff_inverse_nat carrier_matD 
                index_mat_four_block(2,3) less_one min_less_iff_conj nat_add_left_cancel_less)
          also have "... = S $$ (i+1,i+1)" using False S_def i by auto
          finally show ?thesis .
        qed
      qed
    qed
  qed
qed

subsection \<open>Soundness theorem\<close>

theorem is_SNF_Smith_mxn: 
  assumes A: "A \<in> carrier_mat m n"
  shows "is_SNF A (Smith_mxn A)"
  using is_SNF_Smith_mxn_ge_2[OF A] is_SNF_Smith_mxn_less_2[OF A] by linarith

declare Smith_mxn.simps[code]

end

declare Smith_Impl.Smith_mxn.simps[code_unfold]

definition T_spec :: "('a::{comm_ring_1} \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a \<times> 'a)) \<Rightarrow> bool" 
  where "T_spec T = (\<forall>a b::'a. let (a1,b1,d) = T a b in 
                    a = a1*d \<and> b = b1*d \<and> ideal_generated {a1,b1} = ideal_generated {1})"

definition D'_spec :: "('a::{comm_ring_1} \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a)) \<Rightarrow> bool" 
  where "D'_spec D' = (\<forall>a b c::'a. let (p,q) = D' a b c in 
      ideal_generated{a,b,c} = ideal_generated{1} 
      \<longrightarrow> ideal_generated {p*a,p*b+q*c} = ideal_generated {1})"

end