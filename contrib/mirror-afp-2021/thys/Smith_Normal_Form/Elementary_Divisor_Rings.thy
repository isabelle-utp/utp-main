(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Elementary divisor rings\<close>

theory Elementary_Divisor_Rings
  imports           
    SNF_Algorithm
    Rings2_Extended
begin

text \<open>This theory contains the definition of elementary divisor rings and Hermite rings, as 
well as the corresponding relation between both concepts. 
It also includes a complete characterization
for elementary divisor rings, by means of an \emph{if and only if}-statement.

The results presented here follows the article ``Some remarks about elementary divisor rings''
by Leonard Gillman and Melvin Henriksen.\<close>

subsection \<open>Previous definitions and basic properties of Hermite ring\<close>

definition "admits_triangular_reduction A = 
  (\<exists>U::'a::comm_ring_1 mat. U \<in> carrier_mat (dim_col A) (dim_col A) 
  \<and> invertible_mat U \<and> lower_triangular (A*U))"

class Hermite_ring =
  assumes "\<forall>(A::'a::comm_ring_1 mat). admits_triangular_reduction A"

lemma admits_triangular_reduction_intro:
  assumes "invertible_mat (U::'a::comm_ring_1 mat)" 
    and "U \<in> carrier_mat (dim_col A) (dim_col A)"
    and "lower_triangular (A*U)"
  shows "admits_triangular_reduction A" 
  using assms unfolding admits_triangular_reduction_def by auto

lemma OFCLASS_Hermite_ring_def:
  "OFCLASS('a::comm_ring_1, Hermite_ring_class) 
  \<equiv> (\<And>(A::'a::comm_ring_1 mat). admits_triangular_reduction A)"
proof 
  fix A::"'a mat"
  assume H: "OFCLASS('a::comm_ring_1, Hermite_ring_class)"
  have "\<forall>A. admits_triangular_reduction (A::'a mat)"
    using conjunctionD2[OF H[unfolded Hermite_ring_class_def class.Hermite_ring_def]] by auto    
  thus "admits_triangular_reduction A" by auto
next
  assume i: "(\<And>A::'a mat. admits_triangular_reduction A)"
  show "OFCLASS('a, Hermite_ring_class)"
  proof 
    show "\<forall>A::'a mat. admits_triangular_reduction A" using i by auto
  qed
qed


definition admits_diagonal_reduction::"'a::comm_ring_1 mat \<Rightarrow> bool"
  where "admits_diagonal_reduction A = (\<exists>P Q. P \<in> carrier_mat (dim_row A) (dim_row A) \<and>
        Q \<in> carrier_mat (dim_col A) (dim_col A) 
        \<and> invertible_mat P \<and> invertible_mat Q 
        \<and> Smith_normal_form_mat (P * A * Q))"

lemma admits_diagonal_reduction_intro:
  assumes "P \<in> carrier_mat (dim_row A) (dim_row A)"
    and "Q \<in> carrier_mat (dim_col A) (dim_col A)" 
    and "invertible_mat P" and "invertible_mat Q "
    and "Smith_normal_form_mat (P * A * Q)"
  shows "admits_diagonal_reduction A" using assms unfolding admits_diagonal_reduction_def by fast

(*Lemmas for equivalence between admits_diagonal_reduction and is_SNF 
  via the existence of an algorithm*)

lemma admits_diagonal_reduction_imp_exists_algorithm_is_SNF:
  assumes "A \<in> carrier_mat m n"
  and "admits_diagonal_reduction A"
shows "\<exists>algorithm. is_SNF A (algorithm A)" 
  using assms unfolding is_SNF_def admits_diagonal_reduction_def
  by auto

lemma exists_algorithm_is_SNF_imp_admits_diagonal_reduction:
  assumes "A \<in> carrier_mat m n"
  and "\<exists>algorithm. is_SNF A (algorithm A)"
  shows "admits_diagonal_reduction A"
  using assms unfolding is_SNF_def admits_diagonal_reduction_def
  by auto

lemma admits_diagonal_reduction_eq_exists_algorithm_is_SNF:
  assumes A: "A \<in> carrier_mat m n"
  shows "admits_diagonal_reduction A = (\<exists>algorithm. is_SNF A (algorithm A))"
  using admits_diagonal_reduction_imp_exists_algorithm_is_SNF[OF A]
  using exists_algorithm_is_SNF_imp_admits_diagonal_reduction[OF A]
  by auto


lemma admits_diagonal_reduction_imp_exists_algorithm_is_SNF_all:
  assumes "(\<forall>(A::'a::comm_ring_1 mat) \<in> carrier_mat m n. admits_diagonal_reduction A)" 
  shows" (\<exists>algorithm. \<forall>(A::'a mat) \<in> carrier_mat m n. is_SNF A (algorithm A))"
proof -
  let ?algorithm = "\<lambda>A. SOME (P, S, Q). is_SNF A (P,S,Q)"
  show ?thesis
    by (rule exI[of _ ?algorithm]) (metis (no_types, lifting) 
        admits_diagonal_reduction_imp_exists_algorithm_is_SNF assms case_prod_beta prod.collapse someI)
qed

lemma exists_algorithm_is_SNF_imp_admits_diagonal_reduction_all:
  assumes "(\<exists>algorithm. \<forall>(A::'a mat) \<in> carrier_mat m n. is_SNF A (algorithm A))"
  shows "(\<forall>(A::'a::comm_ring_1 mat) \<in> carrier_mat m n. admits_diagonal_reduction A)"
  using assms exists_algorithm_is_SNF_imp_admits_diagonal_reduction by blast  

 
lemma admits_diagonal_reduction_eq_exists_algorithm_is_SNF_all:
  shows "(\<forall>(A::'a::comm_ring_1 mat) \<in> carrier_mat m n. admits_diagonal_reduction A) 
  = (\<exists>algorithm. \<forall>(A::'a mat) \<in> carrier_mat m n. is_SNF A (algorithm A))"
  using exists_algorithm_is_SNF_imp_admits_diagonal_reduction_all
  using admits_diagonal_reduction_imp_exists_algorithm_is_SNF_all by auto


subsection \<open>The class that represents elementary divisor rings\<close>

class elementary_divisor_ring =
  assumes "\<forall>(A::'a::comm_ring_1 mat). admits_diagonal_reduction A"


lemma dim_row_mat_diag[simp]: "dim_row (mat_diag n f) = n" and 
      dim_col_mat_diag[simp]: "dim_col (mat_diag n f) = n" 
  using mat_diag_dim unfolding carrier_mat_def by auto+


subsection \<open>Hermite ring implies B\'ezout ring\<close>

(*HERMITE \<Longrightarrow> BEZOUT*)

text \<open>To prove this fact, we make use of the alternative definition for B\'ezout rings:
each finitely generated ideal is principal\<close>

lemma Hermite_ring_imp_Bezout_ring:
  assumes H: "OFCLASS('a::comm_ring_1, Hermite_ring_class)"
  shows " OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof (rule all_fin_gen_ideals_are_principal_imp_bezout, rule+)
  fix I::"'a set" assume fin: "finitely_generated_ideal I"
  (*We take the list, put it in a 1xn matrix and then multiply it by a matrix Q that I will obtain*)
  obtain S where ig_S: "ideal_generated S = I" and fin_S: "finite S" 
    using fin unfolding finitely_generated_ideal_def by auto
  obtain xs where set_xs: "set xs = S" and d: "distinct xs" 
    using finite_distinct_list[OF fin_S] by blast
  hence length_eq_card: "length xs = card S" using distinct_card by force
  define n where "n = card S"
  define A where "A = mat_of_rows n [vec_of_list xs]"
  have A[simp]: "A \<in> carrier_mat 1 n" unfolding A_def using mat_of_rows_carrier by auto
  have "\<forall>(A::'a::comm_ring_1 mat). admits_triangular_reduction A" 
    using H unfolding OFCLASS_Hermite_ring_def by auto  
  from this obtain Q where inv_Q: "invertible_mat Q" and t_AQ: "lower_triangular (A*Q)"
    and Q[simp]: "Q \<in> carrier_mat n n"
    unfolding admits_triangular_reduction_def using A by auto  
  have AQ[simp]: "A * Q \<in> carrier_mat 1 n" using A Q by auto
  show "principal_ideal I"
  proof (cases "xs=[]")
  case True
    then show ?thesis
      by (metis empty_set ideal_generated_0 ideal_generated_empty ig_S principal_ideal_def set_xs)
  next
    case False
    have a: "0 < dim_row A" using A by auto
    have "0 < length xs" using False by auto  
    hence b: "0 < dim_col A" using A n_def length_eq_card by auto
    have q0: "0 < dim_col Q" by (metis A Q b carrier_matD(2))
    have n0: "0<n" using \<open>0 < length xs\<close> length_eq_card n_def by linarith
    define d where "d = (A*Q) $$ (0,0)"
        let ?h = "(\<lambda>x. THE i. xs ! i = x \<and> i<n)"
        let ?u = "\<lambda>i. xs ! i"
        have bij: "bij_betw ?h (set xs) {0..<n}" 
        proof (rule bij_betw_imageI)
          show "inj_on ?h (set xs)"
          proof -
            have "x=y" if x: "x \<in> set xs" and y: "y \<in> set xs"
              and xy: "(THE i. xs ! i = x \<and> i < n) = (THE i. xs ! i = y \<and> i < n)" for x y
            proof -
              let ?i = "(THE i. xs ! i = x \<and> i < n)"
              let ?j = "(THE i. xs ! i = y \<and> i < n)"
             obtain i where xs_i: "xs ! i = x \<and> i < n" using x
                by (metis in_set_conv_nth length_eq_card n_def)
             from this have 1: "xs ! ?i = x \<and> ?i < n"
               by (rule theI, insert d xs_i length_eq_card n_def nth_eq_iff_index_eq, fastforce)
             obtain j where xs_j: "xs ! j = y \<and> j < n" using y
                by (metis in_set_conv_nth length_eq_card n_def)
             from this have 2: "xs ! ?j = y \<and> ?j < n"
               by (rule theI, insert d xs_j length_eq_card n_def nth_eq_iff_index_eq, fastforce)    
             show ?thesis using 1 2 d xy by argo
           qed
           thus ?thesis unfolding inj_on_def by auto
         qed      
         show "(\<lambda>x. THE i. xs ! i = x \<and> i < n) ` set xs = {0..<n}"
         proof (auto)  
           fix xa assume xa: "xa \<in> set xs"
           let ?i = "(THE i. xs ! i = xa \<and> i < n)"
           obtain i where xs_i: "xs ! i = xa \<and> i < n" using xa
             by (metis in_set_conv_nth length_eq_card n_def)
           from this have 1: "xs ! ?i = xa \<and> ?i < n"
             by (rule theI, insert d xs_i length_eq_card n_def nth_eq_iff_index_eq, fastforce)
           thus "(THE i. xs ! i = xa \<and> i < n) < n" by simp
         next
           fix x assume x: "x<n"
           have "\<exists>xa\<in>set xs. x = (THE i. xs ! i = xa \<and> i < n)"
             by (rule bexI[of _ "xs ! x"], rule the_equality[symmetric], insert x d) 
                (auto simp add: length_eq_card n_def nth_eq_iff_index_eq)+
           thus "x \<in> (\<lambda>x. THE i. xs ! i = x \<and> i < n) ` set xs" unfolding image_def by auto
         qed
       qed
    have i: "ideal_generated {d} = ideal_generated S"
    proof -    
      have ideal_S_explicit: "ideal_generated S = {y. \<exists>f. (\<Sum>i\<in>S. f i * i) = y}"
        unfolding ideal_explicit2[OF fin_S] by simp
      have "ideal_generated {d} \<subseteq> ideal_generated S"
      proof (rule ideal_generated_subset2, auto simp add: ideal_S_explicit)
        have n: "dim_vec (col Q 0) = n" using Q n_def by auto
        have aux: "Matrix.row A 0 $v i = xs ! i" if i: "i<n" for i
        proof -
          have i2: "i < dim_col A"
            by (simp add: A_def i)
          have "Matrix.row A 0 $v i = A $$ (0,i)" by (rule index_row(1), auto simp add: a b i2)
          also have "... = [vec_of_list xs] ! 0 $v i" 
            unfolding A_def by (rule mat_of_rows_index, auto simp add: i)
          also have "... = xs ! i"
            by (simp add: vec_of_list_index)
          finally show ?thesis .
        qed    
        let ?f = "\<lambda>x. let i = (THE i. xs ! i = x \<and> i < n) in col Q 0 $v i"
        let ?g = "(\<lambda>i. xs ! i * col Q 0 $v i)"
        have "d = (A*Q) $$ (0,0)" unfolding d_def by simp 
        also have "... = Matrix.row A 0 \<bullet> col Q 0" by (rule index_mult_mat(1)[OF a q0])
        also have "... = (\<Sum>i = 0..<dim_vec (col Q 0). Matrix.row A 0 $v i * col Q 0 $v i)" 
          unfolding scalar_prod_def by simp
        also have "... = (\<Sum>i = 0..<n. Matrix.row A 0 $v i * col Q 0 $v i)" unfolding n by auto
        also have "... = (\<Sum>i = 0..<n. xs ! i * col Q 0 $v i)" 
          by (rule sum.cong, auto simp add: aux)
        also have "... = (\<Sum>x \<in> set xs. ?g (?h x))"
          by (rule sum.reindex_bij_betw[symmetric, OF bij])
        also have "... = (\<Sum>x \<in> set xs. ?f x * x)"
        proof (rule sum.cong, auto simp add: Let_def)
          fix x assume x: "x \<in> set xs"
          let ?i = "(THE i. xs ! i = x \<and> i < n)"
          obtain i where xs_i: "xs ! i = x \<and> i < n"
            by (metis in_set_conv_nth x length_eq_card n_def)
          from this have "xs ! ?i = x \<and> ?i < n"
            by (rule theI, insert d xs_i length_eq_card n_def nth_eq_iff_index_eq, fastforce)       
          thus "xs ! ?i * col Q 0 $v ?i = col Q 0 $v ?i * x" by auto
        qed
        also have "... = (\<Sum>x \<in> S. ?f x * x)" using set_xs by auto
        finally show "\<exists>f. (\<Sum>i\<in>S. f i * i) = d" by auto
      qed
      moreover have "ideal_generated S \<subseteq> ideal_generated {d}"
      proof 
        fix x assume x: "x \<in> ideal_generated S" thm Matrix.diag_mat_def
        hence x_xs: "x \<in> ideal_generated (set xs)" by (simp add: set_xs)
        from this obtain f where f: "(\<Sum>i\<in>(set xs). f i * i) = x" using x ideal_explicit2 by auto
        define B where "B = Matrix.vec n (\<lambda>i. f (A $$ (0,i)))"
        have B: "B \<in> carrier_vec n" unfolding B_def by auto
        have "(A *\<^sub>v B) $v 0 = Matrix.row A 0 \<bullet> B" by (rule index_mult_mat_vec[OF a])
        also have "... = sum (\<lambda>i. f (A $$ (0,i)) * A $$ (0,i)) {0..<n}"
          unfolding B_def Matrix.row_def scalar_prod_def by (rule sum.cong, auto simp add: A_def)
        also have "... = sum (\<lambda>i. f i * i) (set xs)"
        proof (rule sum.reindex_bij_betw)
          have 1: "inj_on (\<lambda>x. A $$ (0, x)) {0..<n}"
          proof (unfold inj_on_def, auto)
            fix x y assume x: "x < n" and y: "y < n" and xy: "A $$ (0, x) = A $$ (0, y)"
            have "A $$ (0,x) =  [vec_of_list xs] ! 0 $v x" 
              unfolding A_def by (rule mat_of_rows_index, insert x y, auto)
            also have "... = xs ! x" using x by (simp add: vec_of_list_index)
            finally have 1: "A $$ (0,x) = xs ! x" .
            have "A $$ (0,y) =  [vec_of_list xs] ! 0 $v y" 
              unfolding A_def by (rule mat_of_rows_index, insert x y, auto)
            also have "... = xs ! y" using y by (simp add: vec_of_list_index)
            finally have 2: "A $$ (0,y) = xs ! y" .
            show "x = y" using 1 2 x y d length_eq_card n_def nth_eq_iff_index_eq xy by fastforce
          qed
          have 2: "A $$ (0, xa) \<in> set xs" if xa: "xa < n" for xa
          proof -
            have "A $$ (0,xa) =  [vec_of_list xs] ! 0 $v xa" 
              unfolding A_def by (rule mat_of_rows_index, insert xa, auto)
            also have "... = xs ! xa" using xa by (simp add: vec_of_list_index)
            finally show ?thesis using xa by (simp add: length_eq_card n_def)
          qed
          have 3: "x \<in> (\<lambda>x. A $$ (0, x)) ` {0..<n}" if x: "x\<in> set xs" for x
          proof -
            obtain i where xs: "xs ! i = x \<and> i < n"
              by (metis in_set_conv_nth length_eq_card n_def x)
            have "A $$ (0,i) = [vec_of_list xs] ! 0 $v i" 
              unfolding A_def by (rule mat_of_rows_index, insert xs, auto)
            also have "... = xs ! i" using xs by (simp add: vec_of_list_index) 
            finally show ?thesis using xs unfolding image_def by auto
          qed
          show "bij_betw (\<lambda>x. A $$ (0, x)) {0..<n} (set xs)" using 1 2 3 unfolding bij_betw_def by auto
        qed
        finally have AB00_sum: "(A *\<^sub>v B) $v 0 = sum (\<lambda>i. f i * i) (set xs)" by auto
        hence AB_00_x: "(A *\<^sub>v B) $v 0 = x" using f by auto
        obtain Q' where QQ': "inverts_mat Q Q'" 
          and Q'Q: "inverts_mat Q' Q" and Q': "Q' \<in> carrier_mat n n"
          by (rule obtain_inverse_matrix[OF Q inv_Q], auto) 
        have eq: "A = (A*Q)*Q'" using QQ' unfolding inverts_mat_def
          by (metis A Q Q' assoc_mult_mat carrier_matD(1) right_mult_one_mat)        
        let ?g = "\<lambda>i. Matrix.row (A * Q) 0 $v i * (Matrix.row Q' i \<bullet> B)"
        have sum0: "(\<Sum>i = 1..<n. ?g i) = 0"
        proof (rule sum.neutral, rule)
          fix x assume x: "x \<in> {1..<n}"
          hence "Matrix.row (A * Q) 0 $v x = 0" using t_AQ unfolding lower_triangular_def
            by (auto, metis Q Suc_le_lessD a carrier_matD(2) index_mult_mat(2,3) index_row(1))
          thus "Matrix.row (A * Q) 0 $v x * (Matrix.row Q' x \<bullet> B) = 0" by simp
        qed
        have set_rw: "{0..<n} - {0} = {1..<n}"
          by (simp add: atLeast0LessThan atLeast1_lessThan_eq_remove0) 
        have mat_rw: "(A*Q*Q')*\<^sub>v B = A*Q*\<^sub>v(Q' *\<^sub>v B)"
          by (rule assoc_mult_mat_vec, insert Q Q' B AQ, auto)
        from eq have "A *\<^sub>vB = (A*Q)*\<^sub>v(Q'*\<^sub>v B)" using mat_rw by auto
        from this have "(A *\<^sub>v B) $v 0 = (A * Q *\<^sub>v (Q' *\<^sub>v B)) $v 0" by auto
        also have "... =  Matrix.row (A*Q) 0 \<bullet> (Q' *\<^sub>v B)"
          by (rule index_mult_mat_vec, insert a B_def n0, auto)
        also have "... =  (\<Sum>i = 0..<n. ?g i)" using Q' by (auto simp add: scalar_prod_def)
        also have "... = ?g 0 + (\<Sum>i \<in> {0..<n} - {0}. ?g i)"
          by (metis (no_types, lifting) Q atLeast0LessThan carrier_matD(2) finite_atLeastLessThan 
              lessThan_iff q0 sum.remove)        
        also have "... = ?g 0 + (\<Sum>i = 1..<n. ?g i)" using set_rw by simp        
        also have "... = ?g 0" using sum0 by auto
        also have "... = d * (Matrix.row Q' 0 \<bullet> B)" by (simp add: a d_def q0)
        finally show "x \<in> ideal_generated {d}" using AB_00_x unfolding ideal_generated_singleton 
          using mult.commute by auto
      qed
      ultimately show ?thesis by auto
    qed
    thus "principal_ideal I" unfolding principal_ideal_def ig_S by blast
  qed
qed

subsection \<open>Elementary divisor ring implies Hermite ring\<close>

context
  assumes "SORT_CONSTRAINT('a::comm_ring_1)"
begin


lemma triangularizable_m0:
assumes A: "A \<in> carrier_mat m 0" 
shows "\<exists>U. U \<in> carrier_mat 0 0 \<and> invertible_mat U \<and> lower_triangular (A * U)"
  using A unfolding lower_triangular_def carrier_mat_def invertible_mat_def inverts_mat_def  
  by auto (metis gr_implies_not0 index_one_mat(2) index_one_mat(3) right_mult_one_mat')

lemma triangularizable_0n:
assumes A: "A \<in> carrier_mat 0 n" 
shows "\<exists>U. U \<in> carrier_mat n n \<and> invertible_mat U \<and> lower_triangular (A * U)"
  using A unfolding lower_triangular_def carrier_mat_def invertible_mat_def inverts_mat_def  
  by auto (metis index_one_mat(2) index_one_mat(3) right_mult_one_mat')


(*To show this, we have to prove that P is a matrix of one element, which is a unit.*)
lemma diagonal_imp_triangular_1x2:
  assumes A: "A \<in> carrier_mat 1 2" and d: "admits_diagonal_reduction (A::'a mat)"
  shows "admits_triangular_reduction A"
proof -
  obtain P Q where P: "P \<in> carrier_mat (dim_row A) (dim_row A)"
  and Q: "Q \<in> carrier_mat (dim_col A) (dim_col A)" 
  and inv_P: "invertible_mat P" and inv_Q: "invertible_mat Q"
  and SNF: "Smith_normal_form_mat (P * A * Q)"
    using d unfolding admits_diagonal_reduction_def by blast
  have "(P * A * Q) = P * (A * Q)" using P Q assoc_mult_mat by blast
  also have "... = P $$ (0,0) \<cdot>\<^sub>m (A * Q)" by (rule smult_mat_mat_one_element, insert P A Q, auto)
  also have "... = A * (P $$ (0,0) \<cdot>\<^sub>m Q)" using Q by auto
  finally have eq: "(P * A * Q) = A * (P $$ (0,0) \<cdot>\<^sub>m Q)" .
  have inv: "invertible_mat (P $$ (0,0) \<cdot>\<^sub>m Q)"
  proof -
    have d: "Determinant.det P = P $$ (0, 0)" by (rule determinant_one_element, insert P A, auto)
    from this have P_dvd_1: "P $$ (0, 0) dvd 1" 
      using invertible_iff_is_unit_JNF[OF P] using inv_P by auto
    have Q_dvd_1: "Determinant.det Q dvd 1" using inv_Q invertible_iff_is_unit_JNF[OF Q] by simp
    have "Determinant.det (P $$ (0, 0) \<cdot>\<^sub>m Q) =  P $$ (0, 0) ^ dim_col Q * Determinant.det Q" 
      unfolding det_smult by auto
    also have "... dvd 1" using P_dvd_1 Q_dvd_1 unfolding is_unit_mult_iff
      by (metis dvdE dvd_mult_left one_dvd power_mult_distrib power_one)
    finally have det: "(Determinant.det (P $$ (0, 0) \<cdot>\<^sub>m Q) dvd 1)" .
    have PQ: "P $$ (0,0) \<cdot>\<^sub>m Q \<in> carrier_mat 2 2" using A P Q by auto
    show ?thesis using invertible_iff_is_unit_JNF[OF PQ] det by auto
  qed
  moreover have "lower_triangular (A * (P $$ (0,0) \<cdot>\<^sub>m Q))" unfolding lower_triangular_def using SNF eq
    unfolding Smith_normal_form_mat_def isDiagonal_mat_def by auto
  moreover have "(P $$ (0,0) \<cdot>\<^sub>m Q) \<in> carrier_mat (dim_col A) (dim_col A)" using P Q A by auto
  ultimately show ?thesis unfolding admits_triangular_reduction_def by auto
qed

lemma triangular_imp_diagonal_1x2:
assumes A: "A \<in> carrier_mat 1 2" and t: "admits_triangular_reduction (A::'a mat)"
shows "admits_diagonal_reduction A"
proof -
 obtain U where U: "U \<in> carrier_mat (dim_col A) (dim_col A)"  
  and inv_U: "invertible_mat U" and AU: "lower_triangular (A * U)" 
   using t unfolding admits_triangular_reduction_def by blast
  have SNF_AU: "Smith_normal_form_mat (A * U)"
    using AU A unfolding Smith_normal_form_mat_def lower_triangular_def isDiagonal_mat_def by auto
  have "A * U = (1\<^sub>m 1) * A * U" using A by auto
  hence SNF: "Smith_normal_form_mat ((1\<^sub>m 1) * A * U)" using SNF_AU by auto
  moreover have "invertible_mat (1\<^sub>m 1)"
    using invertible_mat_def inverts_mat_def by fastforce
  ultimately show ?thesis using inv_U unfolding admits_diagonal_reduction_def
    by (smt U assms(1) carrier_matD(1) one_carrier_mat)
qed


lemma triangular_eq_diagonal_1x2:
 "(\<forall>A\<in>carrier_mat 1 2. admits_triangular_reduction (A::'a mat)) 
  = (\<forall>A\<in>carrier_mat 1 2. admits_diagonal_reduction (A::'a mat))"
  using triangular_imp_diagonal_1x2 diagonal_imp_triangular_1x2 by auto


lemma admits_triangular_mat_1x1:
  assumes A: "A \<in> carrier_mat 1 1"
  shows "admits_triangular_reduction (A::'a mat)"
  by (rule admits_triangular_reduction_intro[of "1\<^sub>m 1"], insert A,
      auto simp add: admits_triangular_reduction_def  lower_triangular_def)


lemma admits_diagonal_mat_1x1:
  assumes A: "A \<in> carrier_mat 1 1"
  shows "admits_diagonal_reduction (A::'a mat)"
  by (rule admits_diagonal_reduction_intro[of "(1\<^sub>m 1)" _ "(1\<^sub>m 1)"], 
      insert A, auto simp add: Smith_normal_form_mat_def isDiagonal_mat_def)


lemma admits_diagonal_imp_admits_triangular_1xn:
  assumes a: "\<forall>A\<in>carrier_mat 1 2. admits_diagonal_reduction (A::'a mat)"
  shows "\<forall>A\<in>carrier_mat 1 n. admits_triangular_reduction (A::'a mat)"
proof 
  fix A::"'a mat" assume A: "A \<in> carrier_mat 1 n"  
  have "\<exists>U. U \<in> carrier_mat (dim_col A) (dim_col A) 
    \<and> invertible_mat U \<and> lower_triangular (A * U)" (*Zeros above the diagonal*)
    using A
  proof (induct n arbitrary: A rule: less_induct)
    case (less n)
    note A = less.prems(1)
    show ?case
    proof (cases "n=0")
      case True
      then show ?thesis using triangularizable_m0 triangularizable_0n less.prems by auto
    next
      case False note nm_not_0 = False
      from this have n_not_0: "n \<noteq> 0" by auto
      show ?thesis        
      proof (cases "n>2")
        case False note n_less_2 = False
        show ?thesis using admits_triangular_mat_1x1 a diagonal_imp_triangular_1x2 
          unfolding admits_triangular_reduction_def
          by (metis (full_types) admits_triangular_mat_1x1 Suc_1 admits_triangular_reduction_def 
              less(2) less_Suc_eq less_one linorder_neqE_nat n_less_2 nm_not_0 triangular_eq_diagonal_1x2)
      next
        case True note n_ge_2 = True            
        let ?B = "mat_of_row (vec_last (Matrix.row A 0) (n - 1))"
        have "\<exists>V. V\<in> carrier_mat (dim_col ?B) (dim_col ?B) 
        \<and> invertible_mat V \<and> lower_triangular (?B * V)"
        proof (rule less.hyps)     
          show "n-1 < n" using n_not_0 by auto           
          show "mat_of_row (vec_last (Matrix.row A 0) (n - 1)) \<in> carrier_mat 1 (n - 1)" 
            using A by simp
        qed
        from this obtain V where inv_V: "invertible_mat V" and BV: "lower_triangular (?B * V)" 
          and V': "V \<in> carrier_mat (dim_col ?B) (dim_col ?B)"
          by fast  
        have V: "V \<in> carrier_mat (n-1) (n-1)" using V' by auto
        have BV_0: "\<forall>j \<in> {1..<n-1}. (?B * V) $$ (0,j) = 0"
          by (rule, rule lower_triangular_index[OF BV], insert V, auto)
        define b where "b = (?B * V) $$ (0,0)"
        define a where "a = A $$ (0,0)"          
        define ab::"'a mat" where "ab = Matrix.mat 1 2 (\<lambda>(i,j). if i=0 \<and> j=0 then a else b)"
        have ab[simp]: "ab \<in> carrier_mat 1 2" unfolding ab_def by simp
        hence "admits_diagonal_reduction ab" using a by auto
        hence "admits_triangular_reduction ab" using diagonal_imp_triangular_1x2[OF ab] by auto
        from this obtain W where inv_W: "invertible_mat W" and ab_W: "lower_triangular (ab * W)"
          and W: "W \<in> carrier_mat 2 2"
          unfolding admits_triangular_reduction_def using ab by auto
        have id_n2_carrier[simp]: "1\<^sub>m (n-2) \<in> carrier_mat (n-2) (n-2)" by auto
        define U where "U = (four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (n-1)) (0\<^sub>m (n-1) 1) V) * 
                                (four_block_mat W (0\<^sub>m 2 (n-2)) (0\<^sub>m (n-2) 2) (1\<^sub>m (n-2)))"
        let ?U1 = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (n-1)) (0\<^sub>m (n-1) 1) V"
        let ?U2 = "four_block_mat W (0\<^sub>m 2 (n-2)) (0\<^sub>m (n-2) 2) (1\<^sub>m (n-2))"
        have U1[simp]: "?U1 \<in>carrier_mat n n" using four_block_carrier_mat[OF _ V] nm_not_0
          by fastforce
        have U2[simp]: "?U2 \<in>carrier_mat n n" using four_block_carrier_mat[OF W id_n2_carrier]              
          by (metis True add_diff_inverse_nat less_imp_add_positive not_add_less1)
        have U[simp]: "U \<in> carrier_mat n n" unfolding U_def using U1 U2 by auto
        moreover have inv_U: "invertible_mat U"
        proof -
          have "invertible_mat ?U1"
            by (metis U1 V det_four_block_mat_lower_left_zero_col det_one inv_V 
                invertible_iff_is_unit_JNF more_arith_simps(5) one_carrier_mat zero_carrier_mat)
          moreover have "invertible_mat ?U2"
          proof -
            have "Determinant.det ?U2 = Determinant.det W"
              by (rule det_four_block_mat_lower_right_id, insert less.prems W n_ge_2, auto)
            also have " ... dvd 1"
              using W inv_W invertible_iff_is_unit_JNF by auto
            finally show ?thesis using invertible_iff_is_unit_JNF[OF U2] by auto
          qed
          ultimately show ?thesis
            using U1 U2 U_def invertible_mult_JNF by blast
        qed
        moreover have "lower_triangular (A*U)"
        proof -            
          let ?A = "Matrix.mat 1 n (\<lambda>(i,j). if j = 0 then a else if j=1 then b else 0)"
          let ?T = "Matrix.mat 1 n (\<lambda>(i,j). if j = 0 then (ab*W) $$ (0,0) else 0)"
          have "A*?U1 = ?A" 
          proof (rule eq_matI)
            fix i j assume i: "i<dim_row ?A" and j: "j<dim_col ?A"
            have i0: "i=0" using i by auto
            let ?f = "\<lambda> i. A $$ (0, i) * 
            (if i = 0 then if j < 1 then 1\<^sub>m (1) $$ (i, j) else 0\<^sub>m (1) (n - 1) $$ (i, j - 1)
             else if j < 1 then 0\<^sub>m (n - 1) (1) $$ (i - 1, j) else V $$ (i - 1, j - 1))"
            have "(A*?U1) $$ (i,j) = Matrix.row A i \<bullet> col ?U1 j" 
              by (rule index_mult_mat, insert i j A V, auto)           
            also have "... =  (\<Sum>i = 0..<n. ?f i)"
              using i j A V unfolding scalar_prod_def 
              by auto (unfold index_one_mat, insert One_nat_def, presburger)
            also have "... = ?A $$ (i,j)"
            proof (cases "j=0")
              case True
              have rw0: "sum ?f {1..<n} = 0" by (rule sum.neutral, insert True, auto)  
              have set_rw: "{0..<n} = insert 0 {1..<n}" using n_ge_2 by auto
              hence "sum ?f {0..<n} = ?f 0 + sum ?f {1..<n}" by auto
              also have "... = ?f 0" unfolding rw0 by simp
              also have "... = a" using True unfolding a_def by simp
              also have "... = ?A $$ (i,j)" using True i j by auto
              finally show ?thesis .
            next
              case False note j_not_0 = False
              have rw_simp: "Matrix.row (mat_of_row (vec_last (Matrix.row A 0) (n - 1))) 0 
                  = (vec_last (Matrix.row A 0) (n - 1))" unfolding Matrix.row_def by auto               
              let ?g = "\<lambda>i. A $$ (0, i) * V $$ (i - 1, j - 1)"
              let ?h = "\<lambda>i. A $$ (0, i+1) * V $$ (i, j - 1)"
              have f0: "?f 0 = 0" using j_not_0 j by auto
              have set_rw2: "(\<lambda>i. i+1)`{0..<n-1} = {1..<n}" 
                unfolding image_def using Suc_le_D by fastforce                
              have set_rw: "{0..<n} = insert 0 {1..<n}" using n_ge_2 by auto
              hence "sum ?f {0..<n} = ?f 0 + sum ?f {1..<n}" by auto
              also have "... = sum ?f {1..<n}" using f0 by simp
              also have "... = sum ?g {1..<n}" by (rule sum.cong, insert j_not_0,  auto)
              also have "... = sum ?g ((\<lambda>i. i+1)`{0..<n-1})" using set_rw2 by simp
              also have "... = sum (?g \<circ> (\<lambda>i. i+1)) {0..<n-1}" 
                by (rule sum.reindex, unfold inj_on_def, auto)
              also have "... = sum ?h {0..<n-1}" by (rule sum.cong, auto)
              also have "... = Matrix.row ?B 0 \<bullet> col V (j-1)" unfolding scalar_prod_def 
              proof (rule sum.cong)
                fix x assume x: "x \<in> {0..<dim_vec (col V (j - 1))}"
                have "Matrix.row ?B 0 $v x = ?B $$ (0,x)" by (rule index_row, insert x V, auto)
                also have "... = (vec_last (Matrix.row A 0) (n - 1)) $v x" 
                  by (rule mat_of_row_index, insert x V, auto)
                also have "... = A $$ (0, x + 1)"
                  by (smt Suc_less_eq V add.right_neutral add_Suc_right add_diff_cancel_right' 
                      add_diff_inverse_nat atLeastLessThan_iff carrier_matD(1) carrier_matD(2) 
                      dim_col index_row(1) index_row(2) index_vec less.prems less_Suc0 n_not_0 
                      plus_1_eq_Suc vec_last_def x)
                finally have "Matrix.row ?B 0 $v x = A $$ (0, x + 1)" .
                moreover have "col V (j - 1) $v x = V $$ (x, j - 1)" using V j x by auto
                ultimately show "A $$ (0, x + 1) * V $$ (x, j - 1) 
                    = Matrix.row ?B 0 $v x * col V (j - 1) $v x" by simp
              qed (insert V j_not_0, auto)                  
              also have "... = (?B*V) $$ (0,j-1)" 
                by (rule index_mult_mat[symmetric], insert V j False, auto)
              also have "... = ?A $$ (i, j)" 
                by (cases "j=1", insert False V j i0 BV_0 b_def, auto simp add: Suc_leI)                               
              finally show ?thesis .
            qed
            finally show "(A*?U1) $$ (i,j) = ?A $$ (i,j)" .
          next
            show "dim_row (A*?U1) = dim_row ?A" using A by auto
            show "dim_col (A*?U1) = dim_col ?A" using U1 by auto          
          qed         
          also have "... * ?U2 = ?T"
          proof -
            let ?A1.0 = "ab"
            let ?B1.0 = "Matrix.mat 1 (n-2) (\<lambda>(i,j). 0)"
            let ?C1.0 = "Matrix.mat 0 2 (\<lambda>(i,j). 0)"
            let ?D1.0 = "Matrix.mat 0 (n-2) (\<lambda>(i,j). 0)"
            let ?B2.0 = "(0\<^sub>m 2 (n - 2))"
            let ?C2.0 = "(0\<^sub>m (n - 2) 2)"
            let ?D2.0 = "1\<^sub>m (n - 2)"
            have A_eq: "?A = four_block_mat ?A1.0 ?B1.0 ?C1.0 ?D1.0" 
              by (rule eq_matI, insert ab_def n_ge_2, auto)
            hence "?A * ?U2 = four_block_mat ?A1.0 ?B1.0 ?C1.0 ?D1.0 * ?U2" by simp
            also have "... = four_block_mat (?A1.0 * W + ?B1.0 * ?C2.0) 
              (?A1.0 * ?B2.0 + ?B1.0 * ?D2.0) (?C1.0 * W + ?D1.0 * ?C2.0) 
              (?C1.0 * ?B2.0 + ?D1.0 * ?D2.0)"
              by (rule mult_four_block_mat, auto simp add: W ab_def)
            also have "... = four_block_mat (?A1.0 * W) (?B1.0) (?C1.0) (?D1.0)"
              by (rule cong_four_block_mat, insert W ab_def, auto)
            also have "... = ?T"
              by (rule eq_matI, insert W n_ge_2 ab_def ab_W, auto simp add: lower_triangular_def)
            finally show ?thesis .                              
          qed
          finally have "A * U = ?T" 
            using assoc_mult_mat[OF _ U1 U2] less.prems unfolding U_def by auto
          moreover have "lower_triangular ?T" unfolding lower_triangular_def by simp
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis using A U by blast
      qed
    qed
  qed
  from this show "admits_triangular_reduction A" unfolding admits_triangular_reduction_def by simp
qed

lemma admits_diagonal_imp_admits_triangular:
  assumes a: "\<forall>A\<in>carrier_mat 1 2. admits_diagonal_reduction (A::'a mat)"
  shows "\<forall>A. admits_triangular_reduction (A::'a mat)"
proof 
  fix A::"'a mat"
  obtain m n where A: "A \<in> carrier_mat m n" by auto
  have "\<exists>U. U \<in> carrier_mat n n \<and> invertible_mat U \<and> lower_triangular (A * U)" (*Zeros above the diagonal*)
    using A
  proof (induct n arbitrary: m A rule: less_induct)
    case (less n)
    note A = less.prems(1)
    show ?case
    proof (cases "n=0 \<or> m=0")
      case True
      then show ?thesis using triangularizable_m0 triangularizable_0n less.prems by auto
    next
      case False note nm_not_0 = False
      from this have m_not_0: "m \<noteq> 0" and n_not_0: "n \<noteq> 0" by auto    
      show ?thesis        
      proof (cases "m = 1")
        case True note m1 = True
        show ?thesis using admits_diagonal_imp_admits_triangular_1xn A m1 a 
          unfolding admits_triangular_reduction_def by blast
      next
        case False note m_not_1 = False
          (* The article says "Right-multiply A by a unimodular matrix V which reduces the first row.
           To do that, I use the first case of the induction (m=1) to reduce the first row. 
           With lemma mult_eq_first_row I will show that A*V reduces the first row.
        *)
        show ?thesis 
        proof (cases "n=1")
          case True
          thus ?thesis using invertible_mat_zero lower_triangular_def
            by (metis carrier_matD(2) det_one gr_implies_not0 invertible_iff_is_unit_JNF less(2) 
                less_one one_carrier_mat right_mult_one_mat')
        next
          case False note n_not_1 = False                  
          let ?first_row = "mat_of_row (Matrix.row A 0)"
          have first_row: "?first_row \<in> carrier_mat 1 n" using less.prems by auto
          have m1: "m>1" using m_not_1 m_not_0 by linarith
          have n1: "n>1" using n_not_1 n_not_0 by linarith 
          obtain V where lt_first_row_V: "lower_triangular (?first_row * V)"
            and inv_V: "invertible_mat V" and V: "V \<in> carrier_mat n n"
            (*Using the other induction case*)
            using admits_diagonal_imp_admits_triangular_1xn a first_row 
            unfolding admits_triangular_reduction_def by blast
          have AV: "A*V \<in> carrier_mat m n" using V less by auto
          have dim_row_AV: "dim_row (A * V) = 1 + (m-1)" using m1 AV by auto
          have dim_col_AV: "dim_col (A * V) = 1 + (n-1)" using n1 AV by fastforce
          have reduced_first_row: "Matrix.row (?first_row * V) 0 = Matrix.row (A * V) 0"  
            by (rule mult_eq_first_row, insert first_row m1 less.prems, auto)
          obtain a zero B C where split: "split_block (A*V) 1 1 = (a, zero, B, C)"          
            using prod_cases4 by blast
          have a: "a \<in> carrier_mat 1 1" and zero: "zero \<in> carrier_mat 1 (n-1)" and
            B: "B \<in> carrier_mat (m-1) 1" and C: "C \<in> carrier_mat (m-1) (n-1)"
            by (rule split_block[OF split dim_row_AV dim_col_AV])+
          have AV_block: "A*V = four_block_mat a zero B C"
            by (rule split_block[OF split dim_row_AV dim_col_AV])
          have "\<exists>W. W\<in> carrier_mat (n-1) (n-1) \<and> invertible_mat W \<and> lower_triangular (C*W)" 
            by (rule less.hyps, insert n1 C, auto)        
          from this obtain W where inv_W: "invertible_mat W" and lt_CW: "lower_triangular (C*W)" 
            and W: "W \<in> carrier_mat (n-1) (n-1)" by blast
          let ?W2 = "four_block_mat (1\<^sub>m 1) (0\<^sub>m 1 (n-1)) (0\<^sub>m (n-1) 1) W"
          have W2: "?W2 \<in> carrier_mat n n" using V W dim_col_AV by auto
          have "Determinant.det ?W2 = Determinant.det (1\<^sub>m 1) * Determinant.det W" 
            by (rule det_four_block_mat_lower_left_zero_col[OF _ _ _ W], auto)
          hence det_W2: "Determinant.det ?W2 = Determinant.det W" by auto
          hence inv_W2: "invertible_mat ?W2"
            by (metis W four_block_carrier_mat inv_W invertible_iff_is_unit_JNF one_carrier_mat)
          have inv_V_W2: "invertible_mat (V * ?W2)" using inv_W2 inv_V V W2 invertible_mult_JNF by blast
          have "lower_triangular (A*V*?W2)"
          proof -
            let ?T = "(four_block_mat a (0\<^sub>m 1 (n-1)) B (C * W))"
            have zero_eq: "zero = 0\<^sub>m 1 (n-1)"
            proof (rule eq_matI)
              show 1: "dim_row zero = dim_row (0\<^sub>m 1 (n - 1))" and 2: "dim_col zero = dim_col (0\<^sub>m 1 (n - 1))"
                using zero by auto
              fix i j assume i: "i < dim_row (0\<^sub>m 1 (n - 1))" and j: "j < dim_col (0\<^sub>m 1 (n - 1))"
              have i0: "i=0" using i by auto            
              have "0 = Matrix.row (?first_row * V) 0 $v (j+1)"
                using lt_first_row_V j unfolding lower_triangular_def
                by (metis Suc_eq_plus1 carrier_matD(2) index_mult_mat(2,3) index_row(1) less_diff_conv
                    mat_of_row_dim(1) zero zero_less_Suc zero_less_one_class.zero_less_one V 2)
              also have "... = Matrix.row (A*V) 0 $v (j+1)" by (simp add: reduced_first_row)
              also have "... = (A*V) $$ (i, j+1)" using V dim_row_AV i0 j by auto
              also have "... = four_block_mat a zero B C $$ (i, j+1)" by (simp add: AV_block)
              also have "... = (if i < dim_row a then if (j+1) < dim_col a 
              then a $$ (i, (j+1)) else zero $$ (i, (j+1) - dim_col a) else if (j+1) < dim_col a
              then B $$ (i - dim_row a, (j+1)) else C $$ (i - dim_row a, (j+1) - dim_col a))"               
                by (rule index_mat_four_block, insert a zero i j C, auto)
              also have "... = zero $$ (i, (j+1) - dim_col a)" using a zero i j C by auto
              also have "... = zero $$ (i, j)" using a i by auto
              finally show "zero $$ (i, j) = 0\<^sub>m 1 (n - 1) $$ (i, j)" using i j by auto
            qed
            have rw1: "a * (1\<^sub>m 1) + zero * (0\<^sub>m (n-1) 1) = a" using a zero by auto
            have rw2: "a * (0\<^sub>m 1 (n-1)) + zero * W = 0\<^sub>m 1 (n-1)" using a zero zero_eq W by auto
            have rw3: "B * (1\<^sub>m 1) + C * (0\<^sub>m (n-1) 1) = B" using B C by auto
            have rw4: "B * (0\<^sub>m 1 (n-1)) + C * W = C * W" using B C W by auto
            have "A*V = four_block_mat a zero B C" by (rule AV_block)
            also have "... * ?W2 = four_block_mat (a * (1\<^sub>m 1) + zero * (0\<^sub>m (n-1) 1)) 
          (a * (0\<^sub>m 1 (n-1)) + zero * W) (B * (1\<^sub>m 1) + C * (0\<^sub>m (n-1) 1))
          (B * (0\<^sub>m 1 (n-1)) + C * W)" by (rule mult_four_block_mat[OF a zero B C], insert W, auto)
            also have "... = ?T" using rw1 rw2 rw3 rw4 by simp
            finally have AVW2: "A*V * ?W2 = ..." .
            moreover have "lower_triangular ?T" 
              using lt_CW unfolding lower_triangular_def using a zero B C W
              by (auto, metis (full_types) Suc_less_eq Suc_pred basic_trans_rules(19))
            ultimately show ?thesis by simp
          qed
          then show ?thesis using inv_V_W2 V W2 less.prems
            by (smt assoc_mult_mat mult_carrier_mat)
        qed
      qed
    qed
  qed
  thus "admits_triangular_reduction A" using A unfolding admits_triangular_reduction_def by simp
qed

corollary admits_diagonal_imp_admits_triangular':
  assumes a: "\<forall>A. admits_diagonal_reduction (A::'a mat)"
  shows "\<forall>A. admits_triangular_reduction (A::'a mat)"
  using admits_diagonal_imp_admits_triangular assms by blast


lemma admits_triangular_reduction_1x2:
  assumes "\<forall>A::'a mat. A \<in> carrier_mat 1 2 \<longrightarrow> admits_triangular_reduction A"
  shows "\<forall>C::'a mat. admits_triangular_reduction C" 
  using admits_diagonal_imp_admits_triangular assms triangular_eq_diagonal_1x2 by auto  

 
lemma Hermite_ring_OFCLASS:
 assumes "\<forall>A \<in> carrier_mat 1 2. admits_triangular_reduction (A::'a mat)"
 shows "OFCLASS('a, Hermite_ring_class)"
proof
  show "\<forall>A::'a mat. admits_triangular_reduction A" 
    by (rule admits_diagonal_imp_admits_triangular[OF assms[unfolded triangular_eq_diagonal_1x2]])     
qed

lemma Hermite_ring_OFCLASS':
 assumes "\<forall>A \<in> carrier_mat 1 2.admits_diagonal_reduction (A::'a mat)"
 shows "OFCLASS('a, Hermite_ring_class)"
proof
  show "\<forall>A::'a mat. admits_triangular_reduction A" 
    by (rule admits_diagonal_imp_admits_triangular[OF assms])     
qed

lemma theorem3_part1:
  assumes T: "(\<forall>a b::'a. \<exists> a1 b1 d. a = a1*d \<and> b = b1*d 
    \<and> ideal_generated {a1,b1} = ideal_generated {1})"
  shows "\<forall>A::'a mat. admits_triangular_reduction A"
proof (rule admits_triangular_reduction_1x2, rule allI, rule impI)
  fix A::"'a mat"
  assume A: "A \<in> carrier_mat 1 2"
  let ?a = "A $$ (0,0)"
  let ?b = "A $$ (0,1)"
  obtain a1 b1 d where a: "?a = a1*d" and b: "?b = b1*d" 
    and i: "ideal_generated {a1,b1} = ideal_generated {1}" 
    using T by blast
  obtain s t where sa1tb1:"s*a1+t*b1=1" using ideal_generated_pair_exists_pq1[OF i[simplified]] by blast
  let ?Q = "Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then s else
                                    if  i = 0 \<and> j = 1 then -b1 else
                                    if  i = 1 \<and> j = 0 then t else a1)"
  have Q: "?Q \<in> carrier_mat 2 2" by auto
  have det_Q: "Determinant.det ?Q = 1" unfolding det_2[OF Q] 
    using sa1tb1 by (simp add: mult.commute)
  hence inv_Q: "invertible_mat ?Q" using invertible_iff_is_unit_JNF[OF Q] by auto
  have lower_AQ: "lower_triangular (A*?Q)" 
  proof -
    have "Matrix.row A 0 $v Suc 0 * a1 = Matrix.row A 0 $v 0 * b1" if j2: "j<2" and j0: "0<j" for j
      by (metis A One_nat_def a b carrier_matD(1) carrier_matD(2) index_row(1) lessI 
          more_arith_simps(11) mult.commute numeral_2_eq_2 pos2)
    thus ?thesis unfolding lower_triangular_def using A 
      by (auto simp add: scalar_prod_def sum_two_rw)
  qed
  show "admits_triangular_reduction A" 
    unfolding admits_triangular_reduction_def using lower_AQ inv_Q Q A by force    
qed


lemma theorem3_part2:
  assumes 1: "\<forall>A::'a mat. admits_triangular_reduction A"
  shows "\<forall>a b::'a. \<exists> a1 b1 d. a = a1*d \<and> b = b1*d \<and> ideal_generated {a1,b1} = ideal_generated {1}"
proof (rule allI)+
  fix a b::'a
  let ?A = "Matrix.mat 1 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then a else b)"
  obtain Q where AQ: "lower_triangular (?A*Q)" and inv_Q: "invertible_mat Q"
    and Q: "Q \<in> carrier_mat 2 2"
    using 1 unfolding admits_triangular_reduction_def by fastforce
  hence [simp]: "dim_col Q = 2" and [simp]: "dim_row Q = 2" by auto
  let ?s = "Q $$ (0,0)"
  let ?t = "Q $$ (1,0)"
  let ?a1 = "Q $$ (1,1)"
  let ?b1 = "-(Q $$ (0,1))"
  let ?d = "(?A*Q) $$ (0,0)"
  have ab1_ba1: "a*?b1 = b*?a1"
  proof -     
    have  "(?A*Q) $$ (0,1) =  (\<Sum>i = 0..<2. (if i = 0 then a else b) * Q $$ (i, Suc 0))"
      unfolding times_mat_def col_def scalar_prod_def by auto
    also have "... = (\<Sum>i \<in> {0,1}. (if i = 0 then a else b) * Q $$ (i, Suc 0))" 
      by (rule sum.cong, auto)
    also have "... = - a*?b1 + b*?a1" by auto
    finally have "(?A*Q) $$ (0,1) = - a*?b1 + b*?a1" by simp
    moreover have "(?A*Q) $$ (0,1) = 0" using AQ unfolding lower_triangular_def by auto  
    ultimately show ?thesis
      by (metis add_left_cancel more_arith_simps(3) more_arith_simps(7))    
  qed
  have sa_tb_d: "?s*a+?t*b = ?d"
  proof -
    have "?d = (\<Sum>i = 0..<2. (if i = 0 then a else b) * Q $$ (i, 0))"
      unfolding times_mat_def col_def scalar_prod_def by auto
    also have "... = (\<Sum>i \<in> {0,1}. (if i = 0 then a else b) * Q $$ (i, 0))" by (rule sum.cong, auto)
    also have "... = ?s*a+?t*b" by auto
    finally show ?thesis by simp
  qed
  have det_Q_dvd_1: "(Determinant.det Q dvd 1)"
    using invertible_iff_is_unit_JNF[OF Q] inv_Q by auto
  moreover have det_Q_eq: "Determinant.det Q = ?s*?a1 + ?t*?b1" unfolding det_2[OF Q] by simp
  ultimately have "?s*?a1 + ?t*?b1 dvd 1" by auto
  from this obtain u where u_eq: "?s*?a1 + ?t*?b1 = u" and u: "u dvd 1" by auto
  hence eq1: "?s*?a1*a + ?t*?b1*a = u*a"
    by (metis ring_class.ring_distribs(2))
  hence "?s*?a1*a + ?t*?a1*b = u*a"
    by (metis (no_types, lifting) ab1_ba1 mult.assoc mult.commute)
  hence a1d_ua:"?a1*?d=u*a"
    by (smt Groups.mult_ac(2) distrib_left more_arith_simps(11) sa_tb_d)
  hence b1d_ub: "?b1*?d=u*b"
    by (smt Groups.mult_ac(2) Groups.mult_ac(3) ab1_ba1 distrib_right sa_tb_d u_eq)
  obtain inv_u where inv_u: "inv_u * u = 1" using u unfolding dvd_def
    by (metis mult.commute)
  hence inv_u_dvd_1: "inv_u dvd 1" unfolding dvd_def by auto
  have cond1: "(inv_u*?b1)*?d = b" using b1d_ub inv_u
    by (metis (no_types, lifting) Groups.mult_ac(3) more_arith_simps(11) more_arith_simps(6))
  have cond2: "(inv_u*?a1)*?d = a" using a1d_ua inv_u
    by (metis (no_types, lifting) Groups.mult_ac(3) more_arith_simps(11) more_arith_simps(6))
  have "ideal_generated {inv_u*?a1, inv_u*?b1} = ideal_generated {?a1,?b1}"
    by (rule ideal_generated_mult_unit2[OF inv_u_dvd_1])    
  also have "... = UNIV" using ideal_generated_pair_UNIV[OF u_eq u] by simp
  finally have cond3: "ideal_generated {inv_u*?a1, inv_u*?b1} = ideal_generated {1}" by auto
  show "\<exists>a1 b1 d. a = a1 * d \<and> b = b1 * d \<and> ideal_generated {a1, b1} = ideal_generated {1}"
    by (rule exI[of _ "inv_u*?a1"], rule exI[of _ "inv_u*?b1"], rule exI[of _ ?d],
        insert cond1 cond2 cond3, auto)
qed
  

theorem theorem3:
  shows "(\<forall>A::'a mat. admits_triangular_reduction A)
  = (\<forall>a b::'a. \<exists> a1 b1 d. a = a1*d \<and> b = b1*d \<and> ideal_generated {a1,b1} = ideal_generated {1})"
  using theorem3_part1 theorem3_part2 by auto

end



context comm_ring_1
begin


lemma lemma4_prev:
  assumes a: "a = a1*d" and b: "b = b1*d"
  and i: "ideal_generated {a1,b1} = ideal_generated {1}"
shows "ideal_generated {a,b} = ideal_generated {d}"
proof -
 have 1: "\<exists>k. p * (a1 * d) + q * (b1 * d) = k * d" for p q
    by (metis (full_types) local.distrib_right local.mult.semigroup_axioms semigroup.assoc)  
  have "ideal_generated {a,b} \<subseteq> ideal_generated {d}"
  proof -
    have "ideal_generated {a,b} = {p*a+q*b | p q. True}" using ideal_generated_pair by auto
    also have "... = {p*(a1*d)+q*(b1*d) | p q. True}" using a b by auto
    also have "... \<subseteq> {k*d|k. True}" using 1 by auto
    finally show ?thesis
      by (simp add: a b local.dvd_ideal_generated_singleton' local.ideal_generated_subset2)
  qed
  moreover have "ideal_generated{d} \<subseteq> ideal_generated {a,b}" 
  proof (rule ideal_generated_singleton_subset)
    obtain p q where "p*a1+q*b1 = 1" using ideal_generated_pair_exists_UNIV i by auto
    hence "d = p * (a1 * d) + q * (b1 * d)"
      by (metis local.mult_ac(3) local.ring_distribs(1) local.semiring_normalization_rules(12))
    also have "... \<in>  {p*(a1*d)+q*(b1*d) | p q. True}" by auto
    also have "... = ideal_generated {a,b}" unfolding ideal_generated_pair a b by auto
    finally show "d \<in> ideal_generated {a,b}" by simp
  qed (simp)
  ultimately show ?thesis by simp
qed


lemma lemma4:
  assumes a: "a = a1*d" and b: "b = b1*d"
    and i: "ideal_generated {a1,b1} = ideal_generated {1}"
    and i2: "ideal_generated {a,b} = ideal_generated {d'}"
  shows "\<exists>a1' b1'. a = a1' * d' \<and> b = b1' * d' 
    \<and> ideal_generated {a1',b1'} = ideal_generated {1}"
proof -
  have i3: "ideal_generated {a,b} = ideal_generated {d}" using lemma4_prev assms by auto
  have d_dvd_d': "d dvd d'"
    by (metis a b i2 dvd_ideal_generated_singleton dvd_ideal_generated_singleton' 
        dvd_triv_right ideal_generated_subset2)
  have d'_dvd_d: "d' dvd d" 
    using i3 i2 local.dvd_ideal_generated_singleton by auto
  obtain k and l where d: "d = k*d'" and d': "d' = l*d"
    using d_dvd_d' d'_dvd_d mult_ac unfolding dvd_def by auto
  obtain s t where sa1_tb1: "s*a1 + t*b1 = 1"
    using i ideal_generated_pair_exists_UNIV[of a1 b1] by auto
  let ?a1' = "k * l * t - t + a1 * k"
  let ?b1' = "s - k * l * s + b1 * k"
  have 1: "?a1'*d'=a"
    by (metis a d d' add_ac(2) add_diff_cancel add_diff_eq mult_ac(2) ring_distribs(1,4) 
        semiring_normalization_rules(18))
  have 2: "?b1'*d' = b"
    by (metis (no_types, hide_lams) b d d' add_ac(2) add_diff_cancel add_diff_eq mult_ac(2) mult_ac(3) 
        ring_distribs(2,4) semiring_normalization_rules(18)) 
  have "(s*l-b1)*?a1' + (t*l+a1)*?b1' = 1"
  proof -
    have aux_rw1: "s * l * k * l * t = t * l * k * l * s" and aux_rw2: "s * l * t=t * l * s" 
      and aux_rw3: "b1 * a1 * k=a1 * b1 * k" and aux_rw4: "t * l * b1 * k=b1 * k * l * t"
      and aux_rw5: "s * l * a1 * k=a1 * k * l * s"
      using mult.commute mult.assoc by auto
    note aux_rw = aux_rw1 aux_rw2 aux_rw3 aux_rw4 aux_rw5
    have "(s*l-b1)*?a1' + (t*l+a1)*?b1' = s*l*?a1' - b1*?a1' + t*l*?b1'+a1*?b1'"
      using local.add_ac(1) local.left_diff_distrib' local.ring_distribs(2) by auto
    also have "... = s * l * k * l*t - s * l * t + s * l * a1 * k-b1 * k * l * t + b1 * t-b1 * a1 * k
      + t * l * s-t * l * k * l * s + t * l * b1 * k + a1 * s - a1 * k * l * s + a1 * b1 * k"
      by (smt abel_semigroup.commute add.abel_semigroup_axioms diff_add_eq diff_diff_eq2
          mult.semigroup_axioms ring_distribs(4) semiring_normalization_rules(34) semigroup.assoc)
    also have "... = a1 * s + b1 * t" unfolding aux_rw
      by (smt add_ac(2) add_ac(3) add_minus_cancel ring_distribs(4) ring_normalization_rules(2))
    also have "... = 1" using sa1_tb1 mult.commute by auto
    finally show ?thesis by simp
  qed
  hence "ideal_generated {?a1',?b1'} = ideal_generated {1}"
    using ideal_generated_pair_exists_UNIV[of ?a1' ?b1'] by auto
  thus ?thesis using 1 2 by auto
qed


(*In the article, this is a corollary. But here, this needs more work.*)
lemma corollary5:
  assumes T: "\<forall>a b. \<exists>a1 b1 d. a = a1 * d \<and> b = b1 * d 
        \<and> ideal_generated {a1, b1} = ideal_generated {1::'a}"
 and i2: "ideal_generated {a,b,c} = ideal_generated {d}"
  shows "\<exists> a1 b1 c1. a = a1 * d \<and> b = b1 * d \<and> c = c1 * d 
  \<and> ideal_generated {a1,b1,c1} = ideal_generated {1}"
proof -
  have da: "d dvd a" using ideal_generated_singleton_dvd[OF i2] by auto
  have db: "d dvd b" using ideal_generated_singleton_dvd[OF i2] by auto
  have dc: "d dvd c" using ideal_generated_singleton_dvd[OF i2] by auto
  from this obtain c1' where c: "c = c1' * d" using dvd_def mult_ac(2) by auto
  obtain a1 b1 d' where a: "a = a1 * d'" and b: "b = b1 * d' "
    and i: "ideal_generated {a1, b1} = ideal_generated {1::'a}" using T by blast
  have i_ab_d': "ideal_generated {a, b} = ideal_generated {d'}"
    by (simp add: a b i lemma4_prev)
  have i2: "ideal_generated {d', c} = ideal_generated {d}"
    by (rule ideal_generated_triple_pair_rewrite[OF i2 i_ab_d'])  
  obtain u v dp  where d'1: "d' = u * dp" and d'2: "c = v * dp" 
    and xy: "ideal_generated{u,v}=ideal_generated{1}" using T by blast
  have "\<exists>a1' b1'. d' = a1' * d \<and> c = b1' * d \<and> ideal_generated {a1', b1'} = ideal_generated {1}"
    by (rule lemma4[OF d'1 d'2 xy i2])
  from this obtain a1' c1 where d'_a1: "d' = a1' * d" and c: "c = c1 * d" 
    and i3: "ideal_generated {a1', c1} = ideal_generated {1}" by blast
  have r1: "a = a1 * a1' * d" by (simp add: d'_a1 a local.semiring_normalization_rules(18))
  have r2: "b = b1 * a1' * d" by (simp add: d'_a1 b local.semiring_normalization_rules(18))
  have i4: "ideal_generated {a1 * a1',b1 * a1', c1} = ideal_generated {1}"
  proof -
    obtain p q where 1: "p * a1' + q * c1 = 1" 
      using i3 unfolding ideal_generated_pair_exists_UNIV by auto
    obtain x y where 2: "x*a1 + y*b1 = p" using ideal_generated_UNIV_obtain_pair[OF i] by blast
    have "1 = (x*a1 + y*b1) * a1' + q * c1" using 1 2 by auto
    also have "... = x*a1*a1' + y*b1*a1' + q * c1" by (simp add: local.ring_distribs(2))
    finally have "1 = x*a1*a1' + y*b1*a1' + q * c1" .
    hence "1 \<in> ideal_generated {a1 * a1', b1 * a1', c1}" 
      using ideal_explicit2[of "{a1 * a1', b1 * a1', c1}"] sum_three_elements'
      by (simp add: mult_assoc)
    hence "ideal_generated {1} \<subseteq> ideal_generated {a1 * a1',b1 * a1', c1}"
      by (rule ideal_generated_singleton_subset, auto)   
    thus ?thesis by auto
  qed
  show ?thesis using r1 r2 i4 c by auto
qed


end

context
  assumes "SORT_CONSTRAINT('a::comm_ring_1)"
begin

lemma OFCLASS_elementary_divisor_ring_imp_class:
  assumes "OFCLASS('a::comm_ring_1, elementary_divisor_ring_class)"
  shows " class.elementary_divisor_ring TYPE('a)" 
  by (rule conjunctionD2[OF assms[unfolded elementary_divisor_ring_class_def]])


(*ELEMENTARY DIVISOR RING \<Longrightarrow> HERMITE*)
corollary Elementary_divisor_ring_imp_Hermite_ring:
  assumes "OFCLASS('a::comm_ring_1, elementary_divisor_ring_class) "
  shows "OFCLASS('a::comm_ring_1, Hermite_ring_class)"
proof
  have "\<forall>A::'a mat. admits_diagonal_reduction A" 
    using OFCLASS_elementary_divisor_ring_imp_class[OF assms] 
    unfolding class.elementary_divisor_ring_def by auto
  thus "\<forall>A::'a mat. admits_triangular_reduction A" 
    using admits_diagonal_imp_admits_triangular by auto
qed

(*ELEMENTARY DIVISOR RING \<Longrightarrow> BEZOUT*)
corollary Elementary_divisor_ring_imp_Bezout_ring:
  assumes "OFCLASS('a::comm_ring_1, elementary_divisor_ring_class) "
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)"
  by (rule Hermite_ring_imp_Bezout_ring, rule Elementary_divisor_ring_imp_Hermite_ring[OF assms])

subsection \<open>Characterization of Elementary divisor rings\<close>

lemma necessity_D': 
  assumes edr: "(\<forall>(A::'a mat). admits_diagonal_reduction A)"
  shows "\<forall>a b c::'a. ideal_generated {a,b,c} = ideal_generated{1} 
  \<longrightarrow> (\<exists>p q. ideal_generated {p*a,p*b+q*c} = ideal_generated {1})"
proof ((rule allI)+, rule impI)
  fix a b c::'a 
  assume i: "ideal_generated {a,b,c} = ideal_generated{1}"  
  define A where "A = Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then a else
                                    if  i = 0 \<and> j = 1 then b else
                                    if  i = 1 \<and> j = 0 then 0 else c)"
  have A: "A \<in> carrier_mat 2 2" unfolding A_def by auto
  obtain P Q where P: "P \<in> carrier_mat (dim_row A) (dim_row A)"
        and Q: "Q \<in> carrier_mat (dim_col A) (dim_col A)" 
        and inv_P: "invertible_mat P" and inv_Q: "invertible_mat Q" 
        and SNF_PAQ: "Smith_normal_form_mat (P * A * Q)"
    using edr unfolding admits_diagonal_reduction_def by blast
  have [simp]: "dim_row P = 2" and [simp]: "dim_col P = 2 " and [simp]: "dim_row Q = 2" 
    and [simp]: "dim_col Q = 2" and [simp]: "dim_col A = 2" and [simp]: "dim_row A = 2" 
    using A P Q by auto
  define u where "u = (P*A*Q) $$ (0,0)"  
  define p where "p = P $$ (0,0)"
  define q where "q = P $$ (0,1)"
  define x where "x = Q $$ (0,0)"
  define y where "y = Q $$ (1,0)"
  have eq: "p*a*x + p*b*y + q*c*y = u"
  proof -   
    have rw1: "(\<Sum>ia = 0..<2. P $$ (0, ia) * A $$ (ia, x)) * Q $$ (x, 0) 
    = (\<Sum>ia\<in>{0, 1}. P $$ (0, ia) * A $$ (ia, x)) * Q $$ (x, 0)" 
      for x by (unfold sum_distrib_right, rule sum.cong, auto) 
    have "u = (\<Sum>i = 0..<2. (\<Sum>ia = 0..<2. P $$ (0, ia) * A $$ (ia, i)) * Q $$ (i, 0))"
      unfolding u_def p_def q_def x_def y_def
      unfolding times_mat_def scalar_prod_def by auto
    also have "... = (\<Sum>i \<in>{0,1}. (\<Sum>ia \<in> {0,1}. P $$ (0, ia) * A $$ (ia, i)) * Q $$ (i, 0))"
      by (rule sum.cong[OF _ rw1], auto)    
    also have "... = p*a*x + p*b*y+q*c*y"
      unfolding u_def p_def q_def x_def y_def A_def 
      using ring_class.ring_distribs(2) by auto
    finally show ?thesis ..
  qed  
  have u_dvd_1: "u dvd 1"
  (*
  The article deduces this fact since u divides all the elements of the matrix A. Here, this is 
  already proved using GCD and minors, but it requires the semiring_GCD class.
  At the end, I proved this fact by means of matrix multiplications once the inverse matrices of P
  and Q are obtained.
  *)
  proof (rule ideal_generated_dvd2[OF i])
    define D where "D = (P*A*Q)"
    obtain P' where  P'[simp]: "P' \<in> carrier_mat 2 2" and inv_P: "inverts_mat P' P" 
      using inv_P obtain_inverse_matrix[OF P inv_P]
      by (metis \<open>dim_row A = 2\<close>)      
    obtain Q' where [simp]: "Q' \<in> carrier_mat 2 2" and inv_Q: "inverts_mat Q Q'" 
      using inv_Q obtain_inverse_matrix[OF Q inv_Q]
      by (metis \<open>dim_col A = 2\<close>)
    have D[simp]: "D \<in> carrier_mat 2 2" unfolding D_def by auto
    have e: "P' * D * Q' = A" unfolding D_def by (rule inv_P'PAQQ'[OF _ _ inv_P inv_Q], auto)
    have [simp]: "(P' * D) \<in> carrier_mat 2 2" using D P' mult_carrier_mat by blast
    have D_01: "D $$ (0, 1) = 0" 
      using D_def SNF_PAQ unfolding Smith_normal_form_mat_def isDiagonal_mat_def by force
    have D_10: "D $$ (1, 0) = 0"
      using D_def SNF_PAQ unfolding Smith_normal_form_mat_def isDiagonal_mat_def by force
    have "D $$ (0,0) dvd D $$ (1, 1)" 
      using D_def SNF_PAQ unfolding Smith_normal_form_mat_def by auto
    from this obtain k where D11: "D $$ (1, 1) = D $$ (0,0) * k" unfolding dvd_def by blast
    have P'D_00: "(P' * D) $$ (0, 0) = P' $$ (0, 0) * D $$ (0, 0)" 
      using mat_mult2_00[of P' D] D_10 by auto 
    have P'D_01: "(P' * D) $$ (0, 1) =  P' $$ (0, 1) * D $$ (1, 1)" 
      using mat_mult2_01[of P' D] D_01 by auto
    have P'D_10: "(P' * D) $$ (1, 0) = P' $$ (1, 0) * D $$ (0, 0)" 
      using mat_mult2_10[of P' D] D_10 by auto
    have P'D_11: "(P' * D) $$ (1, 1) = P' $$ (1, 1) * D $$ (1, 1)" 
      using mat_mult2_11[of P' D] D_01 by auto
    have "a = (P' * D * Q') $$ (0,0)" using e A_def by auto
    also have "... = (P' * D) $$ (0, 0) * Q' $$ (0, 0) + (P' * D) $$ (0, 1) * Q' $$ (1, 0)" 
      by (rule mat_mult2_00, auto)
    also have "... = P' $$ (0, 0) * D $$ (0, 0) * Q' $$ (0, 0) 
      + P' $$ (0, 1) * (D $$ (0, 0) * k) * Q' $$ (1, 0)" unfolding P'D_00 P'D_01 D11 ..
    also have "... = D $$ (0, 0) * (P' $$ (0, 0) * Q' $$ (0, 0) 
      + P' $$ (0, 1) * k * Q' $$ (1, 0))" by (simp add: distrib_left)
    finally have u_dvd_a: "u dvd a" unfolding u_def D_def dvd_def by auto
    have "b = (P' * D * Q') $$ (0,1)" using e A_def by auto
    also have "... = (P' * D) $$ (0, 0) * Q' $$ (0, 1) + (P' * D) $$ (0, 1) * Q' $$ (1, 1)" 
      by (rule mat_mult2_01, auto)
    also have "... =  P' $$ (0, 0) * D $$ (0, 0) * Q' $$ (0, 1) +
       P' $$ (0, 1) * (D $$ (0, 0) * k) * Q' $$ (1, 1)" 
      unfolding P'D_00 P'D_01 D11 ..
    also have "... = D $$ (0, 0) * (P' $$ (0, 0) * Q' $$ (0, 1) +
       P' $$ (0, 1) * k * Q' $$ (1, 1))"  by (simp add: distrib_left)
    finally have u_dvd_b: "u dvd b" unfolding u_def D_def dvd_def by auto
    have "c = (P' * D * Q') $$ (1,1)" using e A_def by auto
    also have "... = (P' * D) $$ (1, 0) * Q' $$ (0, 1) + (P' * D) $$ (1, 1) * Q' $$ (1, 1)" 
      by (rule mat_mult2_11, auto)
    also have "... = P' $$ (1, 0) * D $$ (0, 0) * Q' $$ (0, 1) 
        + P' $$ (1, 1) * (D $$ (0, 0) * k) * Q' $$ (1, 1)" unfolding P'D_11 P'D_10 D11 ..
    also have "... = D $$ (0, 0) * (P' $$ (1, 0) * Q' $$ (0, 1) 
        + P' $$ (1, 1) * k * Q' $$ (1, 1))" by (simp add: distrib_left)
    finally have u_dvd_c: "u dvd c" unfolding u_def D_def dvd_def by auto
    show "\<forall>x\<in>{a,b,c}. u dvd x" using u_dvd_a u_dvd_b u_dvd_c by auto
  qed (simp)
  have "ideal_generated {p*a,p*b+q*c} = ideal_generated {1}"
    by (metis (no_types, lifting) eq add.assoc ideal_generated_1 ideal_generated_pair_UNIV 
        mult.commute semiring_normalization_rules(34) u_dvd_1)
  from this show "\<exists>p q. ideal_generated {p * a, p * b + q * c} = ideal_generated {1}"
    by auto
qed

lemma necessity:
  assumes "(\<forall>(A::'a mat). admits_diagonal_reduction A)"
  shows "(\<forall>(A::'a mat). admits_triangular_reduction A)"
 and "\<forall>a b c::'a. ideal_generated{a,b,c} = ideal_generated{1} 
  \<longrightarrow> (\<exists>p q. ideal_generated {p*a,p*b+q*c} = ideal_generated {1})"
  using necessity_D' admits_diagonal_imp_admits_triangular assms
  by blast+

text \<open>In the article, the authors change the notation and assume $(a,b,c) = (1)$. However,
we have to provide here the complete prove. To to this, I obtained a $D$ matrix such that
$A' = A*D$ and $D$ is a diagonal matrix with $d$ in the diagonal. Proving that $D$ is 
left and right commutative, I can follow the reasoning in the article\<close>

lemma sufficiency:
  assumes hermite_ring: "(\<forall>(A::'a mat). admits_triangular_reduction A)"
    and D': "\<forall>a b c::'a. ideal_generated{a,b,c} = ideal_generated{1} 
    \<longrightarrow> (\<exists>p q. ideal_generated {p*a,p*b+q*c} = ideal_generated {1})"
  shows "(\<forall>(A::'a mat). admits_diagonal_reduction A)"
proof -
  have admits_1x2: "\<forall>(A::'a mat) \<in> carrier_mat 1 2. admits_diagonal_reduction A"
    using hermite_ring triangular_eq_diagonal_1x2 by blast
  have admits_2x2: "\<forall>(A::'a mat) \<in> carrier_mat 2 2. admits_diagonal_reduction A"
  proof 
    fix B::"'a mat" assume B: "B \<in> carrier_mat 2 2"
    obtain U where BU: "lower_triangular (B*U)" and inv_U: "invertible_mat U"
      and U: "U \<in> carrier_mat 2 2" 
      using hermite_ring unfolding admits_triangular_reduction_def using B by fastforce
    define A where "A = B*U"
    define a where "a = A $$ (0,0)"
    define b where "b = A $$ (1,0)"
    define c where "c = A $$ (1,1)"
    have A: "A \<in> carrier_mat 2 2" using U B A_def by auto
    have A_01: "A$$(0,1) = 0" using BU U B unfolding lower_triangular_def A_def by auto    
    obtain d::'a where i: "ideal_generated {a,b,c} = ideal_generated {d}"      
      (*This fact is true since all the finitely generated ideals are principal ideals 
        in a Hermite ring*)  
    proof -
      have "OFCLASS('a, bezout_ring_class)" by (rule Hermite_ring_imp_Bezout_ring,
            insert OFCLASS_Hermite_ring_def[where ?'a='a] hermite_ring, auto)                
      hence "class.bezout_ring (*) (1::'a) (+) 0 (-) uminus" 
        using OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a = 'a] by auto
      hence "(\<forall>I::'a::comm_ring_1 set. finitely_generated_ideal I \<longrightarrow> principal_ideal I)"
        using bezout_ring_iff_fin_gen_principal_ideal2 by auto 
      moreover have "finitely_generated_ideal (ideal_generated {a,b,c})" 
        unfolding finitely_generated_ideal_def
        using ideal_ideal_generated by force
      ultimately have "principal_ideal (ideal_generated {a,b,c})" by auto
      thus ?thesis using that unfolding principal_ideal_def by auto
    qed
    have d_dvd_a: "d dvd a" and d_dvd_b: "d dvd b" and d_dvd_c: "d dvd c"
      using i ideal_generated_singleton_dvd by blast+    
    obtain a1 b1 c1 where a1: "a = a1 * d" and b1: "b = b1 * d" and c1: "c = c1 * d"
      and i2: "ideal_generated {a1,b1,c1} = ideal_generated {1}"
    proof -
      have T: "\<forall>a b. \<exists>a1 b1 d. a = a1 * d \<and> b = b1 * d 
        \<and> ideal_generated {a1, b1} = ideal_generated {1::'a}"
        by (rule theorem3_part2[OF hermite_ring]) (*Hermite ring is equivalent to the property T*)
      from this obtain a1' b1' d' where 1: "a = a1' * d'" and 2: "b = b1' * d'"
        and 3: "ideal_generated {a1', b1'} = ideal_generated {1::'a}" by blast
      have "\<exists>a1 b1 c1. a = a1 * d \<and> b = b1 * d \<and> c = c1 * d 
        \<and> ideal_generated {a1, b1, c1} = ideal_generated {1}"
        by (rule corollary5[OF T i])      
      from this show ?thesis using that by auto
    qed
     
    define D where "D = d \<cdot>\<^sub>m (1\<^sub>m 2)"
    define A' where "A' = Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then a1 else
                                    if  i = 1 \<and> j = 0 then b1 else
                                    if  i = 0 \<and> j = 1 then 0 else c1)"
    have D: "D \<in> carrier_mat 2 2" and A': "A'\<in> carrier_mat 2 2" unfolding A'_def D_def by auto
    have A_A'D: "A = A' * D" 
      by (rule eq_matI, insert D A' A a1 b1 c1 A_01 sum_two_rw a_def b_def c_def,
      unfold scalar_prod_def Matrix.row_def col_def  D_def A'_def, 
      auto simp add: sum_two_rw less_Suc_eq numerals(2))    
    have "1\<in> ideal_generated{a1,b1,c1}" using i2  by (simp add: ideal_generated_in) 
    from this obtain f where d: "(\<Sum>i\<in>{a1,b1,c1}. f i * i) = 1"
      using ideal_explicit2[of "{a1,b1,c1}"] by auto
    from this obtain x y z where "x*a1+y*b1+z*c1 = 1" 
      using sum_three_elements[of _ a1 b1 c1] by metis
    hence xa1_yb1_zc1_dvd_1: "x * a1 + y * b1 + z * c1 dvd 1" by auto    
    obtain p q where i3: "ideal_generated {p*a1,p*b1+q*c1} = ideal_generated {1}"
      using D' i2 by blast
    have "ideal_generated {p,q} = UNIV"
    proof -
      obtain X Y where e: "X*p*a1 + Y*(p*b1+q*c1) = 1"
        by (metis i3 ideal_generated_1 ideal_generated_pair_exists_UNIV mult.assoc)
      have "X*p*a1 + Y*(p*b1+q*c1) = X*p*a1 + Y*p*b1+Y*q*c1"
        by (simp add: add.assoc mult.assoc semiring_normalization_rules(34))
      also have "... = (X*a1+Y*b1) * p + (Y * c1) * q"
        by (simp add: mult.commute ring_class.ring_distribs)
      finally have "(X*a1+Y*b1) * p + Y * c1 * q = 1" using e by simp
      from this show ?thesis by (rule ideal_generated_pair_UNIV, simp)
    qed
    from this obtain u v where pu_qv_1: "p*u - q * v = 1"
      by (metis Groups.mult_ac(2) diff_minus_eq_add ideal_generated_1 
          ideal_generated_pair_exists_UNIV mult_minus_left)
    let ?P = "Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then p else
                                    if  i = 1 \<and> j = 0 then q else
                                    if  i = 0 \<and> j = 1 then v else u)"
    have P: "?P \<in> carrier_mat 2 2" by auto
    have "Determinant.det ?P = 1" using pu_qv_1 unfolding det_2[OF P] by (simp add: mult.commute)
    hence inv_P: "invertible_mat ?P"
      by (metis (no_types, lifting) P dvd_refl invertible_iff_is_unit_JNF)
    define S1 where "S1 = A'*?P"
    have S1: "S1 \<in> carrier_mat 2 2" using A' P S1_def mult_carrier_mat by blast
    have S1_00: "S1 $$(0,0) = p*a1" and S1_01: "S1 $$(1,0) = p*b1+q*c1" 
      unfolding S1_def times_mat_def scalar_prod_def using A' P BU U B 
      unfolding A'_def upper_triangular_def      
      by (auto, unfold sum_two_rw, auto simp add: A'_def a_def b_def c_def) 
    obtain q00 and q01 where q00_q01: "p*a1*q00 + (p*b1+q*c1)*q01 = 1" using i3
      by (metis ideal_generated_1 ideal_generated_pair_exists_pq1 mult.commute)
    define q10 where "q10 = - (p*b1+q*c1)"
    define q11 where "q11 = p*a1"
    have q10_q11: "p*a1*q10 + (p*b1+q*c1)*q11 = 0" unfolding q10_def q11_def
      by (auto simp add: Rings.ring_distribs(1) Rings.ring_distribs(4) semiring_normalization_rules(7))  
    let ?Q = "Matrix.mat 2 2 (\<lambda>(i,j). if i = 0 \<and> j = 0 then q00 else
                                    if  i = 1 \<and> j = 0 then q10 else
                                    if  i = 0 \<and> j = 1 then q01 else q11)"
    have Q: "?Q \<in> carrier_mat 2 2" by auto
    have "Determinant.det ?Q = 1" using q00_q01 unfolding det_2[OF Q] unfolding q10_def q11_def
      by (auto, metis (no_types, lifting) add_uminus_conv_diff diff_minus_eq_add more_arith_simps(7)
          more_arith_simps(9) mult.commute)
    hence inv_Q: "invertible_mat ?Q" by (smt Q dvd_refl invertible_iff_is_unit_JNF)
    define S2 where "S2 = ?Q * S1 "
    have S2: "S2 \<in> carrier_mat 2 2" using A' P S2_def S1 Q mult_carrier_mat by blast
    have S2_00: "S2 $$ (0,0) = 1" unfolding mat_mult2_00[OF Q S1 S2_def] using q00_q01 
      unfolding S1_00 S1_01 by (simp add: mult.commute)
    have S2_10: "S2 $$ (1,0) = 0" unfolding mat_mult2_10[OF Q S1 S2_def] 
      using q10_q11 unfolding S1_00 S1_01 by (simp add: Groups.mult_ac(2)) 
        (*Now we have a zero in the upper-right position. 
          We want to get also a zero in the lower-left position.*)
    let ?P1 ="(addrow_mat 2 (- (S2$$(0,1))) 0 1)"
    have P1: "?P1 \<in> carrier_mat 2 2" by auto
    have inv_P1: "invertible_mat ?P1"
      by (metis addrow_mat_carrier arithmetic_simps(78) det_addrow_mat dvd_def 
          invertible_iff_is_unit_JNF numeral_One zero_neq_numeral)
    define S3 where "S3 = S2 * ?P1"
    have P1_P_A': " A' *?P *?P1 \<in> carrier_mat 2 2" using P1 P A' mult_carrier_mat by auto
    have S3: "S3 \<in> carrier_mat 2 2" using P1 S2 S3_def mult_carrier_mat by blast
    have S3_00: "S3 $$ (0,0) = 1" using S2_00 unfolding mat_mult2_00[OF S2 P1  S3_def] by auto     
    moreover have S3_01: "S3 $$ (0,1) = 0" using S2_00 unfolding mat_mult2_01[OF S2 P1 S3_def] by auto
    moreover have S3_10: "S3 $$ (1,0) = 0" using S2_10 unfolding mat_mult2_10[OF S2 P1 S3_def] by auto
    ultimately have SNF_S3: "Smith_normal_form_mat S3"
      using S3 unfolding Smith_normal_form_mat_def isDiagonal_mat_def
      using less_2_cases by auto 
    hence SNF_S3_D: "Smith_normal_form_mat (S3*D)"
      using D_def S3 SNF_preserved_multiples_identity by blast
    have "S3 * D = ?Q * A' * ?P * ?P1 * D" using S1_def S2_def S3_def
      by (smt A' P Q S1 addrow_mat_carrier assoc_mult_mat)
    also have "... = ?Q * A' * ?P * (?P1 * D)"
      by (meson A' D addrow_mat_carrier assoc_mult_mat mat_carrier mult_carrier_mat)
    also have "... = ?Q * A' * ?P * (D * ?P1)" 
      using commute_multiples_identity[OF P1] unfolding D_def by auto
    also have "... = ?Q * A' * (?P * (D * ?P1))"
      by (smt A' D assoc_mult_mat carrier_matD(1) carrier_matD(2) mat_carrier times_mat_def)
    also have "... = ?Q * A' * (D * (?P * ?P1))"
      by (smt D D_def P P1 assoc_mult_mat commute_multiples_identity)
    also have "... = ?Q * (A' * D) * (?P * ?P1)"
      by (smt A' D assoc_mult_mat carrier_matD(1) carrier_matD(2) mat_carrier times_mat_def)
    also have "... = ?Q * A * (?P * ?P1)" unfolding A_A'D by auto     
    also have "... = ?Q * B * (U * (?P * ?P1))" unfolding A_def 
      by (smt B U assoc_mult_mat carrier_matD(1) carrier_matD(2) mat_carrier times_mat_def)
   finally have S3_D_rw: "S3 * D = ?Q * B * (U * (?P * ?P1))" .
    show "admits_diagonal_reduction B" 
    proof (rule admits_diagonal_reduction_intro[OF _ _ inv_Q])    
      show "(U* (?P * ?P1)) \<in> carrier_mat (dim_col B) (dim_col B)" using B U by auto
      show "?Q \<in> carrier_mat (dim_row B) (dim_row B)" using Q B by auto
      show "invertible_mat (U * (?P * ?P1))"
        by (metis (no_types, lifting) P1 U carrier_matD(1) carrier_matD(2) inv_P inv_P1 inv_U 
            invertible_mult_JNF mat_carrier times_mat_def)
      show "Smith_normal_form_mat (?Q * B *(U* (?P * ?P1)))" using SNF_S3_D S3_D_rw by simp
    qed    
  qed
  obtain Smith_1x2 where Smith_1x2: "\<forall>(A::'a mat)\<in>carrier_mat 1 2. is_SNF A (Smith_1x2 A)"
    using admits_diagonal_reduction_imp_exists_algorithm_is_SNF_all[OF admits_1x2] by auto
  from this obtain Smith_1x2' 
    where Smith_1x2': "\<forall>(A::'a mat)\<in>carrier_mat 1 2. is_SNF A (1\<^sub>m 1, Smith_1x2' A)"
    using Smith_1xn_two_matrices_all[OF Smith_1x2] by auto
  obtain Smith_2x2 where Smith_2x2: "\<forall>(A::'a mat)\<in>carrier_mat 2 2. is_SNF A (Smith_2x2 A)"
    using admits_diagonal_reduction_imp_exists_algorithm_is_SNF_all[OF admits_2x2] by auto  
  have d: "is_div_op (\<lambda>a b. (SOME k. k * b = a))" using div_op_SOME by auto
  interpret Smith_Impl Smith_1x2' Smith_2x2 "(\<lambda>a b. (SOME k. k * b = a))" 
    using Smith_1x2' Smith_2x2 d by (unfold_locales, auto)
  show ?thesis using is_SNF_Smith_mxn
    by (meson admits_diagonal_reduction_eq_exists_algorithm_is_SNF carrier_mat_triv)
qed

subsection \<open>Final theorem\<close>

(* Characterization of elementary divisor rings (theorem 6)*)

theorem edr_characterization:
  "(\<forall>(A::'a mat). admits_diagonal_reduction A) = ((\<forall>(A::'a mat). admits_triangular_reduction A) 
  \<and> (\<forall>a b c::'a. ideal_generated{a,b,c} = ideal_generated{1} 
                      \<longrightarrow> (\<exists>p q. ideal_generated {p*a,p*b+q*c} = ideal_generated {1})))"
  using necessity sufficiency by blast


corollary OFCLASS_edr_characterization:
"OFCLASS('a, elementary_divisor_ring_class) \<equiv> (OFCLASS('a, Hermite_ring_class) 
  &&& (\<forall>a b c::'a. ideal_generated{a,b,c} = ideal_generated{1} 
    \<longrightarrow> (\<exists>p q. ideal_generated {p*a,p*b+q*c} = ideal_generated {1})))" (is "?lhs \<equiv> ?rhs")
proof 
  assume 1: "OFCLASS('a, elementary_divisor_ring_class)"
  hence admits_diagonal: "\<forall>A::'a mat. admits_diagonal_reduction A"
    using conjunctionD2[OF 1[unfolded elementary_divisor_ring_class_def]] 
    unfolding class.elementary_divisor_ring_def by auto
  have "\<forall>A::'a mat. admits_triangular_reduction A" by (simp add: admits_diagonal necessity(1))
  hence OFCLASS_Hermite: "OFCLASS('a, Hermite_ring_class)" by (intro_classes, simp)
  moreover have "\<forall>a b c::'a. ideal_generated {a, b, c} = ideal_generated {1} 
                  \<longrightarrow> (\<exists>p q. ideal_generated {p * a, p * b + q * c} = ideal_generated {1})"
    using admits_diagonal necessity(2) by blast
  ultimately show "OFCLASS('a, Hermite_ring_class) &&& 
  \<forall>a b c::'a. ideal_generated {a, b, c} = ideal_generated {1} 
  \<longrightarrow> (\<exists>p q. ideal_generated {p * a, p * b + q * c} = ideal_generated {1})"
   by auto
next
  assume 1: "OFCLASS('a, Hermite_ring_class) &&&
      \<forall>a b c::'a. ideal_generated {a, b, c} = ideal_generated {1} \<longrightarrow>
        (\<exists>p q. ideal_generated {p * a, p * b + q * c} = ideal_generated {1})"
  have H: "OFCLASS('a, Hermite_ring_class)"
      and 2: "\<forall>a b c::'a. ideal_generated {a, b, c} = ideal_generated {1} \<longrightarrow>
        (\<exists>p q. ideal_generated {p * a, p * b + q * c} = ideal_generated {1})"
    using conjunctionD1[OF 1] conjunctionD2[OF 1] by auto
  have "\<forall>A::'a mat. admits_triangular_reduction A" 
    using H unfolding OFCLASS_Hermite_ring_def by auto
  hence a: "\<forall>A::'a mat. admits_diagonal_reduction A" using 2 sufficiency by blast
  show "OFCLASS('a, elementary_divisor_ring_class)" by (intro_classes, simp add: a)
qed

corollary edr_characterization_class:
"class.elementary_divisor_ring TYPE('a) 
  = (class.Hermite_ring TYPE('a) 
  \<and> (\<forall>a b c::'a. ideal_generated{a,b,c} = ideal_generated{1} 
\<longrightarrow> (\<exists>p q. ideal_generated {p*a,p*b+q*c} = ideal_generated {1})))" (is "?lhs = (?H \<and> ?D')")
proof 
  assume 1: ?lhs
  hence admits_diagonal: "\<forall>A::'a mat. admits_diagonal_reduction A" 
    unfolding class.elementary_divisor_ring_def .
  have admits_triangular: "\<forall>A::'a mat. admits_triangular_reduction A"
    using 1 necessity(1) unfolding class.elementary_divisor_ring_def by blast 
  hence "?H" unfolding class.Hermite_ring_def by auto 
  moreover have "?D'" using admits_diagonal necessity(2) by blast
  ultimately show "(?H \<and> ?D')" by simp
next
  assume HD': "(?H \<and> ?D')"
  hence admits_triangular: "\<forall>A::'a mat. admits_triangular_reduction A"
    unfolding class.Hermite_ring_def by auto
  hence admits_diagonal: "\<forall>A::'a mat. admits_diagonal_reduction A" 
    using edr_characterization HD' by auto      
  thus ?lhs unfolding class.elementary_divisor_ring_def by auto
qed


corollary edr_iff_T_D':
  shows "class.elementary_divisor_ring TYPE('a) = (
    (\<forall>a b::'a. \<exists> a1 b1 d. a = a1*d \<and> b = b1*d \<and> ideal_generated {a1,b1} = ideal_generated {1})
  \<and> (\<forall>a b c::'a. ideal_generated{a,b,c} = ideal_generated{1} 
      \<longrightarrow> (\<exists>p q. ideal_generated {p*a,p*b+q*c} = ideal_generated {1}))
  )" (is "?lhs = (?T \<and> ?D')")
proof
  assume 1: ?lhs
  hence "\<forall>A::'a mat. admits_triangular_reduction A"
    unfolding class.elementary_divisor_ring_def using necessity(1) by blast 
  hence "?T" using theorem3_part2 by simp
  moreover have "?D'"  using 1 unfolding edr_characterization_class by auto
  ultimately show "(?T \<and> ?D')" by simp
next
  assume TD': "(?T \<and> ?D')"
  hence "class.Hermite_ring TYPE('a)" 
    unfolding class.Hermite_ring_def using theorem3_part1 TD' by auto
  thus ?lhs using edr_characterization_class TD' by auto
qed

end
end
