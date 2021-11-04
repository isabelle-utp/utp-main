(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Generality of the Algorithm to transform from diagonal to Smith normal form\<close>

theory Admits_SNF_From_Diagonal_Iff_Bezout_Ring
  imports   
  Diagonal_To_Smith
  Rings2_Extended
  Smith_Normal_Form_JNF
  Finite_Field_Mod_Type_Connection
begin

hide_const (open) mat

text \<open>This section provides a formal proof on the generality of the algorithm that transforms
a diagonal matrix into its Smith normal form. More concretely, we prove that 
all diagonal matrices with coefficients in a ring R admit Smith normal form if and only if
R is a B\'ezout ring.

Since our algorithm is defined for B\'ezout rings and for any matrices (including non-square and
singular ones), this means that it does not exist another algorithm that performs the transformation
in a more abstract structure.\<close>

text \<open>Firstly, we hide some definitions and facts, since we are interested in the ones 
developed for the @{text "mod_type"} class.\<close>

hide_const (open) Bij_Nat.to_nat Bij_Nat.from_nat Countable.to_nat Countable.from_nat 
hide_fact (open) Bij_Nat.to_nat_from_nat_id Bij_Nat.to_nat_less_card

definition "admits_SNF_HA (A::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}) = (isDiagonal A 
    \<longrightarrow> (\<exists>P Q. invertible ((P::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type})) 
        \<and> invertible (Q::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}) \<and> Smith_normal_form (P**A**Q)))"

definition "admits_SNF_JNF A = (square_mat (A::'a::comm_ring_1 mat) \<and> isDiagonal_mat A 
  \<longrightarrow> (\<exists>P Q. P \<in> carrier_mat (dim_row A) (dim_row A) \<and> Q \<in> carrier_mat (dim_row A) (dim_row A) 
    \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat (P*A*Q)))"


subsection \<open>Proof of the  @{text "\<Longleftarrow>"} implication in HA.\<close>

lemma exists_f_PAQ_Aii':
  fixes A::"'a::{comm_ring_1}^'n::{mod_type}^'n::{mod_type}"
  assumes diag_A: "isDiagonal A"
  shows "\<exists>f. (P**A**Q) $h i $h i = (\<Sum>i\<in>(UNIV::'n set). f i * A $h i $h i)" 
proof -  
  have rw: "(\<Sum>ka\<in>UNIV. P $h i $h ka * A $h ka $h k) = P $h i $h k * A $h k $h k" for k
  proof -
    have "(\<Sum>ka\<in>UNIV. P $h i $h ka * A $h ka $h k) = (\<Sum>ka\<in>{k}. P $h i $h ka * A $h ka $h k)" 
    proof (rule sum.mono_neutral_right, auto)
      fix ia assume "P $h i $h ia * A $h ia $h k \<noteq> 0" 
      hence "A $h ia $h k \<noteq> 0" by auto
      thus" ia = k" using diag_A unfolding isDiagonal_def by auto  
    qed
    also have "... = P $h i $h k * A $h k $h k" by auto
    finally show ?thesis .
  qed
  let ?f = "\<lambda>k. (\<Sum>ka\<in>UNIV. P $h i $h ka) * Q $h k $h i"
  have "(P**A**Q) $h i $h i = (\<Sum>k\<in>UNIV. (\<Sum>ka\<in>UNIV. P $h i $h ka * A $h ka $h k) * Q $h k $h i)" 
    unfolding matrix_matrix_mult_def by auto  
  also have "... = (\<Sum>k\<in>UNIV.  P $h i $h k * Q $h k $h i * A $h k $h k)" 
    unfolding rw
    by (meson semiring_normalization_rules(16))
  finally show ?thesis by auto
qed

(*We would like to have the theorems within contexts:

context semiring_1
begin

lemma foo1:
  fixes foo::"'a::type\<Rightarrow>'a\<Rightarrow>'a"
  shows "foo a = c"
  sorry

end

where 'a has simply type "type". This way, we could have 
thm semiring_1.foo

Which is: class.semiring_1 ?one ?times ?plus ?zero \<Longrightarrow> ?foo ?a = ?c

However, many of them are proven with type restrictions instead of being proved within a context.
For example:

lemma foo2:
  fixes foo::"'a::semiring_1\<Rightarrow>'a\<Rightarrow>'a"
  shows "foo a = c" sorry

To convert foo2 to a statement like foo1, we need interalize_sort developed in From Types to Sets.

lemmas foo2 = foo1[internalize_sort "'a :: semiring_1"]
*)

text \<open>We apply @{text "internalize_sort"} to the lemma that we need\<close>

lemmas diagonal_to_Smith_PQ_exists_internalize_sort 
  = diagonal_to_Smith_PQ_exists[internalize_sort "'a :: bezout_ring"]

text \<open>We get the @{text "\<Longleftarrow>"} implication in HA.\<close>

lemma bezout_ring_imp_diagonal_admits_SNF:
  assumes of: "OFCLASS('a::comm_ring_1, bezout_ring_class)"
  shows "\<forall>A::'a^'n::{mod_type}^'n::{mod_type}. isDiagonal A 
    \<longrightarrow> (\<exists>P Q. 
        invertible (P::'a^'n::mod_type^'n::mod_type) \<and> 
        invertible (Q::'a^'n::mod_type^'n::mod_type) \<and> 
        Smith_normal_form (P**A**Q))"
proof (rule allI, rule impI)
  fix A::"'a^'n::{mod_type}^'n::{mod_type}"
  assume A: "isDiagonal A" 
  have br: "class.bezout_ring (*) (1::'a) (+) 0 (-) uminus" 
    by (rule OFCLASS_bezout_ring_imp_class_bezout_ring[OF of])   
  show "\<exists>P Q. 
        invertible (P::'a^'n::mod_type^'n::mod_type) \<and> 
        invertible (Q::'a^'n::mod_type^'n::mod_type) \<and> 
        Smith_normal_form (P**A**Q)" by (rule diagonal_to_Smith_PQ_exists_internalize_sort[OF br A])
qed

subsection \<open>Trying to prove the @{text "\<Longrightarrow>"} implication in HA.\<close>

text\<open>There is a problem: we need to define a matrix with a concrete dimension, which is not 
  possible in HA (the dimension depends on the number of elements on a set, and Isabelle/HOL does
  not feature dependent types)\<close>

lemma
  assumes "\<forall>A::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}. admits_SNF_HA A"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)" oops

(*
lemma   
  assumes "\<forall>A::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}. isDiagonal A 
    \<longrightarrow> (\<exists>P Q. invertible P \<and> invertible Q \<and> Smith_normal_form (P**A**Q))"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof (rule all_fin_gen_ideals_are_principal_imp_bezout, rule allI, rule impI)
  fix I::"'a set"
  assume fin: "finitely_generated_ideal I"
  obtain S where ig_S: "ideal_generated S = I" and fin_S: "finite S" 
    using fin unfolding finitely_generated_ideal_def by auto
  obtain xs where set_xs: "set xs = S" and d: "distinct xs" 
    using finite_distinct_list[OF fin_S] by blast
  hence length_eq_card: "length xs = card S" using distinct_card by force
(*
  The proof requires:
  1) Obtain a matrix A whose diagonal entries are the elements of xs
  2) Transform such a matrix A into its Smith normal form by means of elementary operations
  3) Put the diagonal entries of the matrix in Smith normal form as a list ys.
  4) Proof that the first element of ys divides all the other elements of such a list.
  5) Show that, ideal_generated (set xs) = ideal_generated (set ys) = ideal_generated (ys!0).
*)
  show "principal_ideal I"

qed

(*Alternative statement (same problems)*)

lemma   
  assumes "\<forall>A::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}. admits_SNF_HA A"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)" oops
*)


subsection \<open>Proof of the  @{text "\<Longrightarrow>"}  implication in JNF.\<close>

lemma exists_f_PAQ_Aii:
  assumes diag_A: "isDiagonal_mat (A::'a:: comm_ring_1 mat)" 
    and P: "P \<in> carrier_mat n n" 
    and A: "A \<in> carrier_mat n n" 
    and Q: "Q \<in> carrier_mat n n" 
    and i: "i < n" 
  (*  and d: "distinct (diag_mat A)" (*With some work, this assumption can be removed.*)*)
  shows "\<exists>f. (P*A*Q) $$ (i, i) = (\<Sum>i\<in>set (diag_mat A). f i * i)" 
proof -
  let ?xs = "diag_mat A"
  let ?n = "length ?xs"
  have length_n: "length (diag_mat A) = n"
    by (metis A carrier_matD(1) diag_mat_def diff_zero length_map length_upt)
  have xs_index: "?xs ! i = A $$ (i, i)" if "i<n" for i
    by (metis (no_types, lifting) add.left_neutral diag_mat_def length_map 
        length_n length_upt nth_map_upt that)
  have i_length: "i<length ?xs" using i length_n by auto
  have rw: "(\<Sum>ka = 0..<?n. P $$ (i, ka) * A $$ (ka, k)) = P $$(i, k) * A $$ (k, k)" 
    if k: "k<length ?xs" for k
  proof -
    have "(\<Sum>ka= 0..<?n. P $$ (i, ka) * A $$ (ka, k)) = (\<Sum>ka\<in>{k}. P $$ (i, ka) * A $$ (ka, k))" 
      by (rule sum.mono_neutral_right, auto simp add: k, 
          insert diag_A A length_n that, unfold isDiagonal_mat_def, fastforce)            
    also have "... = P $$(i, k) * A $$ (k, k)" by auto
    finally show ?thesis .
  qed
  let ?positions_of ="\<lambda>x. {i. A$$(i,i) = x \<and> i<length ?xs}"
  let ?T="set ?xs"
  let ?S ="{0..<?n}"
  let ?f = "\<lambda>x.(\<Sum>k\<in>{i. A $$ (i, i) = x \<and> i < length (diag_mat A)}. P $$ (i, k) * Q $$ (k, i))"
  let ?g = "(\<lambda>k. P $$ (i,k) * Q $$ (k, i) * A $$ (k, k))"
  have UNION_positions_of: "\<Union>(?positions_of ` ?T) = ?S" unfolding diag_mat_def by auto
  have "(P*A*Q) $$ (i,i) = (\<Sum>ia = 0..<?n.
        Matrix.row (Matrix.mat ?n ?n (\<lambda>(i, j). \<Sum>ia = 0..<?n. 
        Matrix.row P i $v ia * col A j $v ia)) i $v ia * col Q i $v ia)" 
    unfolding times_mat_def scalar_prod_def 
    using P Q i_length length_n A by auto
  also have "... = (\<Sum>k = 0..<?n. (\<Sum>ka = 0..<?n. P$$(i,ka) * A$$(ka,k)) * Q $$ (k,i))"
  proof (rule sum.cong, auto)
    fix x assume x: "x < length ?xs" 
    have rw_colQ: "col Q i $v x = Q $$ (x, i)"
      using Q i_length x length_n A by auto
    have rw2: " Matrix.row (Matrix.mat ?n ?n
            (\<lambda>(i, j). \<Sum>ia = 0..<length ?xs. Matrix.row P i $v ia * col A j $v ia)) i $v x 
            =(\<Sum>ia = 0..<length ?xs. Matrix.row P i $v ia * col A x $v ia)"
      unfolding row_mat[OF i_length] unfolding index_vec[OF x] by auto
    also have "... = (\<Sum>ia = 0..<length ?xs.  P $$ (i,ia) * A $$ (ia,x))" 
      by (rule sum.cong, insert P i_length x length_n A, auto)
    finally show "Matrix.row (Matrix.mat ?n ?n (\<lambda>(i, j). \<Sum>ia = 0..<?n. Matrix.row P i $v ia 
            * col A j $v ia)) i $v x * col Q i $v x 
            = (\<Sum>ka = 0..<?n. P $$ (i, ka) * A $$ (ka, x)) * Q $$ (x, i)" unfolding rw_colQ by auto
  qed       
  also have "... = (\<Sum>k = 0..<?n. P $$ (i,k) * Q $$ (k, i) * A $$ (k, k))"
    by (smt rw semiring_normalization_rules(16) sum.ivl_cong)
  also have "... = sum ?g (\<Union>(?positions_of ` ?T))" 
    using UNION_positions_of by auto
  also have "... = (\<Sum>x\<in>?T. sum ?g (?positions_of x))"
    by (rule sum.UNION_disjoint, auto)
  also have "... = (\<Sum>x\<in>set (diag_mat A). (\<Sum>k\<in>{i. A $$ (i, i) = x \<and> i < length (diag_mat A)}. 
    P $$ (i, k) * Q $$ (k, i)) * x)"
    by (rule sum.cong, auto simp add: Groups_Big.sum_distrib_right)  
  finally show ?thesis by auto
qed

text \<open>Proof of the @{text "\<Longrightarrow>"} implication in JNF.\<close>

lemma diagonal_admits_SNF_imp_bezout_ring_JNF:
  assumes admits_SNF: "\<forall>A n. (A::'a mat) \<in> carrier_mat n n \<and> isDiagonal_mat A
  \<longrightarrow> (\<exists>P Q. P \<in> carrier_mat n n \<and> Q \<in> carrier_mat n n \<and> invertible_mat P \<and> invertible_mat Q 
      \<and> Smith_normal_form_mat (P*A*Q))"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof (rule all_fin_gen_ideals_are_principal_imp_bezout, rule allI, rule impI)
  fix I::"'a set"
  assume fin: "finitely_generated_ideal I"
  obtain S where ig_S: "ideal_generated S = I" and fin_S: "finite S" 
    using fin unfolding finitely_generated_ideal_def by auto
  show "principal_ideal I"
  proof (cases "S = {}")
    case True
    then show ?thesis
      by (metis ideal_generated_0 ideal_generated_empty ig_S principal_ideal_def)
  next
    case False    
    obtain xs where set_xs: "set xs = S" and d: "distinct xs" 
      using finite_distinct_list[OF fin_S] by blast
    hence length_eq_card: "length xs = card S" using distinct_card by force
    let ?n = "length xs"
    let ?A = "Matrix.mat ?n ?n (\<lambda>(a,b). if a = b then xs!a else 0)"
    have A_carrier: "?A \<in> carrier_mat ?n ?n" by auto
    have diag_A: "isDiagonal_mat ?A" unfolding isDiagonal_mat_def by auto
    have set_xs_eq: "set xs = {?A$$(i,i)| i. i<dim_row ?A}"
      by (auto, smt case_prod_conv d distinct_Ex1 index_mat(1))
    have set_xs_diag_mat: "set xs = set (diag_mat ?A)" 
      using set_xs_eq unfolding diag_mat_def by auto
    obtain P Q where P: "P \<in> carrier_mat ?n ?n" 
      and Q: "Q \<in> carrier_mat ?n ?n" and inv_P: "invertible_mat P" and inv_Q: "invertible_mat Q"
      and SNF_PAQ: "Smith_normal_form_mat (P*?A*Q)" 
      using admits_SNF A_carrier diag_A by blast
    define ys where ys_def: "ys = diag_mat (P*?A*Q)" 
    have ys: "\<forall>i<?n. ys ! i = (P*?A*Q) $$ (i,i)" using P by (auto simp add: ys_def diag_mat_def)
    have length_ys: "length ys = ?n" unfolding ys_def
      by (metis (no_types, lifting) P carrier_matD(1) diag_mat_def 
          index_mult_mat(2) length_map map_nth)    
    have n0: "?n > 0" using False set_xs by blast
    have set_ys_diag_mat: "set ys = set (diag_mat (P*?A*Q))" using ys_def by auto
    let ?i = "ys ! 0"
    have dvd_all: "\<forall>a \<in> set ys. ?i dvd a"
    proof    
      fix a assume a: "a \<in> set ys"
      obtain j where ys_j_a: "ys ! j = a" and jn: "j<?n" by (metis a in_set_conv_nth length_ys) 
      have jP: "j < dim_row P" using jn P by auto
      have jQ: "j < dim_col Q" using jn Q by auto
      have "(P*?A*Q)$$(0,0) dvd (P*?A*Q)$$(j,j)"
        by (rule SNF_first_divides[OF SNF_PAQ], auto simp add: jP jQ)
      thus "ys ! 0 dvd a" using ys length_ys ys_j_a jn n0 by auto
    qed
    have "ideal_generated S = ideal_generated (set xs)" using set_xs by simp
    also have "... = ideal_generated (set ys)"
    proof
      show "ideal_generated (set xs) \<subseteq> ideal_generated (set ys)"
      proof (rule ideal_generated_subset2, rule ballI)
        fix b assume b: "b \<in> set xs"
        obtain i where b_A_ii: "b = ?A $$ (i,i)" and i_length: "i<length xs" 
          using b set_xs_eq by auto
        obtain P' where inverts_mat_P': "inverts_mat P P' \<and> inverts_mat P' P" 
          using inv_P unfolding invertible_mat_def by auto
        have P': "P' \<in> carrier_mat ?n ?n" 
          using inverts_mat_P' 
          unfolding carrier_mat_def inverts_mat_def
          by (auto,metis P carrier_matD index_mult_mat(3) one_carrier_mat)+
        obtain Q' where inverts_mat_Q': "inverts_mat Q Q' \<and> inverts_mat Q' Q"
          using inv_Q unfolding invertible_mat_def by auto
        have Q': "Q' \<in> carrier_mat ?n ?n" 
          using inverts_mat_Q'
          unfolding carrier_mat_def inverts_mat_def
          by (auto,metis Q carrier_matD index_mult_mat(3) one_carrier_mat)+
        have rw_PAQ: "(P'*(P*?A*Q)*Q') $$ (i, i) = ?A $$ (i,i)"
          using inv_P'PAQQ'[OF A_carrier P _ _ Q P' Q'] inverts_mat_P' inverts_mat_Q' by auto
        have diag_PAQ: "isDiagonal_mat (P*?A*Q)" 
          using SNF_PAQ unfolding Smith_normal_form_mat_def by auto
        have PAQ_carrier: "(P*?A*Q) \<in> carrier_mat ?n ?n" using P Q by auto
        obtain f where f: "(P'*(P*?A*Q)*Q') $$ (i, i) = (\<Sum>i\<in>set (diag_mat (P*?A*Q)). f i * i)"
          using exists_f_PAQ_Aii[OF diag_PAQ P' PAQ_carrier Q' i_length] by auto
        hence "?A $$ (i,i) = (\<Sum>i\<in>set (diag_mat (P*?A*Q)). f i * i)" unfolding rw_PAQ .
        thus "b\<in> ideal_generated (set ys)"
          unfolding ideal_explicit using set_ys_diag_mat b_A_ii by auto
      qed      
      show "ideal_generated (set ys) \<subseteq> ideal_generated (set xs)"
      proof (rule ideal_generated_subset2, rule ballI)
        fix b assume b: "b \<in> set ys"
        have d: "distinct (diag_mat ?A)"
          by (metis (no_types, lifting) A_carrier card_distinct carrier_matD(1) diag_mat_def 
             length_eq_card length_map map_nth set_xs set_xs_diag_mat)
        obtain i where b_PAQ_ii: "(P*?A*Q) $$ (i,i) = b" and i_length: "i<length xs" using b ys
          by (metis (no_types, lifting) in_set_conv_nth length_ys)
        obtain f where "(P * ?A * Q) $$ (i, i) = (\<Sum>i\<in>set (diag_mat ?A). f i * i)" 
          using exists_f_PAQ_Aii[OF diag_A P _ Q i_length] by auto
        thus "b \<in> ideal_generated (set xs)" 
          using b_PAQ_ii unfolding set_xs_diag_mat ideal_explicit by auto
      qed
    qed
    also have "... = ideal_generated (set ys - (set ys - {ys!0}))"
    proof (rule ideal_generated_dvd_eq_diff_set)
      show "?i \<in> set ys" using n0
        by (simp add: length_ys)
      show "?i \<notin> set ys - {?i}" by auto
      show "\<forall>j\<in>set ys - {?i}. ?i dvd j" using dvd_all by auto 
      show "finite (set ys - {?i})" by auto
    qed
    also have "... = ideal_generated {?i}"
      by (metis Diff_cancel Diff_not_in insert_Diff insert_Diff_if length_ys n0 nth_mem)
    finally show "principal_ideal I" unfolding principal_ideal_def using ig_S by auto
  qed
qed



(*Alternative statement:*)
corollary diagonal_admits_SNF_imp_bezout_ring_JNF_alt:
  assumes admits_SNF: "\<forall>A. square_mat (A::'a mat) \<and> isDiagonal_mat A 
\<longrightarrow> (\<exists>P Q. P \<in> carrier_mat (dim_row A) (dim_row A) 
  \<and> Q \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> invertible_mat Q 
  \<and> Smith_normal_form_mat (P*A*Q))"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof (rule diagonal_admits_SNF_imp_bezout_ring_JNF, rule allI, rule allI, rule impI)
  fix A::"'a mat" and n assume A: "A \<in> carrier_mat n n \<and> isDiagonal_mat A"
  have "square_mat A" using A by auto
  thus "\<exists>P Q. P \<in> carrier_mat n n \<and> Q \<in> carrier_mat n n 
  \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat (P * A * Q)" 
    using A admits_SNF by blast
qed


subsection \<open>Trying to transfer the @{text "\<Longrightarrow>"} implication to HA.\<close>

text \<open>We first hide some constants defined in @{text "Mod_Type_Connect"} in order to use the ones
presented in @{text "Perron_Frobenius.HMA_Connect"} by default.\<close>


context 
  includes lifting_syntax
begin

lemma to_nat_mod_type_Bij_Nat:
  fixes a::"'n::mod_type"
  obtains b::'n where "mod_type_class.to_nat a = Bij_Nat.to_nat b"
  using Bij_Nat.to_nat_from_nat_id mod_type_class.to_nat_less_card by metis

lemma inj_on_Bij_nat_from_nat: "inj_on (Bij_Nat.from_nat::nat \<Rightarrow> 'a) {0..<CARD('a::finite)}"  
  by (auto simp add: inj_on_def Bij_Nat.from_nat_def length_univ_list_card 
      nth_eq_iff_index_eq univ_list(1))

text \<open>This lemma only holds if $a$ and $b$ have the same type. Otherwise, 
  it is possible that @{text "Bij_Nat.to_nat a = Bij_Nat.to_nat b"}\<close>

lemma Bij_Nat_to_nat_neq:
  fixes a b ::"'n::mod_type"
  assumes "to_nat a \<noteq> to_nat b"
  shows "Bij_Nat.to_nat a \<noteq> Bij_Nat.to_nat b"  
  using assms to_nat_inj by blast

text \<open>The following proof (a transfer rule for diagonal matrices) 
  is weird, since it does not hold 
  @{text "Bij_Nat.to_nat a = mod_type_class.to_nat a"}. 

  At first, it seems possible to obtain the element $a'$ that satisfies 
   @{text "Bij_Nat.to_nat a' = mod_type_class.to_nat a"} and then continue with the proof, but then
  we cannot prove @{text "HMA_I (Bij_Nat.to_nat a') a"}.

  This means that we must use the previous lemma @{text "Bij_Nat_to_nat_neq"}, but this imposes the 
  matrix to be square.
  \<close>

lemma HMA_isDiagonal[transfer_rule]: "(HMA_M ===> (=)) 
  isDiagonal_mat (isDiagonal::('a::{zero}^'n::{mod_type}^'n::{mod_type} => bool))"
proof (intro rel_funI, goal_cases)
  case (1 x y)
  note rel_xy [transfer_rule] = "1"
  have "y $h a $h b = 0"
    if all0: "\<forall>i j. i \<noteq> j \<and> i < dim_row x \<and> j < dim_col x \<longrightarrow> x $$ (i, j) = 0"
      and a_noteq_b: "a \<noteq> b" for a::'n and b::'n
  proof -
    have "to_nat a \<noteq> to_nat b" using a_noteq_b by auto
    hence distinct: "Bij_Nat.to_nat a \<noteq> Bij_Nat.to_nat b" by (rule Bij_Nat_to_nat_neq)
    moreover have "Bij_Nat.to_nat a < dim_row x" and "Bij_Nat.to_nat b < dim_col x"
      using Bij_Nat.to_nat_less_card dim_row_transfer_rule rel_xy dim_col_transfer_rule 
      by fastforce+
    ultimately have b: "x $$ (Bij_Nat.to_nat a, Bij_Nat.to_nat b) = 0" using all0 by auto
    have [transfer_rule]: "HMA_I (Bij_Nat.to_nat a) a" by (simp add: HMA_I_def)
    have [transfer_rule]: "HMA_I (Bij_Nat.to_nat b) b" by (simp add: HMA_I_def)
    have "index_hma y a b = 0" using b by (transfer', auto)
    thus ?thesis unfolding index_hma_def .
  qed
  moreover have "x $$ (i, j) = 0" 
    if all0: "\<forall>a b. a \<noteq> b \<longrightarrow> y $h a $h b = 0"
      and ij: "i \<noteq> j" and i: "i < dim_row x" and j: "j < dim_col x" for i j
  proof -
    have i_n: "i < CARD('n)" and j_n: "j < CARD('n)"
      using i j rel_xy dim_row_transfer_rule dim_col_transfer_rule
      by fastforce+
    let ?i' = "Bij_Nat.from_nat i::'n"
    let ?j' = "Bij_Nat.from_nat j::'n"
    have i'_neq_j': "?i' \<noteq> ?j'" using ij i_n j_n Bij_Nat.from_nat_inj by blast
    hence y0: "index_hma y ?i' ?j' = 0" using all0 unfolding index_hma_def by auto    
    have [transfer_rule]: "HMA_I i ?i'" unfolding HMA_I_def
      by (simp add: Bij_Nat.to_nat_from_nat_id i_n)
    have [transfer_rule]: "HMA_I j ?j'" unfolding HMA_I_def
      by (simp add: Bij_Nat.to_nat_from_nat_id j_n)
    show ?thesis using y0 by (transfer, auto)
  qed
  ultimately show ?case unfolding isDiagonal_mat_def isDiagonal_def
    by auto
qed

text \<open>Indeed, we can prove the transfer rules with the new connection based on the 
  @{text "mod_type"} class, which was developed in the  @{text "Mod_Type_Connect"} file\<close>

text \<open>This is the same lemma as the one presented above, but now using the @{text "to_nat"} function
  defined in the  @{text "mod_type"} class and then we can prove it for non-square matrices, 
  which is very useful since our algorithms are not restricted to square matrices.\<close>


lemma HMA_isDiagonal_Mod_Type[transfer_rule]: "(Mod_Type_Connect.HMA_M ===> (=)) 
  isDiagonal_mat (isDiagonal::('a::{zero}^'n::{mod_type}^'m::{mod_type} => bool))"
proof (intro rel_funI, goal_cases)
  case (1 x y)
  note rel_xy [transfer_rule] = "1"
  have "y $h a $h b = 0"
    if all0: "\<forall>i j. i \<noteq> j \<and> i < dim_row x \<and> j < dim_col x \<longrightarrow> x $$ (i, j) = 0"
      and a_noteq_b: "to_nat a \<noteq> to_nat b" for a::'m and b::'n
  proof -
    have distinct: "to_nat a \<noteq> to_nat b" using a_noteq_b by auto
    moreover have "to_nat a < dim_row x" and "to_nat b < dim_col x"
      using to_nat_less_card rel_xy 
      using Mod_Type_Connect.dim_row_transfer_rule Mod_Type_Connect.dim_col_transfer_rule 
      by fastforce+
    ultimately have b: "x $$ (to_nat a, to_nat b) = 0" using all0 by auto
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (to_nat a) a" 
      by (simp add: Mod_Type_Connect.HMA_I_def)
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (to_nat b) b" 
      by (simp add: Mod_Type_Connect.HMA_I_def)
    have "index_hma y a b = 0" using b by (transfer', auto)
    thus ?thesis unfolding index_hma_def .
  qed
  moreover have "x $$ (i, j) = 0" 
    if all0: "\<forall>a b. to_nat a \<noteq> to_nat b \<longrightarrow> y $h a $h b = 0"
      and ij: "i \<noteq> j" and i: "i < dim_row x" and j: "j < dim_col x" for i j
  proof -
    have i_n: "i < CARD('m)"
      using i rel_xy by (simp add: Mod_Type_Connect.dim_row_transfer_rule)
    have j_n: "j < CARD('n)"
      using j rel_xy by (simp add: Mod_Type_Connect.dim_col_transfer_rule)
    let ?i' = "from_nat i::'m"
    let ?j' = "from_nat j::'n"
    have "to_nat ?i' \<noteq> to_nat ?j'"
      by (simp add: i_n ij j_n mod_type_class.to_nat_from_nat_id)
    hence y0: "index_hma y ?i' ?j' = 0" using all0 unfolding index_hma_def by auto
    have [transfer_rule]: "Mod_Type_Connect.HMA_I i ?i'" 
      unfolding Mod_Type_Connect.HMA_I_def
      by (simp add: to_nat_from_nat_id i_n)
    have [transfer_rule]: "Mod_Type_Connect.HMA_I j ?j'" 
      unfolding Mod_Type_Connect.HMA_I_def
      by (simp add: to_nat_from_nat_id j_n)
    show ?thesis using y0 by (transfer, auto)
  qed
  ultimately show ?case unfolding isDiagonal_mat_def isDiagonal_def
    by auto
qed


(*We cannot state:

 lemma HMA_SNF[transfer_rule]: "(HMA_M ===> (=)) Smith_normal_form_mat
  (Smith_normal_form::'a::{comm_ring_1}^'n::{mod_type}^'n::{mod_type}\<Rightarrow>bool)"

Since we need properties about Suc (Bij_Nat.to_nat a). This means that is mandatory to use
a bridge that relates the JNF representation with the HA one based on indexes with the mod_type
class restriction. This is carried out in the file Mod_Type_Connect.

Otherwise, I cannot relate 

x $$ (to_nat a, to_nat a) dvd x $$ (to_nat (a + 1), to_nat (a + 1))

with

y $h a $h a dvd y $h (a + 1) $h (a + 1) 

being such to_nat the one presented in Mod_Type, which is not the same as Bij_Nat.to_nat 
(mod_type_class.to_nat satisfies more properties that easier the definitions and proofs, 
and indeed are fundamental for defining the Smith normal form).
*)

text\<open>We state the transfer rule using the relations developed in the new bride of the file
    @{text "Mod_Type_Connect"}.\<close>

lemma HMA_SNF[transfer_rule]: "(Mod_Type_Connect.HMA_M ===> (=)) Smith_normal_form_mat 
(Smith_normal_form::'a::{comm_ring_1}^'n::{mod_type}^'m::{mod_type}\<Rightarrow>bool)"
proof (intro rel_funI, goal_cases)
  case (1 x y)
  note rel_xy[transfer_rule] = "1"
  have "y $h a $h b dvd y $h (a + 1) $h (b + 1)"
    if SNF_condition: "\<forall>a. Suc a < dim_row x \<and> Suc a < dim_col x 
      \<longrightarrow> x $$ (a, a) dvd x $$ (Suc a, Suc a)"
      and a1: "Suc (to_nat a) < nrows y" and a2: "Suc (to_nat b) < ncols y"
      and ab: "to_nat a = to_nat b" for a::'m and b::'n      
  proof -
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (to_nat a) a" 
      by (simp add: Mod_Type_Connect.HMA_I_def)
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (to_nat (a+1)) (a+1)" 
      by (simp add: Mod_Type_Connect.HMA_I_def)
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (to_nat b) b" 
      by (simp add: Mod_Type_Connect.HMA_I_def)
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (to_nat (b+1)) (b+1)" 
      by (simp add: Mod_Type_Connect.HMA_I_def)
    have "Suc (to_nat a) < dim_row x" using a1
      by (metis Mod_Type_Connect.dim_row_transfer_rule nrows_def rel_xy)    
    moreover have "Suc (to_nat b) < dim_col x"
      by (metis Mod_Type_Connect.dim_col_transfer_rule a2 ncols_def rel_xy)
    ultimately have "x $$ (to_nat a, to_nat b) dvd x $$ (Suc (to_nat a), Suc (to_nat b))"
      using SNF_condition by (simp add: ab)
    also have "... = x $$ (to_nat (a+1), to_nat (b+1))"
      by (metis Suc_eq_plus1 a1 a2 nrows_def ncols_def to_nat_suc)
    finally have SNF_cond: "x $$ (to_nat a, to_nat b) dvd x $$ (to_nat (a + 1), to_nat (b + 1))" .    
    have "x $$ (to_nat a, to_nat b) = index_hma y a b" by (transfer, simp)
    moreover have "x $$ (to_nat (a + 1), to_nat (b + 1)) = index_hma y (a+1) (b+1)"
      by (transfer, simp)
    ultimately show ?thesis using SNF_cond unfolding index_hma_def by auto
  qed
  moreover have  "x $$ (a, a) dvd x $$ (Suc a, Suc a)"
    if SNF: "\<forall>a b. to_nat a = to_nat b \<and> Suc (to_nat a) < nrows y \<and> Suc (to_nat b) < ncols y
        \<longrightarrow> y $h a $h b dvd y $h (a + 1) $h (b + 1)" 
      and a1: "Suc a < dim_row x" and a2: "Suc a < dim_col x" for a
  proof -
    have dim_row_CARD: "dim_row x = CARD('m)"
      using Mod_Type_Connect.dim_row_transfer_rule rel_xy by blast
    have dim_col_CARD: "dim_col x = CARD('n)"
      using Mod_Type_Connect.dim_col_transfer_rule rel_xy by blast
    let ?a' = "from_nat a::'m"
    let ?b' = "from_nat a::'n"
    have Suc_a_less_CARD: "a + 1 < CARD('m)" using a1 dim_row_CARD by auto
    have Suc_b_less_CARD: "a + 1 < CARD('n)" using a2
      by (metis Mod_Type_Connect.dim_col_transfer_rule Suc_eq_plus1 rel_xy)
    have aa'[transfer_rule]: "Mod_Type_Connect.HMA_I a ?a'"
      unfolding Mod_Type_Connect.HMA_I_def
      by (metis Suc_a_less_CARD add_lessD1 mod_type_class.to_nat_from_nat_id)
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (a+1) (?a' + 1)" 
      unfolding Mod_Type_Connect.HMA_I_def
      unfolding from_nat_suc[symmetric] using to_nat_from_nat_id[OF Suc_a_less_CARD] by auto
    have ab'[transfer_rule]: "Mod_Type_Connect.HMA_I a ?b'"
      unfolding Mod_Type_Connect.HMA_I_def 
      by (metis Suc_b_less_CARD add_lessD1 mod_type_class.to_nat_from_nat_id)
    have [transfer_rule]: "Mod_Type_Connect.HMA_I (a+1) (?b' + 1)" 
      unfolding Mod_Type_Connect.HMA_I_def
      unfolding from_nat_suc[symmetric] using to_nat_from_nat_id[OF Suc_b_less_CARD] by auto      
    have aa'1: "a = to_nat ?a'" using aa' by (simp add: Mod_Type_Connect.HMA_I_def)
    have ab'1: "a = to_nat ?b'" using ab' by (simp add: Mod_Type_Connect.HMA_I_def)
    have "Suc (to_nat ?a') < nrows y" using a1 dim_row_CARD
      by (simp add: mod_type_class.to_nat_from_nat_id nrows_def)
    moreover have "Suc (to_nat ?b') < ncols y" using a2 dim_col_CARD
      by (simp add: mod_type_class.to_nat_from_nat_id ncols_def)
    ultimately have SNF': "y $h ?a' $h ?b' dvd y $h (?a' + 1) $h (?b' + 1)" 
      using SNF ab'1 aa'1 by auto    
     have "index_hma y ?a' ?b' = x $$ (a, a)" by (transfer, simp)
     moreover have "index_hma y (?a'+1) (?b'+1) = x $$ (a+1, a+1)" by (transfer, simp)
     ultimately show ?thesis using SNF' unfolding index_hma_def by auto
  qed
  ultimately show ?case unfolding Smith_normal_form_mat_def Smith_normal_form_def
    using rel_xy by (auto) (transfer', auto)+
qed



lemma HMA_admits_SNF [transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'n::{mod_type} ^ 'n::{mod_type} \<Rightarrow> _) ===> (=)) 
  admits_SNF_JNF admits_SNF_HA"
proof (intro rel_funI, goal_cases)
  case (1 x y)
  note [transfer_rule] = this
  hence id: "dim_row x = CARD('n)" by (auto simp: Mod_Type_Connect.HMA_M_def)
  then show ?case unfolding admits_SNF_JNF_def admits_SNF_HA_def 
    by (transfer, auto, metis "1" Mod_Type_Connect.dim_col_transfer_rule)
qed  
end



(*If the following result holds, then I will get the result.
  
  But the theorem is false, since the assumption fixes the type 'n (within the proof is not 
  arbitrary any more). We cannot quantify over type variables in Isabelle/HOL.*)

(*
lemma diagonal_admits_SNF_imp_bezout_ring_JNF3:
  assumes admits_SNF: "\<forall>A. (A::'a mat) \<in> carrier_mat (CARD('n)) (CARD('n)) \<and> isDiagonal_mat A 
\<longrightarrow> (\<exists>P Q. P \<in> carrier_mat (dim_row A) (dim_row A) 
  \<and> Q \<in> carrier_mat (dim_row A) (dim_row A) \<and> invertible_mat P \<and> invertible_mat Q 
  \<and> Smith_normal_form_mat (P*A*Q))"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)" 
  apply (rule diagonal_admits_SNF_imp_bezout_ring_JNF, auto)
*)


text\<open>Here we have a problem when trying to apply local type definitions\<close>
(*
Once the assumption is translated to JNF, we get that it holds for all matrices with 
CARD('n) rows and CARD('n) columns. That is, we do not have the result for any matrix, just 
for matrices of such dimensions (within the proof, the type 'n is not arbitrary, is fixed).
*)
lemma diagonal_admits_SNF_imp_bezout_ring:
  assumes admits_SNF: "\<forall>A::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}. isDiagonal A 
    \<longrightarrow> (\<exists>P Q. invertible (P::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}) 
        \<and> invertible (Q::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}) 
        \<and> Smith_normal_form (P**A**Q))"
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class)"
proof (rule diagonal_admits_SNF_imp_bezout_ring_JNF, auto)
  fix A::"'a mat" and n 
    assume A: "A \<in> carrier_mat n n" and diag_A: "isDiagonal_mat A"           
  have a: "\<forall>A::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type}. admits_SNF_HA A" 
    using admits_SNF unfolding admits_SNF_HA_def .
  have JNF: "\<forall>(A::'a mat)\<in> carrier_mat CARD('n) CARD('n). admits_SNF_JNF A" 
  (*We can get this result, but this does not imply that it holds for any n \<times> n matrix, just 
    for the concrete case that n = CARD('n). Within this proof, we cannot apply local type 
    definitions, since the 'n is not an schematic variable any more, it is fixed.*)
  proof
    fix A::"'a mat" 
    assume A: "A \<in> carrier_mat CARD('n) CARD('n)"
    let ?B = "(Mod_Type_Connect.to_hma\<^sub>m  A::'a::comm_ring_1^'n::{mod_type}^'n::{mod_type})"
    have [transfer_rule]: "Mod_Type_Connect.HMA_M A ?B"
      using A unfolding Mod_Type_Connect.HMA_M_def by auto
    have b: "admits_SNF_HA ?B" using a by auto
    show "admits_SNF_JNF A" using b by transfer
  qed 
  (*Here we cannot apply local type definitions (either cancel_card_constraint or 
  cancel_type_definition) to thm JNF*)
  thus "\<exists>P. P \<in> carrier_mat n n \<and>
             (\<exists>Q. Q \<in> carrier_mat n n \<and> invertible_mat P 
        \<and> invertible_mat Q \<and> Smith_normal_form_mat (P * A * Q))"
    using JNF A diag_A unfolding admits_SNF_JNF_def unfolding square_mat.simps oops


text\<open>This means that the @{text "\<Longrightarrow>"}  implication cannot be proven in HA, since we cannot quantify
over type variables in Isabelle/HOL. We then prove both implications in JNF.\<close>


subsection \<open>Transfering the @{text "\<Longleftarrow>"} implication from HA to JNF using transfer rules 
  and local type definitions\<close>

(*
  I need to transfer the theorem bezout_ring_imp_diagonal_admits_SNF (stated in HA) to JNF.
  The first necessary step is to prove transfer rules to connect matrices in HA (when the type
  of the indexes must be mod_type). The original connection HMA_Connect presented in the 
  Perron--Frobenius development just connects matrices of type 'a^'b::finite^'c::finite with 
  the corresponding ones in JNF, but I need to transfer theorems with matrices of type:
  'a^'b::mod_type^'c::mod_type.

  The file that allows this bridge is Mod_Type_Connect.  

  Once that step is carried out, I would have to transfer the result by means of the lifting
  and transfer package and then apply local type definitions to get rid of the type (that is,
  to change CARD('n) by an arbitrary n).

  The usual approach consists of applying lifting and transfer to the theorem, and then we
  obtain a fact like 
        
          A \<in> carrier_mat (CARD('n::mod_type)) (CARD('n::mod_type))

  When trying to apply local type definitions (to substitute CARD('n::mod_type) by n), then
  I would have to apply interalize_sort and then proving the restriction class.mod_type (together
  with the operations associated to that class). Since the mod_type class already introduced
  several type restrictions (times, neg_numeral_well_order), operations (+,-) and constants (1,0),
  this means that we have to proceed using dictionary construction. We would have to define
  a mod_type with explicit operations, to get 'a only of type 'a::type.
  
  definition "mod_type_with n (tms::'a\<Rightarrow>'a\<Rightarrow>'a) mns pls zr umns (one'::'a)  
        (less_eq'::'a\<Rightarrow>'a\<Rightarrow>bool) (less'::'a\<Rightarrow>'a\<Rightarrow>bool) (Rep_op::'a\<Rightarrow>int) (Abs_op::int\<Rightarrow>'a)
      \<equiv> (type_definition Rep_op Abs_op {0..<n} \<and>  1 < n
      \<and> (zr = Abs_op 0)
      \<and> (one' = Abs_op 1)
      \<and> (\<forall>x y. pls x y = Abs_op (((Rep_op x) + (Rep_op y)) mod (n)))
      \<and> (\<forall>x y. tms x y = Abs_op (((Rep_op x) * (Rep_op y)) mod (n)))
      \<and> (\<forall>x y. mns x y = Abs_op (((Rep_op x) - (Rep_op y)) mod (n)))
      \<and> (\<forall>x. umns x = Abs_op ((- (Rep_op x)) mod (n)))
      \<and> (\<forall>x y. less' x y \<longrightarrow> (Rep_op x) < (Rep_op y))
      \<and> class.neg_numeral mns pls zr umns
      \<and> class.wellorder less_eq' less')"

  Once this is completed, I would have to connect mod_type and mod_type_with, 
  prove new transfer rules and so on. This is the usual approach and has been successfully applied,
  for instance, by Fabian Immler to transform a (type based) library of linear algebra into another
  one with explicit carriers.

  Fortunately, in this case there is a shortcut: we can use the type 'a mod_ring from the
  Berlekamp--Zassenhaus development to express the lemma in HA 
  (thm bezout_ring_imp_diagonal_admits_SNF) using that type (the type 'a mod_ring is an instance
  of the mod_type class, and then is a particular case).

  This means that any lemma that has a matrix of type 'a^'b::mod_type^'c^'mod_type can be expressed
  as 'a^'b mod_ring^'c mod_ring, where 'b and 'c must satisfy the nontriv restriction 
  (they must have more than one element).

  This is done in the file Finite_Field_Mod_Type_Connection, which shows that 'a mod_ring is an
  instance of the mod_type class.

  This type 'a mod_ring has a very useful property: CARD('b mod_ring) = CARD('b)
  This means that it is very easy to apply local type definitions. The problematic fact
  would then be transformed to:
  
      A \<in> carrier_mat (CARD('n::nontriv)) (CARD('n::nontriv)). 

  It is very easy to apply local type definitions to this fact, since it is very easy to get rid
  of the nontriv restriction (on the contrary, the mod_type restriction was quite hard).

*)


(*
  In our concrete case: we write the theorem in terms of the mod_ring type thanks to 
  the file Finite_Field_Mod_Type_Connection.

  With this type 'n::nontriv mod_ring I can easily apply local type definitions, since we
  will get CARD(?'n::nontriv).
*)

lemma bezout_ring_imp_diagonal_admits_SNF_mod_ring:
  assumes of: "OFCLASS('a::comm_ring_1, bezout_ring_class)"
  shows "\<forall>A::'a^'n::nontriv mod_ring^'n::nontriv mod_ring. isDiagonal A 
    \<longrightarrow> (\<exists>P Q. 
        invertible (P::'a^'n::nontriv mod_ring^'n::nontriv mod_ring) \<and> 
        invertible (Q::'a^'n::nontriv mod_ring^'n::nontriv mod_ring) \<and> 
        Smith_normal_form (P**A**Q))" 
  using bezout_ring_imp_diagonal_admits_SNF[OF assms] by auto

lemma bezout_ring_imp_diagonal_admits_SNF_mod_ring_admits: 
  assumes of: "class.bezout_ring (*) (1::'a::comm_ring_1) (+) 0 (-) uminus" (*It is equivalent to the statement based on OFCLASS*)
  shows "\<forall>A::'a^'n::nontriv mod_ring^'n::nontriv mod_ring. admits_SNF_HA A"
  using bezout_ring_imp_diagonal_admits_SNF
        [OF Rings2.class.Rings2.bezout_ring.of_class.intro[OF of]] 
  unfolding admits_SNF_HA_def by auto

text\<open>I start here to apply local type definitions\<close>

context
  fixes p::nat
  assumes local_typedef: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<p :: int}"
  and p: "p>1"
begin

lemma type_to_set:
  shows "class.nontriv TYPE('b)" (is ?a) and "p=CARD('b)" (is ?b)
proof -
  from local_typedef obtain Rep::"('b \<Rightarrow> int)" and Abs 
    where t: "type_definition Rep Abs {0..<p :: int}" by auto
  have "card (UNIV :: 'b set) = card {0..<p}" using t type_definition.card by fastforce
  also have "... = p" by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using p by auto
qed


text\<open>I transfer the lemma from HA to JNF, substituting @{text "CARD('n)"} by $p$. 
  I apply @{text "internalize-sort"} to @{text "'n"} and get rid of 
  the @{text "nontriv"} restriction.\<close>

lemma bezout_ring_imp_diagonal_admits_SNF_mod_ring_admits_aux:
  assumes "class.bezout_ring (*) (1::'a::comm_ring_1) (+) 0 (-) uminus"
  shows "Ball {A::'a::comm_ring_1 mat. A \<in> carrier_mat p p} admits_SNF_JNF"
  using bezout_ring_imp_diagonal_admits_SNF_mod_ring_admits[untransferred, unfolded CARD_mod_ring, 
      internalize_sort "'n::nontriv", where ?'a='b]
  unfolding type_to_set(2)[symmetric] using type_to_set(1) assms by auto
end

text\<open>The @{text "\<Longleftarrow>"} implication in JNF\<close>

text\<open>Since @{text "nontriv"} imposes the type to have more than one element, 
  the cases $n=0$ (@{text "A \<in> carrier_mat 0 0"}) and $n = 1$ (@{text "A \<in> carrier_mat 1 1"})
  must be treated separately.\<close>

lemma bezout_ring_imp_diagonal_admits_SNF_mod_ring_admits_aux2:
  assumes of: "class.bezout_ring (*) (1::'a::comm_ring_1) (+) 0 (-) uminus"
  shows "\<forall>(A::'a mat)\<in>carrier_mat n n. admits_SNF_JNF A"
proof (cases "n = 0")
  case True  
  show ?thesis
    by (rule, unfold True admits_SNF_JNF_def isDiagonal_mat_def invertible_mat_def 
        Smith_normal_form_mat_def carrier_mat_def inverts_mat_def, fastforce)
next
  case False note not0 = False
  show ?thesis
  proof (cases "n=1") 
  case True
  show ?thesis 
    by (rule, unfold True admits_SNF_JNF_def isDiagonal_mat_def invertible_mat_def 
        Smith_normal_form_mat_def carrier_mat_def inverts_mat_def, auto)
       (metis dvd_1_left index_one_mat(2) index_one_mat(3) less_Suc0 nat_dvd_not_less 
        right_mult_one_mat' zero_less_Suc)
  next
    case False
    then have "n>1" using not0 by auto
    then show ?thesis (*Here I apply the local type definition rule, to cancel the type*)
      using bezout_ring_imp_diagonal_admits_SNF_mod_ring_admits_aux[cancel_type_definition, of n] of 
      by auto
  qed
qed
    
text \<open>Alternative statements\<close>
  
lemma bezout_ring_imp_diagonal_admits_SNF_JNF:
  assumes of: "class.bezout_ring (*) (1::'a::comm_ring_1) (+) 0 (-) uminus"
  shows "\<forall>A::'a mat. admits_SNF_JNF A"
proof 
  fix A::"'a mat"
  have "A\<in> carrier_mat (dim_row A) (dim_col A)" unfolding carrier_mat_def by auto
  thus "admits_SNF_JNF A" 
    using bezout_ring_imp_diagonal_admits_SNF_mod_ring_admits_aux2[OF of]
    by (metis admits_SNF_JNF_def square_mat.elims(2))
qed


lemma admits_SNF_JNF_alt_def:
  "(\<forall>A::'a::comm_ring_1 mat. admits_SNF_JNF A) 
  = (\<forall>A n. (A::'a mat) \<in> carrier_mat n n \<and> isDiagonal_mat A
  \<longrightarrow> (\<exists>P Q. P \<in> carrier_mat n n \<and> Q \<in> carrier_mat n n \<and> invertible_mat P \<and> invertible_mat Q 
      \<and> Smith_normal_form_mat (P*A*Q)))" (is "?a = ?b")
  by (auto simp add: admits_SNF_JNF_def, metis carrier_matD(1) carrier_matD(2), blast)


subsection \<open>Final theorem in JNF\<close>
text \<open>Final theorem using @{text "class.bezout_ring"}\<close>

theorem diagonal_admits_SNF_iff_bezout_ring:
  shows "class.bezout_ring (*) (1::'a::comm_ring_1) (+) 0 (-) uminus 
  \<longleftrightarrow> (\<forall>A::'a mat. admits_SNF_JNF A)" (is "?a \<longleftrightarrow> ?b")
proof 
  assume ?a
  thus ?b using bezout_ring_imp_diagonal_admits_SNF_JNF by auto
next
  assume b: ?b
  have rw: "\<forall>A n. (A::'a mat) \<in> carrier_mat n n \<and> isDiagonal_mat A \<longrightarrow>
          (\<exists>P Q. P \<in> carrier_mat n n \<and> Q \<in> carrier_mat n n \<and> invertible_mat P 
          \<and> invertible_mat Q \<and> Smith_normal_form_mat (P * A * Q))"
    using admits_SNF_JNF_alt_def b by auto  
  show ?a
    using diagonal_admits_SNF_imp_bezout_ring_JNF[OF rw] 
    using OFCLASS_bezout_ring_imp_class_bezout_ring[where ?'a='a]
    by auto
qed

text \<open>Final theorem using @{text "OFCLASS"}\<close>

theorem diagonal_admits_SNF_iff_bezout_ring':
  shows "OFCLASS('a::comm_ring_1, bezout_ring_class) \<equiv> (\<And>A::'a mat. admits_SNF_JNF A)"
proof 
  fix A::"'a mat"
  assume a: "OFCLASS('a, bezout_ring_class)"  
  show "admits_SNF_JNF A"
    using OFCLASS_bezout_ring_imp_class_bezout_ring[OF a] diagonal_admits_SNF_iff_bezout_ring
    by auto
next
  assume "(\<And>A::'a mat. admits_SNF_JNF A)"  
  hence *: "class.bezout_ring (*) (1::'a) (+) 0 (-) uminus" 
    using diagonal_admits_SNF_iff_bezout_ring by auto
  show "OFCLASS('a, bezout_ring_class)"
    by (rule Rings2.class.Rings2.bezout_ring.of_class.intro, rule *)
qed

end
