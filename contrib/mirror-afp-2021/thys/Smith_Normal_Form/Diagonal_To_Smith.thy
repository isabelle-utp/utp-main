(*
    Author:      Jose Divasón
    Email:       jose.divason@unirioja.es           
*)

section \<open>Algorithm to transform a diagonal matrix into its Smith normal form\<close>

theory Diagonal_To_Smith
  imports Hermite.Hermite
  "HOL-Types_To_Sets.Types_To_Sets"
  Smith_Normal_Form
begin


(*Move this theorem:*)
lemma invertible_mat_1: "invertible (mat (1::'a::comm_ring_1))"
  unfolding invertible_iff_is_unit by simp

subsection \<open>Implementation of the algorithm\<close>

type_synonym 'a bezout = "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"

hide_const Countable.from_nat
hide_const Countable.to_nat

text \<open>The algorithm is based on the one presented by Bradley in his article entitled 
  ``Algorithms for Hermite and Smith normal matrices and linear diophantine equations''. 
  Some improvements have been introduced to get a general version for any matrix (including
  non-square and singular ones).\<close>

text \<open>I also introduced another improvement: the element in the position j does not need 
to be checked each time, since the element $A_{ii}$ will already divide $A_{jj}$ (where $j \le k$). 
The gcd will be placed in $A_{ii}$.\<close>


(*This version is a valid implementation and permits the formalization, 
  but it would not be executable due to the abstraction*)

(*
primrec diagonal_to_Smith_i :: "nat list \<Rightarrow> 'a:: {gcd,divide}^'n::mod_type^'n::mod_type \<Rightarrow> 'n::mod_type \<Rightarrow> 'a^'n::mod_type^'n::mod_type" 
 where
"diagonal_to_Smith_i [] A i  = A" |
"diagonal_to_Smith_i (j#xs) A i  = (
  if A $ i $ i dvd A $ (from_nat j) $ (from_nat j) then diagonal_to_Smith_i xs A i  (*If it divides, then we proceed.*)
  else 
      let c = gcd (A$i$i) (A$(from_nat j)$(from_nat j));
          A' = (\<chi> a b. if a = i \<and> b = i then c else 
               if a = from_nat j \<and> b = from_nat j 
               then A$ i $ i * (A $ (from_nat j) $ (from_nat j) div c) else A $ a $ b)
      in diagonal_to_Smith_i xs A' i (*We do the step and proceed*)
  )
  "
*)

text \<open>This function transforms the element $A_{jj}$ in order to be divisible by $A_{ii}$
(and it changes $A_{ii}$ as well).

The use of @{text "from_nat"} and @{text "from_nat"} is mandatory since the same 
index $i$ cannot be used for both rows
and columns at the same time, since they could have different type, concretely, 
when the matrix is rectangular.\<close>

text\<open>The following definition is valid, but since execution requires the trick of converting
all operations in terms of rows, then we would be recalculating the B\'ezout coefficients each time.\<close>

(*
definition "diagonal_step A i j bezout = (let
              (p, q, u, v, d) = bezout (A $ from_nat i $ from_nat i) (A $ (from_nat j) $ (from_nat j)) in 
              (\<chi> a b. if a = from_nat i \<and> b = from_nat i then d else 
               if a = from_nat j \<and> b = from_nat j 
               then  v * (A $ (from_nat j) $ (from_nat j)) else A $ a $ b))"
*)

text\<open>Thus, the definition is parameterized by the necessary elements instead of the operation, 
     to avoid recalculations.\<close>

definition "diagonal_step A i j d v =               
              (\<chi> a b. if a = from_nat i \<and> b = from_nat i then d else 
               if a = from_nat j \<and> b = from_nat j 
               then  v * (A $ (from_nat j) $ (from_nat j)) else A $ a $ b)"


fun diagonal_to_Smith_i :: 
"nat list \<Rightarrow> 'a::{bezout_ring}^'cols::mod_type^'rows::mod_type \<Rightarrow> nat \<Rightarrow> ('a bezout) 
  \<Rightarrow> 'a^'cols::mod_type^'rows::mod_type" 
 where
"diagonal_to_Smith_i [] A i bezout = A" |
"diagonal_to_Smith_i (j#xs) A i bezout = (
  if A $ (from_nat i) $ (from_nat i) dvd A $ (from_nat j) $ (from_nat j) 
      then diagonal_to_Smith_i xs A i bezout
  else let (p, q, u, v, d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j); 
          A' = diagonal_step A i j d v
      in diagonal_to_Smith_i xs A' i bezout
  )
  "

definition "Diagonal_to_Smith_row_i A i bezout 
  = diagonal_to_Smith_i [i+1..<min (nrows A) (ncols A)] A i bezout"

fun diagonal_to_Smith_aux :: " 'a::{bezout_ring}^'cols::mod_type^'rows::mod_type 
  \<Rightarrow> nat list \<Rightarrow> ('a bezout) \<Rightarrow>  'a^'cols::mod_type^'rows::mod_type"
  where
  "diagonal_to_Smith_aux A [] bezout = A" |
  "diagonal_to_Smith_aux A (i#xs) bezout 
          = diagonal_to_Smith_aux (Diagonal_to_Smith_row_i A i bezout) xs bezout"

text\<open>The minimum arises to include the case of non-square matrices (we do not 
  demand the input diagonal matrix to be square, just have zeros in non-diagonal entries).

  This iteration does not need to be performed until the last element of the diagonal, 
  because in the second-to-last step the matrix will be already in Smith normal form.\<close>

definition "diagonal_to_Smith A bezout 
  = diagonal_to_Smith_aux A [0..<min (nrows A) (ncols A) - 1] bezout"

subsection\<open>Code equations to get an executable version\<close>

definition diagonal_step_row 
  where "diagonal_step_row A i j c v a = vec_lambda (%b. if a = from_nat i \<and> b = from_nat i then c else 
               if a = from_nat j \<and> b = from_nat j 
               then v * (A $ (from_nat j) $ (from_nat j)) else A $ a $ b)"

lemma diagonal_step_code [code abstract]:
  "vec_nth (diagonal_step_row A i j c v a) = (%b. if a = from_nat i \<and> b = from_nat i then c else 
               if a = from_nat j \<and> b = from_nat j 
               then v * (A $ (from_nat j) $ (from_nat j)) else A $ a $ b)"
  unfolding diagonal_step_row_def by auto 

lemma diagonal_step_code_nth [code abstract]: "vec_nth (diagonal_step A i j c v) 
  = diagonal_step_row A i j c v"
  unfolding diagonal_step_def unfolding diagonal_step_row_def[abs_def]
  by auto

text\<open>Code equation to avoid recalculations when computing the Bezout coefficients. \<close>
lemma euclid_ext2_code[code]:
 "euclid_ext2 a b = (let ((p,q),d) = euclid_ext a b in (p,q, - b div d, a div d, d))"
  unfolding euclid_ext2_def split_beta Let_def 
  by auto

subsection\<open>Examples of execution\<close>

value "let A= list_of_list_to_matrix [[12,0,0::int],[0,6,0::int],[0,0,2::int]]::int^3^3 
  in matrix_to_list_of_list (diagonal_to_Smith A euclid_ext2)"

text\<open>Example obtained from:
\url{https://math.stackexchange.com/questions/77063/how-do-i-get-this-matrix-in-smith-normal-form-and-is-smith-normal-form-unique}
\<close>

value "let A= list_of_list_to_matrix 
    [
    [[:-3,1:],0,0,0],
    [0,[:1,1:],0,0],
    [0,0,[:1,1:],0],
    [0,0,0,[:1,1:]]]::rat poly^4^4 
  in matrix_to_list_of_list (diagonal_to_Smith A euclid_ext2)"


text\<open>Polynomial matrix\<close>
value "let A = list_of_list_to_matrix 
      [
        [[:-3,1:],0,0,0],
        [0,[:1,1:],0,0],
        [0,0,[:1,1:],0],
        [0,0,0,[:1,1:]],
        [0,0,0,0]]::rat poly^4^5 
  in matrix_to_list_of_list (diagonal_to_Smith A euclid_ext2)"


subsection\<open>Soundness of the algorithm\<close>

lemma nrows_diagonal_step[simp]: "nrows (diagonal_step A i j c v) = nrows A"
  by (simp add: nrows_def)

lemma ncols_diagonal_step[simp]: "ncols (diagonal_step A i j c v) = ncols A"
  by (simp add: ncols_def)


context
  fixes bezout::"'a::{bezout_ring} \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"
  assumes ib: "is_bezout_ext bezout"
begin

lemma split_beta_bezout: "bezout a b = 
  (fst(bezout a b),
  fst (snd (bezout a b)),
  fst (snd(snd (bezout a b))),
  fst (snd(snd(snd (bezout a b)))),
  snd (snd(snd(snd (bezout a b)))))" unfolding split_beta by (auto simp add: split_beta)

text\<open>The following lemma shows that @{text "diagonal_to_Smith_i"} preserves the previous element. 
  We use the assumption @{text "to_nat a = to_nat b"} in order to ensure that we are treating with 
  a diagonal entry. Since the matrix could be rectangular, the types of a and b can be different, 
  and thus we cannot write either @{text "a = b"} or @{text "A $ a $ b"}.\<close>

lemma diagonal_to_Smith_i_preserves_previous_diagonal:
  fixes A::"'a:: {bezout_ring}^'b::mod_type^'c::mod_type"
  assumes i_min: "i < min (nrows A) (ncols A)" 
  and "to_nat a \<notin> set xs" and "to_nat a = to_nat b"
  and "to_nat a \<noteq> i"
  and elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<min (nrows A) (ncols A)"
  shows "(diagonal_to_Smith_i xs A i bezout) $ a $ b = A $ a $ b" 
  using assms
proof (induct xs A i bezout rule: diagonal_to_Smith_i.induct)
  case (1 A i bezout)
  then show ?case by auto
next
  case (2 j xs A i bezout)   
  let ?Aii = "A $ from_nat i $ from_nat i"
  let ?Ajj = "A $ from_nat j $ from_nat j"
  let ?p="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?A'="diagonal_step A i j ?d ?v" 
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  show ?case
  proof (cases "?Aii dvd ?Ajj")
    case True
    then show ?thesis
      using "2.hyps" "2.prems" by auto
  next
    case False
    note i_min = 2(3)
    note hyp = 2(2)
    note i_notin = 2(4)
    note a_eq_b = "2.prems"(3)
    note elements_xs = 2(7)
    note a_not_i = 2(6)    
    have a_not_j: "a \<noteq> from_nat j"
      by (metis elements_xs i_notin list.set_intros(1) min_less_iff_conj nrows_def to_nat_from_nat_id)
    have "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs ?A' i bezout"
      using False by (auto simp add: split_beta)
    also have "... $ a $ b = ?A' $ a $ b" 
      by (rule hyp[OF False], insert i_notin i_min a_eq_b a_not_i pquvd elements_xs, auto)
    also have "... = A $ a $ b"
      unfolding diagonal_step_def
      using a_not_j a_not_i
      by (smt i_min min.strict_boundedE nrows_def to_nat_from_nat_id vec_lambda_beta)
    finally show ?thesis .
  qed
qed

lemma diagonal_step_dvd1[simp]:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type" and j i
  defines "v==case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  and "d==case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
 shows "diagonal_step A i j d v $ from_nat i $ from_nat i dvd A $ from_nat i $ from_nat i"
  using ib unfolding is_bezout_ext_def diagonal_step_def v_def d_def 
  by (auto simp add: split_beta)

lemma diagonal_step_dvd2[simp]:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type" and j i
  defines "v==case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  and "d==case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
 shows "diagonal_step A i j d v $ from_nat i $ from_nat i dvd A $ from_nat j $ from_nat j"
  using ib unfolding is_bezout_ext_def diagonal_step_def v_def d_def 
  by (auto simp add: split_beta)

end

text\<open>Once the step is carried out, the new element ${A'}_{ii}$ will divide the element $A_{ii}$\<close>

lemma diagonal_to_Smith_i_dvd_ii:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout"
  shows "diagonal_to_Smith_i xs A i bezout $ from_nat i $ from_nat i dvd A $ from_nat i $ from_nat i"
  using ib
proof (induct xs A i bezout rule: diagonal_to_Smith_i.induct)
  case (1 A i bezout)
  then show ?case by auto
next
  case (2 j xs A i bezout)   
  let ?Aii = "A $ from_nat i $ from_nat i"
  let ?Ajj = "A $ from_nat j $ from_nat j"
  let ?p="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?A'="diagonal_step A i j ?d ?v" 
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  note ib = "2.prems"(1) 
  show ?case
  proof (cases "?Aii dvd ?Ajj")
    case True
    then show ?thesis 
      using "2.hyps"(1) "2.prems" by auto
  next
    case False
    note hyp = "2.hyps"(2)    
    have "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs ?A' i bezout" 
      using False by (auto simp add: split_beta)
    also have "... $ from_nat i $ from_nat i dvd ?A' $ from_nat i $ from_nat i"
      by (rule hyp[OF False], insert pquvd ib, auto)
    also have "... dvd A $ from_nat i $ from_nat i" 
      unfolding diagonal_step_def using ib unfolding is_bezout_ext_def
      by (auto simp add: split_beta) 
    finally show ?thesis .
  qed
qed

text\<open>Once the step is carried out, the new element ${A'}_{ii}$ 
  divides the rest of elements of the diagonal. This proof requires commutativity (already
  included in the type restriction @{text "bezout_ring"}).\<close>

lemma diagonal_to_Smith_i_dvd_jj:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout"
  and i_min: "i < min (nrows A) (ncols A)" 
  and elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<min (nrows A) (ncols A)"
  and "to_nat a \<in> set xs"
  and "to_nat a = to_nat b"
  and "to_nat a \<noteq> i"
  and "distinct xs"
shows "(diagonal_to_Smith_i xs A i bezout) $ (from_nat i) $ (from_nat i) 
       dvd (diagonal_to_Smith_i xs A i bezout) $ a $ b"   
  using assms
proof (induct xs A i bezout rule: diagonal_to_Smith_i.induct)
  case (1 A i)
  then show ?case by auto
next
  case (2 j xs A i bezout)     
  let ?Aii = "A $ from_nat i $ from_nat i"
  let ?Ajj = "A $ from_nat j $ from_nat j"
  let ?p="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?A'="diagonal_step A i j ?d ?v" 
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  note ib = "2.prems"(1) 
  note to_nat_a_not_i = 2(8)
  note i_min = 2(4)  
  note elements_xs = "2.prems"(3)
  note a_eq_b = "2.prems"(5)
  note a_in_j_xs = 2(6)
  note distinct = 2(9)
  show ?case
  proof (cases "?Aii dvd ?Ajj")    
    case True note Aii_dvd_Ajj = True
    show ?thesis 
    proof (cases "to_nat a = j")
      case True
      have a: "a = (from_nat j::'c)" using True by auto
      have b: "b = (from_nat j::'b)"
        using True a_eq_b by auto
      have "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs A i bezout" 
        using Aii_dvd_Ajj by auto
      also have "... $ from_nat j $ from_nat j = A $ from_nat j $ from_nat j" 
      proof (rule diagonal_to_Smith_i_preserves_previous_diagonal[OF ib i_min])          
        show "to_nat (from_nat j::'c) \<notin> set xs" using True a_in_j_xs distinct by auto
        show "to_nat (from_nat j::'c) = to_nat (from_nat j::'b)"
          by (metis True a_eq_b from_nat_to_nat_id)
        show "to_nat (from_nat j::'c) \<noteq> i"
          using True to_nat_a_not_i by auto
        show "\<forall>x. x \<in> set xs \<longrightarrow> x < min (nrows A) (ncols A)" using elements_xs by auto
      qed
      finally have "diagonal_to_Smith_i (j # xs) A i bezout $ from_nat j $ from_nat j 
        = A $ from_nat j $ from_nat j " .
      hence "diagonal_to_Smith_i (j # xs) A i bezout $ a $ b = ?Ajj" unfolding a b .
      moreover have "diagonal_to_Smith_i (j # xs) A i bezout $ from_nat i $ from_nat i dvd ?Aii" 
        by (rule diagonal_to_Smith_i_dvd_ii[OF ib])
      ultimately show ?thesis using Aii_dvd_Ajj dvd_trans by auto
    next
      case False
      have a_in_xs: "to_nat a \<in> set xs" using False using "2.prems"(4) by auto
      have "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs A i bezout" 
        using True by auto
      also have "...  $ (from_nat i) $ (from_nat i) dvd diagonal_to_Smith_i xs A i bezout $ a $ b" 
        by (rule "2.hyps"(1)[OF True ib i_min _ a_in_xs a_eq_b to_nat_a_not_i]) 
           (insert elements_xs distinct, auto)
      finally show ?thesis .
    qed
  next
    case False note Aii_not_dvd_Ajj = False    
    show ?thesis
    proof (cases "to_nat a \<in> set xs")
      case True note a_in_xs = True    
      have "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs ?A' i bezout" 
        using False by (auto simp add: split_beta)
      also have "... $ from_nat i $ from_nat i dvd diagonal_to_Smith_i xs ?A' i bezout $ a $ b"
        by (rule "2.hyps"(2)[OF False _ _ _ _ _ _ _ _ _ a_in_xs a_eq_b to_nat_a_not_i ])
           (insert elements_xs distinct i_min ib pquvd, auto simp add: nrows_def ncols_def)    
      finally show ?thesis .    
    next
      case False
      have to_nat_a_eq_j: "to_nat a = j"
        using False a_in_j_xs by auto
      have a: "a = (from_nat j::'c)" using to_nat_a_eq_j by auto
      have b: "b = (from_nat j::'b)" using to_nat_a_eq_j a_eq_b by auto
      have d_eq: "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs ?A' i bezout" 
        using Aii_not_dvd_Ajj by (simp add: split_beta)
      also have "... $ a $ b = ?A' $ a $ b"
        by (rule diagonal_to_Smith_i_preserves_previous_diagonal[OF ib _ False a_eq_b to_nat_a_not_i])
           (insert i_min elements_xs ib, auto)
      finally have "diagonal_to_Smith_i (j # xs) A i bezout $ a $ b = ?A' $ a $ b" .
      moreover have "diagonal_to_Smith_i (j # xs) A i bezout $ from_nat i $ from_nat i 
        dvd ?A' $ from_nat i $ from_nat i" 
        using d_eq diagonal_to_Smith_i_dvd_ii[OF ib] by simp
      moreover have "?A' $ from_nat i $ from_nat i dvd ?A' $ from_nat j $ from_nat j" 
        unfolding diagonal_step_def using ib unfolding is_bezout_ext_def split_beta
        by (auto, meson dvd_mult)+      
      ultimately show ?thesis using dvd_trans a b by auto        
  qed
qed
qed


text\<open>The step preserves everything that is not in the diagonal\<close>

lemma diagonal_to_Smith_i_preserves_previous:
  fixes A::"'a:: {bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout"
    and i_min: "i < min (nrows A) (ncols A)"
  and a_not_b: "to_nat a \<noteq> to_nat b"
  and elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<min (nrows A) (ncols A)"
  shows "(diagonal_to_Smith_i xs A i bezout) $ a $ b = A $ a $ b" 
  using assms
proof (induct xs A i bezout rule: diagonal_to_Smith_i.induct)
case (1 A i)
  then show ?case by auto
next  
  case (2 j xs A i bezout)     
  let ?Aii = "A $ from_nat i $ from_nat i"
  let ?Ajj = "A $ from_nat j $ from_nat j"
  let ?p="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?A'="diagonal_step A i j ?d ?v" 
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  note ib = "2.prems"(1) 
  show ?case
  proof (cases "?Aii dvd ?Ajj")
    case True
    then show ?thesis 
      using "2.hyps"(1) "2.prems" by auto
  next
    case False
    note hyp = "2.hyps"(2)
    have a1: "a = from_nat i \<longrightarrow> b \<noteq> from_nat i" 
      by (metis "2.prems" a_not_b from_nat_not_eq min.strict_boundedE ncols_def nrows_def)
    have a2: "a = from_nat j \<longrightarrow> b \<noteq> from_nat j"       
      by (metis "2.prems" a_not_b list.set_intros(1) min_less_iff_conj 
          ncols_def nrows_def to_nat_from_nat_id)
    have "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs ?A' i bezout" 
      using False by (simp add: split_beta)
    also have "... $ a $ b = ?A' $ a $ b"
      by (rule hyp[OF False], insert "2.prems" ib pquvd, auto)
    also have "... = A $ a $ b" unfolding diagonal_step_def using a1 a2 by auto
    finally show ?thesis .
  qed
qed


lemma diagonal_step_preserves:
  fixes A::"'a::{times}^'b::mod_type^'c::mod_type"
  assumes ai: "a \<noteq> i" and aj: "a \<noteq> j" and a_min: "a < min (nrows A) (ncols A)" 
    and i_min: "i < min (nrows A) (ncols A)"
  and j_min: "j < min (nrows A) (ncols A)"
  shows "diagonal_step A i j d v $ from_nat a $ from_nat b = A $ from_nat a $ from_nat b"
proof -
  have 1: "(from_nat a::'c) \<noteq> from_nat i"
    by (metis a_min ai from_nat_eq_imp_eq i_min min.strict_boundedE nrows_def)
  have 2: "(from_nat a::'c) \<noteq> from_nat j"
    by (metis a_min aj from_nat_eq_imp_eq j_min min.strict_boundedE nrows_def)
  show ?thesis
    using 1 2 unfolding diagonal_step_def by auto
qed

context GCD_ring
begin

lemma gcd_greatest: 
  assumes "is_gcd gcd'" and "c dvd a" and "c dvd b" 
  shows "c dvd gcd' a b" 
  using assms is_gcd_def by blast

end


text\<open>This is a key lemma for the soundness of the algorithm.\<close>

lemma diagonal_to_Smith_i_dvd:
  fixes A::"'a:: {bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout"
  and i_min: "i < min (nrows A) (ncols A)"
  and elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<min (nrows A) (ncols A)"
  and "\<forall>a b. to_nat a\<in>insert i (set xs) \<and> to_nat a = to_nat b \<longrightarrow> 
      A $ (from_nat c) $ (from_nat c) dvd A $ a $ b"
  and "c \<notin> (set xs)" and c: "c<min (nrows A) (ncols A)"
  and "distinct xs"
  shows "A $ (from_nat c) $ (from_nat c) dvd 
  (diagonal_to_Smith_i xs A i bezout) $ (from_nat i) $ (from_nat i)" 
  using assms
proof (induct xs A i bezout rule: diagonal_to_Smith_i.induct)
  case (1 A i)
  then show ?case
    by (auto simp add: ncols_def nrows_def to_nat_from_nat_id)
next
  case (2 j xs A i bezout)
  let ?Aii = "A $ from_nat i $ from_nat i"
  let ?Ajj = "A $ from_nat j $ from_nat j"
  let ?p="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?A'="diagonal_step A i j ?d ?v" 
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  note ib = "2.prems"(1) 
  show ?case
  proof (cases "?Aii dvd ?Ajj")    
    case True note Aii_dvd_Ajj = True
    show ?thesis using True
      using "2.hyps" "2.prems" by force      
  next
    case False 
    let ?Acc = "A $ from_nat c $ from_nat c" 
    let ?D="diagonal_step A i j ?d ?v"
    note hyp = "2.hyps"(2)  
    note dvd_condition = "2.prems"(4)
    note a_eq_b = "2.hyps"
    have 1: "(from_nat c::'c) \<noteq> from_nat i"
      by (metis "2.prems" False c insert_iff list.set_intros(1) 
          min.strict_boundedE ncols_def nrows_def to_nat_from_nat_id)
    have 2: "(from_nat c::'c) \<noteq> from_nat j"
      by (metis  "2.prems" c insertI1 list.simps(15) min_less_iff_conj nrows_def 
          to_nat_from_nat_id)       
    have "?D $ from_nat c $ from_nat c = ?Acc"
      unfolding diagonal_step_def using 1 2 by auto
    have aux: "?D $ from_nat c $ from_nat c dvd ?D $ a $ b"
      if a_in_set: "to_nat a \<in> insert i (set xs)" and ab: "to_nat a = to_nat b" for a b      
    proof -
     have Acc_dvd_Aii: "?Acc dvd ?Aii"
       by (metis "2.prems"(2) "2.prems"(4) insert_iff min.strict_boundedE 
           ncols_def nrows_def to_nat_from_nat_id)
     moreover have Acc_dvd_Ajj: "?Acc dvd ?Ajj"
       by (metis "2.prems"(3) "2.prems"(4) insert_iff list.set_intros(1) 
           min_less_iff_conj ncols_def nrows_def to_nat_from_nat_id)
     ultimately have Acc_dvd_gcd: "?Acc dvd ?d"
       by (metis (mono_tags, lifting) ib is_gcd_def is_gcd_is_bezout_ext)
     show ?thesis 
      using 1 2 Acc_dvd_Ajj Acc_dvd_Aii Acc_dvd_gcd a_in_set ab dvd_condition 
      unfolding diagonal_step_def by auto     
  qed   
    have "?A' $ from_nat c $ from_nat c = A $ from_nat c $ from_nat c" 
      unfolding diagonal_step_def using 1 2 by auto
    moreover have "?A' $ from_nat c $ from_nat c 
      dvd diagonal_to_Smith_i xs ?A' i bezout $ from_nat i $ from_nat i"
      by (rule hyp[OF False _ _ _ _ _ _ ib]) 
         (insert nrows_def ncols_def "2.prems" "2.hyps" aux pquvd, auto)
    ultimately show ?thesis using False by (auto simp add: split_beta)
  qed
qed


lemma diagonal_to_Smith_i_dvd2:
  fixes A::"'a:: {bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout" 
  and i_min: "i < min (nrows A) (ncols A)"
  and elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<min (nrows A) (ncols A)"
  and dvd_condition: "\<forall>a b. to_nat a \<in> insert i (set xs) \<and> to_nat a = to_nat b \<longrightarrow> 
      A $ (from_nat c) $ (from_nat c) dvd A $ a $ b"
  and c_notin: "c \<notin> (set xs)" 
  and c: "c < min (nrows A) (ncols A)"
  and distinct: "distinct xs"
  and ab: "to_nat a = to_nat b" 
  and a_in: "to_nat a \<in> insert i (set xs)"
  shows "A $ (from_nat c) $ (from_nat c) dvd (diagonal_to_Smith_i xs A i bezout) $ a $ b" 
proof (cases "a = from_nat i")
  case True
  hence b: "b = from_nat i"
    by (metis ab from_nat_to_nat_id i_min min_less_iff_conj nrows_def to_nat_from_nat_id)
  show ?thesis by (unfold True b, rule diagonal_to_Smith_i_dvd, insert assms, auto)
next
  case False
  have ai: "to_nat a \<noteq> i" using False by auto
  hence bi: "to_nat b \<noteq> i" by (simp add: ab)
  have "A $ (from_nat c) $ (from_nat c) dvd (diagonal_to_Smith_i xs A i bezout) $ from_nat i $ from_nat i"
    by (rule diagonal_to_Smith_i_dvd, insert assms, auto)
  also have "... dvd (diagonal_to_Smith_i xs A i bezout) $ a $ b" 
    by (rule diagonal_to_Smith_i_dvd_jj, insert assms False ai bi, auto)
  finally show ?thesis .
qed


lemma diagonal_to_Smith_i_dvd2_k:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout" 
  and i_min: "i < min (nrows A) (ncols A)"
  and elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<k" and "k\<le>min (nrows A) (ncols A)"
  and dvd_condition: "\<forall>a b. to_nat a \<in> insert i (set xs) \<and> to_nat a = to_nat b \<longrightarrow> 
      A $ (from_nat c) $ (from_nat c) dvd A $ a $ b"
  and c_notin: "c \<notin> (set xs)" 
  and c: "c < min (nrows A) (ncols A)"
  and distinct: "distinct xs"
  and ab: "to_nat a = to_nat b" 
  and a_in: "to_nat a \<in> insert i (set xs)"
  shows "A $ (from_nat c) $ (from_nat c) dvd (diagonal_to_Smith_i xs A i bezout) $ a $ b" 
proof (cases "a = from_nat i")
  case True
  hence b: "b = from_nat i"
    by (metis ab from_nat_to_nat_id i_min min_less_iff_conj nrows_def to_nat_from_nat_id)
  show ?thesis by (unfold True b, rule diagonal_to_Smith_i_dvd, insert assms, auto)
next
  case False
  have ai: "to_nat a \<noteq> i" using False by auto
  hence bi: "to_nat b \<noteq> i" by (simp add: ab)
  have "A $ (from_nat c) $ (from_nat c) dvd (diagonal_to_Smith_i xs A i bezout) $ from_nat i $ from_nat i"
    by (rule diagonal_to_Smith_i_dvd, insert assms, auto)
  also have "... dvd (diagonal_to_Smith_i xs A i bezout) $ a $ b" 
    by (rule diagonal_to_Smith_i_dvd_jj, insert assms False ai bi, auto)
  finally show ?thesis .
qed



lemma diagonal_to_Smith_row_i_preserves_previous:
  fixes A::"'a:: {bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout"
  and i_min: "i < min (nrows A) (ncols A)"
  and a_not_b: "to_nat a \<noteq> to_nat b"  
  shows "Diagonal_to_Smith_row_i A i bezout $ a $ b = A $ a $ b" 
    unfolding Diagonal_to_Smith_row_i_def
    by (rule diagonal_to_Smith_i_preserves_previous, insert assms, auto)


lemma diagonal_to_Smith_row_i_preserves_previous_diagonal:
  fixes A::"'a:: {bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout"
  and i_min: "i < min (nrows A) (ncols A)"  
  and a_notin: "to_nat a \<notin> set [i + 1..<min (nrows A) (ncols A)]"
  and ab: "to_nat a = to_nat b"
  and ai: "to_nat a \<noteq> i" 
  shows "Diagonal_to_Smith_row_i A i bezout $ a $ b = A $ a $ b" 
  unfolding Diagonal_to_Smith_row_i_def
  by (rule diagonal_to_Smith_i_preserves_previous_diagonal[OF ib i_min a_notin ab ai], auto)

context
  fixes bezout::"'a::{bezout_ring} \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"
  assumes ib: "is_bezout_ext bezout"
begin

lemma diagonal_to_Smith_row_i_dvd_jj:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes "to_nat a \<in> {i..<min (nrows A) (ncols A)}"
  and "to_nat a = to_nat b"
  shows "(Diagonal_to_Smith_row_i A i bezout) $ (from_nat i) $ (from_nat i) 
          dvd (Diagonal_to_Smith_row_i A i bezout) $ a $ b"
proof (cases "to_nat a = i")
  case True
  then show ?thesis
    by (metis assms(2) dvd_refl from_nat_to_nat_id)
next
  case False
  show ?thesis 
    unfolding Diagonal_to_Smith_row_i_def 
    by (rule diagonal_to_Smith_i_dvd_jj, insert assms False ib, auto)
qed


lemma diagonal_to_Smith_row_i_dvd_ii:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  shows "Diagonal_to_Smith_row_i A i bezout $ from_nat i $ from_nat i dvd A $ from_nat i $ from_nat i"
  unfolding Diagonal_to_Smith_row_i_def
  by (rule diagonal_to_Smith_i_dvd_ii[OF ib])


lemma diagonal_to_Smith_row_i_dvd_jj':
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes a_in: "to_nat a \<in> {i..<min (nrows A) (ncols A)}"
  and ab: "to_nat a = to_nat b" 
  and ci: "c\<le>i"
  and dvd_condition: "\<forall>a b. to_nat a \<in> (set [i..<min (nrows A) (ncols A)]) \<and> to_nat a = to_nat b 
    \<longrightarrow> A $ from_nat c $ from_nat c dvd A $ a $ b"
  shows "(Diagonal_to_Smith_row_i A i bezout) $ (from_nat c) $ (from_nat c) 
          dvd (Diagonal_to_Smith_row_i A i bezout) $ a $ b"
proof (cases "c = i")
  case True
  then show ?thesis using assms True diagonal_to_Smith_row_i_dvd_jj
    by metis
  next
  case False
  hence ci2: "c<i" using ci by auto
  have 1: "to_nat (from_nat c::'c) \<notin> (set [i+1..<min (nrows A) (ncols A)])"    
    by (metis Suc_eq_plus1 ci atLeastLessThan_iff from_nat_mono 
        le_imp_less_Suc less_irrefl less_le_trans set_upt to_nat_le to_nat_less_card)
  have 2: "to_nat (from_nat c) \<noteq> i"
    using ci2 from_nat_mono to_nat_less_card by fastforce
  have 3: "to_nat (from_nat c::'c) = to_nat (from_nat c::'b)"
    by (metis a_in ab atLeastLessThan_iff ci dual_order.strict_trans2 to_nat_from_nat_id to_nat_less_card)
  have "(Diagonal_to_Smith_row_i A i bezout) $ (from_nat c) $ (from_nat c) 
    = A $(from_nat c) $ (from_nat c)"
    unfolding Diagonal_to_Smith_row_i_def 
    by (rule diagonal_to_Smith_i_preserves_previous_diagonal[OF ib _ 1 3 2], insert assms, auto)
  also have "... dvd (Diagonal_to_Smith_row_i A i bezout) $ a $ b"
    unfolding Diagonal_to_Smith_row_i_def 
    by (rule diagonal_to_Smith_i_dvd2, insert assms False ci ib, auto)  
  finally show ?thesis .
qed
end


lemma diagonal_to_Smith_aux_append:
  "diagonal_to_Smith_aux A (xs @ ys) bezout 
    = diagonal_to_Smith_aux (diagonal_to_Smith_aux A xs bezout) ys bezout"
  by (induct A xs bezout rule: diagonal_to_Smith_aux.induct, auto)
 

lemma diagonal_to_Smith_aux_append2[simp]:
  "diagonal_to_Smith_aux A (xs @ [ys]) bezout 
    = Diagonal_to_Smith_row_i (diagonal_to_Smith_aux A xs bezout) ys bezout"
  by (induct A xs bezout rule: diagonal_to_Smith_aux.induct, auto)  


lemma isDiagonal_eq_upt_k_min:
"isDiagonal A = isDiagonal_upt_k A (min (nrows A) (ncols A))" 
  unfolding isDiagonal_def isDiagonal_upt_k_def nrows_def ncols_def  
  by (auto, meson less_trans not_less_iff_gr_or_eq to_nat_less_card)


lemma isDiagonal_eq_upt_k_max:
"isDiagonal A = isDiagonal_upt_k A (max (nrows A) (ncols A))" 
  unfolding isDiagonal_def isDiagonal_upt_k_def nrows_def ncols_def  
  by (auto simp add: less_max_iff_disj to_nat_less_card)

lemma isDiagonal: 
  assumes "isDiagonal A"
    and "to_nat a \<noteq> to_nat b" shows "A $ a $ b = 0" 
  using assms unfolding isDiagonal_def by auto

lemma nrows_diagonal_to_Smith_aux[simp]: 
  shows "nrows (diagonal_to_Smith_aux A xs bezout) = nrows A" unfolding nrows_def by auto

lemma ncols_diagonal_to_Smith_aux[simp]:
  shows "ncols (diagonal_to_Smith_aux A xs bezout) = ncols A" unfolding ncols_def by auto

context
  fixes bezout::"'a::{bezout_ring} \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"
  assumes ib: "is_bezout_ext bezout"
begin

lemma isDiagonal_diagonal_to_Smith_aux:
  assumes diag_A: "isDiagonal A" and k: "k < min (nrows A) (ncols A)"
  shows "isDiagonal (diagonal_to_Smith_aux A [0..<k] bezout)"
  using k
proof (induct k)
  case 0
  then show ?case using diag_A by auto
next
  case (Suc k)
  have "Diagonal_to_Smith_row_i (diagonal_to_Smith_aux A [0..<k] bezout) k bezout $ a $ b = 0" 
    if a_not_b: "to_nat a \<noteq> to_nat b" for a b
  proof -
    have "Diagonal_to_Smith_row_i (diagonal_to_Smith_aux A [0..<k] bezout) k bezout $ a $ b 
      = (diagonal_to_Smith_aux A [0..<k] bezout) $ a $ b"
      by (rule diagonal_to_Smith_row_i_preserves_previous[OF ib _ a_not_b], insert Suc.prems, auto)
    also have "... = 0" 
      by (rule isDiagonal[OF Suc.hyps a_not_b], insert Suc.prems, auto)
    finally show ?thesis .
  qed
  thus ?case unfolding isDiagonal_def by auto
qed
end

(*TODO: move!*)
lemma to_nat_less_nrows[simp]:
  fixes A::"'a^'b::mod_type^'c::mod_type"
    and a::'c
  shows "to_nat a < nrows A"
  by (simp add: nrows_def to_nat_less_card)

lemma to_nat_less_ncols[simp]:
  fixes A::"'a^'b::mod_type^'c::mod_type"
    and a::'b
  shows "to_nat a < ncols A"
  by (simp add: ncols_def to_nat_less_card)

context
  fixes bezout::"'a::{bezout_ring} \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"
  assumes ib: "is_bezout_ext bezout"
begin

text\<open>The variables a and b must be arbitrary in the induction\<close>
lemma diagonal_to_Smith_aux_dvd:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ab: "to_nat a = to_nat b"
  and c: "c < k" and ca: "c \<le> to_nat a" and k: "k<min (nrows A) (ncols A)"
  shows "diagonal_to_Smith_aux A [0..<k] bezout $ from_nat c $ from_nat c
    dvd diagonal_to_Smith_aux A [0..<k] bezout $ a $ b"
  using c ab ca k
proof (induct k arbitrary: a b)
  case 0
  then show ?case by auto
next
  case (Suc k)
  note c = Suc.prems(1)
  note ab = Suc.prems(2)
  note ca = Suc.prems(3)
  note k = Suc.prems(4)
  have k_min: "k < min (nrows A) (ncols A)" using k by auto
  have a_less_ncols: "to_nat a < ncols A" using ab by auto
  show ?case
  proof (cases "c=k")
    case True
    hence k: "k\<le>to_nat a" using ca by auto
    show ?thesis unfolding True
      by (auto, rule diagonal_to_Smith_row_i_dvd_jj[OF ib _ ab], insert k a_less_ncols, auto)  
  next
    case False note c_not_k = False
    let ?Dk="diagonal_to_Smith_aux A [0..<k] bezout"
    have ck: "c<k" using Suc.prems False by auto
    have hyp: "?Dk $ from_nat c $ from_nat c dvd ?Dk $ a $ b" 
      by (rule Suc.hyps[OF ck ab ca k_min])
    have Dkk_Daa_bb: "?Dk $ from_nat c $ from_nat c dvd ?Dk $ aa $ bb"
      if "to_nat aa \<in> set [k..<min (nrows ?Dk) (ncols ?Dk)]" and "to_nat aa = to_nat bb"
      for aa bb using Suc.hyps ck k_min that(1) that(2) by auto
    show ?thesis  
    proof (cases "k\<le>to_nat a")
      case True
      show ?thesis
        by (auto, rule diagonal_to_Smith_row_i_dvd_jj'[OF ib _ ab]) 
           (insert True a_less_ncols ck Dkk_Daa_bb, force+)       
    next
      case False
      have "diagonal_to_Smith_aux A [0..<Suc k] bezout $ from_nat c $ from_nat c 
        = Diagonal_to_Smith_row_i ?Dk k bezout $ from_nat c $ from_nat c" by auto
      also have "... = ?Dk $ from_nat c $ from_nat c" 
      proof (rule diagonal_to_Smith_row_i_preserves_previous_diagonal[OF ib])
        show "k < min (nrows ?Dk) (ncols ?Dk)" using k by auto
        show "to_nat (from_nat c::'c) = to_nat (from_nat c::'b)"
          by (metis assms(2) assms(4) less_trans min_less_iff_conj 
             ncols_def nrows_def to_nat_from_nat_id)
        show "to_nat (from_nat c::'c) \<noteq> k"
          using False ca from_nat_mono' to_nat_less_card to_nat_mono' by fastforce      
        show "to_nat (from_nat c::'c) \<notin> set [k + 1..<min (nrows ?Dk) (ncols ?Dk)]"
          by (metis Suc_eq_plus1 atLeastLessThan_iff c ca from_nat_not_eq 
              le_less_trans not_le set_upt to_nat_less_card)
      qed
      also have "... dvd ?Dk $ a $ b" using hyp .
      also have "... = Diagonal_to_Smith_row_i ?Dk k bezout $ a $ b"
        by (rule diagonal_to_Smith_row_i_preserves_previous_diagonal[symmetric, OF ib _ _ ab])
           (insert False k, auto)
      also have "... = diagonal_to_Smith_aux A [0..<Suc k] bezout $ a $ b" by auto
      finally show ?thesis .
    qed
  qed
qed


lemma Smith_normal_form_upt_k_Suc_imp_k:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes s: "Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<Suc k] bezout) k"
  and k: "k<min (nrows A) (ncols A)"
  shows "Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<k] bezout) k"
proof (rule Smith_normal_form_upt_k_intro) 
  let ?Dk="diagonal_to_Smith_aux A [0..<k] bezout"
  fix a::'c and b::'b assume "to_nat a = to_nat b \<and> to_nat a + 1 < k \<and> to_nat b + 1 < k"
  hence ab: "to_nat a = to_nat b" and ak: "to_nat a + 1 < k" and bk: "to_nat b + 1 < k" by auto  
  have a_not_k: "to_nat a \<noteq> k" using ak by auto    
  have a1_less_k1: "to_nat a + 1 < k + 1" using ak by linarith
  have "?Dk $a $ b = diagonal_to_Smith_aux A [0..<Suc k] bezout $ a $ b"
    by (auto, rule diagonal_to_Smith_row_i_preserves_previous_diagonal[symmetric, OF ib _ _ ab a_not_k]) 
       (insert ak k, auto)
  also have "... dvd diagonal_to_Smith_aux A [0..<Suc k] bezout $ (a + 1) $ (b + 1)" 
    using ab ak bk s unfolding Smith_normal_form_upt_k_def by auto
  also have "... = ?Dk $ (a+1) $ (b+1)"
  proof (auto, rule diagonal_to_Smith_row_i_preserves_previous_diagonal[OF ib])
    show "to_nat (a + 1) \<noteq> k" using ak
      by (metis add_less_same_cancel2 nat_neq_iff not_add_less2 to_nat_0 
         to_nat_plus_one_less_card' to_nat_suc)
    show "to_nat (a + 1) = to_nat (b + 1)"
      by (metis ab ak from_nat_suc from_nat_to_nat_id k less_asym' min_less_iff_conj 
          ncols_def nrows_def suc_not_zero to_nat_from_nat_id to_nat_plus_one_less_card')
    show "to_nat (a + 1) \<notin> set [k + 1..<min (nrows ?Dk) (ncols ?Dk)]"      
      by (metis a1_less_k1 add_to_nat_def atLeastLessThan_iff k less_asym' min.strict_boundedE 
          not_less nrows_def set_upt suc_not_zero to_nat_1 to_nat_from_nat_id to_nat_plus_one_less_card')
    show "k < min (nrows ?Dk) (ncols ?Dk)" using k by auto
  qed
  finally show "?Dk $ a $ b dvd ?Dk $ (a+1) $ (b+1)" .
next
  let ?Dk="diagonal_to_Smith_aux A [0..<k] bezout"
  fix a::'c and b::'b
  assume "to_nat a \<noteq> to_nat b \<and> (to_nat a < k \<or> to_nat b < k)" 
  hence ab: "to_nat a \<noteq> to_nat b" and ak_bk: "(to_nat a < k \<or> to_nat b < k)" by auto
  have "?Dk $a $ b = diagonal_to_Smith_aux A [0..<Suc k] bezout $ a $ b"
    by (auto, rule diagonal_to_Smith_row_i_preserves_previous[symmetric, OF ib _ ab], insert k, auto)
  also have "... = 0"
    using ab ak_bk s unfolding Smith_normal_form_upt_k_def isDiagonal_upt_k_def 
    by auto
  finally show "?Dk $ a $ b = 0" .
qed


lemma Smith_normal_form_upt_k_le:
  assumes "a\<le>k" and "Smith_normal_form_upt_k A k"
  shows "Smith_normal_form_upt_k A a" using assms
  by (smt Smith_normal_form_upt_k_def isDiagonal_upt_k_def less_le_trans)

lemma Smith_normal_form_upt_k_imp_Suc_k:
  assumes s: "Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<k] bezout) k"
  and k: "k<min (nrows A) (ncols A)"
  shows "Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<Suc k] bezout) k"
proof (rule Smith_normal_form_upt_k_intro)
  let ?Dk="diagonal_to_Smith_aux A [0..<k] bezout"
  fix a::'c and b::'b assume "to_nat a = to_nat b \<and> to_nat a + 1 < k \<and> to_nat b + 1 < k"
  hence ab: "to_nat a = to_nat b" and ak: "to_nat a + 1 < k" and bk: "to_nat b + 1 < k" by auto
  have a_not_k: "to_nat a \<noteq> k" using ak by auto    
  have a1_less_k1: "to_nat a + 1 < k + 1" using ak by linarith
  have "diagonal_to_Smith_aux A [0..<Suc k] bezout $ a $ b = ?Dk $a $ b"
    by (auto, rule diagonal_to_Smith_row_i_preserves_previous_diagonal[OF ib _ _ ab a_not_k]) 
       (insert ak k, auto)
  also have "... dvd ?Dk $ (a+1) $ (b+1)"
    using s ak k ab unfolding Smith_normal_form_upt_k_def by auto
  also have "... = diagonal_to_Smith_aux A [0..<Suc k] bezout $ (a + 1) $ (b + 1)" 
  proof (auto, rule diagonal_to_Smith_row_i_preserves_previous_diagonal[symmetric, OF ib])
    show "to_nat (a + 1) \<noteq> k" using ak
      by (metis add_less_same_cancel2 nat_neq_iff not_add_less2 to_nat_0 
         to_nat_plus_one_less_card' to_nat_suc)
    show "to_nat (a + 1) = to_nat (b + 1)"
      by (metis ab ak from_nat_suc from_nat_to_nat_id k less_asym' min_less_iff_conj 
          ncols_def nrows_def suc_not_zero to_nat_from_nat_id to_nat_plus_one_less_card')
    show "to_nat (a + 1) \<notin> set [k + 1..<min (nrows ?Dk) (ncols ?Dk)]"      
      by (metis a1_less_k1 add_to_nat_def to_nat_plus_one_less_card' less_asym' min.strict_boundedE 
          not_less nrows_def set_upt suc_not_zero to_nat_1 to_nat_from_nat_id atLeastLessThan_iff k)
    show "k < min (nrows ?Dk) (ncols ?Dk)" using k by auto
  qed
  finally show "diagonal_to_Smith_aux A [0..<Suc k] bezout $ a $ b 
    dvd diagonal_to_Smith_aux A [0..<Suc k] bezout $ (a + 1) $ (b + 1)" .
next
  let ?Dk="diagonal_to_Smith_aux A [0..<k] bezout"
  fix a::'c and b::'b
  assume "to_nat a \<noteq> to_nat b \<and> (to_nat a < k \<or> to_nat b < k)" 
  hence ab: "to_nat a \<noteq> to_nat b" and ak_bk: "(to_nat a < k \<or> to_nat b < k)" by auto
  have "diagonal_to_Smith_aux A [0..<Suc k] bezout $ a $ b = ?Dk $a $ b"
    by (auto, rule diagonal_to_Smith_row_i_preserves_previous[OF ib _ ab], insert k, auto)
  also have "... = 0"
    using ab ak_bk s unfolding Smith_normal_form_upt_k_def isDiagonal_upt_k_def 
    by auto
  finally show "diagonal_to_Smith_aux A [0..<Suc k] bezout $ a $ b = 0" .
qed

corollary Smith_normal_form_upt_k_Suc_eq:
  assumes k: "k<min (nrows A) (ncols A)"
  shows "Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<Suc k] bezout) k 
    = Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<k] bezout) k"  
  using Smith_normal_form_upt_k_Suc_imp_k Smith_normal_form_upt_k_imp_Suc_k k 
  by blast

end

lemma nrows_diagonal_to_Smith_i[simp]: "nrows (diagonal_to_Smith_i xs A i bezout) = nrows A"
  by (induct xs A i bezout rule: diagonal_to_Smith_i.induct, auto simp add: nrows_def)

lemma ncols_diagonal_to_Smith_i[simp]: "ncols (diagonal_to_Smith_i xs A i bezout) = ncols A"
  by (induct xs A i bezout rule: diagonal_to_Smith_i.induct, auto simp add: ncols_def)

lemma nrows_Diagonal_to_Smith_row_i[simp]: "nrows (Diagonal_to_Smith_row_i A i bezout) = nrows A" 
  unfolding Diagonal_to_Smith_row_i_def by auto

lemma ncols_Diagonal_to_Smith_row_i[simp]: "ncols (Diagonal_to_Smith_row_i A i bezout) = ncols A" 
  unfolding Diagonal_to_Smith_row_i_def by auto

lemma isDiagonal_diagonal_step:
  assumes diag_A: "isDiagonal A" and i: "i<min (nrows A) (ncols A)"
    and j: "j<min (nrows A) (ncols A)"
  shows "isDiagonal (diagonal_step A i j d v)"
proof -
  have i_eq: "to_nat (from_nat i::'b) = to_nat (from_nat i::'c)" using i
    by (simp add: ncols_def nrows_def to_nat_from_nat_id)
  moreover have j_eq: "to_nat (from_nat j::'b) = to_nat (from_nat j::'c)" using j
    by (simp add: ncols_def nrows_def to_nat_from_nat_id)
    ultimately show ?thesis
    using assms
    unfolding isDiagonal_def diagonal_step_def by auto
qed

lemma isDiagonal_diagonal_to_Smith_i:
  assumes "isDiagonal A"
    and elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<min (nrows A) (ncols A)" 
    and "i<min (nrows A) (ncols A)"
  shows "isDiagonal (diagonal_to_Smith_i xs A i bezout)"
  using assms
proof (induct xs A i bezout rule: diagonal_to_Smith_i.induct)
  case (1 A i bezout)
  then show ?case by auto
next
  case (2 j xs A i bezout)  
  let ?Aii = "A $ from_nat i $ from_nat i"
  let ?Ajj = "A $ from_nat j $ from_nat j"
  let ?p="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?A'="diagonal_step A i j ?d ?v" 
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  show ?case 
  proof (cases "?Aii dvd ?Ajj")
    case True
    thus ?thesis
        using "2.hyps" "2.prems" by auto
  next
    case False
    have "diagonal_to_Smith_i (j # xs) A i bezout = diagonal_to_Smith_i xs ?A' i bezout" 
      using False by (simp add: split_beta) 
    also have "isDiagonal ..." thm "2.prems"
    proof (rule "2.hyps"(2)[OF False])
      show "isDiagonal
        (diagonal_step A i j ?d ?v)" by (rule isDiagonal_diagonal_step, insert "2.prems", auto)
    qed (insert pquvd "2.prems", auto)
    finally show ?thesis .
  qed  
qed


lemma isDiagonal_Diagonal_to_Smith_row_i:
  assumes "isDiagonal A" and "i < min (nrows A) (ncols A)"
  shows "isDiagonal (Diagonal_to_Smith_row_i A i bezout)"   
  using assms isDiagonal_diagonal_to_Smith_i
  unfolding Diagonal_to_Smith_row_i_def by force


lemma isDiagonal_diagonal_to_Smith_aux_general:
  assumes elements_xs_range: "\<forall>x. x \<in> set xs \<longrightarrow> x<min (nrows A) (ncols A)" 
  and "isDiagonal A"
shows "isDiagonal (diagonal_to_Smith_aux A xs bezout)"
  using assms
proof (induct A xs bezout rule: diagonal_to_Smith_aux.induct)
  case (1 A)
  then show ?case by auto
next
  case (2 A i xs bezout)  
  note k = "2.prems"(1)
  note elements_xs_range = "2.prems"(2)
  have "diagonal_to_Smith_aux A (i # xs) bezout 
  = diagonal_to_Smith_aux (Diagonal_to_Smith_row_i A i bezout) xs bezout" 
    by auto
  also have "isDiagonal (...)"
    by (rule "2.hyps", insert isDiagonal_Diagonal_to_Smith_row_i "2.prems" k, auto)   
  finally show ?case .
qed

context
  fixes bezout::"'a::{bezout_ring} \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a"
  assumes ib: "is_bezout_ext bezout"
begin

text\<open>The algorithm is iterated up to position k (not included). Thus, the matrix
is in Smith normal form up to position k (not included).\<close>

lemma Smith_normal_form_upt_k_diagonal_to_Smith_aux:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes "k<min (nrows A) (ncols A)" and d: "isDiagonal A"
  shows "Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<k] bezout) k"
  using assms
proof (induct k)
  case 0
  then show ?case by auto
next
  case (Suc k)
  note Suc_k = "Suc.prems"(1)
  have hyp: "Smith_normal_form_upt_k (diagonal_to_Smith_aux A [0..<k] bezout) k"
    by (rule Suc.hyps, insert Suc.prems, simp)
  have k: "k < min (nrows A) (ncols A)" using Suc.prems by auto
  let ?A = "diagonal_to_Smith_aux A [0..<k] bezout"
  let ?D_Suck = "diagonal_to_Smith_aux A [0..<Suc k] bezout"
  have set_rw: "[0..<Suc k] = [0..<k] @ [k]" by auto
  show ?case
  proof (rule Smith_normal_form_upt_k1_intro_diagonal)
    show "Smith_normal_form_upt_k (?D_Suck) k"
      by (rule Smith_normal_form_upt_k_imp_Suc_k[OF ib hyp k])
    show "?D_Suck $ from_nat (k - 1) $ from_nat (k - 1) dvd ?D_Suck $ from_nat k $ from_nat k"
    proof (rule diagonal_to_Smith_aux_dvd[OF ib _ _ _ Suc_k])
      show "to_nat (from_nat k::'c) = to_nat (from_nat k::'b)"
        by (metis k min_less_iff_conj ncols_def nrows_def to_nat_from_nat_id)
      show "k - 1 \<le> to_nat (from_nat k::'c)"
        by (metis diff_le_self k min_less_iff_conj nrows_def to_nat_from_nat_id)
    qed auto
    show "isDiagonal (diagonal_to_Smith_aux A [0..<Suc k] bezout)"
      by (rule isDiagonal_diagonal_to_Smith_aux[OF ib d Suc_k])
  qed
qed

end

lemma nrows_diagonal_to_Smith[simp]: "nrows (diagonal_to_Smith A bezout) = nrows A"
  unfolding diagonal_to_Smith_def by auto

lemma ncols_diagonal_to_Smith[simp]: "ncols (diagonal_to_Smith A bezout) = ncols A"
  unfolding diagonal_to_Smith_def by auto

lemma isDiagonal_diagonal_to_Smith:
  assumes d: "isDiagonal A"
  shows "isDiagonal (diagonal_to_Smith A bezout)"
  unfolding diagonal_to_Smith_def 
  by (rule isDiagonal_diagonal_to_Smith_aux_general[OF _ d], auto)

text\<open>This is the soundess lemma.\<close>

lemma Smith_normal_form_diagonal_to_Smith:
  fixes A::"'a::{bezout_ring}^'b::mod_type^'c::mod_type"
  assumes ib: "is_bezout_ext bezout"
  and d: "isDiagonal A"
  shows "Smith_normal_form (diagonal_to_Smith A bezout)"
proof -
  let ?k = "min (nrows A) (ncols A) - 2"
  let ?Dk = "(diagonal_to_Smith_aux A [0..<?k] bezout)"
  have min_eq: "min (nrows A) (ncols A) - 1 = Suc ?k" 
    by (metis Suc_1 Suc_diff_Suc min_less_iff_conj ncols_def nrows_def to_nat_1 to_nat_less_card)
  have set_rw: "[0..<min (nrows A) (ncols A) - 1] = [0..<?k] @ [?k]" 
    unfolding min_eq by auto    
  have d2: "isDiagonal (diagonal_to_Smith A bezout)" 
    by (rule isDiagonal_diagonal_to_Smith[OF d])
  have smith_Suc_k: "Smith_normal_form_upt_k (diagonal_to_Smith A bezout) (Suc ?k)" 
  proof (rule Smith_normal_form_upt_k1_intro_diagonal[OF _ d2])
    have "diagonal_to_Smith A bezout = diagonal_to_Smith_aux A [0..<min (nrows A) (ncols A) - 1] bezout" 
      unfolding diagonal_to_Smith_def by auto
    also have "... = Diagonal_to_Smith_row_i ?Dk ?k bezout" 
      unfolding set_rw
      unfolding diagonal_to_Smith_aux_append2 by auto
    finally have d_rw: "diagonal_to_Smith A bezout = Diagonal_to_Smith_row_i ?Dk ?k bezout" .
    have "Smith_normal_form_upt_k ?Dk ?k" 
      by (rule Smith_normal_form_upt_k_diagonal_to_Smith_aux[OF ib _ d], insert min_eq, linarith)
    thus "Smith_normal_form_upt_k (diagonal_to_Smith A bezout) ?k" unfolding d_rw 
      by (metis Smith_normal_form_upt_k_Suc_eq Suc_1 ib d_rw diagonal_to_Smith_def diff_0_eq_0 
          diff_less min_eq not_gr_zero zero_less_Suc)        
    show "diagonal_to_Smith A bezout $ from_nat (?k - 1) $ from_nat (?k - 1) dvd
          diagonal_to_Smith A bezout $ from_nat ?k $ from_nat ?k"
    proof (unfold diagonal_to_Smith_def, rule diagonal_to_Smith_aux_dvd[OF ib])
      show "?k - 1 < min (nrows A) (ncols A) - 1"
        using min_eq by linarith
      show "min (nrows A) (ncols A) - 1 < min (nrows A) (ncols A)" using min_eq by linarith
      thus "to_nat (from_nat ?k::'c) = to_nat (from_nat ?k::'b)"
        by (metis (mono_tags, lifting) Suc_lessD min_eq min_less_iff_conj 
            ncols_def nrows_def to_nat_from_nat_id)
      show "?k - 1 \<le> to_nat (from_nat ?k::'c)"         
        by (metis (no_types, lifting) diff_le_self from_nat_not_eq lessI less_le_trans 
            min.cobounded1 min_eq nrows_def)     
    qed
  qed
  have s_eq: "Smith_normal_form (diagonal_to_Smith A bezout) 
     = Smith_normal_form_upt_k (diagonal_to_Smith A bezout) 
    (Suc (min (nrows (diagonal_to_Smith A bezout)) (ncols (diagonal_to_Smith A bezout)) - 1))"
    unfolding Smith_normal_form_min by (simp add: ncols_def nrows_def)
  let ?min1="(min (nrows (diagonal_to_Smith A bezout)) (ncols (diagonal_to_Smith A bezout)) - 1)"
  show ?thesis unfolding s_eq
  proof (rule Smith_normal_form_upt_k1_intro_diagonal[OF _ d2])
    show "Smith_normal_form_upt_k (diagonal_to_Smith A bezout) ?min1"
      using smith_Suc_k min_eq by auto   
    have "diagonal_to_Smith A bezout $ from_nat ?k $ from_nat ?k 
      dvd diagonal_to_Smith A bezout $ from_nat (?k + 1) $ from_nat (?k + 1)"
      by (smt One_nat_def Suc_eq_plus1 ib Suc_pred diagonal_to_Smith_aux_dvd diagonal_to_Smith_def 
          le_add1 lessI min_eq min_less_iff_conj ncols_def nrows_def to_nat_from_nat_id zero_less_card_finite)
    thus "diagonal_to_Smith A bezout $ from_nat (?min1 - 1) $ from_nat (?min1 - 1) 
      dvd diagonal_to_Smith A bezout $ from_nat ?min1 $ from_nat ?min1" 
      using min_eq by auto
  qed
qed

subsection\<open>Implementation and formal proof 
  of the matrices $P$ and $Q$ which transform the input matrix by means of elementary operations.\<close>


fun diagonal_step_PQ :: "'a::{bezout_ring}^'cols::mod_type^'rows::mod_type \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a bezout \<Rightarrow> 
(
('a::{bezout_ring}^'rows::mod_type^'rows::mod_type) \<times>
('a::{bezout_ring}^'cols::mod_type^'cols::mod_type)
)"
  where "diagonal_step_PQ A i k bezout = 
  (let  i_row = from_nat i; k_row = from_nat k; i_col = from_nat i; k_col = from_nat k;
        (p, q, u, v, d) = bezout (A $ i_row $ from_nat i) (A $ k_row $ from_nat k);
        P = row_add (interchange_rows (row_add (mat 1) k_row i_row p) i_row k_row) k_row i_row (-v);
        Q = mult_column (column_add (column_add (mat 1) i_col k_col q) k_col i_col u) k_col (-1)
        in (P,Q)
        )"

text\<open>Examples\<close>

value "let A = list_of_list_to_matrix [[12,0,0::int],[0,6,0::int],[0,0,2::int]]::int^3^3;
            i=0; k=1;
           (p, q, u, v, d) = euclid_ext2 (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k);
            (P,Q) = diagonal_step_PQ A i k euclid_ext2
  in matrix_to_list_of_list (diagonal_step A i k d v)"

value "let A = list_of_list_to_matrix [[12,0,0::int],[0,6,0::int],[0,0,2::int]]::int^3^3;
            i=0; k=1;
           (p, q, u, v, d) = euclid_ext2 (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k);
            (P,Q) = diagonal_step_PQ A i k euclid_ext2
  in matrix_to_list_of_list (P**(A)**Q)"


value "let A = list_of_list_to_matrix [[12,0,0::int],[0,6,0::int],[0,0,2::int]]::int^3^3;
            i=0; k=1;
           (p, q, u, v, d) = euclid_ext2 (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k);
            (P,Q) = diagonal_step_PQ A i k euclid_ext2
  in matrix_to_list_of_list (P**(A)**Q)"


lemmas diagonal_step_PQ_def = diagonal_step_PQ.simps

lemma from_nat_neq_rows:
  fixes A::"'a^'cols::mod_type^'rows::mod_type"
  assumes i: "i<(nrows A)" and k: "k<(nrows A)" and ik: "i \<noteq> k"
  shows "from_nat i \<noteq> (from_nat k::'rows)"
proof (rule ccontr, auto)
  let ?i="from_nat i::'rows"
  let ?k="from_nat k::'rows"
  assume "?i = ?k"
  hence "to_nat ?i = to_nat ?k" by auto
  hence "i = k" 
    unfolding to_nat_from_nat_id[OF i[unfolded nrows_def]] 
    unfolding to_nat_from_nat_id[OF k[unfolded nrows_def]] .
  thus False using ik by contradiction
qed


lemma from_nat_neq_cols:
  fixes A::"'a^'cols::mod_type^'rows::mod_type"
  assumes i: "i<(ncols A)" and k: "k<(ncols A)" and ik: "i \<noteq> k"
  shows "from_nat i \<noteq> (from_nat k::'cols)"
proof (rule ccontr, auto)
  let ?i="from_nat i::'cols"
  let ?k="from_nat k::'cols"
  assume "?i = ?k"
  hence "to_nat ?i = to_nat ?k" by auto
  hence "i = k" 
    unfolding to_nat_from_nat_id[OF i[unfolded ncols_def]] 
    unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]] .
  thus False using ik by contradiction
qed



lemma diagonal_step_PQ_invertible_P:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
  and pquvd: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
  and i_not_k: "i \<noteq> k" 
  and i: "i<min (nrows A) (ncols A)" and k: "k<min (nrows A) (ncols A)"
shows "invertible P"
proof -
  let ?step1 = "(row_add (mat 1) (from_nat k::'rows) (from_nat i) p)"
  let ?step2 = "interchange_rows ?step1 (from_nat i) (from_nat k)"
  let ?step3 = "row_add (?step2) (from_nat k) (from_nat i) (- v)"
  have p: "p = fst (bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k))"
    using pquvd by (metis fst_conv)
  have v: "-v = (- fst (snd (snd (snd (bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k))))))"
    using pquvd by (metis fst_conv snd_conv)
  have i_not_k2: "from_nat k \<noteq> (from_nat i::'rows)" 
    by (rule from_nat_neq_rows, insert i k i_not_k, auto)
  have "invertible ?step3" 
  unfolding row_add_mat_1[of _ _ _ ?step2, symmetric] 
  proof (rule invertible_mult)
    show "invertible (row_add (mat 1) (from_nat k::'rows) (from_nat i) (- v))"
      by (rule invertible_row_add[OF i_not_k2])          
    show "invertible ?step2"      
      by (metis i_not_k2 interchange_rows_mat_1 invertible_interchange_rows
          invertible_mult invertible_row_add)
  qed
  thus ?thesis
    using PQ p v unfolding diagonal_step_PQ_def Let_def split_beta 
    by auto
qed



lemma diagonal_step_PQ_invertible_Q:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
  and pquvd: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
  and i_not_k: "i \<noteq> k" 
  and i: "i<min (nrows A) (ncols A)" and k: "k<min (nrows A) (ncols A)"
shows "invertible Q"
proof -
  let ?step1 = "column_add (mat 1) (from_nat i::'cols) (from_nat k) q"
  let ?step2 = "column_add ?step1 (from_nat k) (from_nat i) u"
  let ?step3 = "mult_column ?step2 (from_nat k) (- 1)"
  have u: "u = (fst (snd (snd (bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)))))"
    by (metis fst_conv pquvd snd_conv)
  have q: "q = (fst (snd (bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k))))"
    by (metis fst_conv pquvd snd_conv)
  have "invertible ?step3"
    unfolding column_add_mat_1[of _ _ _ ?step2, symmetric] 
    unfolding mult_column_mat_1[of  ?step2, symmetric]
  proof (rule invertible_mult)
    show "invertible (mult_column (mat 1) (from_nat k::'cols) (- 1::'a))"
      by (rule invertible_mult_column[of _ "-1"], auto)
    show "invertible ?step2"
      by (metis column_add_mat_1 i i_not_k invertible_column_add invertible_mult k 
          min_less_iff_conj ncols_def to_nat_from_nat_id)
  qed
  thus ?thesis 
    using PQ pquvd u q unfolding diagonal_step_PQ_def
    by (auto simp add: Let_def split_beta)
qed

lemma mat_q_1[simp]: "mat q $ a $ a = q" unfolding mat_def by auto

lemma mat_q_0[simp]:
  assumes ab: "a \<noteq> b" 
  shows "mat q $ a $ b = 0" using ab unfolding mat_def by auto

text\<open>This is an alternative definition for the matrix P in each step, where entries are 
  given explicitly instead of being computed as a composition of elementary operations. \<close>

lemma diagonal_step_PQ_P_alt:
fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
  and pquvd: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
  and i: "i<min (nrows A) (ncols A)" and k: "k<min (nrows A) (ncols A)" and ik: "i \<noteq> k"
shows "
  P = (\<chi> a b. 
  if a = from_nat i \<and> b = from_nat i then p else 
  if a = from_nat i \<and> b = from_nat k then 1 else
  if a = from_nat k \<and> b = from_nat i then -v * p + 1 else
  if a = from_nat k \<and> b = from_nat k then -v else
  if a = b then 1 else 0)"
proof -  
  have ik1: "from_nat i \<noteq> (from_nat k::'rows)"
    using from_nat_neq_rows i ik k by auto
  have "P $ a $ b =
              (if a = from_nat i \<and> b = from_nat i then p
               else if a = from_nat i \<and> b = from_nat k then 1
                    else if a = from_nat k \<and> b = from_nat i then - v * p + 1
                         else if a = from_nat k \<and> b = from_nat k then - v else if a = b then 1 else 0)" 
    for a b
      using PQ ik1  pquvd  
      unfolding diagonal_step_PQ_def 
      unfolding row_add_def interchange_rows_def
      by (auto simp add: Let_def split_beta)
         (metis (mono_tags, hide_lams) fst_conv snd_conv)+
    thus ?thesis unfolding vec_eq_iff unfolding vec_lambda_beta by auto
qed


text\<open>This is an alternative definition for the matrix Q in each step, where entries are
  given explicitly instead of being computed as a composition of elementary operations.\<close>

lemma diagonal_step_PQ_Q_alt:
fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
  and pquvd: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
  and i: "i<min (nrows A) (ncols A)" and k: "k<min (nrows A) (ncols A)" and ik: "i \<noteq> k"
shows "
  Q = (\<chi> a b. 
  if a = from_nat i \<and> b = from_nat i then 1 else 
  if a = from_nat i \<and> b = from_nat k then -u else
  if a = from_nat k \<and> b = from_nat i then q else
  if a = from_nat k \<and> b = from_nat k then -q*u-1 else
  if a = b then 1 else 0)"
proof -
  have ik1: "from_nat i \<noteq> (from_nat k::'cols)"
    using from_nat_neq_cols i ik k by auto
  have "Q $ a $ b =
  (if a = from_nat i \<and> b = from_nat i then 1 else 
  if a = from_nat i \<and> b = from_nat k then -u else
  if a = from_nat k \<and> b = from_nat i then q else
  if a = from_nat k \<and> b = from_nat k then -q*u-1 else
  if a = b then 1 else 0)"  for a b
  using PQ ik1 pquvd unfolding diagonal_step_PQ_def
  unfolding column_add_def mult_column_def
  by (auto simp add: Let_def split_beta)
     (metis (mono_tags, hide_lams) fst_conv snd_conv)+
  thus ?thesis unfolding vec_eq_iff unfolding vec_lambda_beta by auto
qed
  
text\<open>P**A can be rewriten as elementary operations over A.\<close>

lemma diagonal_step_PQ_PA:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
    and b: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
shows "P**A = row_add (interchange_rows 
  (row_add A (from_nat k) (from_nat i) p) (from_nat i) (from_nat k)) (from_nat k) (from_nat i) (- v)" 
proof -
  let ?i_row = "from_nat i::'rows" and ?k_row = "from_nat k::'rows"
  let ?P1 = "row_add (mat 1) ?k_row ?i_row p"
  let ?P2' = "interchange_rows ?P1 ?i_row ?k_row"
  let ?P2 = "interchange_rows (mat 1) (from_nat i) (from_nat k)"
  let ?P3 = "row_add (mat 1) (from_nat k) (from_nat i) (- v)"
  have "P = row_add ?P2' ?k_row ?i_row (- v)"
    using PQ b unfolding diagonal_step_PQ_def 
    by (auto simp add: Let_def split_beta, metis fstI sndI)
  also have "... = ?P3 ** ?P2'" 
    unfolding row_add_mat_1[of _ _ _ ?P2', symmetric] by auto
  also have "... = ?P3 ** (?P2 ** ?P1)" 
    unfolding interchange_rows_mat_1[of _ _ ?P1, symmetric] by auto  
  also have "... ** A = row_add (interchange_rows 
  (row_add A (from_nat k) (from_nat i) p) (from_nat i) (from_nat k)) (from_nat k) (from_nat i) (- v)"
    by (metis interchange_rows_mat_1 matrix_mul_assoc row_add_mat_1)
  finally show ?thesis .
qed


lemma diagonal_step_PQ_PAQ':
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
    and b: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
  shows "P**A**Q = (mult_column (column_add (column_add (P**A) (from_nat i) (from_nat k) q) 
                   (from_nat k) (from_nat i) u) (from_nat k) (- 1))" 
proof -
  let ?i_col = "from_nat i::'cols" and ?k_col = "from_nat k::'cols"
  let ?Q1="(column_add (mat 1) ?i_col ?k_col q)"
  let ?Q2' = "(column_add ?Q1 ?k_col ?i_col u)"
  let ?Q2 = "column_add (mat 1) (from_nat k) (from_nat i) u"
  let ?Q3 = "mult_column (mat 1) (from_nat k) (- 1)"
  have "Q = mult_column ?Q2' ?k_col (-1)"
    using PQ b unfolding diagonal_step_PQ_def 
    by (auto simp add: Let_def split_beta, metis fstI sndI)
  also have "... = ?Q2' ** ?Q3" 
    unfolding mult_column_mat_1[of ?Q2', symmetric] by auto
  also have "... = (?Q1**?Q2)**?Q3" 
    unfolding column_add_mat_1[of ?Q1, symmetric] by auto
  also have " (P**A) **  ((?Q1**?Q2)**?Q3) = 
    (mult_column (column_add (column_add (P**A) ?i_col ?k_col q) ?k_col ?i_col u) ?k_col (- 1))"
    by (metis (no_types, lifting) column_add_mat_1 matrix_mul_assoc mult_column_mat_1)
  finally show ?thesis .
qed

corollary diagonal_step_PQ_PAQ:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
    and b: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
  shows "P**A**Q = (mult_column (column_add (column_add (row_add (interchange_rows 
                    (row_add A (from_nat k) (from_nat i) p) (from_nat i) 
                    (from_nat k)) (from_nat k) (from_nat i) (- v)) (from_nat i) (from_nat k) q) 
                   (from_nat k) (from_nat i) u) (from_nat k) (- 1))"
  using diagonal_step_PQ_PA diagonal_step_PQ_PAQ' assms by metis

lemma isDiagonal_imp_0: 
  assumes "isDiagonal A"
  and "from_nat a \<noteq> from_nat b"
  and "a < min (nrows A) (ncols A)"
  and "b < min (nrows A) (ncols A)"
  shows "A $ from_nat a $ from_nat b = 0" 
  by (metis assms isDiagonal min.strict_boundedE ncols_def nrows_def to_nat_from_nat_id)



lemma diagonal_step_PQ:
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type"
  assumes PQ: "(P,Q) = diagonal_step_PQ A i k bezout"
    and b: "(p,q,u,v,d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat k $ from_nat k)"
  and i: "i<min (nrows A) (ncols A)" and k: "k<min (nrows A) (ncols A)" and ik: "i \<noteq> k"
  and ib: "is_bezout_ext bezout" and diag: "isDiagonal A"
  shows "diagonal_step A i k d v = P**A**Q"
proof -
  let ?i_row = "from_nat i::'rows" 
    and ?k_row = "from_nat k::'rows" and ?i_col = "from_nat i::'cols" and ?k_col = "from_nat k::'cols"
  let ?P1 = "(row_add (mat 1) ?k_row ?i_row p)"
  let ?Aii = "A $ ?i_row $ ?i_col"
  let ?Akk = "A $ ?k_row $ ?k_col"
  have k1: "k<ncols A" and k2: "k<nrows A" and i1: "i<nrows A" and i2: "i<ncols A" using i k by auto
  have Aik0: "A $ ?i_row $ ?k_col = 0"
    by (metis diag i ik isDiagonal k min.strict_boundedE ncols_def nrows_def to_nat_from_nat_id)
  have Aki0: "A $ ?k_row $ ?i_col = 0"
    by (metis diag i ik isDiagonal k min.strict_boundedE ncols_def nrows_def to_nat_from_nat_id)
  have du: "d * u = - A $ ?k_row $ ?k_col"
    using b ib unfolding is_bezout_ext_def 
    by (auto simp add: split_beta) (metis fst_conv snd_conv)
  have dv: "d * v = A $ ?i_row $ ?i_col"
    using b ib unfolding is_bezout_ext_def 
    by (auto simp add: split_beta) (metis fst_conv snd_conv)
  have d: "d = p * ?Aii + ?Akk * q" 
    using b ib unfolding is_bezout_ext_def 
    by (auto simp add: split_beta) (metis fst_conv mult.commute snd_conv)
  have "(?Aii - v * (p * ?Aii) - v * ?Akk * q) * u = (?Aii - v * ((p * ?Aii) + ?Akk * q)) * u"
      by (simp add: diff_diff_add distrib_left mult.assoc)
    also have "... = (?Aii*u - d* v *u)"
      by (simp add: mult.commute right_diff_distrib d)
    also have "... = 0" by (simp add: dv)
    finally have rw: "(?Aii - v * (p * ?Aii) - v * ?Akk * q) * u = 0" .
    have a1: "from_nat k \<noteq> (from_nat i::'rows)"
      using from_nat_neq_rows i ik k by auto
    have a2: "from_nat k \<noteq> (from_nat i::'cols)"
      using from_nat_neq_cols i ik k by auto
    have Aab0: "A $ a $ from_nat b = 0" if ab: "a \<noteq> from_nat b" and b_ncols: "b < ncols A" for a b
      by (metis ab b_ncols diag from_nat_to_nat_id isDiagonal ncols_def to_nat_from_nat_id)  
    have Aab0': "A $ from_nat a $ b = 0" if ab: "from_nat a \<noteq> b" and a_nrows: "a < nrows A" for a b
      by (metis ab a_nrows diag from_nat_to_nat_id isDiagonal nrows_def to_nat_from_nat_id)
  show ?thesis
  proof (unfold diagonal_step_def vec_eq_iff, auto)
    show "d = (P ** A ** Q) $ from_nat i $ from_nat i"
      and "d = (P ** A ** Q) $ from_nat i $ from_nat i"
      and "d = (P ** A ** Q) $ from_nat i $ from_nat i"
    unfolding diagonal_step_PQ_PAQ[OF PQ b] 
    unfolding mult_column_def column_add_def interchange_rows_def row_add_def 
      unfolding vec_lambda_beta using a1 a2
      using Aik0 Aki0 d by auto
    show "v * A $ from_nat k $ from_nat k = (P ** A ** Q) $ from_nat k $ from_nat k"
      and "v * A $ from_nat k $ from_nat k = (P ** A ** Q) $ from_nat k $ from_nat k"
      using a1 a2  
      unfolding diagonal_step_PQ_PAQ[OF PQ b] mult_column_def column_add_def 
      unfolding interchange_rows_def row_add_def 
      unfolding vec_lambda_beta unfolding Aik0 Aki0 by (auto simp add: rw)
    fix a::'rows and b::'cols 
    assume ak: "a \<noteq> from_nat k" and ai: "a \<noteq> from_nat i" 
    show "A $ a $ b = (P ** A ** Q) $ a $ b"
      using ai ak a1 a2 Aab0 k1 i2
      unfolding diagonal_step_PQ_PAQ[OF PQ b] 
      unfolding mult_column_def column_add_def interchange_rows_def row_add_def 
      unfolding vec_lambda_beta by auto
  next
    fix a::'rows and b::'cols 
    assume ak: "a \<noteq> from_nat k" and ai: "b \<noteq> from_nat i" 
    show "A $ a $ b = (P ** A ** Q) $ a $ b"
      using ai ak a1 a2 Aab0 Aab0' d du k1 k2 i1 i2
      unfolding diagonal_step_PQ_PAQ[OF PQ b] 
      unfolding mult_column_def column_add_def interchange_rows_def row_add_def 
      unfolding vec_lambda_beta by auto
  next
    fix a::'rows and b::'cols 
    assume ak: "b \<noteq> from_nat k" and ai: "a \<noteq> from_nat i" 
    show "A $ a $ b = (P ** A ** Q) $ a $ b"
      using ai ak a1 a2 Aab0 Aab0' d du k1 k2 i1 i2
      unfolding diagonal_step_PQ_PAQ[OF PQ b] 
      unfolding mult_column_def column_add_def interchange_rows_def row_add_def 
      unfolding vec_lambda_beta apply auto (*TODO: cleanup this sledeghammer proof*)
      proof -
        assume "d = p * ?Aii+ ?Akk* q"
        then have "v * (p * ?Aii) + v * (?Akk* q) = d * v"
          by (simp add: ring_class.ring_distribs(1) semiring_normalization_rules(7))
        then have "?Aii- v * (p * ?Aii) - v * (?Akk* q) = 0"
          by (simp add: diff_diff_add dv)
        then show "?Aii- v * (p * ?Aii) = v * ?Akk* q"
          by force
      qed
    next
    fix a::'rows and b::'cols 
    assume ak: "b \<noteq> from_nat k" and ai: "b \<noteq> from_nat i" 
    show "A $ a $ b = (P ** A ** Q) $ a $ b"
      using ai ak a1 a2 Aab0 Aab0' d du k1 k2 i1 i2
      unfolding diagonal_step_PQ_PAQ[OF PQ b] 
      unfolding mult_column_def column_add_def interchange_rows_def row_add_def 
      unfolding vec_lambda_beta by auto
  qed
qed



fun diagonal_to_Smith_i_PQ :: 
"nat list \<Rightarrow> nat \<Rightarrow> ('a::{bezout_ring} bezout) 
  \<Rightarrow> (('a^'rows::mod_type^'rows::mod_type)\<times>('a^'cols::mod_type^'rows::mod_type)\<times> ('a^'cols::mod_type^'cols::mod_type))
  \<Rightarrow> (('a^'rows::mod_type^'rows::mod_type)\<times> ('a^'cols::mod_type^'rows::mod_type) \<times> ('a^'cols::mod_type^'cols::mod_type))"
 where
"diagonal_to_Smith_i_PQ [] i bezout (P,A,Q) = (P,A,Q)" |
"diagonal_to_Smith_i_PQ (j#xs) i bezout (P,A,Q) = (
  if A $ (from_nat i) $ (from_nat i) dvd A $ (from_nat j) $ (from_nat j) 
     then diagonal_to_Smith_i_PQ xs i bezout (P,A,Q)
  else let (p, q, u, v, d) = bezout (A $ from_nat i $ from_nat i) (A $ from_nat j $ from_nat j); 
           A' = diagonal_step A i j d v;
          (P',Q') = diagonal_step_PQ A i j bezout
      in diagonal_to_Smith_i_PQ xs i bezout (P'**P,A',Q**Q') \<comment> \<open>Apply the step\<close>
  )
  "


text\<open>This is implemented by fun. This way, I can do pattern-matching for $(P,A,Q)$.\<close>

fun Diagonal_to_Smith_row_i_PQ
  where "Diagonal_to_Smith_row_i_PQ i bezout (P,A,Q) 
  = diagonal_to_Smith_i_PQ [i + 1..<min (nrows A) (ncols A)] i bezout (P,A,Q)"


text\<open>Deleted from the simplified and renamed as it would be a definition.\<close>

declare Diagonal_to_Smith_row_i_PQ.simps[simp del]
lemmas Diagonal_to_Smith_row_i_PQ_def = Diagonal_to_Smith_row_i_PQ.simps

fun diagonal_to_Smith_aux_PQ 
  where
  "diagonal_to_Smith_aux_PQ [] bezout (P,A,Q) = (P,A,Q)" |
  "diagonal_to_Smith_aux_PQ (i#xs) bezout (P,A,Q) 
      = diagonal_to_Smith_aux_PQ xs bezout (Diagonal_to_Smith_row_i_PQ i bezout (P,A,Q))"


lemma diagonal_to_Smith_aux_PQ_append:
  "diagonal_to_Smith_aux_PQ (xs @ ys) bezout (P,A,Q)
    = diagonal_to_Smith_aux_PQ ys bezout (diagonal_to_Smith_aux_PQ xs bezout (P,A,Q))"
  by (induct xs bezout "(P,A,Q)" arbitrary: P A Q rule: diagonal_to_Smith_aux_PQ.induct)
     (auto, metis prod_cases3)


lemma diagonal_to_Smith_aux_PQ_append2[simp]:
  "diagonal_to_Smith_aux_PQ (xs @ [ys]) bezout (P,A,Q) 
    = Diagonal_to_Smith_row_i_PQ ys bezout (diagonal_to_Smith_aux_PQ xs bezout (P,A,Q))"
proof (induct xs bezout "(P,A,Q)" arbitrary: P A Q rule: diagonal_to_Smith_aux_PQ.induct)
  case (1 bezout P A Q)
  then show ?case 
    by (metis append.simps(1) diagonal_to_Smith_aux_PQ.simps prod.exhaust)
next
  case (2 i xs bezout P A Q)
  then show ?case
    by (metis (no_types, hide_lams) append_Cons diagonal_to_Smith_aux_PQ.simps(2) prod_cases3)
qed 

(*
definition "diagonal_to_Smith_PQ A bezout 
  = diagonal_to_Smith_aux_PQ [0..<min (nrows A) (ncols A) - 1] bezout (mat 1, A, mat 1)"
*)

context
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type" (*This is the input matrix*)
  and B::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type" (*This is the matrix in each step*)
  and P and Q
  and bezout::"'a bezout"
  assumes PAQ: "P**A**Q = B"
  and P: "invertible P" and Q: "invertible Q"
  and ib: "is_bezout_ext bezout"
begin

text\<open>The output is the same as the one in the version where $P$ and $Q$ are not computed.\<close>

lemma diagonal_to_Smith_i_PQ_eq:
  assumes P'B'Q': "(P',B',Q') = diagonal_to_Smith_i_PQ xs i bezout (P,B,Q)"
  and xs: "\<forall>x. x \<in> set xs \<longrightarrow> x < min (nrows A) (ncols A)" 
  and diag: "isDiagonal B" and i_notin: "i \<notin> set xs" and i: "i<min (nrows A) (ncols A)"
shows "B' = diagonal_to_Smith_i xs B i bezout"     
  using assms PAQ ib P Q 
proof (induct xs i bezout "(P,B,Q)" arbitrary: P B Q rule:diagonal_to_Smith_i_PQ.induct)
  case (1 i bezout P A Q)
  then show ?case by auto
next
  case (2 j xs i bezout P B Q)
  let ?Bii = "B $ from_nat i $ from_nat i"
  let ?Bjj = "B $ from_nat j $ from_nat j"
  let ?p="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?B'="diagonal_step B i j ?d ?v" 
  let ?P' = "fst (diagonal_step_PQ B i j bezout)"
  let ?Q' = "snd (diagonal_step_PQ B i j bezout)"
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  note hyp = "2.hyps"(2)
    note P'B'Q' = "2.prems"(1)
    note i_min = "2.prems"(5)
    note PAQ_B = "2.prems"(6)
    note i_notin = "2.prems"(4)
    note diagB = "2.prems"(3)    
    note xs_min = "2.prems"(2)      
    note ib = "2.prems"(7)
    note inv_P = "2.prems"(8)
    note inv_Q = "2.prems"(9)
  show ?case
  proof (cases "?Bii dvd ?Bjj")
    case True    
    show ?thesis using "2.prems" "2.hyps"(1) True by auto
  next
    case False    
    have aux: "diagonal_to_Smith_i_PQ (j # xs) i bezout (P, B, Q) 
      = diagonal_to_Smith_i_PQ xs i bezout (?P'**P,?B', Q**?Q')"
      using False by (auto simp add: split_beta)
    have i: "i < min (nrows B) (ncols B)" using i_min unfolding nrows_def ncols_def by auto
    have j: "j < min (nrows B) (ncols B)" using xs_min unfolding nrows_def ncols_def by auto     
    have aux2: "diagonal_to_Smith_i(j # xs) B i bezout = diagonal_to_Smith_i xs ?B' i bezout"
      using False by (auto simp add: split_beta)
    have res: " B' = diagonal_to_Smith_i xs ?B' i bezout"
    proof (rule hyp[OF False])
      show "(P', B', Q') = diagonal_to_Smith_i_PQ xs i bezout (?P'**P,?B', Q**?Q')" 
        using aux P'B'Q' by auto
      have B'_P'B'Q': "?B' = ?P'**B**?Q'"
        by (rule diagonal_step_PQ[OF _ _ i j _ ib diagB], insert i_notin pquvd, auto)
      show "?P'**P ** A ** (Q**?Q') = ?B'"
        unfolding B'_P'B'Q' unfolding PAQ_B[symmetric]
        by (simp add: matrix_mul_assoc)       
      show "isDiagonal ?B'" by (rule isDiagonal_diagonal_step[OF diagB i j])
      show "invertible (?P'** P)"
        by (metis inv_P diagonal_step_PQ_invertible_P i i_notin in_set_member 
           invertible_mult j member_rec(1) prod.exhaust_sel)
      show "invertible (Q ** ?Q')"
        by (metis diagonal_step_PQ_invertible_Q i i_notin inv_Q 
            invertible_mult j list.set_intros(1) prod.collapse)
    qed (insert pquvd xs_min i_min i_notin ib, auto)
    show ?thesis using aux aux2 res by auto
  qed
qed


lemma diagonal_to_Smith_i_PQ':
  assumes P'B'Q': "(P',B',Q') = diagonal_to_Smith_i_PQ xs i bezout (P,B,Q)"
  and xs: "\<forall>x. x \<in> set xs \<longrightarrow> x < min (nrows A) (ncols A)" 
  and diag: "isDiagonal B" and i_notin: "i \<notin> set xs" and i: "i<min (nrows A) (ncols A)"
shows "B' = P'**A**Q' \<and> invertible P' \<and> invertible Q'"
  using assms PAQ ib P Q
proof (induct xs i bezout "(P,B,Q)" arbitrary: P B Q rule:diagonal_to_Smith_i_PQ.induct)
  case (1 i bezout)
  then show ?case using PAQ by auto
next
  case (2 j xs i bezout P B Q)
  let ?Bii = "B $ from_nat i $ from_nat i"
  let ?Bjj = "B $ from_nat j $ from_nat j"
  let ?p="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> p"  
  let ?q="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> q"
  let ?u="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> u"
  let ?v="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> v"
  let ?d="case bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j) of (p,q,u,v,d) \<Rightarrow> d"
  let ?B'="diagonal_step B i j ?d ?v" 
  let ?P' = "fst (diagonal_step_PQ B i j bezout)"
  let ?Q' = "snd (diagonal_step_PQ B i j bezout)"
  have pquvd: "(?p, ?q, ?u, ?v,?d) = bezout (B $ from_nat i $ from_nat i) (B $ from_nat j $ from_nat j)"
    by (simp add: split_beta)
  show ?case
  proof (cases "?Bii dvd ?Bjj")
    case True    
    then show ?thesis using "2.prems"
      using "2.hyps"(1) by auto
  next
    case False
    note hyp = "2.hyps"(2)
    note P'B'Q' = "2.prems"(1)
    note i_min = "2.prems"(5)
    note PAQ_B = "2.prems"(6)
    note i_notin = "2.prems"(4)
    note diagB = "2.prems"(3)    
    note xs_min = "2.prems"(2)      
    note ib = "2.prems"(7)
    note inv_P = "2.prems"(8)
    note inv_Q = "2.prems"(9)
    have aux: "diagonal_to_Smith_i_PQ (j # xs) i bezout (P, B, Q) 
      = diagonal_to_Smith_i_PQ xs i bezout (?P'**P,?B', Q**?Q')"
      using False by (auto simp add: split_beta)
    have i: "i < min (nrows B) (ncols B)" using i_min unfolding nrows_def ncols_def by auto
    have j: "j < min (nrows B) (ncols B)" using xs_min unfolding nrows_def ncols_def by auto     
    show ?thesis
    proof (rule hyp[OF False])
      show "(P', B', Q') = diagonal_to_Smith_i_PQ xs i bezout (?P'**P,?B', Q**?Q')" 
        using aux P'B'Q' by auto
      have B'_P'B'Q': "?B' = ?P'**B**?Q'"
        by (rule diagonal_step_PQ[OF _ _ i j _ ib diagB], insert i_notin pquvd, auto)
      show "?P'**P ** A ** (Q**?Q') = ?B'"
        unfolding B'_P'B'Q' unfolding PAQ_B[symmetric]
        by (simp add: matrix_mul_assoc)       
      show "isDiagonal ?B'" by (rule isDiagonal_diagonal_step[OF diagB i j])
      show "invertible (?P'** P)"
        by (metis inv_P diagonal_step_PQ_invertible_P i i_notin in_set_member 
           invertible_mult j member_rec(1) prod.exhaust_sel)
      show "invertible (Q ** ?Q')"
        by (metis diagonal_step_PQ_invertible_Q i i_notin inv_Q 
            invertible_mult j list.set_intros(1) prod.collapse)
    qed (insert pquvd xs_min i_min i_notin ib, auto)    
  qed
qed


corollary diagonal_to_Smith_i_PQ:
  assumes P'B'Q': "(P',B',Q') = diagonal_to_Smith_i_PQ xs i bezout (P,B,Q)"
  and xs: "\<forall>x. x \<in> set xs \<longrightarrow> x < min (nrows A) (ncols A)" 
  and diag: "isDiagonal B" and i_notin: "i \<notin> set xs" and i: "i<min (nrows A) (ncols A)"
shows "B' = P'**A**Q' \<and> invertible P' \<and> invertible Q' \<and> B' = diagonal_to_Smith_i xs B i bezout"
  using assms diagonal_to_Smith_i_PQ' diagonal_to_Smith_i_PQ_eq by metis

lemma Diagonal_to_Smith_row_i_PQ_eq:
  assumes P'B'Q': "(P',B',Q') = Diagonal_to_Smith_row_i_PQ i bezout (P,B,Q)"
    and diag: "isDiagonal B" and i: "i < min (nrows A) (ncols A)"
  shows "B' = Diagonal_to_Smith_row_i B i bezout"
  using assms unfolding Diagonal_to_Smith_row_i_def Diagonal_to_Smith_row_i_PQ_def
  using diagonal_to_Smith_i_PQ by (auto simp add: nrows_def ncols_def)

lemma Diagonal_to_Smith_row_i_PQ':
  assumes P'B'Q': "(P',B',Q') = Diagonal_to_Smith_row_i_PQ i bezout (P,B,Q)"
    and diag: "isDiagonal B" and i: "i < min (nrows A) (ncols A)"
  shows "B' = P'**A**Q' \<and> invertible P' \<and> invertible Q'"
  by (rule diagonal_to_Smith_i_PQ'[OF P'B'Q'[unfolded Diagonal_to_Smith_row_i_PQ_def] _ diag _ i],
     auto simp add: nrows_def ncols_def)

lemma Diagonal_to_Smith_row_i_PQ:
  assumes P'B'Q': "(P',B',Q') = Diagonal_to_Smith_row_i_PQ i bezout (P,B,Q)"
    and diag: "isDiagonal B" and i: "i < min (nrows A) (ncols A)"
  shows "B' = P'**A**Q' \<and> invertible P' \<and> invertible Q' \<and> B' = Diagonal_to_Smith_row_i B i bezout"
  using assms Diagonal_to_Smith_row_i_PQ' Diagonal_to_Smith_row_i_PQ_eq by presburger

end

context
  fixes A::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type" (*This is the input matrix*)
  and B::"'a::{bezout_ring}^'cols::mod_type^'rows::mod_type" (*This is the matrix in each step*)
  and P and Q
  and bezout::"'a bezout"
  assumes PAQ: "P**A**Q = B"
  and P: "invertible P" and Q: "invertible Q"
  and ib: "is_bezout_ext bezout"
begin


lemma diagonal_to_Smith_aux_PQ:
  assumes P'B'Q': "(P',B',Q') = diagonal_to_Smith_aux_PQ [0..<k] bezout (P,B,Q)"
  and diag: "isDiagonal B" and k:"k<min (nrows A) (ncols A)"
shows "B' = P'**A**Q' \<and> invertible P' \<and> invertible Q' \<and> B' = diagonal_to_Smith_aux B [0..<k] bezout"
  using k P'B'Q' P Q PAQ diag
proof (induct k arbitrary: P B Q P' Q' B')
  case 0
  then show ?case using P Q PAQ by auto
next
  case (Suc k P B Q P' Q' B')
  note Suc_k = Suc.prems(1)
  note PBQ = Suc.prems(2)
  note P = Suc.prems(3)
  note Q = Suc.prems(4)
  note PAQ_B = Suc.prems(5)
  note diag_B = Suc.prems(6)
  let ?Dk = "(diagonal_to_Smith_aux_PQ [0..<k] bezout (P, P ** A ** Q, Q))"
  let ?P' = "fst ?Dk"
  let ?B'="fst (snd ?Dk)"
  let ?Q' = "snd (snd ?Dk)"
  have k: "k<min (nrows A) (ncols A)" using Suc_k by auto
  have hyp: "?B' = ?P' ** A ** ?Q' \<and> invertible ?P' \<and> invertible ?Q' 
      \<and> ?B' = diagonal_to_Smith_aux B [0..<k] bezout"
    by (rule Suc.hyps[OF k _ P Q PAQ_B diag_B], auto simp add: PAQ_B)
  have diag_B': "isDiagonal ?B'"
    by (metis diag_B hyp ib isDiagonal_diagonal_to_Smith_aux k ncols_def nrows_def)
  have "B' = diagonal_to_Smith_aux B [0..<Suc k] bezout"
    by (auto, metis Diagonal_to_Smith_row_i_PQ_eq PAQ_B Suc(3) diag_B' 
        diagonal_to_Smith_aux_PQ_append2 eq_fst_iff hyp ib k sndI upt.simps(2) zero_order(1))
  moreover have "B' = P' ** A ** Q' \<and> invertible P' \<and> invertible Q'"
  proof (rule Diagonal_to_Smith_row_i_PQ')
    show "(P', B', Q') = Diagonal_to_Smith_row_i_PQ k bezout (?P',?B',?Q')" using Suc.prems by auto
    show "invertible ?P'" using hyp by auto
    show "?P' ** A ** ?Q' = ?B'" using hyp by auto
    show "invertible ?Q'" using hyp by auto
    show "is_bezout_ext bezout" using ib by auto
    show "k < min (nrows A) (ncols A)" using k by auto
    show diag_B': "isDiagonal ?B'" using diag_B' by auto
  qed 
  ultimately show ?case by auto
qed

end

fun diagonal_to_Smith_PQ 
  where "diagonal_to_Smith_PQ A bezout 
  = diagonal_to_Smith_aux_PQ  [0..<min (nrows A) (ncols A) - 1] bezout (mat 1, A ,mat 1)"

declare diagonal_to_Smith_PQ.simps[simp del]
lemmas diagonal_to_Smith_PQ_def = diagonal_to_Smith_PQ.simps

lemma diagonal_to_Smith_PQ:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" 
  assumes A: "isDiagonal A" and ib: "is_bezout_ext bezout"
  assumes PBQ: "(P,B,Q) = diagonal_to_Smith_PQ A bezout"
  shows "B = P**A**Q \<and> invertible P \<and> invertible Q \<and> B = diagonal_to_Smith A bezout"   
proof (unfold diagonal_to_Smith_def, rule diagonal_to_Smith_aux_PQ[OF  _ _ _ ib _ A])
  let ?P = "mat 1::'a^'rows::mod_type^'rows::mod_type"
  let ?Q = "mat 1::'a^'cols::mod_type^'cols::mod_type"
  show "(P, B, Q) = diagonal_to_Smith_aux_PQ [0..<min (nrows A) (ncols A) - 1] bezout (?P, A, ?Q)"
    using PBQ unfolding diagonal_to_Smith_PQ_def .
  show "?P ** A ** ?Q = A" by simp
  show " min (nrows A) (ncols A) - 1 < min (nrows A) (ncols A)"    
    by (metis (no_types, lifting) One_nat_def diff_less dual_order.strict_iff_order le_less_trans 
        min_def mod_type_class.to_nat_less_card ncols_def not_less_eq nrows_not_0 zero_order(1))
qed (auto simp add: invertible_mat_1)


lemma diagonal_to_Smith_PQ_exists:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" 
  assumes A: "isDiagonal A"
  shows "\<exists>P Q. 
         invertible (P::'a^'rows::{mod_type}^'rows::{mod_type}) 
       \<and> invertible (Q::'a^'cols::{mod_type}^'cols::{mod_type})
       \<and> Smith_normal_form (P**A**Q)"   
proof -
  obtain bezout::"'a bezout" where ib: "is_bezout_ext bezout"
    using exists_bezout_ext by blast
  obtain P B Q where PBQ: "(P,B,Q) = diagonal_to_Smith_PQ A bezout"
    by (metis prod_cases3)
  have "B = P**A**Q \<and> invertible P \<and> invertible Q \<and> B = diagonal_to_Smith A bezout" 
    by (rule diagonal_to_Smith_PQ[OF A ib PBQ])
  moreover have "Smith_normal_form (P**A**Q)"
    using Smith_normal_form_diagonal_to_Smith assms calculation ib by fastforce
  ultimately show ?thesis by auto
qed

subsection\<open>The final soundness theorem\<close>

lemma diagonal_to_Smith_PQ':
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" 
  assumes A: "isDiagonal A" and ib: "is_bezout_ext bezout"
  assumes PBQ: "(P,S,Q) = diagonal_to_Smith_PQ A bezout"
  shows "S = P**A**Q \<and> invertible P \<and> invertible Q \<and> Smith_normal_form S"   
  using A PBQ Smith_normal_form_diagonal_to_Smith diagonal_to_Smith_PQ ib by fastforce

end
