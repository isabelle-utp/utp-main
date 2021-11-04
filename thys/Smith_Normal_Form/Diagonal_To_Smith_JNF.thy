(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Algorithm to transform a diagonal matrix into its Smith normal form in JNF\<close>

theory Diagonal_To_Smith_JNF
  imports Admits_SNF_From_Diagonal_Iff_Bezout_Ring
begin


text \<open>In this file, we implement an algorithm to transform a diagonal matrix into its Smith
normal form, using the JNF library.

There are, at least, three possible options:
\begin{enumerate}
\item Implement and prove the soundness of the algorithm from scratch in JNF
\item Implement it in JNF and connect it to the HOL Analysis version by means of transfer rules.
Thus, we could obtain the soundness lemma in JNF.
\item Implement it in JNF, with calls to the HOL Analysis version by means of the functions 
@{text " from_hma\<^sub>m"} and @{text "to_hma\<^sub>m"}. That is, transform the matrix to HOL Analysis, apply
the existing algorith in HOL Analysis to get the Smith normal form and then transform the output 
to JNF. Then, we could try to get the soundness theorem in JNF by means of 
transfer rules and local type definitions.
\end{enumerate}

The first option requires much effort. As we will see, the third option is not possible.
\<close>


subsection \<open>Attempt with the third option: definitions and conditional transfer rules\<close>

context
  fixes A::"'a::bezout_ring mat"
  assumes "A \<in> carrier_mat CARD('nr::mod_type) CARD('nc::mod_type)"
begin

private definition "diagonal_to_Smith_PQ_JNF' bezout = (
  let A' = Mod_Type_Connect.to_hma\<^sub>m A::'a^'nc::mod_type^'nr::mod_type;
     (P,S,Q) = (diagonal_to_Smith_PQ A' bezout)
  in (Mod_Type_Connect.from_hma\<^sub>m P, Mod_Type_Connect.from_hma\<^sub>m S, Mod_Type_Connect.from_hma\<^sub>m Q))"

end

text \<open>This approach will not work. The type is necessary in the definition of the function.
That is, outside the context, the function will be:

@{text "diagonal_to_Smith_PQ_JNF' TYPE('nc) TYPE('nr) A bezout"}

And we cannot get rid of such @{text "TYPE('nc)"}.

That is, we could get a lemma like:

@{theory_text "
lemma
  assumes A \<in> carrier_mat m n
  and (P,S,Q) = diagonal_to_Smith_PQ_JNF' TYPE('nr::mod_type) TYPE('nc::mod_type) A bezout
  shows invertible_mat P \<and> invertible_mat Q \<and> S = P * A * Q \<and> Smith_normal_form_mat S
"}

But we wouldn't be able to get rid of such types.
\<close>

subsection \<open>Attempt with the second option: implementation and soundness in JNF\<close>


definition "diagonal_step_JNF A i j d v =               
              Matrix.mat (dim_row A) (dim_col A) (\<lambda> (a,b). if a = i \<and> b = i then d else 
               if a = j \<and> b = j 
               then v * (A $$ (j,j)) else A $$ (a,b))"

text \<open>Conditional transfer rules are required, so I prove them within context with assumptions.\<close>

context
  includes lifting_syntax
  fixes i and j::nat
  assumes i: "i<min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
  and j: "j<min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
begin
  
lemma HMA_diagonal_step[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: comm_ring_1 ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _) 
    ===> (=) ===> (=) ===> Mod_Type_Connect.HMA_M) 
    (\<lambda>A. diagonal_step_JNF A i j) (\<lambda>B. diagonal_step B i j)" 
  by (intro rel_funI, goal_cases, auto simp add: Mod_Type_Connect.HMA_M_def 
      diagonal_step_JNF_def diagonal_step_def)
 (rule eq_matI, auto simp add: Mod_Type_Connect.from_hma\<^sub>m_def, insert from_nat_eq_imp_eq i j, auto)

end

definition diagonal_step_PQ_JNF :: 
  "'a::{bezout_ring} mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a bezout \<Rightarrow> ('a mat \<times> ('a mat))"
  where "diagonal_step_PQ_JNF A i k bezout = 
  (let  m = dim_row A; n = dim_col A;
        (p, q, u, v, d) = bezout (A $$ (i,i)) (A $$ (k,k));
        P = addrow (-v) k i (swaprows i k (addrow p k i (1\<^sub>m m)));
        Q = multcol k (-1) (addcol u k i (addcol q i k (1\<^sub>m n)))
        in (P,Q)
        )"

context
  includes lifting_syntax
  fixes i and k::nat
  assumes i: "i < min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
  and k: "k < min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
begin

lemma HMA_diagonal_step_PQ[transfer_rule]: 
  "((Mod_Type_Connect.HMA_M :: _ \<Rightarrow> 'a :: bezout_ring ^ 'nc :: mod_type ^ 'nr :: mod_type \<Rightarrow> _) 
    ===> (=) ===> rel_prod Mod_Type_Connect.HMA_M Mod_Type_Connect.HMA_M) 
    (\<lambda>A bezout. diagonal_step_PQ_JNF A i k bezout) (\<lambda>A bezout. diagonal_step_PQ A i k bezout)" 
proof (intro rel_funI, goal_cases)
  case (1 A A' bezout bezout')  
  note HMA_M_AA'[transfer_rule] = 1(1)
  let ?d_JNF = "(diagonal_step_PQ_JNF A i k bezout)"
  let ?d_HA = "(diagonal_step_PQ A' i k bezout)"
  have [transfer_rule]: "Mod_Type_Connect.HMA_I k (from_nat k::'nc)"
    and [transfer_rule]: "Mod_Type_Connect.HMA_I k (from_nat k::'nr)"
    by (metis Mod_Type_Connect.HMA_I_def k min.strict_boundedE to_nat_from_nat_id)+
  have [transfer_rule]: "Mod_Type_Connect.HMA_I i (from_nat i::'nc)"
    and [transfer_rule]: "Mod_Type_Connect.HMA_I i (from_nat i::'nr)"
      by (metis Mod_Type_Connect.HMA_I_def i min.strict_boundedE to_nat_from_nat_id)+
  have [transfer_rule]: "A $$ (i,i) = A' $h from_nat i $h from_nat i"
  proof -
    have "A $$ (i,i) = index_hma A' (from_nat i) (from_nat i)"  by (transfer, simp)
    also have "... = A' $h from_nat i $h from_nat i" unfolding index_hma_def by auto
    finally show ?thesis .
  qed
  have [transfer_rule]: "A $$ (k,k) = A' $h from_nat k $h from_nat k"
  proof -
    have "A $$ (k,k) = index_hma A' (from_nat k) (from_nat k)"  by (transfer, simp)
    also have "... = A' $h from_nat k $h from_nat k" unfolding index_hma_def by auto
    finally show ?thesis .
  qed
  have dim_row_CARD: "dim_row A = CARD('nr)"
    using HMA_M_AA' Mod_Type_Connect.dim_row_transfer_rule by blast
  have dim_col_CARD: "dim_col A = CARD('nc)"
    using HMA_M_AA' Mod_Type_Connect.dim_col_transfer_rule by blast  
  let ?p = "fst (bezout (A' $h from_nat i $h from_nat i) (A' $h from_nat k $h from_nat k))"
  let ?v = "fst (snd (snd (snd (bezout (A $$ (i, i)) (A $$ (k, k))))))"
  have "Mod_Type_Connect.HMA_M (fst ?d_JNF) (fst ?d_HA)" 
    unfolding diagonal_step_PQ_JNF_def diagonal_step_PQ_def Mod_Type_Connect.HMA_M_def    
    unfolding Let_def split_beta dim_row_CARD
    by (auto, transfer, auto simp add: Mod_Type_Connect.HMA_M_def Rel_def rel_funI)
  moreover have "Mod_Type_Connect.HMA_M (snd ?d_JNF) (snd ?d_HA)"
    unfolding diagonal_step_PQ_JNF_def diagonal_step_PQ_def Mod_Type_Connect.HMA_M_def    
    unfolding Let_def split_beta dim_col_CARD
    by (auto, transfer, auto simp add: Mod_Type_Connect.HMA_M_def Rel_def rel_funI)
  ultimately show ?case unfolding rel_prod_conv using 1
    by (simp add: split_beta)
qed

end


fun diagonal_to_Smith_i_PQ_JNF :: 
  "nat list \<Rightarrow> nat \<Rightarrow> ('a::{bezout_ring} bezout) 
  \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat) \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat)"
 where
"diagonal_to_Smith_i_PQ_JNF [] i bezout (P,A,Q) = (P,A,Q)" |
"diagonal_to_Smith_i_PQ_JNF (j#xs) i bezout (P,A,Q) = (
  if A $$ (i,i) dvd A $$ (j,j) 
     then diagonal_to_Smith_i_PQ_JNF xs i bezout (P,A,Q)
  else let (p, q, u, v, d) = bezout (A $$ (i,i)) (A $$ (j,j)); 
           A' = diagonal_step_JNF A i j d v;
          (P',Q') = diagonal_step_PQ_JNF A i j bezout
      in diagonal_to_Smith_i_PQ_JNF xs i bezout (P'*P,A',Q*Q') \<comment> \<open>Apply the step\<close>
  )
  "

context
  includes lifting_syntax
  fixes i and xs
  assumes i: "i < min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
  and xs: "\<forall>j\<in>set xs. j < min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
begin

declare diagonal_step_PQ.simps[simp del]

lemma HMA_diagonal_to_Smith_i_PQ_aux: "HMA_M3 (P,A,Q)  
  (P' :: 'a :: bezout_ring ^ 'nr :: mod_type ^ 'nr :: mod_type,
   A' :: 'a :: bezout_ring ^ 'nc :: mod_type ^ 'nr :: mod_type,
   Q' :: 'a :: bezout_ring ^ 'nc :: mod_type ^ 'nc :: mod_type)
  \<Longrightarrow> HMA_M3 (diagonal_to_Smith_i_PQ_JNF xs i bezout (P,A,Q)) 
             (diagonal_to_Smith_i_PQ xs i bezout (P',A',Q'))"
  using i xs
proof (induct xs i bezout "(P',A',Q')" arbitrary: P' A' Q' P A Q rule: diagonal_to_Smith_i_PQ.induct)
  case (1 i bezout P' A' Q')
  then show ?case by auto
next
  case (2 j xs i bezout P' A' Q')
  note HMA_M3[transfer_rule] = "2.prems"(1)
  note i = 2(4)
  note j = 2(5)
  note IH1="2.hyps"(1)
  note IH2="2.hyps"(2)
  have j_min: "j < min CARD('nr) CARD('nc)" using j by auto
  have HMA_M_AA'[transfer_rule]: "Mod_Type_Connect.HMA_M A A'" using HMA_M3 by auto
  have [transfer_rule]: "Mod_Type_Connect.HMA_I j (from_nat j::'nc)"  
    and [transfer_rule]: "Mod_Type_Connect.HMA_I j (from_nat j::'nr)"
    by (metis Mod_Type_Connect.HMA_I_def j_min min.strict_boundedE to_nat_from_nat_id)+
  have [transfer_rule]: "Mod_Type_Connect.HMA_I i (from_nat i::'nc)"
    and [transfer_rule]: "Mod_Type_Connect.HMA_I i (from_nat i::'nr)"
      by (metis Mod_Type_Connect.HMA_I_def i min.strict_boundedE to_nat_from_nat_id)+
  have [transfer_rule]: "A $$ (i, i) = A' $h from_nat i $h from_nat i"
  proof -
    have "A $$ (i,i) = index_hma A' (from_nat i) (from_nat i)"  by (transfer, simp)
    also have "... = A' $h from_nat i $h from_nat i" unfolding index_hma_def by auto
    finally show ?thesis .
  qed
  have [transfer_rule]: "A $$ (j, j) = A' $h from_nat j $h from_nat j"
  proof -
    have "A $$ (j,j) = index_hma A' (from_nat j) (from_nat j)"  by (transfer, simp)
    also have "... = A' $h from_nat j $h from_nat j" unfolding index_hma_def by auto
    finally show ?thesis .
  qed
  show ?case
  proof (cases "A $$ (i, i) dvd A $$ (j, j)")
    case True
    hence "A' $h from_nat i $h from_nat i dvd A' $h from_nat j $h from_nat j" by transfer
    then show ?thesis using True IH1 HMA_M3 i j by auto
  next
    case False    
    obtain p q u v d where b: "(p, q, u, v, d) = bezout (A $$ (i,i)) (A $$ (j,j))"
      by (metis prod_cases5)
    let ?A'_JNF = "diagonal_step_JNF A i j d v"
    obtain P''_JNF Q''_JNF where P''Q''_JNF: "(P''_JNF,Q''_JNF) = diagonal_step_PQ_JNF A i j bezout"
      by (metis surjective_pairing)
    have not_dvd: "\<not> A' $h from_nat i $h from_nat i dvd A' $h from_nat j $h from_nat j" using False by transfer
    let ?A' = "diagonal_step A' i j d v"
    obtain P'' Q'' where P''Q'': "(P'',Q'') = diagonal_step_PQ A' i j bezout" 
      by (metis surjective_pairing)
    have b2: "(p, q, u, v, d) = bezout (A' $h from_nat i $h from_nat i) (A' $h from_nat j $h from_nat j)" 
      using b by (transfer,auto)
    let ?D_HA = "diagonal_to_Smith_i_PQ xs i bezout (P''**P',?A',Q'**Q'')"
    let ?D_JNF = "diagonal_to_Smith_i_PQ_JNF xs i bezout (P''_JNF*P,?A'_JNF,Q*Q''_JNF)"
    have rw_1: "diagonal_to_Smith_i_PQ_JNF (j # xs) i bezout (P, A, Q) = ?D_JNF" 
      using False b P''Q''_JNF
      by (auto, unfold split_beta, metis fst_conv snd_conv)
    have rw_2: "diagonal_to_Smith_i_PQ (j # xs) i bezout (P', A', Q') = ?D_HA" 
      using not_dvd b2 P''Q'' by (auto, unfold split_beta, metis fst_conv snd_conv)
    have "HMA_M3 ?D_JNF ?D_HA" 
    proof (rule IH2[OF not_dvd b2], auto)
      have j: "j < min CARD('nr) CARD('nc)" using j by auto
      have [transfer_rule]: "rel_prod Mod_Type_Connect.HMA_M Mod_Type_Connect.HMA_M 
       (diagonal_step_PQ_JNF A i j bezout) (diagonal_step_PQ A' i j bezout)"
        using HMA_diagonal_step_PQ[OF i j] HMA_M_AA' unfolding rel_fun_def by auto
      hence [transfer_rule]: "Mod_Type_Connect.HMA_M P''_JNF P''" 
        and [transfer_rule]: "Mod_Type_Connect.HMA_M Q''_JNF Q''"
        using P''Q'' P''Q''_JNF unfolding rel_prod_conv split_beta
        by (metis fst_conv, metis snd_conv)
      have [transfer_rule]: "Mod_Type_Connect.HMA_M P P'" using HMA_M3 by auto
      show "Mod_Type_Connect.HMA_M (P''_JNF * P) (P'' ** P')" 
        (* apply (transfer, auto) does not finish the goal*)
        by (transfer_prover_start, transfer_step+, auto)      
     (* note HMA_diagonal_step[OF i j,transfer_rule]*)            
     (*transfer does not work for the following goal*)
      show "Mod_Type_Connect.HMA_M (diagonal_step_JNF A i j d v) (diagonal_step A' i j d v)"
        using HMA_diagonal_step[OF i j] HMA_M_AA' unfolding rel_fun_def by auto
      have [transfer_rule]: "Mod_Type_Connect.HMA_M Q Q'" using HMA_M3 by auto
      show "Mod_Type_Connect.HMA_M (Q * Q''_JNF) (Q' ** Q'')"
        by (transfer_prover_start, transfer_step+, auto)
    qed (insert i j P''Q'', auto)
    then show ?thesis using rw_1 rw_2 by auto
  qed
qed

lemma HMA_diagonal_to_Smith_i_PQ[transfer_rule]: 
  "((=) 
  ===> (HMA_M3 :: (_ \<Rightarrow> (_\<times>('a :: bezout_ring ^ 'nc :: mod_type ^ 'nr :: mod_type) \<times> _) \<Rightarrow>_)) 
  ===> HMA_M3) (diagonal_to_Smith_i_PQ_JNF xs i) (diagonal_to_Smith_i_PQ xs i)" 
proof (intro rel_funI, goal_cases)
  case (1 x y bezout bezout')
  then show ?case using HMA_diagonal_to_Smith_i_PQ_aux
    by (auto, smt HMA_M3.elims(2))
qed

end

fun Diagonal_to_Smith_row_i_PQ_JNF
  where "Diagonal_to_Smith_row_i_PQ_JNF i bezout (P,A,Q) 
  = diagonal_to_Smith_i_PQ_JNF [i + 1..<min (dim_row A) (dim_col A)] i bezout (P,A,Q)"

declare Diagonal_to_Smith_row_i_PQ_JNF.simps[simp del]
lemmas Diagonal_to_Smith_row_i_PQ_JNF_def = Diagonal_to_Smith_row_i_PQ_JNF.simps

context 
  includes lifting_syntax
  fixes i
  assumes i: "i < min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
begin

lemma HMA_Diagonal_to_Smith_row_i_PQ[transfer_rule]:
  "((=) ===> (HMA_M3 :: (_ \<Rightarrow> (_ \<times> ('a::bezout_ring^'nc::mod_type^'nr::mod_type) \<times> _) \<Rightarrow> _)) ===> HMA_M3) 
  (Diagonal_to_Smith_row_i_PQ_JNF i) (Diagonal_to_Smith_row_i_PQ i)"
proof (intro rel_funI, clarify, goal_cases)
  case (1 _ bezout P A Q P' A' Q')
  note HMA_M3[transfer_rule] = 1
  let ?xs1="[i + 1..<min (dim_row A) (dim_col A)]"
  let ?xs2="[i + 1..<min (nrows A') (ncols A')]"
  have xs_eq[transfer_rule]: "?xs1 = ?xs2"
    using HMA_M3
    by (auto intro: arg_cong2[where f = upt]
        simp: Mod_Type_Connect.dim_col_transfer_rule Mod_Type_Connect.dim_row_transfer_rule
        nrows_def ncols_def)
  have j_xs: "\<forall>j\<in>set ?xs1. j < min CARD('nr) CARD('nc)" using i
    by (metis atLeastLessThan_iff ncols_def nrows_def set_upt xs_eq)
  have rel: "HMA_M3 (diagonal_to_Smith_i_PQ_JNF ?xs1 i bezout (P,A,Q)) 
            (diagonal_to_Smith_i_PQ ?xs1 i bezout (P',A',Q'))"
  using HMA_diagonal_to_Smith_i_PQ[OF i j_xs] HMA_M3 unfolding rel_fun_def by blast
  then show ?case 
    unfolding Diagonal_to_Smith_row_i_PQ_JNF_def Diagonal_to_Smith_row_i_PQ_def
    by (metis Suc_eq_plus1 xs_eq)
qed

end

fun diagonal_to_Smith_aux_PQ_JNF 
  where
  "diagonal_to_Smith_aux_PQ_JNF [] bezout (P,A,Q) = (P,A,Q)" |
  "diagonal_to_Smith_aux_PQ_JNF (i#xs) bezout (P,A,Q) 
      = diagonal_to_Smith_aux_PQ_JNF xs bezout (Diagonal_to_Smith_row_i_PQ_JNF i bezout (P,A,Q))"

context
  includes lifting_syntax
  fixes xs
  assumes xs: "\<forall>j\<in>set xs. j < min (CARD('nr::mod_type)) (CARD('nc::mod_type))"
begin

lemma HMA_diagonal_to_Smith_aux_PQ_JNF[transfer_rule]:
  "((=) ===> (HMA_M3 :: (_ \<Rightarrow> (_ \<times> ('a::bezout_ring^'nc::mod_type^'nr::mod_type) \<times> _) \<Rightarrow> _)) ===> HMA_M3) 
  (diagonal_to_Smith_aux_PQ_JNF xs) (diagonal_to_Smith_aux_PQ xs)"
proof (intro rel_funI, clarify, goal_cases)
  case (1 _ bezout P A Q P' A' Q')
  note HMA_M3[transfer_rule] = 1
  show ?case
    using xs HMA_M3
  proof (induct xs arbitrary: P' A' Q' P A Q)
    case Nil
    then show ?case by auto
  next
    case (Cons i xs)
    note IH = Cons(1)
    note HMA_M3 = Cons.prems(2)
    have i: "i < min CARD('nr) CARD('nc)" using Cons.prems by auto
    let ?D_JNF = "(Diagonal_to_Smith_row_i_PQ_JNF i bezout (P, A, Q))"
    let ?D_HA = "(Diagonal_to_Smith_row_i_PQ i bezout (P', A', Q'))"
    have rw_1: "diagonal_to_Smith_aux_PQ_JNF (i # xs) bezout (P, A, Q) 
        = diagonal_to_Smith_aux_PQ_JNF xs bezout ?D_JNF" by auto
    have rw_2: "diagonal_to_Smith_aux_PQ (i # xs) bezout (P', A', Q') 
        = diagonal_to_Smith_aux_PQ xs bezout ?D_HA" by auto
    have "HMA_M3 ?D_JNF ?D_HA" 
      using HMA_Diagonal_to_Smith_row_i_PQ[OF i] HMA_M3 unfolding rel_fun_def by blast
    then show ?case
      by (auto, smt Cons.hyps HMA_M3.elims(2) list.set_intros(2) local.Cons(2))
  qed
qed

end

fun diagonal_to_Smith_PQ_JNF
  where "diagonal_to_Smith_PQ_JNF A bezout 
  = diagonal_to_Smith_aux_PQ_JNF [0..<min (dim_row A) (dim_col A) - 1] 
    bezout (1\<^sub>m (dim_row A),A,1\<^sub>m (dim_col A))"


declare diagonal_to_Smith_PQ_JNF.simps[simp del]
lemmas diagonal_to_Smith_PQ_JNF_def = diagonal_to_Smith_PQ_JNF.simps

lemma diagonal_step_PQ_JNF_dim:
  assumes A: "A \<in> carrier_mat m n"
    and d: "diagonal_step_PQ_JNF A i j bezout = (P,Q)"
  shows "P \<in> carrier_mat m m \<and> Q \<in> carrier_mat n n"
  using A d unfolding diagonal_step_PQ_JNF_def split_beta Let_def by auto

lemma diagonal_step_JNF_dim:
  assumes A: "A \<in> carrier_mat m n"
  shows "diagonal_step_JNF A i j d v \<in> carrier_mat m n"
  using A unfolding diagonal_step_JNF_def by auto

lemma diagonal_to_Smith_i_PQ_JNF_dim:
  assumes "P' \<in> carrier_mat m m \<and> A' \<in> carrier_mat m n \<and> Q' \<in> carrier_mat n n"
    and "diagonal_to_Smith_i_PQ_JNF xs i bezout (P',A',Q') = (P,A,Q)"
  shows "P \<in> carrier_mat m m \<and> A \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"
  using assms 
  proof (induct xs i bezout "(P',A',Q')" arbitrary: P A Q P' A' Q' rule: diagonal_to_Smith_i_PQ_JNF.induct)
    case (1 i bezout P A Q)
    then show ?case by auto
  next
    case (2 j xs i bezout P' A' Q')
    show ?case
    proof (cases "A' $$ (i, i) dvd A' $$ (j, j)")
      case True
      then show ?thesis using 2 by auto
    next
      case False
      obtain p q u v d where b: "(p, q, u, v, d) = bezout (A' $$ (i,i)) (A' $$ (j,j))"
      by (metis prod_cases5)
      let ?A' = "diagonal_step_JNF A' i j d v"
      obtain P'' Q'' where P''Q'': "(P'',Q'') = diagonal_step_PQ_JNF A' i j bezout"
        by (metis surjective_pairing)
      let ?A' = "diagonal_step_JNF A' i j d v"
      let ?D_JNF = "diagonal_to_Smith_i_PQ_JNF xs i bezout (P''*P',?A',Q'*Q'')"
      have rw_1: "diagonal_to_Smith_i_PQ_JNF (j # xs) i bezout (P', A', Q') = ?D_JNF" 
        using False b P''Q''
        by (auto, unfold split_beta, metis fst_conv snd_conv)            
      show ?thesis 
      proof (rule "2.hyps"(2)[OF False b])
        show "?D_JNF = (P,A,Q)" using rw_1 2 by auto
        have "P'' \<in> carrier_mat m m" and "Q'' \<in> carrier_mat n n" 
          using diagonal_step_PQ_JNF_dim[OF _ P''Q''[symmetric]] "2.prems" by auto
        thus "P'' * P' \<in> carrier_mat m m \<and> ?A' \<in> carrier_mat m n \<and> Q' * Q'' \<in> carrier_mat n n" 
          using diagonal_step_JNF_dim 2 by (metis mult_carrier_mat)
    qed (insert P''Q'', auto)  
  qed  
qed

lemma Diagonal_to_Smith_row_i_PQ_JNF_dim:
  assumes "P' \<in> carrier_mat m m \<and> A' \<in> carrier_mat m n \<and> Q' \<in> carrier_mat n n"
    and "Diagonal_to_Smith_row_i_PQ_JNF i bezout (P',A',Q') = (P,A,Q)"
  shows "P \<in> carrier_mat m m \<and> A \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"
  by (rule diagonal_to_Smith_i_PQ_JNF_dim, insert assms, 
      auto simp add: Diagonal_to_Smith_row_i_PQ_JNF_def)  

lemma diagonal_to_Smith_aux_PQ_JNF_dim:
  assumes "P' \<in> carrier_mat m m \<and> A' \<in> carrier_mat m n \<and> Q' \<in> carrier_mat n n"
    and "diagonal_to_Smith_aux_PQ_JNF xs bezout (P',A',Q') = (P,A,Q)"
  shows "P \<in> carrier_mat m m \<and> A \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"
  using assms 
  proof (induct xs bezout "(P',A',Q')" arbitrary: P A Q P' A' Q' rule: diagonal_to_Smith_aux_PQ_JNF.induct)
    case (1 bezout P A Q)
    then show ?case by simp
  next
    case (2 i xs bezout P' A' Q')
    let ?D="(Diagonal_to_Smith_row_i_PQ_JNF i bezout (P', A', Q'))"
    have "diagonal_to_Smith_aux_PQ_JNF (i # xs) bezout (P', A', Q') = 
      diagonal_to_Smith_aux_PQ_JNF xs bezout ?D" by auto
    hence *: "... = (P,A,Q)" using 2 by auto
    let ?P="fst ?D"
    let ?S="fst (snd ?D)"
    let ?Q="snd (snd ?D)"
    show ?case
    proof (rule "2.hyps")      
      show "Diagonal_to_Smith_row_i_PQ_JNF i bezout (P', A', Q') = (?P,?S,?Q)" by auto
      show "diagonal_to_Smith_aux_PQ_JNF xs bezout (?P, ?S, ?Q) = (P, A, Q)" using * by simp
      show "?P \<in> carrier_mat m m \<and> ?S \<in> carrier_mat m n \<and> ?Q \<in> carrier_mat n n" 
        by (rule Diagonal_to_Smith_row_i_PQ_JNF_dim, insert 2, auto)           
    qed
qed

lemma diagonal_to_Smith_PQ_JNF_dim:
  assumes "A \<in> carrier_mat m n" 
    and PSQ: "diagonal_to_Smith_PQ_JNF A bezout = (P,S,Q)"
  shows "P \<in> carrier_mat m m \<and> S \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"
  by (rule diagonal_to_Smith_aux_PQ_JNF_dim, insert assms, 
      auto simp add: diagonal_to_Smith_PQ_JNF_def)

context
  includes lifting_syntax
begin

lemma HMA_diagonal_to_Smith_PQ_JNF[transfer_rule]:
 "((Mod_Type_Connect.HMA_M) ===> (=) ===> HMA_M3) (diagonal_to_Smith_PQ_JNF) (diagonal_to_Smith_PQ)"
proof (intro rel_funI, clarify, goal_cases)
  case (1 A A' _ bezout)
  let ?xs1 = "[0..<min (dim_row A) (dim_col A) - 1]"
  let ?xs2 = "[0..<min (nrows A') (ncols A') - 1]"
  let ?PAQ="(1\<^sub>m (dim_row A), A, 1\<^sub>m (dim_col A))"
  have dr: "dim_row A = CARD('c)"
    using 1 Mod_Type_Connect.dim_row_transfer_rule by blast
  have dc: "dim_col A = CARD('b)" 
    using 1 Mod_Type_Connect.dim_col_transfer_rule by blast
  have xs_eq: "?xs1 = ?xs2"
    by (simp add: dc dr ncols_def nrows_def)
  have j_xs: "\<forall>j\<in>set ?xs1. j < min CARD('c) CARD('b)"
    using dc dr less_imp_diff_less by auto
  let ?D_JNF = "diagonal_to_Smith_aux_PQ_JNF ?xs1 bezout ?PAQ"
  let ?D_HA = "diagonal_to_Smith_aux_PQ ?xs1 bezout (mat 1, A', mat 1)"
  have mat_rel_init: "HMA_M3 ?PAQ (mat 1, A', mat 1)"
  proof -    
    have "Mod_Type_Connect.HMA_M (1\<^sub>m (dim_row A)) (mat 1::'a^'c::mod_type^'c::mod_type)" 
      unfolding dr by (transfer_prover_start,transfer_step, auto)
    moreover have "Mod_Type_Connect.HMA_M (1\<^sub>m (dim_col A)) (mat 1::'a^'b::mod_type^'b::mod_type)"
      unfolding dc by (transfer_prover_start,transfer_step, auto)
    ultimately show ?thesis using 1 by auto
  qed
  have "HMA_M3 ?D_JNF ?D_HA"
    using HMA_diagonal_to_Smith_aux_PQ_JNF[OF j_xs] mat_rel_init unfolding rel_fun_def by blast
  then show ?case using xs_eq unfolding diagonal_to_Smith_PQ_JNF_def diagonal_to_Smith_PQ_def 
    by auto 
qed

end

subsection \<open>Applying local type definitions\<close>

text \<open>Now we get the soundness lemma in JNF, via the one in HOL Analysis. I need transfer rules 
and local type definitions.\<close>

context
  includes lifting_syntax
begin


private lemma diagonal_to_Smith_PQ_JNF_with_types:
  assumes A: "A \<in> carrier_mat CARD('nr::mod_type) CARD('nc::mod_type)"
  and S: "S \<in> carrier_mat CARD('nr) CARD('nc)"
  and P: "P \<in> carrier_mat CARD('nr) CARD('nr)"
  and Q: "Q \<in> carrier_mat CARD('nc) CARD('nc)"
  and PSQ: "diagonal_to_Smith_PQ_JNF A bezout = (P, S, Q)"
  and d:"isDiagonal_mat A" and ib: "is_bezout_ext bezout"
shows "S = P * A * Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S"
proof -
  let ?P = "Mod_Type_Connect.to_hma\<^sub>m P::'a^'nr::mod_type^'nr::mod_type"
  let ?A = "Mod_Type_Connect.to_hma\<^sub>m A::'a^'nc::mod_type^'nr::mod_type"
  let ?Q = "Mod_Type_Connect.to_hma\<^sub>m Q::'a^'nc::mod_type^'nc::mod_type"
  let ?S = "Mod_Type_Connect.to_hma\<^sub>m S::'a^'nc::mod_type^'nr::mod_type"
  have [transfer_rule]: "Mod_Type_Connect.HMA_M A ?A"
    by (simp add: Mod_Type_Connect.HMA_M_def A)
  moreover have [transfer_rule]: "Mod_Type_Connect.HMA_M P ?P"
    by (simp add: Mod_Type_Connect.HMA_M_def P)  
  moreover have [transfer_rule]: "Mod_Type_Connect.HMA_M Q ?Q"
    by (simp add: Mod_Type_Connect.HMA_M_def Q)
  moreover have [transfer_rule]: "Mod_Type_Connect.HMA_M S ?S"
    by (simp add: Mod_Type_Connect.HMA_M_def S)
  ultimately have [transfer_rule]: "HMA_M3 (P,S,Q) (?P,?S,?Q)" by simp
  have [transfer_rule]: "bezout = bezout" ..
  have PSQ2: "(?P,?S,?Q) = diagonal_to_Smith_PQ ?A bezout" by (transfer, insert PSQ, auto)  
  have "?S = ?P**?A**?Q \<and> invertible ?P \<and> invertible ?Q \<and> Smith_normal_form ?S"
    by (rule diagonal_to_Smith_PQ'[OF _ ib PSQ2], transfer, auto simp add: d)  
  with this[untransferred] show ?thesis by auto  
qed


private lemma diagonal_to_Smith_PQ_JNF_mod_ring_with_types:
  assumes A: "A \<in> carrier_mat CARD('nr::nontriv mod_ring) CARD('nc::nontriv mod_ring)"
  and S: "S \<in> carrier_mat CARD('nr mod_ring) CARD('nc mod_ring)"
  and P: "P \<in> carrier_mat CARD('nr mod_ring) CARD('nr mod_ring)"
  and Q: "Q \<in> carrier_mat CARD('nc mod_ring) CARD('nc mod_ring)"
  and PSQ: "diagonal_to_Smith_PQ_JNF A bezout = (P, S, Q)"
  and d:"isDiagonal_mat A" and ib: "is_bezout_ext bezout"
shows "S = P * A * Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S"
  by (rule diagonal_to_Smith_PQ_JNF_with_types[OF assms])


(*I don't know how to internalize the sort constraint of 'nr and 'nc at once,
so I do it in two steps.*)
thm diagonal_to_Smith_PQ_JNF_mod_ring_with_types[unfolded CARD_mod_ring, 
      internalize_sort "'nr::nontriv"]

private lemma diagonal_to_Smith_PQ_JNF_internalized_first:
  "class.nontriv TYPE('a::type) \<Longrightarrow>
  A \<in> carrier_mat CARD('a) CARD('nc::nontriv) \<Longrightarrow>
  S \<in> carrier_mat CARD('a) CARD('nc) \<Longrightarrow>
  P \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow>
  Q \<in> carrier_mat CARD('nc) CARD('nc) \<Longrightarrow>
  diagonal_to_Smith_PQ_JNF A bezout = (P, S, Q) \<Longrightarrow>
  isDiagonal_mat A \<Longrightarrow> is_bezout_ext bezout \<Longrightarrow> 
  S = P * A * Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S"
  using diagonal_to_Smith_PQ_JNF_mod_ring_with_types[unfolded CARD_mod_ring, 
      internalize_sort "'nr::nontriv"] by blast


private lemma diagonal_to_Smith_PQ_JNF_internalized:
  "class.nontriv TYPE('c::type) \<Longrightarrow>
  class.nontriv TYPE('a::type) \<Longrightarrow>
  A \<in> carrier_mat CARD('a) CARD('c) \<Longrightarrow>
  S \<in> carrier_mat CARD('a) CARD('c) \<Longrightarrow>
  P \<in> carrier_mat CARD('a) CARD('a) \<Longrightarrow>
  Q \<in> carrier_mat CARD('c) CARD('c) \<Longrightarrow>
  diagonal_to_Smith_PQ_JNF A bezout = (P, S, Q) \<Longrightarrow>
  isDiagonal_mat A \<Longrightarrow> is_bezout_ext bezout \<Longrightarrow> 
S = P * A * Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S"
  using diagonal_to_Smith_PQ_JNF_internalized_first[internalize_sort "'nc::nontriv"] by blast


context
  fixes m::nat and n::nat
  assumes local_typedef1: "\<exists>(Rep :: ('b \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<m :: int}"
  assumes local_typedef2: "\<exists>(Rep :: ('c \<Rightarrow> int)) Abs. type_definition Rep Abs {0..<n :: int}"
  and m: "m>1"
  and n: "n>1"
begin

lemma type_to_set1:
  shows "class.nontriv TYPE('b)" (is ?a) and "m=CARD('b)" (is ?b)
proof -
  from local_typedef1 obtain Rep::"('b \<Rightarrow> int)" and Abs 
    where t: "type_definition Rep Abs {0..<m :: int}" by auto
  have "card (UNIV :: 'b set) = card {0..<m}" using t type_definition.card by fastforce
  also have "... = m" by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using m by auto
qed

lemma type_to_set2:
  shows "class.nontriv TYPE('c)" (is ?a) and "n=CARD('c)" (is ?b)
proof -
  from local_typedef2 obtain Rep::"('c \<Rightarrow> int)" and Abs 
    where t: "type_definition Rep Abs {0..<n :: int}" by blast
  have "card (UNIV :: 'c set) = card {0..<n}" using t type_definition.card by force
  also have "... = n" by auto
  finally show ?b ..
  then show ?a unfolding class.nontriv_def using n by auto
qed

lemma diagonal_to_Smith_PQ_JNF_local_typedef:  
  assumes A: "isDiagonal_mat A" and ib: "is_bezout_ext bezout"
  and A_dim: "A \<in> carrier_mat m n"
  assumes PSQ: "(P,S,Q) = diagonal_to_Smith_PQ_JNF A bezout"
  shows "S = P*A*Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S
  \<and> P \<in> carrier_mat m m \<and> S \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"  
proof -  
  have dim_matrices: "P \<in> carrier_mat m m \<and> S \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n" 
    by (rule diagonal_to_Smith_PQ_JNF_dim[OF A_dim PSQ[symmetric]])
  show ?thesis
  using diagonal_to_Smith_PQ_JNF_internalized[where ?'c='c, where ?'a='b, 
      OF type_to_set2(1) type_to_set(1), of m A S P Q]  
  unfolding type_to_set1(2)[symmetric] type_to_set2(2)[symmetric] 
  using assms m dim_matrices local_typedef1 by auto
qed
end
end

(*Canceling the first local type definitions (I was not able to cancel both in one step)*)
context
begin
private lemma diagonal_to_Smith_PQ_JNF_canceled_first:
  "\<exists>Rep Abs. type_definition Rep Abs {0..<int n} \<Longrightarrow> {0..<int m} \<noteq> {} \<Longrightarrow>
  1 < m \<Longrightarrow> 1 < n \<Longrightarrow> isDiagonal_mat A \<Longrightarrow> is_bezout_ext bezout \<Longrightarrow>
  A \<in> carrier_mat m n \<Longrightarrow> (P, S, Q) = diagonal_to_Smith_PQ_JNF A bezout \<Longrightarrow>
  S = P * A * Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S 
  \<and> P \<in> carrier_mat m m \<and> S \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"
  using diagonal_to_Smith_PQ_JNF_local_typedef[cancel_type_definition] by blast

(*Canceling the second*)
private lemma diagonal_to_Smith_PQ_JNF_canceled_both:
  "{0..<int n} \<noteq> {} \<Longrightarrow> {0..<int m} \<noteq> {} \<Longrightarrow> 1 < m \<Longrightarrow> 1 < n \<Longrightarrow>
  isDiagonal_mat A \<Longrightarrow> is_bezout_ext bezout \<Longrightarrow> A \<in> carrier_mat m n \<Longrightarrow>
  (P, S, Q) = diagonal_to_Smith_PQ_JNF A bezout \<Longrightarrow> S = P * A * Q \<and>
  invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S 
  \<and> P \<in> carrier_mat m m \<and> S \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"
  using diagonal_to_Smith_PQ_JNF_canceled_first[cancel_type_definition] by blast

subsection \<open>The final result\<close>

lemma diagonal_to_Smith_PQ_JNF:  
  assumes A: "isDiagonal_mat A" and ib: "is_bezout_ext bezout"
  and "A \<in> carrier_mat m n" 
  and PBQ: "(P,S,Q) = diagonal_to_Smith_PQ_JNF A bezout" 
(*The following two assumptions appear since mod_type requires 1<CARD. 
Those cases could be treated separately.*)
  and n: "n>1" and m: "m>1" 
  shows "S = P*A*Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S
  \<and> P \<in> carrier_mat m m \<and> S \<in> carrier_mat m n \<and> Q \<in> carrier_mat n n"   
  using diagonal_to_Smith_PQ_JNF_canceled_both[OF _ _ m n] using assms by force
end
end
