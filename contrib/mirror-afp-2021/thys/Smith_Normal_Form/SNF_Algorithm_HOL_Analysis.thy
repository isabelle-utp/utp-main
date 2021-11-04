(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>The Smith normal form algorithm in HOL Analysis\<close>

theory SNF_Algorithm_HOL_Analysis
  imports
    SNF_Algorithm
    Admits_SNF_From_Diagonal_Iff_Bezout_Ring
begin

subsection \<open>Transferring the result from JNF to HOL Anaylsis\<close>

(*Now, we transfer the algorithm to HMA and get the final lemma.*)

definition Smith_mxn_HMA :: "(('a::comm_ring_1^2) \<Rightarrow> (('a^2) \<times> ('a^2^2)))
   \<Rightarrow> (('a^2^2) \<Rightarrow> (('a^2^2) \<times> ('a^2^2) \<times> ('a^2^2))) \<Rightarrow> ('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> ('a^'n::mod_type^'m::mod_type) 
  \<Rightarrow> (('a^'m::mod_type^'m::mod_type)\<times> ('a^'n::mod_type^'m::mod_type) \<times> ('a^'n::mod_type^'n::mod_type))"
  where
"Smith_mxn_HMA Smith_1x2 Smith_2x2 div_op A =
  (let Smith_1x2_JNF = (\<lambda>A'. let (S',Q') = Smith_1x2 (Mod_Type_Connect.to_hma\<^sub>v (Matrix.row A' 0))
                        in (mat_of_row (Mod_Type_Connect.from_hma\<^sub>v S'), Mod_Type_Connect.from_hma\<^sub>m Q'));
       Smith_2x2_JNF = (\<lambda>A'. let (P', S',Q') = Smith_2x2 (Mod_Type_Connect.to_hma\<^sub>m A') 
                        in (Mod_Type_Connect.from_hma\<^sub>m P', Mod_Type_Connect.from_hma\<^sub>m S', Mod_Type_Connect.from_hma\<^sub>m Q'));
       (P,S,Q) = Smith_Impl.Smith_mxn Smith_1x2_JNF Smith_2x2_JNF div_op (Mod_Type_Connect.from_hma\<^sub>m A)
  in (Mod_Type_Connect.to_hma\<^sub>m P, Mod_Type_Connect.to_hma\<^sub>m S, Mod_Type_Connect.to_hma\<^sub>m Q)
  )"


definition "is_SNF_HMA A R = (case R of (P,S,Q) \<Rightarrow> 
   invertible P \<and> invertible Q 
  \<and> Smith_normal_form S \<and> S = P ** A ** Q)"

subsection \<open>Soundness in HOL Anaylsis\<close>

lemma is_SNF_Smith_mxn_HMA:
  fixes A::"'a::comm_ring_1 ^ 'n::mod_type ^ 'm::mod_type"
  assumes PSQ: "(P,S,Q) = Smith_mxn_HMA Smith_1x2 Smith_2x2 div_op A"
  and SNF_1x2_works: "\<forall>A. let (S',Q) = Smith_1x2 A in S' $h 1 = 0 \<and> invertible Q \<and> S' = A v* Q"
    and SNF_2x2_works: "\<forall>A. is_SNF_HMA A (Smith_2x2 A)"
    and d: "is_div_op div_op"
  shows "is_SNF_HMA A (P,S,Q)"
proof -
  let ?A = "Mod_Type_Connect.from_hma\<^sub>m A"
  define Smith_1x2_JNF where "Smith_1x2_JNF = (\<lambda>A'. let (S',Q') 
    = Smith_1x2 (Mod_Type_Connect.to_hma\<^sub>v (Matrix.row A' 0))
    in (mat_of_row (Mod_Type_Connect.from_hma\<^sub>v S'), Mod_Type_Connect.from_hma\<^sub>m Q'))"
  define Smith_2x2_JNF where "Smith_2x2_JNF = (\<lambda>A'. let (P', S',Q') = Smith_2x2 (Mod_Type_Connect.to_hma\<^sub>m A') 
    in (Mod_Type_Connect.from_hma\<^sub>m P', Mod_Type_Connect.from_hma\<^sub>m S', Mod_Type_Connect.from_hma\<^sub>m Q'))"
  obtain P' S' Q' where P'S'Q': "(P',S',Q') = Smith_Impl.Smith_mxn Smith_1x2_JNF Smith_2x2_JNF div_op ?A"    
    by (metis prod_cases3)
  have PSQ_P'S'Q': "(P,S,Q) = 
      (Mod_Type_Connect.to_hma\<^sub>m P', Mod_Type_Connect.to_hma\<^sub>m S', Mod_Type_Connect.to_hma\<^sub>m Q')"
    using PSQ P'S'Q' Smith_1x2_JNF_def Smith_2x2_JNF_def 
    unfolding Smith_mxn_HMA_def Let_def by (metis case_prod_conv)
  have SNF_1x2_works': "\<forall>(A::'a mat) \<in> carrier_mat 1 2. is_SNF A (1\<^sub>m 1, (Smith_1x2_JNF A))" 
  proof (rule+)
    fix A'::"'a mat" assume A': "A' \<in> carrier_mat 1 2" 
    let ?A' = "(Mod_Type_Connect.to_hma\<^sub>v (Matrix.row A' 0))::'a^2"    
    obtain S2 Q2 where S'Q': "(S2,Q2) = Smith_1x2 ?A'"       
      by (metis surjective_pairing)
    let ?S2 = "(Mod_Type_Connect.from_hma\<^sub>v S2)"
    let ?S' = "mat_of_row ?S2"
    let ?Q' = "Mod_Type_Connect.from_hma\<^sub>m Q2"
    have [transfer_rule]: "Mod_Type_Connect.HMA_V ?S2 S2"
      unfolding Mod_Type_Connect.HMA_V_def by auto
    have [transfer_rule]: "Mod_Type_Connect.HMA_M ?Q' Q2"
      unfolding Mod_Type_Connect.HMA_M_def by auto
    have [transfer_rule]: "Mod_Type_Connect.HMA_I 1 (1::2)"
      unfolding Mod_Type_Connect.HMA_I_def by (simp add: to_nat_1)
    have c[transfer_rule]: "Mod_Type_Connect.HMA_V ((Matrix.row A' 0)) ?A'" 
      unfolding Mod_Type_Connect.HMA_V_def 
      by (rule from_hma_to_hma\<^sub>v[symmetric], insert A', auto simp add: Matrix.row_def)      
    have *: "Smith_1x2_JNF A' = (?S', ?Q')" by (metis Smith_1x2_JNF_def S'Q' case_prod_conv)    
    show "is_SNF A' (1\<^sub>m 1, Smith_1x2_JNF A')" unfolding *
    proof (rule is_SNF_intro)
      let ?row_A' = "(Matrix.row A' 0)"
      have w: "S2 $h 1 = 0 \<and> invertible Q2 \<and> S2 = ?A' v* Q2"
        using SNF_1x2_works by (metis (mono_tags, lifting) S'Q' fst_conv prod.case_eq_if snd_conv)      
      have "?S2 $v 1 = 0" using w[untransferred] by auto      
      thus "Smith_normal_form_mat ?S'" unfolding Smith_normal_form_mat_def isDiagonal_mat_def
        by (auto simp add: less_2_cases_iff)
      have S2_Q2_A: "S2 = transpose Q2 *v ?A'" using w transpose_matrix_vector by auto      
      have S2_Q2_A': "?S2 = transpose_mat ?Q' *\<^sub>v ((Matrix.row A' 0))" using S2_Q2_A by transfer'      
      show "1\<^sub>m 1 \<in> carrier_mat (dim_row A') (dim_row A')" using A' by auto
      show "?Q' \<in> carrier_mat (dim_col A') (dim_col A')" using A' by auto
      show "invertible_mat (1\<^sub>m 1)" by auto
      show "invertible_mat ?Q'" using w[untransferred] by auto
      have "?S' = A' * ?Q'" 
      proof (rule eq_matI)
        show "dim_row ?S' = dim_row (A' * ?Q')" and "dim_col ?S' = dim_col (A' * ?Q')"
          using A' by auto
        fix i j assume i: "i < dim_row (A' * ?Q')" and j: "j < dim_col (A' * ?Q')"
        have "?S' $$ (i, j) = ?S' $$ (0, j)"
          by (metis A' One_nat_def carrier_matD(1) i index_mult_mat(2) less_Suc0)
        also have "... =?S2 $v j" using j by auto
        also have "... = (transpose_mat ?Q' *\<^sub>v ?row_A') $v j" unfolding S2_Q2_A' by simp
        also have "... = Matrix.row (transpose_mat ?Q') j \<bullet> ?row_A'"
          by (rule index_mult_mat_vec, insert j, auto)
        also have "... = Matrix.col ?Q' j \<bullet> ?row_A'" using j by auto
        also have "... = ?row_A' \<bullet> Matrix.col ?Q' j" 
          by (metis (no_types, lifting) Mod_Type_Connect.HMA_V_def Mod_Type_Connect.from_hma\<^sub>m_def 
              Mod_Type_Connect.from_hma\<^sub>v_def c col_def comm_scalar_prod dim_row_mat(1) vec_carrier)       
        also have "... = (A' * ?Q') $$ (0, j)" using A' j by auto
        finally show "?S' $$ (i, j) = (A' * ?Q') $$ (i, j)" using i j A' by auto
      qed
      thus "?S' = 1\<^sub>m 1 * A' * ?Q'" using A' by auto
    qed
  qed
  have SNF_2x2_works': "\<forall>(A::'a mat) \<in> carrier_mat 2 2. is_SNF A (Smith_2x2_JNF A)"
  proof 
    fix A'::"'a mat" assume A': "A' \<in> carrier_mat 2 2"
    let ?A' = "Mod_Type_Connect.to_hma\<^sub>m A'::'a^2^2"
    obtain P2 S2 Q2 where P2S2Q2: "(P2, S2, Q2) = Smith_2x2 ?A'"
      by (metis prod_cases3)
    let ?P2 = "Mod_Type_Connect.from_hma\<^sub>m P2" 
    let ?S2 = "Mod_Type_Connect.from_hma\<^sub>m S2"
    let ?Q2 = "Mod_Type_Connect.from_hma\<^sub>m Q2"    
    have [transfer_rule]: "Mod_Type_Connect.HMA_M ?Q2 Q2"
      and [transfer_rule]: "Mod_Type_Connect.HMA_M ?P2 P2"
      and [transfer_rule]: "Mod_Type_Connect.HMA_M ?S2 S2"
      and [transfer_rule]: "Mod_Type_Connect.HMA_M A' ?A'"
      unfolding Mod_Type_Connect.HMA_M_def using A' by auto
    have "is_SNF A' (?P2,?S2,?Q2)"
    proof -
      have P2: "?P2 \<in> carrier_mat (dim_row A') (dim_row A')" and 
        Q2: "?Q2 \<in> carrier_mat (dim_col A') (dim_col A')" using A' by auto
      have "is_SNF_HMA ?A' (P2,S2,Q2)" using SNF_2x2_works by (simp add: P2S2Q2)
      hence "invertible P2 \<and> invertible Q2 \<and> Smith_normal_form S2 \<and> S2 = P2 ** ?A' ** Q2"
        unfolding is_SNF_HMA_def by auto
      from this[untransferred] show ?thesis using P2 Q2 unfolding is_SNF_def by auto
    qed
    thus "is_SNF A' (Smith_2x2_JNF A')" using P2S2Q2 by (metis Smith_2x2_JNF_def case_prod_conv) 
  qed  
  interpret Smith_Impl Smith_1x2_JNF Smith_2x2_JNF div_op
    using SNF_2x2_works' SNF_1x2_works' d by (unfold_locales, auto)
  have A: "?A \<in> carrier_mat CARD('m) CARD('n)" by auto
  have "is_SNF ?A (Smith_Impl.Smith_mxn Smith_1x2_JNF Smith_2x2_JNF div_op ?A)"
    by (rule is_SNF_Smith_mxn[OF A])
  hence inv_P': "invertible_mat P'" 
    and Smith_S': "Smith_normal_form_mat S'" and inv_Q': "invertible_mat Q'" 
    and S'_P'AQ': "S' = P' * ?A * Q'" 
    and P': "P' \<in> carrier_mat (dim_row ?A) (dim_row ?A)"
    and Q': "Q' \<in> carrier_mat (dim_col ?A) (dim_col ?A)"
    unfolding is_SNF_def P'S'Q'[symmetric] by auto
  have S': "S' \<in> carrier_mat (dim_row ?A) (dim_col ?A)" using P' Q' S'_P'AQ' by auto
  have [transfer_rule]: "Mod_Type_Connect.HMA_M P' P"    
  and [transfer_rule]: "Mod_Type_Connect.HMA_M S' S" 
  and [transfer_rule]: "Mod_Type_Connect.HMA_M Q' Q" 
  and [transfer_rule]: "Mod_Type_Connect.HMA_M ?A A" 
    unfolding Mod_Type_Connect.HMA_M_def using PSQ_P'S'Q'
    using from_hma_to_hma\<^sub>m[symmetric] P' A Q' S' by auto
  have inv_Q: "invertible Q" using inv_Q' by transfer
  moreover have Smith_S: "Smith_normal_form S" using Smith_S' by transfer
  moreover have inv_P: "invertible P" using inv_P' by transfer
  moreover have "S = P ** A ** Q" using S'_P'AQ' by transfer
  thus ?thesis using inv_Q inv_P Smith_S unfolding is_SNF_HMA_def by auto
qed
end