(*
    Author:      Jose Divasón
    Email:       jose.divason@unirioja.es           
*)

section \<open>Diagonalizing matrices in JNF and HOL Analysis\<close>

theory Diagonalize
  imports Admits_SNF_From_Diagonal_Iff_Bezout_Ring
begin


text \<open>This section presents a @{text "locale"} that assumes a sound operation to make a matrix
diagonal. Then, the result is transferred to HOL Analysis.\<close>

subsection \<open>Diagonalizing matrices in JNF\<close>

text \<open>We assume a @{text "diagonalize_JNF"} operation in JNF, which is applied to matrices over
a B\'ezout ring. However, probably a more restrictive type class is required.\<close>

locale diagonalize =
  fixes diagonalize_JNF :: "'a::bezout_ring mat \<Rightarrow> 'a bezout \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat)"
  assumes soundness_diagonalize_JNF: 
    "\<forall>A bezout. A \<in> carrier_mat m n \<and> is_bezout_ext bezout \<longrightarrow>
     (case diagonalize_JNF A bezout of (P,S,Q) \<Rightarrow>    
      P \<in> carrier_mat m m \<and> Q \<in> carrier_mat n n \<and> S \<in> carrier_mat m n 
      \<and> invertible_mat P \<and> invertible_mat Q \<and> isDiagonal_mat S \<and> S = P*A*Q)"
begin

lemma soundness_diagonalize_JNF':
  fixes A::"'a mat"
  assumes "is_bezout_ext bezout" and "A \<in> carrier_mat m n"
  and "diagonalize_JNF A bezout = (P,S,Q)"
  shows "P \<in> carrier_mat m m \<and> Q \<in> carrier_mat n n \<and> S \<in> carrier_mat m n 
      \<and> invertible_mat P \<and> invertible_mat Q \<and> isDiagonal_mat S \<and> S = P*A*Q"
  using soundness_diagonalize_JNF assms unfolding case_prod_beta by (metis fst_conv snd_conv)


subsection \<open>Implementation and soundness result moved to HOL Analysis.\<close>

definition diagonalize :: "'a::bezout_ring ^ 'nc :: mod_type ^ 'nr :: mod_type
     \<Rightarrow> 'a bezout \<Rightarrow> 
    (('a ^ 'nr :: mod_type ^ 'nr :: mod_type) 
    \<times> ('a ^ 'nc :: mod_type ^ 'nr :: mod_type) 
    \<times> ('a ^ 'nc :: mod_type ^ 'nc :: mod_type))"
  where "diagonalize A bezout = (
    let (P,S,Q) = diagonalize_JNF (Mod_Type_Connect.from_hma\<^sub>m A) bezout
    in (Mod_Type_Connect.to_hma\<^sub>m P,Mod_Type_Connect.to_hma\<^sub>m S,Mod_Type_Connect.to_hma\<^sub>m Q)
  )"

lemma soundness_diagonalize:
  assumes b: "is_bezout_ext bezout"
  and d: "diagonalize A bezout = (P,S,Q)"
shows "invertible P \<and> invertible Q \<and> isDiagonal S \<and> S = P**A**Q"
proof -
  define A' where "A' = Mod_Type_Connect.from_hma\<^sub>m A"  
  obtain P' S' Q' where d_JNF: "(P',S',Q') = diagonalize_JNF A' bezout"
    by (metis prod_cases3)
  define m and n where "m = dim_row A'" and "n = dim_col A'"
  hence A': "A' \<in> carrier_mat m n" by auto
  have res_JNF: "P' \<in> carrier_mat m m \<and> Q' \<in> carrier_mat n n \<and> S' \<in> carrier_mat m n 
      \<and> invertible_mat P' \<and> invertible_mat Q' \<and> isDiagonal_mat S' \<and> S' = P'*A'*Q'"
    by (rule soundness_diagonalize_JNF'[OF b A' d_JNF[symmetric]])
  have "Mod_Type_Connect.to_hma\<^sub>m P' = P" using d unfolding diagonalize_def Let_def
    by (metis A'_def d_JNF fst_conv old.prod.case)
  hence "P' = Mod_Type_Connect.from_hma\<^sub>m P" using A'_def m_def res_JNF by auto
  hence [transfer_rule]: "Mod_Type_Connect.HMA_M P' P" 
    unfolding Mod_Type_Connect.HMA_M_def by auto
  have "Mod_Type_Connect.to_hma\<^sub>m Q' = Q" using d unfolding diagonalize_def Let_def
    by (metis A'_def d_JNF snd_conv old.prod.case)
  hence "Q' = Mod_Type_Connect.from_hma\<^sub>m Q" using A'_def n_def res_JNF by auto
  hence [transfer_rule]: "Mod_Type_Connect.HMA_M Q' Q"
    unfolding Mod_Type_Connect.HMA_M_def by auto
  have "Mod_Type_Connect.to_hma\<^sub>m S' = S" using d unfolding diagonalize_def Let_def
    by (metis A'_def d_JNF snd_conv old.prod.case)
  hence "S' = Mod_Type_Connect.from_hma\<^sub>m S" using A'_def m_def n_def res_JNF by auto
  hence [transfer_rule]: "Mod_Type_Connect.HMA_M S' S"
    unfolding Mod_Type_Connect.HMA_M_def by auto
  have [transfer_rule]: "Mod_Type_Connect.HMA_M A' A"
    using A'_def unfolding Mod_Type_Connect.HMA_M_def by auto
  have "invertible P" using res_JNF by (transfer, simp)
  moreover have "invertible Q" using res_JNF by (transfer, simp)
  moreover have "isDiagonal S" using res_JNF by (transfer, simp)
  moreover have "S = P**A**Q" using res_JNF by (transfer, simp)
  ultimately show ?thesis by simp
qed
end

end