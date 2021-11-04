(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Smith normal form algorithm based on two steps in HOL Analysis\<close>

theory SNF_Algorithm_Two_Steps
  imports Diagonalize
begin


text \<open>This file contains an algorithm to transform a matrix to its Smith normal form, based 
on two steps: first it is converted into a diagonal matrix and then transformed from diagonal
to Smith.

We assume the existence of a diagonalize operation, and then we just have to connect it to the 
existing algorithm (in HOL Analysis) to transform a diagonal matrix into its Smith normal form.
\<close>

subsection \<open>The implementation\<close>

context diagonalize
begin

definition "Smith_normal_form_of A bezout = (
   let (P'',D,Q'') = diagonalize A bezout;
       (P',S,Q') = diagonal_to_Smith_PQ D bezout
   in (P'**P'',S,Q''**Q')
  )"

subsection \<open>Soundness in HOL Analysis\<close>

lemma Smith_normal_form_of_soundness:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" 
  assumes b: "is_bezout_ext bezout"
  assumes PSQ: "(P,S,Q) = Smith_normal_form_of A bezout"
  shows "S = P**A**Q \<and> invertible P \<and> invertible Q \<and> Smith_normal_form S"   
proof -
  obtain P'' D Q'' where PDQ_diag: "(P'',D,Q'') = diagonalize A bezout"
    by (metis prod_cases3)
  have 1: "invertible P'' \<and> invertible Q'' \<and> isDiagonal D \<and> D = P''**A**Q''" 
    by (rule soundness_diagonalize[OF b PDQ_diag[symmetric]])
  obtain P' Q' where PSQ_D: "(P',S,Q') = diagonal_to_Smith_PQ D bezout"
    using PSQ PDQ_diag unfolding Smith_normal_form_of_def
    unfolding Let_def by (smt Pair_inject case_prod_beta' surjective_pairing)    
  have 2: "invertible P' \<and> invertible Q' \<and> Smith_normal_form S \<and> S = P'**D**Q'"
    using diagonal_to_Smith_PQ' 1 b PSQ_D by blast
  have P: "P = P'**P''"
    by (metis (mono_tags, lifting) PDQ_diag PSQ_D Pair_inject 
        Smith_normal_form_of_def PSQ old.prod.case)
  have Q: "Q = Q''**Q'"
    by (metis (mono_tags, lifting) PDQ_diag PSQ_D Pair_inject 
        Smith_normal_form_of_def PSQ old.prod.case)
  have "S = P**A**Q" using 1 2 by (simp add: P Q matrix_mul_assoc)
  moreover have "invertible P" using P by (simp add: 1 2 invertible_mult)
  moreover have "invertible Q" using Q by (simp add: 1 2 invertible_mult)
  ultimately show ?thesis using 2 by auto
qed

end
end