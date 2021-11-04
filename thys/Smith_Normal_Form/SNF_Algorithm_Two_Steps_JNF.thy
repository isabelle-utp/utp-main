(*
  Author: Jose Divasón
  Email:  jose.divason@unirioja.es
*)

section \<open>Smith normal form algorithm based on two steps in JNF\<close>

theory SNF_Algorithm_Two_Steps_JNF
  imports   
  Diagonalize
  Diagonal_To_Smith_JNF
begin

subsection \<open>Moving the result from HOL Analysis to JNF\<close>
context diagonalize
begin

definition "Smith_normal_form_of_JNF A bezout = (
   let (P'',D,Q'') = diagonalize_JNF A bezout;
       (P',S,Q') = diagonal_to_Smith_PQ_JNF D bezout
   in (P'*P'',S,Q''*Q')
  )"

(*Soundness theorem in the JNF library*)

lemma Smith_normal_form_of_JNF_soundness:
  assumes b: "is_bezout_ext bezout" and A: "A \<in> carrier_mat m n"
  and n: "1 < n" and m: "1 < m" (*Same as previously, those assumptions arose from the requirements 
of mod_type. They could be dropped proving them as particular cases*)
  and PSQ: "Smith_normal_form_of_JNF A bezout = (P,S,Q)"
shows "S = P*A*Q \<and> invertible_mat P \<and> invertible_mat Q \<and> Smith_normal_form_mat S
  \<and> P \<in> carrier_mat m m \<and> S \<in> carrier_mat m n \<and> Q\<in> carrier_mat n n"   
proof -
  obtain P'' D Q'' where PDQ_diag: "(P'',D,Q'') = diagonalize_JNF A bezout"
    by (metis prod_cases3)
  have 1: "invertible_mat P'' \<and> invertible_mat Q'' \<and> isDiagonal_mat D \<and> D = P''*A*Q''
      \<and> P'' \<in> carrier_mat m m \<and> Q'' \<in> carrier_mat n n \<and> D \<in> carrier_mat m n"
    using soundness_diagonalize_JNF'[OF b A PDQ_diag[symmetric]] by auto    
  obtain P' Q' where PSQ_D: "(P',S,Q') = diagonal_to_Smith_PQ_JNF D bezout"
    using PSQ PDQ_diag unfolding Smith_normal_form_of_JNF_def Let_def split_beta
    by (metis Pair_inject prod.collapse)
  have 2: "invertible_mat P' \<and> invertible_mat Q' \<and> Smith_normal_form_mat S \<and> S = P'*D*Q'
    \<and> P' \<in> carrier_mat m m \<and> Q' \<in> carrier_mat n n \<and> S \<in> carrier_mat m n"
    using diagonal_to_Smith_PQ_JNF[OF _ b _ PSQ_D n m] 1 n m by auto
  have P: "P = P'*P''"
    by (metis (no_types, lifting) PDQ_diag PSQ PSQ_D Smith_normal_form_of_JNF_def fst_conv prod.simps(2))    
  have Q: "Q = Q''*Q'"
    by (metis (no_types, lifting) PDQ_diag PSQ PSQ_D Smith_normal_form_of_JNF_def snd_conv prod.simps(2))
  have "S = P'*(P''*A*Q'')*Q'" using 1 2 by auto
  also have "... = (P'*P'')*A*(Q''*Q')" 
    by (smt "1" "2" A assoc_mult_mat carrier_matD carrier_mat_triv index_mult_mat)
  finally have "S = (P' * P'') * A * (Q'' * Q')" .
  moreover have "invertible_mat P" unfolding P by (rule invertible_mult_JNF, insert 1 2, auto)
  moreover have "invertible_mat Q" unfolding Q by (rule invertible_mult_JNF, insert 1 2, auto)
  ultimately show ?thesis using 1 2 P Q by auto
qed

end
end