(*
    Author:      Jose Divasón
    Email:       jose.divason@unirioja.es
*)

section \<open>A certified checker based on an external algorithm to compute Smith normal form\<close>

theory Smith_Certified
  imports
    SNF_Algorithm_Euclidean_Domain
begin

text\<open>This (unspecified) function takes as input the matrix $A$ and returns five matrices
$(P,S,Q,P',Q')$, which must satisfy $S = PAQ$, $S$ is in Smith normal form, $P'$ and $Q'$
are the inverse matrices of $P$ and $Q$ respectively\<close>

text\<open>The matrices are given in terms of lists for the sake of simplicity when connecting the
function to external solvers, like Mathematica or Sage.\<close>

consts external_SNF ::
  "int list list \<Rightarrow> int list list \<times> int list list \<times> int list list \<times> int list list \<times> int list list"


text \<open>We implement the checker by means of the following definition. The checker is implemented
in the JNF representation of matrices to make use of the Strassen matrix multiplication algorithm.
In case that the certification fails, then the verified Smith normal form algorithm is executed.
Thus, we will always get a verified result.\<close>

definition "checker_SNF A = (
    let A' = mat_to_list A; m = dim_row A; n = dim_col A in
      case external_SNF A' of (P_ext,S_ext,Q_ext,P'_ext,Q'_ext) \<Rightarrow> let
          P = mat_of_rows_list m P_ext;
          S = mat_of_rows_list m S_ext;
          Q = mat_of_rows_list m Q_ext;
          P' = mat_of_rows_list m P'_ext;
          Q' = mat_of_rows_list m Q'_ext in
            (if dim_row P = m \<and> dim_col P = m
              \<and> dim_row S = m \<and> dim_col S = n
              \<and> dim_row Q = n \<and> dim_col Q = n
              \<and> dim_row P' = m \<and> dim_col P' = m
              \<and> dim_row Q' = n \<and> dim_col Q' = n
              \<and> P * P' = 1\<^sub>m m \<and> Q * Q' = 1\<^sub>m n
              \<and> Smith_normal_form_mat S \<and> (S = P*A*Q) then
      (P,S,Q) else Code.abort (STR ''Certification failed'') (\<lambda> _. Smith_ED_mxn A))
)"

theorem checker_SNF_soudness:
  assumes A: "A \<in> carrier_mat m n"
    and c: "checker_SNF A = (P,S,Q)"
  shows "is_SNF A (P,S,Q)"
proof -
  let ?ext = "external_SNF (mat_to_list A)"
  obtain P_ext S_ext Q_ext P'_ext Q'_ext where ext: "?ext = (P_ext,S_ext,Q_ext,P'_ext,Q'_ext)"
    by (cases "?ext", auto)
  let ?case_external = "let
          P = mat_of_rows_list m P_ext;
          S = mat_of_rows_list m S_ext;
          Q = mat_of_rows_list n Q_ext;
          P' = mat_of_rows_list m P'_ext;
          Q' = mat_of_rows_list n Q'_ext in
            (dim_row P = m \<and> dim_col P = m
              \<and> dim_row S = m \<and> dim_col S = n
              \<and> dim_row Q = n \<and> dim_col Q = n
              \<and> dim_row P' = m \<and> dim_col P' = m
              \<and> dim_row Q' = n \<and> dim_col Q' = n
              \<and> P * P' = 1\<^sub>m m \<and> Q * Q' = 1\<^sub>m n
              \<and> Smith_normal_form_mat S \<and> (S = P*A*Q))"
  show ?thesis
  proof (cases ?case_external)
    case True
    define P' where "P' = mat_of_rows_list m P'_ext"
    define Q' where "Q' = mat_of_rows_list m Q'_ext"
    have S_PAQ: "S = P * A * Q "
      and SNF_S: "Smith_normal_form_mat S" and PP'_1: "P * P' = 1\<^sub>m m" and QQ'_1: "Q * Q' = 1\<^sub>m n"
      and sm_P: "square_mat P" and sm_Q: "square_mat Q"
      using ext True c A
      unfolding checker_SNF_def Let_def mat_of_rows_list_def P'_def Q'_def
      by (auto split: if_splits)
    have inv_P: "invertible_mat P"
    proof (unfold invertible_mat_def, rule conjI, rule sm_P,
        unfold inverts_mat_def, rule exI[of _ P'], rule conjI)
      show *: "P * P' = 1\<^sub>m (dim_row P)"
        by (metis PP'_1 True index_mult_mat(2))
      show "P' * P = 1\<^sub>m (dim_row P')"
      proof (rule mat_mult_left_right_inverse)
        show "P \<in> carrier_mat (dim_row P') (dim_row P')"
          by (metis * P'_def PP'_1 True carrier_mat_triv index_one_mat(2) sm_P square_mat.elims(2))
        show "P' \<in> carrier_mat (dim_row P') (dim_row P')"
          by (metis P'_def True carrier_mat_triv)
        show "P * P' = 1\<^sub>m (dim_row P')"
          by (metis P'_def PP'_1 True)
      qed
    qed
    have inv_Q: "invertible_mat Q"
    proof (unfold invertible_mat_def, rule conjI, rule sm_Q,
        unfold inverts_mat_def, rule exI[of _ Q'], rule conjI)
      show *: "Q * Q' = 1\<^sub>m (dim_row Q)"
        by (metis QQ'_1 True index_mult_mat(2))
      show "Q' * Q = 1\<^sub>m (dim_row Q')"
      proof (rule mat_mult_left_right_inverse)
        show 1: "Q \<in> carrier_mat (dim_row Q') (dim_row Q')"
          by (metis Q'_def QQ'_1 True carrier_mat_triv dim_row_mat(1) index_mult_mat(2)
              mat_of_rows_list_def sm_Q square_mat.simps)
        thus "Q' \<in> carrier_mat (dim_row Q') (dim_row Q')"
          by (metis * carrier_matD(1) carrier_mat_triv index_mult_mat(3) index_one_mat(3))
        show "Q * Q' = 1\<^sub>m (dim_row Q')" using * 1 by auto
      qed
    qed
    have "P \<in> carrier_mat m m"
      by (metis PP'_1 True carrier_matI index_mult_mat(2) sm_P square_mat.simps)
    moreover have  "Q \<in> carrier_mat n n"
      by (metis QQ'_1 True carrier_matI index_mult_mat(2) sm_Q square_mat.simps)
    ultimately show ?thesis unfolding is_SNF_def using inv_P inv_Q SNF_S S_PAQ A by auto
  next
    case False
    hence "checker_SNF A = Smith_ED_mxn A"
      using ext False c A
      unfolding checker_SNF_def Let_def Code.abort_def
      by (smt carrier_matD case_prod_conv dim_col_mat(1) mat_of_rows_list_def)
    then show ?thesis using Smith_ED.is_SNF_Smith_mxn[OF A] c unfolding is_SNF_def
      by auto
  qed
qed

end
