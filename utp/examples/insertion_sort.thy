subsection \<open> Verification of Insertion Sort (with Local Variables) \<close>

theory insertion_sort
  imports "UTP.utp" "HOL-Library.Permutation"
begin recall_syntax

utp_lit_vars

alphabet global =
  arr :: "int list"

declare global.splits [alpha_splits del]

alphabet local = global +
  i   :: nat
  j   :: nat

declare global.splits [alpha_splits]

abbreviation lv :: "<global, _> \<Longleftrightarrow> local" where
"lv \<equiv> \<lparr> view = (global.base\<^sub>L :: (global \<Longrightarrow> local)), coview = global.more\<^sub>L \<rparr>"

lemma sym_lens_lv [simp]: "sym_lens lv"
  by (rule sym_lens.intro, simp_all)

abbreviation "I xs \<equiv> U(0 < i \<and> i < length arr \<and> j \<le> i \<and>
      sorted(nths arr {0..<j}) \<and> sorted(nths arr {j..i}) \<and>
      (0<j \<and> j<i  \<Rightarrow> arr!(j-1) \<le> arr!(j+1)) \<and>
      perm arr \<guillemotleft>xs\<guillemotright>)"

definition insert_elem :: "int list \<Rightarrow> local hrel" where
"insert_elem xs =
    while (0 < j \<and> arr!j < arr!(j-1))
    invr @(I xs)
    do
      (arr[j-1], arr[j]) := (arr!j, arr!(j-1)) ;;
      j := j - 1
    od"

abbreviation insertion_sort :: "int list \<Rightarrow> global hrel" where
  "insertion_sort xs \<equiv>
  arr := \<guillemotleft>xs\<guillemotright> ;;
  open\<^bsub>lv\<^esub> ;;
   (i := 1 ;;
    while (i < length arr)
    invr 
      0 < i \<and> i \<le> length arr \<and> sorted(nths arr {0..i-1}) \<and> perm arr \<guillemotleft>xs\<guillemotright>
    do 
      j := i ;;
      insert_elem xs ;;
      i := i + 1
    od) ;;
  close\<^bsub>lv\<^esub>"

lemma insert_elem_correct: "
    \<lbrace>0 < i \<and> i < length arr \<and> j = i \<and> sorted(nths arr {0..i-1}) \<and> perm arr \<guillemotleft>xs\<guillemotright>\<rbrace>
    insert_elem xs
    \<lbrace>0 < i \<and> i < length arr \<and> sorted(nths arr {0..i}) \<and> perm arr \<guillemotleft>xs\<guillemotright>\<rbrace>\<^sub>u"
  apply (simp add: insert_elem_def)
  apply (rule while_invr_hoare_r)
    apply (hoare_split)
    apply (rel_auto'; simp_all add: list_augment_as_update)
   apply (metis diff_le_self lessThan_iff linorder_not_less nths_atLeastLessThan_0_take nths_list_update_out nths_upt_eq_take order_less_irrefl sorted_nths_atLeastLessThan_0)
          apply (simp add: nths_uptoLessThan nths_single)
  apply (meson diff_le_self le_less_trans perm.trans perm_swap)
       apply (rename_tac arr i)
  apply (smt Suc_pred diff_Suc_Suc diff_le_self diff_less diff_zero le_less_trans less_imp_le_nat nths_upt_length nths_upt_nth sorted_iff_nth_mono zero_less_Suc)
  apply (metis One_nat_def atLeastLessThan_iff diff_le_self le_less le_less_trans less_irrefl nths_list_update_out sorted_nths_atLeastLessThan_0)
  apply (simp add: sorted_iff_nth_mono_less nths_upt_le_length nths_upt_le_nth)
      apply (auto)[1]
  apply (rename_tac arr i j m n)
     apply (case_tac "m>1")
      apply (simp)
      apply (drule_tac x="m-1" in spec) back
  apply (drule_tac x="n-1" in spec) back
      apply (simp)
     apply (simp)
     apply (subgoal_tac "m\<in>{0,1}")
      apply (case_tac "n>1")
  defer (* apply (smt Nat.add_diff_assoc2 Nat.diff_diff_right Suc_pred diff_Suc_Suc diff_commute diff_diff_cancel gr0I lessI less_nat_zero_code nat_le_linear nat_neq_iff zero_less_diff) *)
       apply (simp)
       apply (subgoal_tac "n=1")
  apply (simp)
       apply linarith
  apply (metis One_nat_def insert_iff less_one linorder_neqE_nat)
  apply (smt diff_le_self le_less_trans mset_eq_perm mset_swap)
  apply (rename_tac arr i j)
    apply (subgoal_tac " (nths arr {0..<j}) ! (j - Suc (Suc 0)) \<le> (nths arr {0..<j}) ! (j - Suc 0)")
         apply (simp add: nths_upt_nth)
    apply (rule sorted_nth_mono)
            apply (simp)
  apply linarith
  apply (metis Suc_le_lessD Suc_pred diff_zero eq_imp_le le_less_trans less_imp_le_nat nths_upt_length)
    apply (rel_auto')
  apply (simp add: nths_atLeastAtMost_0_take nths_atLeastLessThan_0_take)
  apply (simp add: nths_single)
   apply (rel_auto')
  using neq0_conv apply blast
  apply (smt Suc_diff_le Suc_leI add.commute add.left_neutral atLeastLessThanSuc_atLeastAtMost diff_Suc_1 diff_Suc_less diff_is_0_eq' diff_zero le_add1 le_neq_implies_less less_imp_Suc_add less_imp_le_nat nths_upt_le_append_split nths_upt_le_nth nths_upt_length sorted_append_middle zero_less_one)
    apply (rename_tac arr i j)
  apply (subgoal_tac "sorted (nths arr {0..<j} @ nths arr {j..i})")
  apply (auto)
      apply (simp add: nths_upt_le_append_split)
     apply (simp add: sorted_append_middle)
  apply (auto)
     apply (simp add: nths_upt_length nths_upt_nth nths_upt_le_nth)
     apply (simp add: atLeast0LessThan)
   apply (drule_tac x="0" in spec) back
   apply (drule_tac x="n-1" in spec) back
   apply (simp)
  apply (subgoal_tac "arr ! Suc j \<le> arr ! (n + j - Suc 0)")
  apply (simp)
  apply (drule_tac x="1" in spec) back
  apply (drule_tac x="n-1" in spec) back
  apply (simp)
  by (metis (no_types, lifting) Nat.add_diff_assoc Nat.add_diff_assoc2 One_nat_def Suc_lessD Suc_lessI Suc_less_eq Suc_pred le_SucI less_imp_le_nat plus_1_eq_Suc)

lemma insertion_sort_correct:
  "\<lbrace>length(xs) > 0\<rbrace>
    insertion_sort xs
   \<lbrace>sorted(arr) \<and> perm arr xs\<rbrace>\<^sub>u"
  apply (rule hoare_safe) back
     apply (simp_all add: unrest)
  apply (rule hoare_block)
   apply (simp)
  apply (simp add: alpha)
  apply (rule hoare_safe) back
     apply (simp_all add: unrest)
  apply (rule while_invr_hoare_r)
  apply (rule hoare_safe) back back
       apply (simp_all add: unrest)
  apply (rule hoare_safe) back
    apply (rule hoare_r_conseq)
       apply (rule insert_elem_correct)
      apply (rel_auto')
    apply (rel_auto')
      apply (rel_auto')
  apply (simp add: Suc_leI)
    apply (simp add: nths_single)
      apply (rel_auto')
   apply (simp add: nths_atLeastAtMost_0_take)
  done

lemma "TRY(id\<^sub>s \<Turnstile> insertion_sort [4,3,7,1,12,8])"
  apply (unfold insert_elem_def)
  apply (sym_eval)
  apply (simp add: usubst unrest)
  oops

end