theory insertion_sort
  imports "UTP.utp_easy_parser" "HOL-Library.Permutation"
begin

alphabet st_insertion_sort =
  arr :: "int list"
  i   :: nat
  key :: int
  j   :: nat

abbreviation insertion_sort :: "int list \<Rightarrow> st_insertion_sort hrel" where
  "insertion_sort xs \<equiv>
  arr := \<guillemotleft>xs\<guillemotright> ;;
  i := 1 ;;
  while (i < #arr) 
  invr 
    0 < i \<and> i < #arr \<and> sorted(nths(arr, {0..i-1})) \<and> perm(arr, \<guillemotleft>xs\<guillemotright>)
  do 
    key := arr[i] ;;
    j := i ;;
    while (j > 0 \<and> arr[j-1] > key)
    invr 
      0 < i \<and> i < #arr \<and> j \<le> i \<and> key = arr[j] \<and>
      sorted(nths(arr, {0..<j-1})) \<and> 
      sorted(nths(arr, {j-1..i-1})) \<and> 
      perm(arr, \<guillemotleft>xs\<guillemotright>)
    do
      arr[j] := arr[j-1] ;;
      arr[j-1] := key ;;
      j := j - 1
    od ;;
    i := i + 1
  od"

lemma "TRY(id \<Turnstile> insertion_sort [4,3,7,1,12,8])"
  apply (sym_eval)
  oops

lemma "{{i < #arr \<and> j \<le> i \<and> key = arr[j] \<and> sorted(nths(arr, {0..<j-1})) \<and> sorted (nths(arr, {j-1..i-1})) \<and> perm(arr, \<guillemotleft>xs\<guillemotright>)}}
    while (j > 0 \<and> arr[j-1] > key)
    do
      arr[j] := arr[j-1] ;;
      arr[j-1] := key ;;
      j := j - 1
    od
    {{(\<not> (j > 0 \<and> arr[j-1] > key)) \<and> (i < #arr \<and> j \<le> i \<and> key = arr[j] \<and> sorted(nths(arr, {0..<j-1})) \<and> sorted (nths(arr, {j-1..i-1})) \<and> perm(arr, \<guillemotleft>xs\<guillemotright>))}}"
  apply (rule while_hoare_r)
  apply (rel_auto)
     apply (smt Suc_diff_Suc diff_less_Suc diff_zero length_list_augment_1 length_list_augment_2 less_trans_Suc linorder_not_less nat_less_le)
  apply (simp add: nth_list_augment)
    apply (subst nths_list_augment_out)
  apply (auto)
     apply (metis diff_less_Suc length_list_augment_1 length_list_augment_2 less_imp_diff_less linorder_not_less)
    apply (subst nths_list_augment_out)
  apply (auto)
    apply (metis Suc_pred diff_Suc_less le_simps(2) sorted_nths_atLeastLessThan_0)
   defer
   apply (simp add: list_augment_as_update)
   apply (rename_tac arr i j)
  apply (subgoal_tac "arr[j := arr!(j - Suc 0), j - Suc 0 := arr!j] <~~> arr")
  apply blast
  apply (simp add: perm_swap)
  oops

lemma "{{true}}insertion_sort xs{{arr = sort(\<guillemotleft>xs\<guillemotright>)}}"
  apply (rule hoare_safe)
     apply (simp_all add: unrest)
  apply (rule hoare_safe)
     apply (simp_all add: unrest)
  apply (rule hoare_safe)
    apply (rule hoare_safe) back
       apply (simp_all add: unrest)
    apply (rule hoare_safe) back
       apply (simp_all add: unrest)
    apply (rule seq_hoare_inv_r_3)
  apply (rule while_invr_hoare_r)
  apply (hoare_auto)
  apply (metis (no_types, lifting) Suc_le_eq Suc_pred diff_less_Suc length_list_augment_1 length_list_augment_2 less_le_trans not_less)
  apply (simp_all add: nth_list_augment list_augment_as_update)
  apply (smt Suc_le_eq Suc_le_mono Suc_pred atLeastLessThan_iff diff_diff_cancel diff_is_0_eq diff_le_self nat_less_le nths_list_update_out sorted_nths_atLeastLessThan_0)
        defer
        defer
  apply (rel_auto)
         apply (metis Suc_pred atLeast0AtMost atLeast0LessThan diff_le_self lessThan_Suc_atMost sorted_nths_atLeastLessThan_0)
        defer
  apply (rel_auto)
  oops

end