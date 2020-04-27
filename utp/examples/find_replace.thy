section \<open> Find and Replace Algorithm \<close>

theory find_replace
  imports "UTP.utp"
begin

utp_lit_vars

alphabet ss = arr::"nat \<Rightarrow> string" occ::"nat" i::"nat"

definition find_replace :: 
  "(nat \<Rightarrow> string) \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> string \<Rightarrow> ss hrel" where
"find_replace A len mtc rpl =
  arr := A ;; i := 0 ;; occ := 0 ;;
  while i < len 
  invr arr = (\<lambda> k. if k < i \<and> A k = mtc then rpl else A k)
     \<and> occ = length (filter ((=) mtc) (map A [0..<i])) \<and> i \<le> len
  do
    if (arr i = mtc) then arr[i] := rpl ;; occ := occ + 1
    else arr[i] := arr i
    fi ;; i := i + 1
  od"    

lemma find_replace_inv:
  "\<^bold>{true\<^bold>}
    find_replace A len mtc rpl
   \<^bold>{arr = (\<lambda> k. if k < i \<and> A k = mtc then rpl else A k)\<^bold>}"
  unfolding find_replace_def
  by (hoare_split, rel_auto', metis less_Suc_eq)

lemma find_replace_prop1:
  "\<^bold>{true\<^bold>} find_replace A len mtc rpl \<^bold>{\<forall> i < len. arr(i) = (rpl \<triangleleft> A(i) = mtc \<triangleright> A(i)) \<^bold>}"
  unfolding find_replace_def by (hoare_auto, metis less_Suc_eq)
  
lemma find_replace_prop2:
  "\<^bold>{true\<^bold>} find_replace A len mtc rpl \<^bold>{occ = length (filter ((=) mtc) (map A [0..<len]))\<^bold>}"
  unfolding find_replace_def by (hoare_auto, metis less_Suc_eq)



end