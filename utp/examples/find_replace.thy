section \<open> Find and Replace Algorithm \<close>

theory find_replace
  imports "UTP.utp"
begin

utp_lit_vars

alphabet ss = 
  arr :: "nat \<Rightarrow> string"
  occ :: "nat"
  i   :: "nat"

definition find_replace :: "(nat \<Rightarrow> string) \<Rightarrow> nat \<Rightarrow> string \<Rightarrow> string \<Rightarrow> ss hrel" where
"find_replace inp len mtc rpl =
  arr := inp ;;
  i := 0 ;;
  occ := 0 ;;
  while i < len 
  invr arr = (\<lambda> k. if k < i \<and> inp k = mtc then rpl else inp k)
        \<and> occ = length (filter ((=) mtc) (map inp [0..<i]))
  do
    if (arr i = mtc)
    then 
      arr[i] := rpl ;;
      occ := occ + 1
    else
      arr[i] := inp i
    fi ;;
    i := i + 1
  od"    

lemma find_replace_correct:
  "\<^bold>{true\<^bold>}find_replace inp len mtc rpl\<^bold>{arr = (\<lambda> k. if k < i \<and> inp k = mtc then rpl else inp k)\<^bold>}"
  unfolding find_replace_def
  apply (hoare_split)
     apply (rel_simp')
     apply (simp add: fun_eq_iff)
    apply (rel_simp')
  apply (simp add: fun_eq_iff)
   apply (rel_simp')
  apply (rel_simp')
  done

end