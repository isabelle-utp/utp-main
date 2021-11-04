section\<open>Same Register\<close>
text\<open>The \texttt{same\_register} heuristic aims to replace registers which are used in the same way.\<close>

theory Same_Register
  imports "../Inference"
begin

definition replace_with :: "iEFSM \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> iEFSM" where
  "replace_with e r1 r2 = (fimage (\<lambda>(u, tf, t). (u, tf,Transition.rename_regs (id(r1:=r2)) t)) e)"

fun merge_if_same :: "iEFSM \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> (nat \<times> nat) list \<Rightarrow> iEFSM" where
  "merge_if_same e _ [] = e" |
  "merge_if_same e check ((r1, r2)#rs) = (
    let transitions = fimage (snd \<circ> snd) e in
    if \<exists>(t1, t2) |\<in>| ffilter (\<lambda>(t1, t2). t1 < t2) (transitions |\<times>| transitions).
      same_structure t1 t2 \<and> r1 \<in> enumerate_regs t1 \<and> r2 \<in> enumerate_regs t2
    then
      let newE = replace_with e r1 r2 in
      if check (tm newE) then
        merge_if_same newE check rs
      else
        merge_if_same e check rs
    else
      merge_if_same e check rs
  )"

definition merge_regs :: "iEFSM \<Rightarrow> (transition_matrix \<Rightarrow> bool) \<Rightarrow> iEFSM" where
  "merge_regs e check = (
    let
      regs = all_regs e;
      reg_pairs = sorted_list_of_set (Set.filter (\<lambda>(r1, r2). r1 < r2) (regs \<times> regs))
    in
    merge_if_same e check reg_pairs
  )"

fun same_register :: update_modifier where
  "same_register t1ID t2ID s new _ old check = (
    let new' = merge_regs new check in
    if new' = new then None else Some new'
   )"

end
