subsection \<open> Quicksort \<close>

theory quicksort
  imports "UTP.utp"
begin

declare length_list_augment_2 [simp]

abbreviation rforloop :: "('a::{ord,plus,one} \<Longrightarrow> 's) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('a, 's) uexpr \<Rightarrow> 's hrel \<Rightarrow> 's hrel" 
  ("for _ := _ to _ do _ od") 
  where "rforloop x i j P \<equiv> x := i ;; while &x \<le> j do P ;; x := &x + 1 od"

abbreviation rforloop_inv :: "('a::{ord,plus,one} \<Longrightarrow> 's) \<Rightarrow> ('a, 's) uexpr \<Rightarrow> ('a, 's) uexpr \<Rightarrow> 's upred \<Rightarrow> 's hrel \<Rightarrow> 's hrel" 
  ("for _ := _ to _ invr _ do _ od")
  where "rforloop_inv x i j I P \<equiv> x := i ;; while &x \<le> j invr I do P ;; x := &x + 1 od"

utp_lift_notation rforloop (1 2)

utp_lift_notation rforloop_inv (1 2 3)

utp_lit_vars

alphabet global = 
  A :: "int list"
  pivot :: int
  i :: nat
  j :: nat

(*
alphabet local = global +
  pivot :: int
  i :: nat
  j :: nat

abbreviation lv :: "<global, _> \<Longleftrightarrow> local" where
"lv \<equiv> \<lparr> view = (global.base\<^sub>L :: (global \<Longrightarrow> local)), coview = global.more\<^sub>L \<rparr>"

lemma sym_lens_lv [simp]: "sym_lens lv"
  by (rule sym_lens.intro, simp_all)
*)

abbreviation "partition_inv p r \<equiv> 
             U(i < j \<and> j \<le> p \<and> p \<le> r \<and> r < length A \<and> (\<forall> k. k < length A \<Rightarrow> 
               (p \<le> k \<and> k \<le> i \<Rightarrow> A!k \<le> pivot)
             \<and> (i + 1 \<le> k \<and> k \<le> j - 1 \<Rightarrow> pivot < A!k) 
             \<and> (k = r \<Rightarrow> A!k = pivot)))"

abbreviation partition :: "nat \<Rightarrow> nat \<Rightarrow> global hrel" where
"partition p r \<equiv>
   pivot := A!r ;;
   i := (p - 1) ;;
   for j := p to r - 1
   invr @(partition_inv p r)
   do
     if (A ! j) \<le> pivot then
       i := i + 1 ;;
       (A[j], A[i]) := (A!i, A!j)
     fi
   od ;;
   (A[i+1], A[r]) := (A!r, A!i+1)"

lemma "\<lbrace>@(partition_inv p r)\<rbrace>   
   while j \<le> r - 1
   invr @(partition_inv p r)
   do
     if (A ! j) \<le> pivot then
       i := i + 1 ;;
       (A[j], A[i]) := (A!i, A!j)
     fi ;;
     j := j + 1
   od
   \<lbrace>@(partition_inv p r)\<rbrace>\<^sub>u"
  apply (rule while_invr_hoare_r)
    apply (hoare_split)
      apply (rel_auto')
  oops

end
