section\<open>Finite Sets\<close>
text\<open>Here we define the operations on the \texttt{fset} datatype in terms of lists rather than sets.
This allows the Scala implementation to skip a case match each time, which makes for cleaner and
slightly faster code.\<close>

theory Code_Target_FSet
  imports "Extended_Finite_State_Machines.FSet_Utils"
begin

code_datatype fset_of_list

declare FSet.fset_of_list.rep_eq [code]

lemma fprod_code [code]:
  "fprod (fset_of_list xs) (fset_of_list ys) = fset_of_list (remdups [(x, y). x \<leftarrow> xs, y \<leftarrow> ys])"
  apply (simp add: fprod_def fset_of_list_def fset_both_sides Abs_fset_inverse)
  by auto

lemma fminus_fset_filter [code]:
  "fset_of_list A -  xs = fset_of_list (remdups (filter (\<lambda>x. x |\<notin>| xs) A))"
  by auto

lemma sup_fset_fold [code]:
  "(fset_of_list f1) |\<union>| (fset_of_list f2) = fset_of_list (remdups (f1@f2))"
  by simp

lemma bot_fset [code]: "{||} = fset_of_list []"
  by simp

lemma finsert [code]:
  "finsert a (fset_of_list as) = fset_of_list (List.insert a as)"
  by (simp add: List.insert_def finsert_absorb fset_of_list_elem)

lemma ffilter_filter [code]:
  "ffilter f (fset_of_list as) = fset_of_list (List.filter f (remdups as))"
  by simp

lemma fimage_map [code]:
  "fimage f (fset_of_list as) = fset_of_list (List.map f (remdups as))"
  by simp

lemma ffUnion_fold [code]:
  "ffUnion (fset_of_list as) = fold (|\<union>|) as {||}"
  by (simp add: fold_union_ffUnion)

lemma fmember [code]: "a |\<in>| (fset_of_list as) = List.member as a"
  by (simp add: fset_of_list_elem member_def)

lemma fthe_elem [code]: "fthe_elem (fset_of_list [x]) = x"
  by simp

lemma size [code]: "size (fset_of_list as) = length (remdups as)"
proof(induct as)
  case Nil
  then show ?case
    by simp
next
  case (Cons a as)
  then show ?case
    by (simp add: fset_of_list.rep_eq insert_absorb)
qed

lemma fMax_fold [code]: "fMax (fset_of_list (a#as)) = fold max as a"
  by (metis Max.set_eq_fold fMax.F.rep_eq fset_of_list.rep_eq)

lemma fMin_fold [code]: "fMin (fset_of_list (h#t)) = fold min t h"
  apply (simp add: fset_of_list_def)
  by (metis Min.set_eq_fold fMin_Min fset_of_list.abs_eq list.simps(15))

lemma fremove_code [code]:
  "fremove a (fset_of_list A) = fset_of_list (filter (\<lambda>x. x \<noteq> a) A)"
  apply (simp add: fremove_def minus_fset_def ffilter_def fset_both_sides Abs_fset_inverse fset_of_list.rep_eq)
  by auto

lemma fsubseteq [code]:
  "(fset_of_list l) |\<subseteq>| A = List.list_all (\<lambda>x. x |\<in>| A) l"
  by (induct l, auto)

lemma fsum_fold [code]: "fSum (fset_of_list l) = fold (+) (remdups l) 0"
proof(induct l)
case Nil
then show ?case
  by (simp add: fsum.F.rep_eq fSum_def)
next
  case (Cons a l)
  then show ?case
    apply simp
    apply standard
     apply (simp add: finsert_absorb fset_of_list_elem)
    by (simp add: add.commute fold_plus_sum_list_rev fset_of_list.rep_eq fsum.F.rep_eq fSum_def)
qed

lemma code_fset_eq [code]:
  "HOL.equal X (fset_of_list Y) \<longleftrightarrow> size X = length (remdups Y) \<and> (\<forall>x |\<in>| X. List.member Y x)"
  apply (simp only: HOL.equal_class.equal_eq fset_eq_alt)
  apply (simp only: size)
  using fmember by fastforce

lemma code_fsubset [code]:
  "s |\<subset>| s' = (s |\<subseteq>| s' \<and> size s < size s')"
  apply standard
   apply (simp only: size_fsubset)
  by auto

lemma code_fset [code]: "fset (fset_of_list l) = fold insert l {}"
  using fset_of_list.rep_eq union_set_fold by fastforce

lemma code_fBall [code]: "fBall (fset_of_list l) f = list_all f l"
  by (simp add: Ball_set fBall.rep_eq fset_of_list.rep_eq)

lemma code_fBex [code]: "fBex (fset_of_list l) f = list_ex f l"
  by (meson Bex_set fBexE fset_of_list_elem rev_fBexI)

definition "nativeSort = sort"
code_printing constant nativeSort \<rightharpoonup> (Scala) "_.sortWith((Orderings.less))"

lemma [code]: "sorted_list_of_fset (fset_of_list l) = nativeSort (remdups l)"
  by (simp add: nativeSort_def sorted_list_of_fset_sort)

lemma [code]: "sorted_list_of_set (set l) = nativeSort (remdups l)"
  by (simp add: nativeSort_def sorted_list_of_set_sort_remdups)

lemma [code]: "fMin (fset_of_list (h#t)) = hd (nativeSort (h#t))"
  by (metis fMin_Min hd_sort_Min list.distinct(1) nativeSort_def)

lemma sorted_Max_Cons:
  "l \<noteq> [] \<Longrightarrow>
   sorted (a#l) \<Longrightarrow>
   Max (set (a#l)) = Max (set l)"
  using eq_iff by fastforce

lemma sorted_Max:
  "l \<noteq> [] \<Longrightarrow>
   sorted l \<Longrightarrow>
   Max (set l) = hd (rev l)"
proof(induct l)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by (metis sorted_Max_Cons Max_singleton hd_rev last.simps list.set(1) list.simps(15) sorted.simps(2))
qed

lemma [code]: "fMax (fset_of_list (h#t)) = last (nativeSort (h#t))"
  by (metis Max.set_eq_fold fMax_fold hd_rev list.simps(3) nativeSort_def set_empty2 set_sort sorted_Max sorted_sort)

definition "list_max l = fold max l"
code_printing constant list_max \<rightharpoonup> (Scala) "_.par.fold((_))(Orderings.max)"

lemma [code]: "fMax (fset_of_list (h#t)) = list_max t h"
  by (metis fMax_fold list_max_def)

definition "list_min l = fold min l"
code_printing constant list_min \<rightharpoonup> (Scala) "_.par.fold((_))(Orderings.min)"

lemma [code]: "fMin (fset_of_list (h#t)) = list_min t h"
  by (metis fMin_fold list_min_def)

lemma fis_singleton_code [code]: "fis_singleton s = (size s = 1)"
  apply (simp add: fis_singleton_def is_singleton_def)
  by (simp add: card_Suc_eq)

end
