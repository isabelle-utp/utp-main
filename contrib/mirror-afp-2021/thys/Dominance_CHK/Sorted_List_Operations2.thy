
section \<open>Operations on sorted lists\<close>

theory Sorted_List_Operations2
imports Sorted_Less2
begin 

text\<open>The definition and the inter\_sorted\_correct lemma in this theory are the same as those
     in Collections \cite{OpsOnSortedLists-AFP}. 
     except the former is for a descending list while the latter is for an ascending one.\<close>

fun inter_sorted_rev :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "inter_sorted_rev [] l2 = []"
 | "inter_sorted_rev l1 [] = []"
 | "inter_sorted_rev (x1 # l1) (x2 # l2) =
    (if (x1 > x2) then (inter_sorted_rev l1 (x2 # l2)) else 
      (if (x1 = x2) then x1 # (inter_sorted_rev l1 l2) else inter_sorted_rev (x1 # l1) l2))"

lemma inter_sorted_correct :
  assumes l1_OK: "sorted (rev l1)"
  assumes l2_OK: "sorted (rev l2)"
    shows "sorted (rev (inter_sorted_rev l1 l2)) \<and> set (inter_sorted_rev l1 l2) = set l1 \<inter> set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "sorted (rev l1)"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_gt: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 > x"
    by (auto simp add: Ball_def sorted_wrt_append)

  note ind_hyp_l1 = Cons(1)[OF l1_props]
  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)  (* sorted (rev (x2 # l2))*)
    from x2_l2_props have l2_props: "sorted (rev l2)"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_gt: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 > x"
    by (auto simp  add: Ball_def sorted_wrt_append )

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 > x2")
      case True note x1_gt_x2 = this
      have "set l1 \<inter> set (x2 # l2) = set (x1 # l1)\<inter> set (x2 # l2)" 
        using x1_gt_x2 x1_nin_l1 x2_nin_l2 x1_gt x2_gt 
        by fastforce
      then show ?thesis using ind_hyp_l1[OF x2_l2_props]  using x1_gt_x2 x1_nin_l1 x2_nin_l2 x1_gt x2_gt 
        by (auto simp add:Ball_def sorted_wrt_append)
    next
      case False note x2_ge_x1 = this      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this        
        then show ?thesis using ind_hyp_l1[OF l2_props]  
          using x1_eq_x2  x1_nin_l1 x2_nin_l2 x1_gt x2_gt by (auto simp add:Ball_def sorted_wrt_append)
      next
        case False note x1_neq_x2 = this
        with x2_ge_x1 have x2_gt_x1 : "x2 > x1" by auto
        from ind_hyp_l2 x2_ge_x1 x1_neq_x2 x2_gt x2_nin_l2 x1_gt 
        show ?thesis by auto         
      qed
    qed
  qed
qed

lemma inter_sorted_rev_refl: "inter_sorted_rev xs xs = xs" 
  by (induct xs) auto

lemma  inter_sorted_correct_col: 
  assumes "sorted (rev xs)"
      and "sorted (rev ys)"
    shows "(inter_sorted_rev xs ys) = rev (sorted_list_of_set (set xs \<inter> set ys))"
  using assms
proof-
  from assms have 1: "sorted (rev (inter_sorted_rev xs ys)) " 
              and 2: "set (inter_sorted_rev xs ys) = set xs \<inter> set ys" using inter_sorted_correct by auto
  have "sorted (rev (rev (sorted_list_of_set (set xs \<inter> set ys))))" by ( simp add:sorted_less_sorted_list_of_set)
  with 1 2 show ?thesis by (auto intro:sorted_less_rev_set_unique)
qed

lemma cons_set_eq: "set (x # xs) \<inter> set xs = set xs"  
  by auto

lemma inter_sorted_cons: "sorted (rev (x # xs)) \<Longrightarrow> inter_sorted_rev (x # xs) xs = xs" 
proof-
  assume ass: "sorted (rev (x # xs))" 
  then have sorted_xs: "sorted (rev xs)" by (auto simp add:sorted_wrt_append)
  with ass have "inter_sorted_rev (x # xs) xs = rev (sorted_list_of_set (set (x # xs) \<inter> set xs))" 
    by (simp add:inter_sorted_correct_col)
  then have "inter_sorted_rev (x # xs) xs = rev (rev xs)"using  sorted_xs by (simp only:cons_set_eq sorted_less_rev_set_eq)
  then show ?thesis using sorted_xs by auto
qed

end
