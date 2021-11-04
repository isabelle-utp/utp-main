(* Author: Nan Jiang *)

section \<open>More auxiliary lemmas for Lists Sorted wrt $<$\<close>

theory Sorted_Less2
  imports Main "HOL-Data_Structures.Cmp" "HOL-Data_Structures.Sorted_Less" 
begin

lemma Cons_sorted_less: "sorted (rev xs) \<Longrightarrow> \<forall>x\<in>set xs. x < p \<Longrightarrow>   sorted (rev (p # xs))" 
  by (induct xs) (auto simp add:sorted_wrt_append)

lemma Cons_sorted_less_nth:  "\<forall>x<length xs. xs ! x < p \<Longrightarrow> sorted (rev xs) \<Longrightarrow> sorted (rev (p # xs))"
  apply(subgoal_tac "\<forall>x\<in>set xs. x < p")
  apply(fastforce dest:Cons_sorted_less)
  apply(auto simp add: set_conv_nth)
  done

lemma distinct_sorted_rev: "sorted (rev xs) \<Longrightarrow> distinct xs"
  by (induct xs) (auto simp add:sorted_wrt_append)

lemma sorted_le2lt: 
  assumes "List.sorted xs"
      and "distinct xs"
    shows "sorted xs"
  using assms
proof (induction xs)
  case Nil then show ?case by auto
next
  case (Cons x xs) 
  note ind_hyp_xs = Cons(1)
  note sorted_le_x_xs = Cons(2)
  note dist_x_xs = Cons(3)
  from dist_x_xs have x_neq_xs: "\<forall>v \<in> set xs. x \<noteq> v" 
                  and     dist: "distinct xs" by auto
  from sorted_le_x_xs have sorted_le_xs: "List.sorted xs" 
                       and      x_le_xs: "\<forall>v \<in> set xs. v \<ge> x" by auto
  from x_neq_xs x_le_xs have x_lt_xs: "\<forall>v \<in> set xs. v > x" by fastforce  
  from ind_hyp_xs[OF sorted_le_xs dist] have "sorted xs" by auto
  with x_lt_xs show ?case by auto
qed

lemma sorted_less_sorted_list_of_set: "sorted (sorted_list_of_set S)"
  by (auto intro:sorted_le2lt)

lemma distinct_sorted: "sorted xs \<Longrightarrow> distinct xs" 
  by (induct xs) (auto simp add: sorted_wrt_append sorted_sorted_wrt)  

lemma sorted_less_set_unique:
  assumes "sorted xs"
      and "sorted ys"
      and "set xs = set ys"
    shows "xs = ys" 
  using assms
proof -
  from assms(1) have "distinct xs" and "List.sorted xs" by (induct xs) auto
  also from assms(2) have "distinct ys" and "List.sorted ys" by (induct ys) auto
  ultimately show "xs = ys" using assms(3) by (auto intro: sorted_distinct_set_unique)
qed

lemma sorted_less_rev_set_unique: 
  assumes "sorted (rev xs)"
      and "sorted (rev ys)"
      and "set xs = set ys"
    shows "xs = ys" 
  using assms sorted_less_set_unique[of "rev xs" "rev ys"] by auto

lemma sorted_less_set_eq: 
  assumes "sorted xs "
    shows "xs = sorted_list_of_set (set xs)"
  using assms
  apply(subgoal_tac "sorted (sorted_list_of_set (set xs))")
   apply(auto intro: sorted_less_set_unique sorted_le2lt)
  done

lemma sorted_less_rev_set_eq: 
  assumes "sorted (rev xs) "
    shows "sorted_list_of_set (set xs) = rev xs"
  using assms sorted_less_set_eq[of "rev xs"] by auto

end