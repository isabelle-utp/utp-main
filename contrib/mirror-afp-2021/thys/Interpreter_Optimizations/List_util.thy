theory List_util
  imports Main
begin

inductive same_length :: "'a list \<Rightarrow> 'b list \<Rightarrow> bool" where
  same_length_Nil: "same_length [] []" |
  same_length_Cons: "same_length xs ys \<Longrightarrow> same_length (x # xs) (y # ys)"

code_pred same_length .

lemma same_length_iff_eq_lengths: "same_length xs ys \<longleftrightarrow> length xs = length ys"
proof
  assume "same_length xs ys"
  then show "length xs = length ys"
    by (induction xs ys rule: same_length.induct) simp_all
next
  assume "length xs = length ys"
  then show "same_length xs ys"
  proof (induction xs arbitrary: ys)
    case Nil
    then show ?case
      by (simp add: same_length_Nil)
  next
    case (Cons x xs)
    then show ?case
      by (metis length_Suc_conv same_length_Cons)
  qed
qed

lemma same_length_Cons:
  "same_length (x # xs) ys \<Longrightarrow> \<exists>y ys'. ys = y # ys'"
  "same_length xs (y # ys) \<Longrightarrow> \<exists>x xs'. xs = x # xs'"
proof -
  assume "same_length (x # xs) ys"
  then show "\<exists>y ys'. ys = y # ys'"
    by (induction "x # xs" ys rule: same_length.induct) simp
next
  assume "same_length xs (y # ys)"
  then show "\<exists>x xs'. xs = x # xs'"
    by (induction xs "y # ys" rule: same_length.induct) simp
qed

inductive for_all2 for r where
  for_all2_Nil: "for_all2 r [] []" |
  for_all2_Cons: "r x y \<Longrightarrow> for_all2 r xs ys \<Longrightarrow> for_all2 r (x # xs) (y # ys)"

code_pred for_all2 .

declare for_all2_Nil[intro]
declare for_all2_Cons[intro]

lemma for_all2_refl: "(\<forall>x. r x x) \<Longrightarrow> for_all2 r xs xs"
  by (induction xs) auto

lemma for_all2_same_length: "for_all2 r xs ys \<Longrightarrow> same_length xs ys"
  by (induction rule: for_all2.induct) (auto intro: same_length.intros)

lemma for_all2_ConsD: "for_all2 r (x # xs) (y # ys) \<Longrightarrow> r x y \<and> for_all2 r xs ys"
  using for_all2.cases by blast


section \<open>nth\_opt\<close>

fun nth_opt where
  "nth_opt (x # _) 0 = Some x" |
  "nth_opt (_ # xs) (Suc n) = nth_opt xs n" |
  "nth_opt _ _ = None"

lemma nth_opt_eq_Some_conv: "nth_opt xs n = Some x \<longleftrightarrow> n < length xs \<and> xs ! n = x"
  by (induction xs n rule: nth_opt.induct; simp)

lemmas nth_opt_eq_SomeD[dest] = nth_opt_eq_Some_conv[THEN iffD1]


section \<open>Generic lemmas\<close>

lemma map_list_update_id:
  "f (xs ! pc) = f instr \<Longrightarrow> map f (xs[pc := instr]) = map f xs"
  using list_update_id map_update by metis

lemma list_all_eq_const_imp_replicate:
  assumes "list_all (\<lambda>x. x = y) xs"
  shows "xs = replicate (length xs) y"
  using assms
  by (induction xs; simp)

lemma list_all_eq_const_replicate_lhs[intro]:
  "list_all (\<lambda>x. y = x) (replicate n y)"
  by (simp add: list_all_length)

lemma list_all_eq_const_replicate_rhs[intro]:
  "list_all (\<lambda>x. x = y) (replicate n y)"
  by (simp add: list_all_length)

lemma replicate_eq_map:
  assumes "list_all g (take n xs)" and "n \<le> length xs" and "\<forall>y. g y \<longrightarrow> f y = x"
  shows "replicate n x = map f (take n xs)"
  using assms
proof (induction xs arbitrary: n)
  case Nil
  thus ?case by simp
next
  case (Cons x xs)
  thus ?case by (cases n; auto)
qed

end
