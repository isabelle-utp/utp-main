theory Group_By
imports Main
begin

fun group_by :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "group_by f [] = []" |
  "group_by f (h#t) = (
    let
      group = (takeWhile (f h) t);
      dropped = drop (length group) t
    in
      (h#group)#(group_by f dropped)
  )"

lemma "(group_by f xs = []) = (xs = [])"
  by (induct xs, auto simp add: Let_def)

lemma not_empty_group_by_drop: "\<forall>x \<in> set (group_by f (drop l xs)). x \<noteq> []"
  by (induct xs arbitrary: l, auto simp add: drop_Cons' Let_def)

lemma no_empty_groups: "\<forall>x\<in>set (group_by f xs). x \<noteq> []"
  by (metis not_empty_group_by_drop empty_iff empty_set group_by.elims list.distinct(1) set_ConsD)

lemma "(drop (length (takeWhile f l)) l) = dropWhile f l"
  by (simp add: dropWhile_eq_drop)

lemma takeWhile_dropWhile: "takeWhile f l @ dropWhile f l = l' \<Longrightarrow> l' = l"
  by simp

lemma append_pref: "l' = l'' \<Longrightarrow> (l@l' = l@l'')"
  by simp

lemma dropWhile_drop: "\<exists>x. dropWhile f l = drop x l"
  using dropWhile_eq_drop by blast

lemma group_by_drop_foldr: "drop x l = foldr (@) (group_by f (drop x l)) []"
proof (induct l arbitrary: x)
  case (Cons a l)
  then show ?case
    apply (simp add: drop_Cons' Let_def)
    by (metis append_take_drop_id takeWhile_eq_take)
qed auto

lemma group_by_inverse: "foldr (@) (group_by f l) [] = l"
proof(induct l)
  case (Cons a l)
  then show ?case
    apply (simp add: Let_def dropWhile_eq_drop[symmetric])
    apply (rule takeWhile_dropWhile[of "f a"])
    apply (rule append_pref)
    apply (insert dropWhile_drop[of "f a" l])
    apply (erule exE)
    by (simp add: group_by_drop_foldr)
qed auto

end