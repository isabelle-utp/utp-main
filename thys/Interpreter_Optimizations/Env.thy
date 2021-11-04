theory Env
  imports Main
begin

section \<open>Environment\<close>

locale env =
  fixes
    empty :: 'env and
    get :: "'env \<Rightarrow> 'key \<Rightarrow> 'val option" and
    add :: "'env \<Rightarrow> 'key \<Rightarrow> 'val \<Rightarrow> 'env" and
    to_list :: "'env \<Rightarrow> ('key \<times> 'val) list"
  assumes
    get_empty: "get empty x = None" and
    get_add_eq: "get (add e x v) x = Some v" and
    get_add_neq: "x \<noteq> y \<Longrightarrow> get (add e x v) y = get e y" and
    to_list_correct: "map_of (to_list e) = get e"

begin

declare get_empty[simp]
declare get_add_eq[simp]
declare get_add_neq[simp]

definition singleton where
  "singleton \<equiv> add empty"

fun add_list :: "'env \<Rightarrow> ('key \<times> 'val) list \<Rightarrow> 'env" where
  "add_list e [] = e" |
  "add_list e (x # xs) = add (add_list e xs) (fst x) (snd x)"

definition from_list :: "('key \<times> 'val) list \<Rightarrow> 'env" where
  "from_list \<equiv> add_list empty"

lemma from_list_correct: "map_of xs k = get (from_list xs) k"
proof (induction xs)
  case Nil
  then show ?case
    using get_empty by (simp add: from_list_def)
next
  case (Cons x xs)
  then show ?case
    using get_add_eq get_add_neq by (simp add: from_list_def)
qed

lemma from_list_Nil[simp]: "from_list [] = empty"
  by (simp add: from_list_def)

lemma get_from_list_to_list: "get (from_list (to_list e)) = get e"
proof
  fix x
  show "get (from_list (to_list e)) x = get e x"
    unfolding from_list_correct[symmetric]
    unfolding to_list_correct[symmetric]
    by simp
qed

end

end