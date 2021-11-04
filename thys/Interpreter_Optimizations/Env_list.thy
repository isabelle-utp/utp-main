theory Env_list
  imports Env
begin

subsection \<open>List-based implementation of environment\<close>

context
begin

qualified
datatype ('key, 'val) t = T "('key \<times> 'val) list"

qualified definition empty :: "('key, 'val) t" where
  "empty \<equiv> T []"

qualified fun get :: "('key, 'val) t \<Rightarrow> 'key \<Rightarrow> 'val option" where
  "get (T xs) = Map.map_of xs"

qualified fun add :: "('key, 'val) t \<Rightarrow> 'key \<Rightarrow> 'val \<Rightarrow> ('key, 'val) t" where
  "add (T xs) k v = T ((k, v) # xs)"

qualified fun to_list :: "('key, 'val) t \<Rightarrow> ('key \<times> 'val) list" where
  "to_list (T xs) = xs"

lemma get_empty: "get empty x = None"
  by (simp add: empty_def)

lemma get_add_eq: "get (add e x v) x = Some v"
  by (cases e; simp)

lemma get_add_neq: "x \<noteq> y \<Longrightarrow> get (add e x v) y = get e y"
  by (cases e; simp)

lemma to_list_correct: "map_of (to_list e) = get e"
proof (rule ext)
  fix k
  obtain xs where "e = T xs"
    by (cases e; simp)
  show "map_of (to_list e) k = get e k"
    unfolding \<open>e = T xs\<close>
    by (induction xs) simp_all
qed

end


global_interpretation env_list:
  env Env_list.empty Env_list.get Env_list.add Env_list.to_list
  defines
    singleton = env_list.singleton and
    add_list = env_list.add_list and
    from_list = env_list.from_list
  apply (unfold_locales)
  by (simp_all add: get_empty get_add_eq get_add_neq to_list_correct)


export_code Env_list.empty Env_list.get Env_list.add Env_list.to_list singleton add_list from_list
  in SML module_name Env

end