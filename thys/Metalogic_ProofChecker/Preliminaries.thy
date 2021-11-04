
section "Preliminaries"

theory Preliminaries
  imports Complex_Main 
    "List-Index.List_Index"
    "HOL-Library.AList"
    "HOL-Library.Sublist"
    "HOL-Eisbach.Eisbach" 
    "HOL-Library.Simps_Case_Conv"
begin

text \<open>Stuff about options\<close>

fun the_default :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "the_default a None = a"
| "the_default _ (Some b) = b"

abbreviation Or :: "'a option \<Rightarrow> 'a option \<Rightarrow> 'a option" (infixl "OR" 60) where
  "e1 OR e2 \<equiv> case e1 of None \<Rightarrow> e2 | p \<Rightarrow> p"

lemma Or_Some: "(e1 OR e2) = Some x \<longleftrightarrow> e1 = Some x \<or> (e1 = None \<and> e2 = Some x)"
  by(auto split: option.split)

lemma Or_None: "(e1 OR e2) = None \<longleftrightarrow> e1 = None \<and> e2 = None"
  by(auto split: option.split)

fun lift2_option :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a option \<Rightarrow> 'b option \<Rightarrow> 'c option" where
  "lift2_option _ None _ = None" |
  "lift2_option _ _ None = None" |
  "lift2_option f (Some x) (Some y) = Some (f x y)"

lemma lift2_option_not_None: "lift2_option f x y \<noteq> None \<longleftrightarrow> (x \<noteq> None \<and> y \<noteq> None)" 
  using lift2_option.elims by blast
lemma lift2_option_None: "lift2_option f x y = None \<longleftrightarrow> (x = None \<or> y = None)" 
  using lift2_option.elims by blast

text \<open>Lookup functions for assoc lists\<close>

fun find :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b option" where
"find f [] = None" |
"find f (x#xs) = f x OR find f xs"

lemma findD:
  "find f xs = Some p \<Longrightarrow> \<exists>x \<in> set xs. f x = Some p"
  by(induction xs arbitrary: p) (auto split: option.splits)

lemma find_None:
  "find f xs = None \<longleftrightarrow> (\<forall>x \<in> set xs. f x = None)"
  by(induction xs) (auto split: option.splits)

lemma find_ListFind: "find f l = Option.bind (List.find (\<lambda>x. case f x of None \<Rightarrow> False | _ \<Rightarrow> True) l) f" 
  by (induction l) (auto split: option.split)
     
lemma "List.find P l = Some p \<Longrightarrow> \<exists>p \<in> set l . P p"
  by (induction l) (auto split: if_splits)

lemma find_the_pair:
  assumes "distinct (map fst pairs)" 
    and "\<And>x y. x\<in>set (map fst pairs) \<Longrightarrow> y\<in>set (map fst pairs) \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> x = y"
    and "(x,y) \<in> set pairs" and "P x" 
  shows "List.find (\<lambda>(x,_) . P x) pairs = Some (x,y)"
  using assms(1-3)
proof (induction pairs)
  case Nil
  then show ?case by simp
next
  case (Cons pair pairs)
  thm Cons.prems

  show ?case
  proof(cases "fst pair = x")
    case True
    then show ?thesis
      using eq_key_imp_eq_value[OF Cons.prems(1,3)] assms(4) by force
  next
    case False
    hence "(x,y) \<in> set pairs"
      using Cons.prems(3) by fastforce
    moreover have "\<And>x y. x \<in> set (map fst pairs) \<Longrightarrow> y \<in> set (map fst pairs) \<Longrightarrow> P x \<Longrightarrow> P y \<Longrightarrow> x = y"
      using Cons.prems(2) by (metis list.set_intros(2) list.simps(9))
    ultimately have I: "List.find (\<lambda>(x,_) . P x) pairs = Some (x,y)"
      using Cons.prems(1,3) by (auto intro!: Cons.IH)
    moreover have "\<And>y. y \<in> set (map fst (pair # pairs)) \<Longrightarrow> P y \<Longrightarrow> x = y"
      using Cons.prems(2,3) assms(4) by (metis set_zip_leftD zip_map_fst_snd)
    ultimately show ?thesis
      using False by fastforce
  qed
qed

fun remdups_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remdups_on  _ [] = []" 
| "remdups_on cmp (x # xs) = 
    (if \<exists>x' \<in> set xs . cmp x x' then remdups_on cmp xs else x # remdups_on cmp xs)"

fun distinct_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "distinct_on _ [] \<longleftrightarrow> True"
| "distinct_on cmp (x # xs) \<longleftrightarrow> \<not>(\<exists>x' \<in> set xs . cmp x x') \<and> distinct_on cmp xs"

lemma "remdups_on (=) xs = remdups xs"
  by (induction xs) auto

lemma remdups_on_antimono:
  "(\<And>x y . f x y \<Longrightarrow> g x y) \<Longrightarrow> set (remdups_on g xs) \<subseteq> set (remdups_on f xs)"
  by (induction xs) auto

lemma remdups_on_subset_input: "set (remdups_on f xs) \<subseteq> set xs"
  by (induction xs) auto

lemma distinct_on_remdups_on: "distinct_on f (remdups_on f xs)" 
proof (induction xs)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  then show ?case 
    using remdups_on_subset_input by fastforce
qed
  

lemma distinct_on_no_compare: "(\<And>x y . f x y \<Longrightarrow> f y x)\<Longrightarrow> 
  distinct_on f xs \<Longrightarrow> x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> x\<noteq>y \<Longrightarrow> \<not> f x y"
  by (induction xs) auto

fun lookup :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b option" where
  "lookup _ [] = None"
| "lookup f ((x,y)#xs) = (if f x then Some y else lookup f xs)"

lemma lookup_present_eq_key: "distinct (map fst al) \<Longrightarrow> (k, v) \<in> set al \<longleftrightarrow> lookup (\<lambda>x. x=k) al = Some v"
  by (induction al) (auto simp add: rev_image_eqI split: if_splits)

lemma lookup_None_iff: "lookup P xs = None \<longleftrightarrow> \<not> (\<exists>x. x \<in> set (map fst xs) \<and> P x)"
  by (induction xs) (auto split: if_splits)

lemma find_Some: "List.find P l = Some p \<Longrightarrow> p\<in>set l \<and> P p"
  by (induction l) (auto split: if_splits) 

(* This means lookup seems somewhat superflouus *)
lemma find_Some_imp_lookup_Some: 
  "List.find (\<lambda>(k,_). P k) xs = Some (k,v) \<Longrightarrow> lookup P xs = Some v"
  by (induction xs) auto

lemma lookup_Some_imp_find_Some: 
  "lookup P xs = Some v \<Longrightarrow> \<exists>x. List.find (\<lambda>(k,_). P k) xs = Some (x,v)"
  by (induction xs) auto

lemma lookup_None_iff_find_None: "lookup P xs = None \<longleftrightarrow> List.find (\<lambda>(k,_). P k) xs = None"
  by (induction xs) auto

lemma lookup_eq_order_irrelevant:
  assumes "distinct (map fst pairs)" and "distinct (map fst pairs')" and "set pairs = set pairs'"
  shows "lookup (\<lambda>x. x=k) pairs = lookup (\<lambda>x. x=k) pairs'"
proof (cases "lookup (\<lambda>x. x=k) pairs")
  case None
  then show ?thesis using lookup_None_iff
    by (metis assms(3) set_map)
next
  case (Some v)
  hence "(k,v)\<in>set pairs" 
    using assms(1) by (simp add: lookup_present_eq_key)
  hence el: "(k,v)\<in>set pairs'" using assms(3) by blast
  show ?thesis using lookup_present_eq_key[OF assms(2)] el Some by simp
qed

lemma lookup_Some_append_back:
  "lookup (\<lambda>x. x=k) insts = Some v \<Longrightarrow> lookup (\<lambda>x. x=k) (insts@[(k,v')]) = Some v"
  by (induction insts arbitrary: ) auto

lemma lookup_eq_key_not_present: "key \<notin> set (map fst inst) \<Longrightarrow> lookup (\<lambda>x. x = key) inst = None"
  by (induction inst) auto

lemma lookup_in_empty[simp]: "lookup f [] = None" by simp
lemma lookup_in_single[simp]: "lookup f [(k, v)] = (if f k then Some v else None)" by simp

lemma lookup_present_eq_key': "lookup (\<lambda>x. x=k) al = Some v \<Longrightarrow> (k, v) \<in> set al "
  by (induction al) (auto simp add: rev_image_eqI split: if_splits)

lemma lookup_present_eq_key'': "distinct (map fst al) \<Longrightarrow> lookup (\<lambda>x. x=k) al = Some v \<longleftrightarrow> (k, v) \<in> set al "
  by (induction al) (auto simp add: rev_image_eqI split: if_splits)

lemma key_present_imp_eq_lookup_finds_value: "k \<in> fst ` set al \<Longrightarrow> \<exists>v . lookup (\<lambda>x. x=k) al = Some v"
  by (induction al) (auto simp add: rev_image_eqI)

lemma list_allI: "(\<And>x. x\<in>set l \<Longrightarrow> P x) \<Longrightarrow> list_all P l"
  by (induction l) auto

lemma map2_sym: "(\<And>x y . f x y = f y x) \<Longrightarrow> map2 f xs ys = map2 f ys xs"
proof (induction xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (induction ys) auto
qed

lemma idem_map2: assumes "(\<And>x. f x x = x)" shows "map2 f l l = l"
proof-
  have "length l = length l" by simp
  then show "map2 f l l = l" by (induction l l rule: list_induct2) (use assms in auto)
qed

lemma rev_induct2[consumes 1, case_names Nil snoc]:
  assumes "length xs = length ys"
  assumes "P [] []"
  assumes "(\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y]))"
  shows "P xs ys"
proof-
  have "length (rev xs) = length (rev ys)" using assms(1) by simp
  hence "P (rev (rev xs)) (rev (rev ys))" 
    using assms(2-3) by (induction rule: list_induct2[of "rev xs" "rev ys"]) simp_all
  thus ?thesis by simp
qed

lemma alist_map_corr: "distinct (map fst al) \<Longrightarrow> (k,v) \<in> set al \<longleftrightarrow> map_of al k = Some v"
  by simp

lemma distinct_fst_imp_distinct: "distinct (map fst l) \<Longrightarrow> distinct l"
  by (induction l) auto

lemma length_alist:
  assumes "distinct (map fst al)" and "distinct (map fst al')" and "set al = set al'"
  shows "length al = length al'"
  using assms by (metis distinct_card length_map set_map)

lemma same_map_of_imp_same_length: 
  "distinct (map fst ars1) \<Longrightarrow> distinct (map fst ars2) \<Longrightarrow> map_of ars1 = map_of ars2
  \<Longrightarrow> length ars1 = length ars2"
  (* Name is a bit to specific*)
  using length_alist map_of_inject_set by blast

lemma in_range_if_ex_key: "v \<in> ran m \<longleftrightarrow> (\<exists>k. m k = Some v)" 
  by (auto simp add: ranI ran_def)

lemma set_AList_delete_bound: "set (AList.delete a l) \<subseteq> set l"
  by (induction l) auto

lemma list_all_clearjunk_cons: 
  "list_all P (x#(AList.clearjunk l)) \<Longrightarrow> list_all P (AList.clearjunk (x#l))"
  by (induction l rule: AList.clearjunk.induct) (auto simp add: delete_twist)

lemma lookup_AList_delete: "k'\<noteq>k \<Longrightarrow> lookup (\<lambda>x. x = k) al = lookup (\<lambda>x. x = k) (AList.delete k' al)" 
  by (induction al) auto

lemma lookup_AList_clearjunk: "lookup (\<lambda>x. x = k) al = lookup (\<lambda>x. x = k) (AList.clearjunk al)"
proof (induction al)
  case Nil
  then show ?case
    by simp
next
  case (Cons a al)
  then show ?case 
  proof(cases "fst a=k")
    case True
    then show ?thesis
      by (metis (full_types) clearjunk.simps(2) lookup.simps(2) prod.collapse)
  next
    case False
    have "lookup (\<lambda>x. x = k) (AList.clearjunk (a # al)) 
      = lookup (\<lambda>x. x = k) (a # AList.clearjunk (AList.delete (fst a) al))"
      by simp
    also have "\<dots> = lookup (\<lambda>x. x = k) (AList.clearjunk (AList.delete (fst a) al))"
      by (metis (full_types) False lookup.simps(2) surjective_pairing)
    also have "\<dots> = lookup (\<lambda>x. x = k) (AList.clearjunk al)"
      by (metis False clearjunk_delete lookup_AList_delete)
    also have "\<dots> = lookup (\<lambda>x. x = k) al"
      using Cons.IH by auto
    also have "\<dots> = lookup (\<lambda>x. x = k) (a # al)"
      by (metis (full_types) False lookup.simps(2) surjective_pairing)
    finally show ?thesis 
      by simp
  qed
qed

definition "diff_list xs ys \<equiv> fold removeAll ys xs"

lemma diff_list_set[simp]: "set (diff_list xs ys) = set xs - set ys"
  unfolding diff_list_def by (induction ys arbitrary: xs) auto

lemma diff_list_set_from_Nil[simp]: "diff_list [] ys = []"
  using last_in_set by fastforce

lemma diff_list_set_remove_Nil[simp]: "diff_list xs [] = xs"
  unfolding diff_list_def by (induction xs) auto

lemma diff_list_rec: "diff_list (x # xs) ys = (if x\<in>set ys then diff_list xs ys else x#diff_list xs ys)"
  unfolding diff_list_def by (induction ys arbitrary: x xs) auto
lemma diff_list_order_irr: "set ys = set ys' \<Longrightarrow> diff_list xs ys = diff_list xs ys'"
proof (induction ys arbitrary: ys' xs)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case
    by (induction xs arbitrary: y ys ys') (simp_all add: diff_list_rec)
qed

(* Folding lists with option return typs. probably no longer relevant, was for implementing sorts by lists *)
lemma fold_Option_bind_eq_Some_start_not_None:
  "fold (\<lambda>new option . Option.bind option (f new)) list start = Some res
  \<Longrightarrow> start \<noteq> None"
  by (induction list arbitrary: start res)
    (fastforce split: option.splits if_splits simp add: bind_eq_Some_conv)+

lemma fold_Option_bind_eq_Some_at_point_not_None:
  "fold (\<lambda>new option . Option.bind option (f new)) (l1@l2) start = Some res
  \<Longrightarrow> fold (\<lambda>new option . Option.bind option (f new)) (l1) start \<noteq> None"
  by (induction l1 arbitrary: start res l2) (use fold_Option_bind_eq_Some_start_not_None in 
      \<open>fastforce split: option.splits if_splits simp add: bind_eq_Some_conv\<close>)+

lemma fold_Option_bind_eq_Some_start_not_None':
  "fold (\<lambda>(x,y) option . Option.bind option (f x y)) list start = Some res
  \<Longrightarrow> start \<noteq> None"
proof (induction list arbitrary: start res)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a list)
  then show ?case 
    by (fastforce split: option.splits if_splits prod.splits simp add: bind_eq_Some_conv)
qed

lemma fold_Option_bind_eq_None_start_None:
  "fold (\<lambda>(x,y) option . Option.bind option (f x y)) list None = None"
  by (induction list) (auto split: option.splits if_splits prod.splits)

lemma fold_Option_bind_at_some_point_None_eq_None:
  "fold (\<lambda>(x,y) option . Option.bind option (f x y)) l1 start = None \<Longrightarrow>
  fold (\<lambda>(x,y) option . Option.bind option (f x y)) (l1@l2) start = None"
proof (induction l1 arbitrary: start  l2)
  case Nil
  then show ?case using fold_Option_bind_eq_Some_start_not_None' by fastforce
next
  case (Cons a l1)
  then show ?case by simp
qed

lemma fold_Option_bind_eq_Some_at_each_point_Some:
  "fold (\<lambda>(x,y) option . Option.bind option (f x y)) (l1@l2) start = Some res
  \<Longrightarrow> (\<exists>point . fold (\<lambda>(x,y) option . Option.bind option (f x y)) l1 start = Some point
    \<and> fold (\<lambda>(x,y) option . Option.bind option (f x y)) l2 (Some point) = Some res)"
proof (induction l1 arbitrary: start res l2)
  case Nil
  then show ?case 
    using fold_Option_bind_eq_Some_start_not_None' by fastforce
next
  case (Cons a l1)
  then show ?case by simp
qed

lemma fold_Option_bind_eq_Some_at_each_point_Some':
  assumes "fold (\<lambda>(x,y) option . Option.bind option (f x y)) (xs@ys) start = Some res"
  obtains point where 
    "fold (\<lambda>(x,y) option . Option.bind option (f x y)) xs start = Some point" and
    "fold (\<lambda>(x,y) option . Option.bind option (f x y)) ys (Some point) = Some res"
  using assms fold_Option_bind_eq_Some_at_each_point_Some by fast

(* Legacy *)
corollary fold_Option_bind_eq_Some_at_point_not_None':
  "fold (\<lambda>(x,y) option . Option.bind option (f x y)) (l1@l2) start = Some res
  \<Longrightarrow> fold (\<lambda>(x,y) option . Option.bind option (f x y)) (l1) start \<noteq> None"
  using fold_Option_bind_eq_Some_at_each_point_Some by fast

(* Interestingly no longer need helper... *)
lemma fold_matches_first_step_not_None:
  assumes
    "fold (\<lambda>(T, U) subs . Option.bind subs (f T U)) (zip (x#xs) (y#ys)) (Some subs) = Some subs'" 
  obtains point where
    "f x y subs = Some point"
    "fold (\<lambda>(T, U) subs . Option.bind subs (f T U)) (zip (xs) (ys)) (Some point) = Some subs'"
  using assms fold_Option_bind_eq_Some_start_not_None' not_None_eq by fastforce

lemma fold_matches_last_step_not_None:
  assumes
    "length xs = length ys"
    "fold (\<lambda>(T, U) subs . Option.bind subs (f T U)) (zip (xs@[x]) (ys@[y])) (Some subs) = Some subs'" 
  obtains point where
    "fold (\<lambda>(T, U) subs . Option.bind subs (f T U)) (zip (xs) (ys)) (Some subs) = Some point"
    "f x y point = Some subs'"
  using assms fold_Option_bind_eq_Some_at_each_point_Some'[where xs="zip xs ys" and ys="[(x,y)]" 
      and start="Some subs" and res="subs'" and f="f"] by auto

end