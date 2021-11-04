chapter\<open>Code Generation\<close>
text\<open>This chapter details the code generator setup to produce executable Scala code for our
inference technique.\<close>

section\<open>Lists\<close>
text\<open>Here we define some equivalent definitions which make for a faster implementation. We also
make use of the \texttt{code\_printing} statement such that native Scala implementations of common
list operations are used instead of redefining them. This allows us to use the \texttt{par}
construct such that the parallel implementations are used, which makes for an even faster
implementation.\<close>

theory Code_Target_List
imports Main
begin

declare List.insert_def [code del]
declare member_rec [code del]

lemma [code]: "List.insert x xs = (if List.member xs x then xs else x#xs)"
  by (simp add: in_set_member)

declare enumerate_eq_zip [code]
declare foldr_conv_foldl [code]
declare map_filter_map_filter [code_unfold del]

(* Use the native implementations of list functions *)
definition "flatmap l f = List.maps f l"

lemma [code]: "List.maps f l = flatmap l f"
  by (simp add: flatmap_def)

definition "map_code l f = List.map f l"
lemma [code]:"List.map f l = map_code l f"
  by (simp add: map_code_def)

lemma [code]: "removeAll a l = filter (\<lambda>x. x \<noteq> a) l"
  by (induct l arbitrary: a) simp_all

definition "filter_code l f = List.filter f l"

lemma [code]: "List.filter l f = filter_code f l"
  by (simp add: filter_code_def)

definition all :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "all l f = list_all f l"

lemma [code]: "list_all f l = all l f"
  by (simp add: all_def)

definition ex :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "ex l f = list_ex f l"

lemma [code]: "list_ex f l = ex l f"
  by (simp add: ex_def)

declare foldl_conv_fold[symmetric]

lemma fold_conv_foldl [code]: "fold f xs s = foldl (\<lambda>x s. f s x) s xs"
  by (simp add: foldl_conv_fold)

lemma code_list_eq [code]:
  "HOL.equal xs ys \<longleftrightarrow> length xs = length ys \<and> (\<forall>(x,y) \<in> set (zip xs ys). x = y)"
  apply (simp add: HOL.equal_class.equal_eq)
  by (simp add: Ball_set list_eq_iff_zip_eq)

definition take_map :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "take_map n l = (if length l \<le> n then l else map (\<lambda>i. l ! i) [0..<n])"

lemma nth_take_map: "i < n \<Longrightarrow> take_map n xs ! i = xs ! i"
  by (simp add: take_map_def)

lemma [code]: "take n l = take_map n l"
  by (simp add: list_eq_iff_nth_eq min_def take_map_def)

fun upt_tailrec :: "nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "upt_tailrec i 0 l = l" |
  "upt_tailrec i (Suc j) l = (if i \<le> j then upt_tailrec i j ([j]@l) else l)"

lemma upt_arbitrary_l: "(upt i j)@l = upt_tailrec i j l"
  by (induct i j l rule: upt_tailrec.induct, auto)

lemma [code]: "upt i j = upt_tailrec i j []"
  by (metis upt_arbitrary_l append_Nil2)

function max_sort :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "max_sort [] l = l" |
  "max_sort (h#t) l = (let u = (h#t); m = Max (set u) in max_sort (removeAll m u) (m#l))"
  using splice.cases apply blast
  by auto
termination
  apply (relation "measures [\<lambda>(l1, l2). length l1]")
   apply simp
  by (metis Max_eq_iff List.finite_set case_prod_conv length_removeAll_less list.distinct(1) measures_less set_empty)

lemma remdups_fold [code]:
  "remdups l = foldr (\<lambda>i l. if i \<in> set l then l else i#l) l []"
proof(induct l)
  case Nil
  then show ?case
    by simp
next
  case (Cons a l)
  then show ?case
    apply (simp)
    apply standard
     apply (metis set_remdups)
    using set_remdups by fastforce
qed

code_printing
  constant Cons \<rightharpoonup> (Scala) "_::_"
  | constant rev \<rightharpoonup> (Scala) "_.par.reverse.toList"
  | constant List.member \<rightharpoonup> (Scala) "_.contains((_))"
  | constant "List.remdups" \<rightharpoonup> (Scala) "_.par.distinct.toList"
  | constant "List.length" \<rightharpoonup> (Scala) "Nat.Nata(_.par.length)"
  | constant "zip" \<rightharpoonup> (Scala) "_.par.zip((_)).toList"
  | constant "flatmap" \<rightharpoonup> (Scala) "_.par.flatMap((_)).toList"
  | constant "List.null" \<rightharpoonup> (Scala) "_.isEmpty"
  | constant "map_code" \<rightharpoonup> (Scala) "_.par.map((_)).toList"
  | constant "filter_code" \<rightharpoonup> (Scala) "_.par.filter((_)).toList"
  | constant "all" \<rightharpoonup> (Scala) "_.par.forall((_))"
  | constant "ex" \<rightharpoonup> (Scala) "_.par.exists((_))"
  | constant "nth" \<rightharpoonup> (Scala) "_(Code'_Numeral.integer'_of'_nat((_)).toInt)"
  | constant "foldl" \<rightharpoonup> (Scala) "Dirties.foldl"
  | constant "hd" \<rightharpoonup> (Scala) "_.head"

end
