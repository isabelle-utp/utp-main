theory BTree_Split
  imports BTree_Set
begin

section "Abstract split functions"

subsection "Linear split"

text "Finally we show that the split axioms are feasible
       by providing an example split function"

(*TODO: at some point this better be replaced with something binary search like *)
fun linear_split_help:: "(_\<times>'a::linorder) list \<Rightarrow> _ \<Rightarrow> (_\<times>_) list \<Rightarrow>  ((_\<times>_) list \<times> (_\<times>_) list)" where
  "linear_split_help [] x prev = (prev, [])" |
  "linear_split_help ((sub, sep)#xs) x prev = (if sep < x then linear_split_help xs x (prev @ [(sub, sep)]) else (prev, (sub,sep)#xs))"

fun linear_split:: "(_\<times>'a::linorder) list \<Rightarrow> _ \<Rightarrow> ((_\<times>_) list \<times> (_\<times>_) list)" where
  "linear_split xs x = linear_split_help xs x []"

text "Linear split is similar to well known functions, therefore a quick proof can be done."

lemma linear_split_alt: "linear_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"
proof -

  have "linear_split_help xs x prev = (prev @ takeWhile (\<lambda>(_, s). s < x) xs, dropWhile (\<lambda>(_, s). s < x) xs)"
    for prev
    apply (induction xs arbitrary: prev)
     apply auto
    done
  thus ?thesis by auto
qed

global_interpretation btree_linear_search: split linear_split
  (* the below definitions are required to be set here for evaluating example code... *)
  defines btree_ls_isin = btree_linear_search.isin 
    and btree_ls_ins = btree_linear_search.ins
    and btree_ls_insert = btree_linear_search.insert
    and btree_ls_del = btree_linear_search.del
    and btree_ls_delete = btree_linear_search.delete
  apply unfold_locales
  unfolding linear_split_alt
    apply (auto split: list.splits)
  subgoal
    by (metis (no_types, lifting) case_prodD in_set_conv_decomp takeWhile_eq_all_conv takeWhile_idem)
  subgoal
    by (metis case_prod_conv hd_dropWhile le_less_linear list.sel(1) list.simps(3))
  done


text "Some examples follow to show that the implementation works
      and the above lemmas make sense. The examples are visualized in the thesis."

abbreviation "btree\<^sub>i \<equiv> btree_ls_insert"
abbreviation "btree\<^sub>d \<equiv> btree_ls_delete"

value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      root_order k x"
value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      bal x"
value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      sorted_less (inorder x)"
value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      x"
value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      btree\<^sub>i k 9 x"
value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      btree\<^sub>i k 1 (btree\<^sub>i k 9 x)"
value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      btree\<^sub>d k 10 (btree\<^sub>i k 1 (btree\<^sub>i k 9 x))"
value "let k=2::nat; x::nat btree = (Node [(Node [(Leaf, 3),(Leaf, 5),(Leaf, 6)] Leaf, 10)] (Node [(Leaf, 14), (Leaf, 20)] Leaf)) in
      btree\<^sub>d k 3 (btree\<^sub>d k 10 (btree\<^sub>i k 1 (btree\<^sub>i k 9 x)))"

text "For completeness, we also proved an explicit proof of the locale
requirements."

lemma some_child_sm: "linear_split_help t y xs = (ls,(sub,sep)#rs) \<Longrightarrow> y \<le> sep"
  apply(induction t y xs rule: linear_split_help.induct)
   apply(simp_all)
  by (metis Pair_inject le_less_linear list.inject)



lemma linear_split_append: "linear_split_help xs p ys = (ls,rs) \<Longrightarrow> ls@rs = ys@xs"
  apply(induction xs p ys rule: linear_split_help.induct)
   apply(simp_all)
  by (metis Pair_inject)

lemma linear_split_sm: "\<lbrakk>linear_split_help xs p ys = (ls,rs); sorted_less (separators (ys@xs)); \<forall>sep \<in> set (separators ys). p > sep\<rbrakk> \<Longrightarrow> \<forall>sep \<in> set (separators ls). p > sep"
  apply(induction xs p ys rule: linear_split_help.induct)
   apply(simp_all)
  by (metis prod.inject)+

value "linear_split [((Leaf::nat btree), 2)] (1::nat)"

(* TODO still has format for older proof *)
lemma linear_split_gr:
  "\<lbrakk>linear_split_help xs p ys = (ls,rs); sorted_less (separators (ys@xs)); \<forall>(sub,sep) \<in> set ys. p > sep\<rbrakk> \<Longrightarrow> 
(case rs of [] \<Rightarrow> True | (_,sep)#_ \<Rightarrow> p \<le> sep)"
  apply(cases rs)
  by (auto simp add: some_child_sm)


lemma linear_split_req:
  assumes  "linear_split xs p = (ls,(sub,sep)#rs)"
    and "sorted_less (separators xs)"
  shows  "p \<le> sep"
  using assms linear_split_gr by fastforce

lemma linear_split_req2:
  assumes  "linear_split xs p = (ls@[(sub,sep)],rs)"
    and "sorted_less (separators xs)"
  shows  "sep < p"
  using linear_split_sm[of xs p "[]" "ls@[(sub,sep)]" rs]
  using assms(1) assms(2)
  by (metis Nil_is_map_conv Un_iff append_self_conv2 empty_iff empty_set linear_split.elims prod_set_simps(2) separators_split snd_eqD snds.intros)


interpretation split linear_split
  by (simp add: linear_split_req linear_split_req2 linear_split_append split_def)


subsection "Binary split"

text "It is possible to define a binary split predicate.
      However, even proving that it terminates is uncomfortable."

function (sequential) binary_split_help:: "(_\<times>'a::linorder) list \<Rightarrow> (_\<times>'a) list \<Rightarrow> (_\<times>'a) list \<Rightarrow> 'a \<Rightarrow>  ((_\<times>_) list \<times> (_\<times>_) list)" where
  "binary_split_help ls [] rs x = (ls,rs)" |
  "binary_split_help ls as rs x = (let (mls, mrs) = split_half as in (
  case mrs of (sub,sep)#mrrs \<Rightarrow> (
    if x < sep then binary_split_help ls mls (mrs@rs) x
    else if x > sep then binary_split_help (ls@mls@[(sub,sep)]) mrrs rs x
    else (ls@mls, mrs@rs)
    )
  )
)"
  by pat_completeness auto
termination
  apply(relation "measure (\<lambda>(ls,xs,rs,x). length xs)")
    apply (auto)
  by (metis append_take_drop_id length_Cons length_append lessI trans_less_add2)


fun binary_split where
  "binary_split as x = binary_split_help [] as [] x"

text "We can show that it will return sublists that concatenate to
      the original list again but will not show that it fulfils sortedness properties."

lemma "binary_split_help as bs cs x = (ls,rs) \<Longrightarrow> (as@bs@cs) = (ls@rs)"
  apply(induction as bs cs x arbitrary: ls rs rule: binary_split_help.induct)
   apply (auto simp add: drop_not_empty split!: list.splits )
  subgoal for ls a b va rs  x lsa rsa aa ba x22
    apply(cases "cmp x ba")
      apply auto
      apply (metis Cons_eq_appendI append_eq_appendI append_take_drop_id)
     apply (metis append_take_drop_id)
    by (metis Cons_eq_appendI append_eq_appendI append_take_drop_id)
  done

lemma "\<lbrakk>sorted_less (separators (as@bs@cs)); binary_split_help as bs cs x = (ls,rs); \<forall>y \<in> set (separators as). y < x\<rbrakk>
\<Longrightarrow> \<forall>y \<in> set (separators ls). y < x"
  oops



end
