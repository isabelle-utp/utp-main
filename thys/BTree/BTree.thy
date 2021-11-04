theory BTree                 
  imports Main "HOL-Data_Structures.Sorted_Less" "HOL-Data_Structures.Cmp"
begin

(* some setup to cover up the redefinition of sorted in Sorted_Less
   but keep the lemmas *)
hide_const (open) Sorted_Less.sorted
abbreviation "sorted_less \<equiv> Sorted_Less.sorted"

section "Definition of the B-Tree"

subsection "Datatype definition"

text "B-trees can be considered to have all data stored interleaved
as child nodes and separating elements (also keys or indices).
We define them to either be a Node that holds a list of pairs of children
and indices or be a completely empty Leaf."


datatype 'a btree = Leaf | Node "('a btree * 'a) list" "'a btree"

type_synonym 'a btree_list =  "('a btree * 'a) list"
type_synonym 'a btree_pair =  "('a btree * 'a)"

abbreviation subtrees where "subtrees xs \<equiv> (map fst xs)"
abbreviation separators where "separators xs \<equiv> (map snd xs)"

subsection "Inorder and Set"

text "The set of B-tree elements is defined automatically."

thm btree.set
value "set_btree (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"

text "The inorder view is defined with the help of the concat function."

fun inorder :: "'a btree \<Rightarrow> 'a list" where
  "inorder Leaf = []" |
  "inorder (Node ts t) = concat (map (\<lambda> (sub, sep). inorder sub @ [sep]) ts) @ inorder t"

abbreviation "inorder_pair  \<equiv> \<lambda>(sub,sep). inorder sub @ [sep]"
abbreviation "inorder_list ts \<equiv> concat (map inorder_pair ts)"

(* this abbreviation makes handling the list much nicer *)
thm inorder.simps

value "inorder (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"

subsection "Height and Balancedness"

class height =
  fixes height :: "'a \<Rightarrow> nat"

instantiation btree :: (type) height
begin

fun height_btree :: "'a btree \<Rightarrow> nat" where
  "height Leaf = 0" |
  "height (Node ts t) = Suc (Max (height ` (set (subtrees ts@[t]))))"

instance ..

end

text "Balancedness is defined is close accordance to the definition by Ernst"

fun bal:: "'a btree \<Rightarrow> bool" where
  "bal Leaf = True" |
  "bal (Node ts t) = (
    (\<forall>sub \<in> set (subtrees ts). height sub = height t) \<and>
    (\<forall>sub \<in> set (subtrees ts). bal sub) \<and> bal t
  )"


value "height (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"


subsection "Order"

text "The order of a B-tree is defined just as in the original paper by Bayer."

(* alt1: following knuths definition to allow for any
   natural number as order and resolve ambiguity *)
(* alt2: use range [k,2*k] allowing for valid btrees
   from k=1 onwards NOTE this is what I ended up implementing *)

fun order:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
  "order k Leaf = True" |
  "order k (Node ts t) = (
  (length ts \<ge> k)  \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>sub \<in> set (subtrees ts). order k sub) \<and> order k t
)"

text \<open>The special condition for the root is called \textit{root\_order}\<close>

(* the invariant for the root of the btree *)
fun root_order:: "nat \<Rightarrow> 'a btree \<Rightarrow> bool" where
  "root_order k Leaf = True" |
  "root_order k (Node ts t) = (
  (length ts > 0) \<and>
  (length ts \<le> 2*k) \<and>
  (\<forall>s \<in> set (subtrees ts). order k s) \<and> order k t
)"


subsection "Auxiliary Lemmas"

(* auxiliary lemmas when handling sets *)
lemma separators_split:
  "set (separators (l@(a,b)#r)) = set (separators l) \<union> set (separators r) \<union> {b}"
  by simp

lemma subtrees_split:
  "set (subtrees (l@(a,b)#r)) = set (subtrees l) \<union> set (subtrees r) \<union> {a}"
  by simp

(* height and set lemmas *)


lemma finite_set_ins_swap:
  assumes "finite A"
  shows "max a (Max (Set.insert b A)) = max b (Max (Set.insert a A))"
  using Max_insert assms max.commute max.left_commute by fastforce

lemma finite_set_in_idem:
  assumes "finite A"
  shows "max a (Max (Set.insert a A)) = Max (Set.insert a A)"
  using Max_insert assms max.commute max.left_commute by fastforce

lemma height_Leaf: "height t = 0 \<longleftrightarrow> t = Leaf"
  by (induction t) (auto)

lemma height_btree_order:
  "height (Node (ls@[a]) t) = height (Node (a#ls) t)"
  by simp

lemma height_btree_sub: 
  "height (Node ((sub,x)#ls) t) = max (height (Node ls t)) (Suc (height sub))"
  by simp

lemma height_btree_last: 
  "height (Node ((sub,x)#ts) t) = max (height (Node ts sub)) (Suc (height t))"
  by (induction ts) auto


lemma set_btree_inorder: "set (inorder t) = set_btree t"
  apply(induction t)
   apply(auto)
  done


lemma child_subset: "p \<in> set t \<Longrightarrow> set_btree (fst p) \<subseteq> set_btree (Node t n)"
  apply(induction p arbitrary: t n)
  apply(auto)
  done

lemma some_child_sub: 
  assumes "(sub,sep) \<in> set t"
  shows "sub \<in> set (subtrees t)"
    and "sep \<in> set (separators t)"
  using assms by force+ 

(* balancedness lemmas *)


lemma bal_all_subtrees_equal: "bal (Node ts t) \<Longrightarrow> (\<forall>s1 \<in> set (subtrees ts). \<forall>s2 \<in> set (subtrees ts). height s1 = height s2)"
  by (metis BTree.bal.simps(2))


lemma fold_max_set: "\<forall>x \<in> set t. x = f \<Longrightarrow> fold max t f = f"
  apply(induction t)
   apply(auto simp add: max_def_raw)
  done

lemma height_bal_tree: "bal (Node ts t) \<Longrightarrow> height (Node ts t) = Suc (height t)"
  by (induction ts) auto



lemma bal_split_last: 
  assumes "bal (Node (ls@(sub,sep)#rs) t)"
  shows "bal (Node (ls@rs) t)"
    and "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@rs) t)"
  using assms by auto


lemma bal_split_right: 
  assumes "bal (Node (ls@rs) t)"
  shows "bal (Node rs t)"
    and "height (Node rs t) = height (Node (ls@rs) t)"
  using assms by (auto simp add: image_constant_conv)

lemma bal_split_left:
  assumes "bal (Node (ls@(a,b)#rs) t)"
  shows "bal (Node ls a)"
    and "height (Node ls a) = height (Node (ls@(a,b)#rs) t)"
  using assms by (auto simp add: image_constant_conv)


lemma bal_substitute: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height t = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  unfolding bal.simps
  by auto

lemma bal_substitute_subtree: "\<lbrakk>bal (Node (ls@(a,b)#rs) t); height a = height c; bal c\<rbrakk> \<Longrightarrow> bal (Node (ls@(c,b)#rs) t)"
  using bal_substitute
  by auto

lemma bal_substitute_separator: "bal (Node (ls@(a,b)#rs) t) \<Longrightarrow> bal (Node (ls@(a,c)#rs) t)"
  unfolding bal.simps
  by auto

(* order lemmas *)

lemma order_impl_root_order: "\<lbrakk>k > 0; order k t\<rbrakk> \<Longrightarrow> root_order k t"
  apply(cases t)
   apply(auto)
  done


(* sorted inorder implies that some sublists are sorted. This can be followed directly *)

lemma sorted_inorder_list_separators: "sorted_less (inorder_list ts) \<Longrightarrow> sorted_less (separators ts)"
  apply(induction ts)
   apply (auto simp add: sorted_lems)
  done

corollary sorted_inorder_separators: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (separators ts)"
  using sorted_inorder_list_separators sorted_wrt_append
  by auto


lemma sorted_inorder_list_subtrees:
  "sorted_less (inorder_list ts) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
  apply(induction ts)
   apply (auto simp add: sorted_lems)+
  done

corollary sorted_inorder_subtrees: "sorted_less (inorder (Node ts t)) \<Longrightarrow> \<forall> sub \<in> set (subtrees ts). sorted_less (inorder sub)"
  using sorted_inorder_list_subtrees sorted_wrt_append by auto

lemma sorted_inorder_list_induct_subtree:
  "sorted_less (inorder_list (ls@(sub,sep)#rs)) \<Longrightarrow> sorted_less (inorder sub)"
  by (simp add: sorted_wrt_append)

corollary sorted_inorder_induct_subtree:
  "sorted_less (inorder (Node (ls@(sub,sep)#rs) t)) \<Longrightarrow> sorted_less (inorder sub)"
  by (simp add: sorted_wrt_append)

lemma sorted_inorder_induct_last: "sorted_less (inorder (Node ts t)) \<Longrightarrow> sorted_less (inorder t)"
  by (simp add: sorted_wrt_append)



end