subsection \<open>Optimal Binary Search Trees\<close>

text \<open>
The material presented in this section just contains a simple and non-optimal version
(cubic instead of quadratic in the number of keys).
It can now be viewed to be superseded by the AFP entry \<open>Optimal_BST\<close>.
It is kept here as a more easily understandable example and for archival purposes.
\<close>

theory OptBST
imports
  "HOL-Library.Tree"
  "HOL-Library.Code_Target_Numeral"
  "../state_monad/State_Main" 
  "../heap_monad/Heap_Default"
  Example_Misc
  "HOL-Library.Product_Lexorder"
  "HOL-Library.RBT_Mapping"
begin

subsubsection \<open>Function \<open>argmin\<close>\<close>

text \<open>Function \<open>argmin\<close> iterates over a list and returns the rightmost element
that minimizes a given function:\<close>

fun argmin :: "('a \<Rightarrow> ('b::linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a" where
"argmin f (x#xs) =
  (if xs = [] then x else
   let m = argmin f xs in if f x < f m then x else m)"

text \<open>Note that @{term arg_min_list} is similar but returns the leftmost element.\<close>

lemma argmin_forall: "xs \<noteq> [] \<Longrightarrow> (\<And>x. x\<in>set xs \<Longrightarrow> P x) \<Longrightarrow> P (argmin f xs)"
by(induction xs) (auto simp: Let_def)

lemma argmin_Min: "xs \<noteq> [] \<Longrightarrow> f (argmin f xs) = Min (f ` set xs)"
by(induction xs) (auto simp: min_def intro!: antisym)


subsubsection \<open>Misc\<close>

lemma upto_join: "\<lbrakk> i \<le> j; j \<le> k \<rbrakk> \<Longrightarrow> [i..j-1] @ j # [j+1..k] = [i..k]"
  using upto_rec1 upto_split1 by auto

lemma atLeastAtMost_split:
  "{i..j} = {i..k} \<union> {k+1..j}" if "i \<le> k" "k \<le> j" for i j k :: int
  using that by auto

lemma atLeastAtMost_split_insert:
  "{i..k} = insert k {i..k-1}" if "k \<ge> i" for i :: int
  using that by auto

subsubsection \<open>Definitions\<close>

context
fixes W :: "int \<Rightarrow> int \<Rightarrow> nat"
begin

fun wpl :: "int \<Rightarrow> int \<Rightarrow> int tree \<Rightarrow> nat" where
   "wpl i j Leaf = 0"
 | "wpl i j (Node l k r) = wpl i (k-1) l + wpl (k+1) j r + W i j"

function min_wpl :: "int \<Rightarrow> int \<Rightarrow> nat" where
"min_wpl i j =
  (if i > j then 0
   else min_list (map (\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) [i..j]))"
  by auto
termination by (relation "measure (\<lambda>(i,j) . nat(j-i+1))") auto
declare min_wpl.simps[simp del]

function opt_bst :: "int * int \<Rightarrow> int tree" where
"opt_bst (i,j) =
  (if i > j then Leaf else argmin (wpl i j) [\<langle>opt_bst (i,k-1), k, opt_bst (k+1,j)\<rangle>. k \<leftarrow> [i..j]])"
  by auto
termination by (relation "measure (\<lambda>(i,j) . nat(j-i+1))") auto
declare opt_bst.simps[simp del]


subsubsection \<open>Functional Memoization\<close>

context
  fixes n :: nat
begin

context fixes
  mem :: "nat option array"
begin

memoize_fun min_wpl\<^sub>T: min_wpl
  with_memory dp_consistency_heap_default where bound = "Bound (0, 0) (int n, int n)" and mem="mem"
  monadifies (heap) min_wpl.simps

context includes heap_monad_syntax begin
thm min_wpl\<^sub>T'.simps min_wpl\<^sub>T_def
end

memoize_correct
  by memoize_prover

lemmas memoized_empty = min_wpl\<^sub>T.memoized_empty

end (* Fixed array *)

context
  includes heap_monad_syntax
  notes [simp del] = min_wpl\<^sub>T'.simps
begin

definition "min_wpl\<^sub>h \<equiv> \<lambda> i j. Heap_Monad.bind (mem_empty (n * n)) (\<lambda> mem. min_wpl\<^sub>T' mem i j)"

lemma min_wpl_heap:
  "min_wpl i j = result_of (min_wpl\<^sub>h i j) Heap.empty"
  unfolding min_wpl\<^sub>h_def
  using memoized_empty[of _ "\<lambda> m. \<lambda> (a, b). min_wpl\<^sub>T' m a b" "(i, j)", OF min_wpl\<^sub>T.crel]
  by (simp add: index_size_defs)

end

end (* Bound *)

context includes state_monad_syntax begin

memoize_fun min_wpl\<^sub>m: min_wpl with_memory dp_consistency_mapping monadifies (state) min_wpl.simps
thm min_wpl\<^sub>m'.simps

memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = min_wpl\<^sub>m.memoized_correct

memoize_fun opt_bst\<^sub>m: opt_bst with_memory dp_consistency_mapping monadifies (state) opt_bst.simps
thm opt_bst\<^sub>m'.simps

memoize_correct
  by memoize_prover
print_theorems
lemmas [code] = opt_bst\<^sub>m.memoized_correct

end


subsubsection \<open>Correctness Proof\<close>

lemma min_wpl_minimal:
  "inorder t = [i..j] \<Longrightarrow> min_wpl i j \<le> wpl i j t"
proof(induction i j t rule: wpl.induct)
  case (1 i j)
  then show ?case by (simp add: min_wpl.simps)
next
  case (2 i j l k r)
  then show ?case 
  proof cases
    assume "i > j" thus ?thesis by(simp add: min_wpl.simps)
  next
    assume [arith]: "\<not> i > j"
    have kk_ij: "k\<in>set[i..j]" using 2 
        by (metis set_inorder tree.set_intros(2))
        
    let ?M = "((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) ` {i..j})"
    let ?w = "min_wpl i (k-1) + min_wpl (k+1) j + W i j"
 
    have aux_min:"Min ?M \<le> ?w"
    proof (rule Min_le)
      show "finite ?M" by simp
      show "?w \<in> ?M" using kk_ij by auto
    qed

    have"inorder \<langle>l,k,r\<rangle> = inorder l @k#inorder r" by auto
    from this have C:"[i..j] = inorder l @ k#inorder r" using 2 by auto
    have D: "[i..j] = [i..k-1]@k#[k+1..j]" using kk_ij upto_rec1 upto_split1
      by (metis atLeastAtMost_iff set_upto) 

    have l_inorder: "inorder l = [i..k-1]"
      by (smt C D append_Cons_eq_iff atLeastAtMost_iff set_upto)
    have r_inorder: "inorder r = [k+1..j]" 
      by (smt C D append_Cons_eq_iff atLeastAtMost_iff set_upto)

    have "min_wpl i j = Min ?M" by (simp add: min_wpl.simps min_list_Min)
    also have "... \<le> ?w" by (rule aux_min)    
    also have "... \<le> wpl i (k-1) l + wpl (k+1) j r + W i j" using l_inorder r_inorder "2.IH" by simp
    also have "... = wpl i j \<langle>l,k,r\<rangle>" by simp
    finally show ?thesis .
  qed
qed

lemma opt_bst_correct: "inorder (opt_bst (i,j)) = [i..j]"
  by (induction "(i,j)" arbitrary: i j rule: opt_bst.induct)
     (clarsimp simp: opt_bst.simps upto_join | rule argmin_forall)+

lemma wpl_opt_bst: "wpl i j (opt_bst (i,j)) = min_wpl i j"
proof(induction i j rule: min_wpl.induct)
  case (1 i j)
  show ?case
  proof cases
    assume "i > j" thus ?thesis by(simp add: min_wpl.simps opt_bst.simps)
  next
    assume *[arith]: "\<not> i > j"
    let ?ts = "[\<langle>opt_bst (i,k-1), k, opt_bst (k+1,j)\<rangle>. k <- [i..j]]"
    let ?M = "((\<lambda>k. min_wpl i (k-1) + min_wpl (k+1) j + W i j) ` {i..j})"
    have "?ts \<noteq> []" by (auto simp add: upto.simps)
    have "wpl i j (opt_bst (i,j)) = wpl i j (argmin (wpl i j) ?ts)" by (simp add: opt_bst.simps)
    also have "\<dots> = Min (wpl i j ` (set ?ts))" by (rule argmin_Min[OF \<open>?ts \<noteq> []\<close>])
    also have "\<dots> = Min ?M"
    proof (rule arg_cong[where f=Min])
      show "wpl i j ` (set ?ts) = ?M"
        by (fastforce simp: Bex_def image_iff 1[OF *])
    qed
    also have "\<dots> = min_wpl i j" by (simp add: min_wpl.simps min_list_Min)
    finally show ?thesis .
  qed
qed

lemma opt_bst_is_optimal:
  "inorder t = [i..j] \<Longrightarrow> wpl i j (opt_bst (i,j)) \<le> wpl i j t"
  by (simp add: min_wpl_minimal wpl_opt_bst)

end (* Weight function *)

subsubsection \<open>Access Frequencies\<close>
text \<open>Usually, the problem is phrased in terms of access frequencies.
We now give an interpretation of @{term wpl} in this view and show that we have actually computed
the right thing.\<close>

context
  \<comment> \<open>We are given a range \<open>[i..j]\<close> of integer keys with access frequencies \<open>p\<close>.
  These can be thought of as a probability distribution but are not required to represent one.
  This model assumes that the tree will contain all keys in the range \<open>[i..j]\<close>.
  See \<open>Optimal_BST\<close> for a model with missing keys.
  \<close>
  fixes p :: "int \<Rightarrow> nat"
begin

\<comment> \<open>The \<^emph>\<open>weighted path path length\<close> (or \<open>cost\<close>) of a tree.\<close>
fun cost :: "int tree \<Rightarrow> nat" where
  "cost Leaf = 0"
| "cost (Node l k r) = sum p (set_tree l) + cost l + p k + cost r + sum p (set_tree r)"

\<comment> \<open>Deriving a weight function from \<open>p\<close>.\<close>
qualified definition W where
  "W i j = sum p {i..j}"

\<comment> \<open>We will use this later for computing \<open>W\<close> efficiently.\<close>
lemma W_rec:
  "W i j = (if j \<ge> i then W i (j - 1) + p j else 0)"
  unfolding W_def by (simp add: atLeastAtMost_split_insert)

\<comment> \<open>The weight function correctly implements costs.\<close>
lemma inorder_wpl_correct:
  "inorder t = [i..j] \<Longrightarrow> wpl W i j t = cost t"
proof (induction t arbitrary: i j)
case Leaf
  show ?case
    by simp
next
  case (Node l k r)
  from \<open>inorder \<langle>l, k, r\<rangle> = [i..j]\<close> have *: "i \<le> k" "k \<le> j"
     by - (simp, metis atLeastAtMost_iff in_set_conv_decomp set_upto)+
   moreover from \<open>i \<le> k\<close> \<open>k \<le> j\<close> have "inorder l = [i..k-1]" "inorder r = [k+1..j]"
    using \<open>inorder \<langle>l, k, r\<rangle> = [i..j]\<close>[symmetric] by (simp add: upto_split3 append_Cons_eq_iff)+
  ultimately show ?case
    by (simp add: Node.IH, subst W_def, subst atLeastAtMost_split)
       (simp add: sum.union_disjoint atLeastAtMost_split_insert flip: set_inorder)+
qed

text \<open>The optimal binary search tree has minimal cost among all binary search trees.\<close>
lemma opt_bst_has_optimal_cost:
  "inorder t = [i..j] \<Longrightarrow> cost (opt_bst W (i,j)) \<le> cost t"
  using inorder_wpl_correct opt_bst_is_optimal opt_bst_correct by metis

text \<open>
  The function @{term min_wpl} correctly computes the minimal cost among all binary search trees:
  \<^item> Its cost is a lower bound for the cost of all binary search trees
  \<^item> Its cost actually corresponds to an optimal binary search tree
\<close>
lemma min_wpl_minimal_cost:
  "inorder t = [i..j] \<Longrightarrow> min_wpl W i j \<le> cost t"
  using inorder_wpl_correct min_wpl_minimal by metis

lemma min_wpl_tree:
  "cost (opt_bst W (i,j)) = min_wpl W i j"
  using wpl_opt_bst opt_bst_correct inorder_wpl_correct by metis


paragraph \<open>An alternative view of costs.\<close>

fun depth :: "'a \<Rightarrow> 'a tree \<Rightarrow> nat extended" where
  "depth x Leaf = \<infinity>"
| "depth x (Node l k r) = (if x = k then 1 else min (depth x l) (depth x r) + 1)"

fun the_fin where
  "the_fin (Fin x) = x" | "the_fin _ = undefined"

definition cost' :: "int tree \<Rightarrow> nat" where
  "cost' t = sum (\<lambda>x. the_fin (depth x t) * p x) (set_tree t)"

lemma [simp]:
  "the_fin 1 = 1"
  by (simp add: one_extended_def)

lemma set_tree_depth:
  assumes "x \<notin> set_tree t"
  shows "depth x t = \<infinity>"
  using assms by (induction t) auto

lemma depth_inf_iff:
  "depth x t = \<infinity> \<longleftrightarrow> x \<notin> set_tree t"
  apply (induction t)
   apply (auto simp: one_extended_def)
  subgoal for t1 k t2
    by (cases "depth x t1"; cases "depth x t2") auto
  subgoal for t1 k t2
    by (cases "depth x t1"; cases "depth x t2") auto
  subgoal for t1 k t2
    by (cases "depth x t1"; cases "depth x t2") auto
  subgoal for t1 k t2
    by (cases "depth x t1"; cases "depth x t2") auto
  done

lemma depth_not_neg_inf[simp]:
  "depth x t = -\<infinity> \<longleftrightarrow> False"
  apply (induction t)
   apply (auto simp: one_extended_def)
  subgoal for t1 k t2
    by (cases "depth x t1"; cases "depth x t2") auto
  done

lemma depth_FinD:
  assumes "x \<in> set_tree t"
  obtains d where "depth x t = Fin d"
  using assms by (cases "depth x t") (auto simp: depth_inf_iff)

lemma cost'_Leaf[simp]:
  "cost' Leaf = 0"
  unfolding cost'_def by simp

lemma cost'_Node:
  "distinct (inorder \<langle>l, x, r\<rangle>) \<Longrightarrow>
  cost' \<langle>l, x, r\<rangle> = sum p (set_tree l) + cost' l + p x + cost' r + sum p (set_tree r)"
  unfolding cost'_def
  apply simp
  apply (subst sum.union_disjoint)
     apply (simp; fail)+
  apply (subst sum.cong[OF HOL.refl, where h = "\<lambda>x. (the_fin (depth x l) + 1) * p x"])
  subgoal for k
    using set_tree_depth by (force simp: one_extended_def elim: depth_FinD)
  apply (subst (2) sum.cong[OF HOL.refl, where h = "\<lambda>x. (the_fin (depth x r) + 1) * p x"])
  subgoal
    using set_tree_depth by (force simp: one_extended_def elim: depth_FinD)
  apply (simp add: sum.distrib)
  done

\<comment> \<open>The two variants coincide\<close>
lemma weight_correct:
  "distinct (inorder t) \<Longrightarrow> cost' t = cost t"
  by (induction t; simp add: cost'_Node)


subsubsection \<open>Memoizing Weights\<close>

function W_fun where
  "W_fun i j = (if i > j then 0 else W_fun i (j - 1) + p j)"
  by auto

termination
  by (relation "measure (\<lambda>(i::int, j::int). nat (j - i + 1))") auto

lemma W_fun_correct:
  "W_fun i j = W i j"
  by (induction rule: W_fun.induct) (simp add: W_def atLeastAtMost_split_insert)

memoize_fun W\<^sub>m: W_fun
  with_memory  dp_consistency_mapping
  monadifies (state) W_fun.simps

memoize_correct
  by memoize_prover

definition
  "compute_W n = snd (run_state (State_Main.map\<^sub>T' (\<lambda>i. W\<^sub>m' i n) [0..n]) Mapping.empty)"

notation W\<^sub>m.crel_vs ("crel")

lemmas W\<^sub>m_crel = W\<^sub>m.crel[unfolded W\<^sub>m.consistentDP_def, THEN rel_funD,
      of "(m, x)" "(m, y)" for m x y, unfolded prod.case]

lemma compute_W_correct:
  assumes "Mapping.lookup (compute_W n) (i, j) = Some x"
  shows "W i j = x"
proof -
  include state_monad_syntax app_syntax lifting_syntax
  let ?p = "State_Main.map\<^sub>T' (\<lambda>i. W\<^sub>m' i n) [0..n]"
  let ?q = "map (\<lambda>i. W i n) [0..n]"
  have "?q = map $ \<llangle>(\<lambda>i. W_fun i n)\<rrangle> $ \<llangle>[0..n]\<rrangle>"
    unfolding Wrap_def App_def W_fun_correct ..
  have "?p = State_Main.map\<^sub>T . \<langle>\<lambda>i. W\<^sub>m' i n\<rangle> . \<langle>[0..n]\<rangle>"
    unfolding State_Monad_Ext.fun_app_lifted_def State_Main.map\<^sub>T_def bind_left_identity ..
  \<comment> \<open>Not forgetting to write @{term  "list_all2 (=)"} instead of @{term "(=)"} was the tricky part.\<close>
  have "W\<^sub>m.crel_vs (list_all2 (=)) ?q ?p"
    unfolding \<open>?p = _\<close> \<open>?q = _\<close>
    apply (subst Transfer.Rel_def[symmetric])
    apply memoize_prover_match_step+
    apply (subst Rel_def, rule W\<^sub>m_crel, rule HOL.refl)
    done
  then have "W\<^sub>m.cmem (compute_W n)"
    unfolding compute_W_def by (elim W\<^sub>m.crel_vs_elim[OF _ W\<^sub>m.cmem_empty]; simp del: W\<^sub>m'.simps)
  with assms show ?thesis
    unfolding W_fun_correct[symmetric] by (elim W\<^sub>m.cmem_elim) (simp)+
qed

definition
  "min_wpl' i j \<equiv>
  let
    M = compute_W j;
    W = (\<lambda>i j. case Mapping.lookup M (i, j) of None \<Rightarrow> W i j | Some x \<Rightarrow> x)
  in min_wpl W i j"

lemma W_compute: "W i j = (case Mapping.lookup (compute_W n) (i, j) of None \<Rightarrow> W i j | Some x \<Rightarrow> x)"
  by (auto dest: compute_W_correct split: option.split)

lemma min_wpl'_correct:
  "min_wpl' i j = min_wpl W i j"
  using W_compute unfolding min_wpl'_def by simp

definition
  "opt_bst' i j \<equiv>
  let
    M = compute_W j;
    W = (\<lambda>i j. case Mapping.lookup M (i, j) of None \<Rightarrow> W i j | Some x \<Rightarrow> x)
  in opt_bst W (i, j)"

lemma opt_bst'_correct:
  "opt_bst' i j = opt_bst W (i, j)"
  using W_compute unfolding opt_bst'_def by simp

end (* fixed p *)


subsubsection \<open>Test Case\<close>

text \<open>Functional Implementations\<close>

lemma "min_wpl (\<lambda>i j. nat(i+j)) 0 4 = 10"
  by eval

lemma "opt_bst (\<lambda>i j. nat(i+j)) (0, 4) = \<langle>\<langle>\<langle>\<langle>\<langle>\<langle>\<rangle>, 0, \<langle>\<rangle>\<rangle>, 1, \<langle>\<rangle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 3, \<langle>\<rangle>\<rangle>, 4, \<langle>\<rangle>\<rangle>"
  by eval

text \<open>Using Frequencies\<close>
definition
  "list_to_p xs (i::int) = (if i - 1 \<ge> 0 \<and> nat (i - 1) < length xs then xs ! nat (i - 1) else 0)"

definition
  "ex_p_1 = [10, 30, 15, 25, 20]"

definition
  "opt_tree_1 =
  \<langle>
    \<langle>
      \<langle>\<langle>\<rangle>, 1::int, \<langle>\<rangle>\<rangle>,
      2,
      \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>
    \<rangle>,
    4,
    \<langle>\<langle>\<rangle>, 5, \<langle>\<rangle>\<rangle>
  \<rangle>"

lemma "opt_bst' (list_to_p ex_p_1) 1 5 = opt_tree_1"
  by eval


text \<open>Imperative Implementation\<close>

code_thms min_wpl

definition "min_wpl_test = min_wpl\<^sub>h (\<lambda>i j. nat(i+j)) 4 0 4"

code_reflect Test functions min_wpl_test

ML \<open>Test.min_wpl_test ()\<close>

end