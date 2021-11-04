theory BTree_Height
  imports BTree
begin

section "Maximum and minimum height"

text "Textbooks usually provide some proofs relating the maxmimum and minimum height of the BTree
for a given number of nodes. We therefore introduce this counting and show the respective proofs."

subsection "Definition of node/size"

thm BTree.btree.size
  (* the automatically derived size is a bit weird for our purposes *)
value "size (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"


text "The default size function does not suit our needs as it regards the length of the list in each node.
 We would like to count the number of nodes in the tree only, not regarding the number of keys."

(* we want a different counting method,
  namely only the number of nodes in a tree *)

(* TODO what if we count Leafs as nodes? *)

fun nodes::"'a btree \<Rightarrow> nat" where
  "nodes Leaf = 0" |
  "nodes (Node ts t) = 1 + (\<Sum>t\<leftarrow>subtrees ts. nodes t) + (nodes t)"

value "nodes (Node [(Leaf, (0::nat)), (Node [(Leaf, 1), (Leaf, 10)] Leaf, 12), (Leaf, 30), (Leaf, 100)] Leaf)"


(* maximum number of nodes for given height *)
subsection "Maximum number of nodes for a given height"


lemma sum_list_replicate: "sum_list (replicate n c) = n*c"
  apply(induction n)
   apply(auto simp add: ring_class.ring_distribs(2))
  done

abbreviation "bound k h \<equiv> ((k+1)^h - 1)"

lemma nodes_height_upper_bound: 
  "\<lbrakk>order k t; bal t\<rbrakk> \<Longrightarrow> nodes t * (2*k) \<le> bound (2*k) (height t)"
proof(induction t rule: nodes.induct)
  case (2 ts t)
  let ?sub_height = "((2 * k + 1) ^ height t - 1)"
  have "sum_list (map nodes (subtrees ts)) * (2*k) =
        sum_list (map (\<lambda>t. nodes t * (2 * k)) (subtrees ts))"
    using sum_list_mult_const by metis
  also have "\<dots> \<le> sum_list (map (\<lambda>x.?sub_height) (subtrees ts))"
    using 2
    using sum_list_mono[of "subtrees ts" "\<lambda>t. nodes t * (2 * k)" "\<lambda>x. bound (2 * k) (height t)"]
    by (metis bal.simps(2) order.simps(2))
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> = (length ts)*(?sub_height)"
    using sum_list_replicate by simp
  also have "\<dots> \<le> (2*k)*(?sub_height)"
    using "2.prems"(1)
    by simp
  finally have "sum_list (map nodes (subtrees ts))*(2*k) \<le> ?sub_height*(2*k)"
    by simp
  moreover have "(nodes t)*(2*k) \<le> ?sub_height"
    using 2 by simp
  ultimately have "(nodes (Node ts t))*(2*k) \<le> 
         2*k
        + ?sub_height * (2*k)
        + ?sub_height"
    unfolding nodes.simps add_mult_distrib
    by linarith
  also have "\<dots> =  2*k + (2*k)*((2 * k + 1) ^ height t) - 2*k + (2 * k + 1) ^ height t - 1"
    by (simp add: diff_mult_distrib2 mult.assoc mult.commute)
  also have "\<dots> = (2*k)*((2 * k + 1) ^ height t) + (2 * k + 1) ^ height t - 1"
    by simp
  also have "\<dots> = (2*k+1)^(Suc(height t)) - 1"
    by simp
  finally show ?case
    by (metis "2.prems"(2) height_bal_tree)
qed simp

text "To verify our lower bound is sharp, we compare it to the height of artificially constructed
full trees."

fun full_node::"nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a btree" where
  "full_node k c 0 = Leaf"|
  "full_node k c (Suc n) = (Node (replicate (2*k) ((full_node k c n),c)) (full_node k c n))"

value "let k = (2::nat) in map (\<lambda>x. nodes x * 2*k) (map (full_node k (1::nat)) [0,1,2,3,4])"
value "let k = (2::nat) in map (\<lambda>x. ((2*k+(1::nat))^(x)-1)) [0,1,2,3,4]"

lemma compow_comp_id: "c > 0 \<Longrightarrow> f \<circ> f = f \<Longrightarrow> (f ^^ c) = f"
  apply(induction c)
   apply auto
  by fastforce

(* required only for the fold definition of height *)
lemma compow_id_point: "f x = x \<Longrightarrow> (f ^^ c) x = x"
  apply(induction c)
   apply auto
  done

lemma height_full_node: "height (full_node k a h) = h"
  apply(induction k a h rule: full_node.induct)
   apply (auto simp add: set_replicate_conv_if)
  done

lemma bal_full_node: "bal (full_node k a h)"
  apply(induction k a h rule: full_node.induct)
   apply auto
  done

lemma order_full_node: "order k (full_node k a h)"
  apply(induction k a h rule: full_node.induct)
   apply auto
  done

lemma full_btrees_sharp: "nodes (full_node k a h) * (2*k) = bound (2*k) h"
  apply(induction k a h rule: full_node.induct)
   apply (auto simp add: height_full_node algebra_simps sum_list_replicate)
  done

lemma upper_bound_sharp_node:
  "t = full_node k a h \<Longrightarrow> height t = h \<and> order k t \<and> bal t \<and> bound (2*k) h = nodes t * (2*k)"
  by (simp add: bal_full_node height_full_node order_full_node full_btrees_sharp)


(* maximum number of nodes *)
subsection "Maximum height for a given number of nodes"


lemma nodes_height_lower_bound: 
  "\<lbrakk>order k t; bal t\<rbrakk> \<Longrightarrow> bound k (height t) \<le> nodes t * k"
proof(induction t rule: nodes.induct)
  case (2 ts t)
  let ?sub_height = "((k + 1) ^ height t - 1)"
  have "k*(?sub_height) \<le> (length ts)*(?sub_height)"
    using "2.prems"(1)
    by simp
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using sum_list_replicate by simp
  also have "\<dots> = sum_list (map (\<lambda>x.?sub_height) (subtrees ts))"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> \<le> sum_list (map (\<lambda>t. nodes t * k) (subtrees ts))"
    using 2 
    using sum_list_mono[of "subtrees ts" "\<lambda>x. bound k (height t)" "\<lambda>t. nodes t * k"]
    by (metis bal.simps(2) order.simps(2))
  also have "\<dots> = sum_list (map nodes (subtrees ts)) * k"
    using sum_list_mult_const[of nodes k "subtrees ts"] by auto
  finally have "sum_list (map nodes (subtrees ts))*k \<ge> ?sub_height*k"
    by simp
  moreover have "(nodes t)*k \<ge> ?sub_height"
    using 2 by simp
  ultimately have "(nodes (Node ts t))*k \<ge> 
        k
        + ?sub_height * k
        + ?sub_height"
    unfolding nodes.simps add_mult_distrib
    by linarith
  also have
    "k + ?sub_height * k + ?sub_height = 
     k + k*((k + 1) ^ height t) - k + (k + 1) ^ height t - 1"
    by (simp add: diff_mult_distrib2 mult.assoc mult.commute)
  also have "\<dots> = k*((k + 1) ^ height t) + (k + 1) ^ height t - 1"
    by simp
  also have "\<dots> = (k+1)^(Suc(height t)) - 1"
    by simp
  finally show ?case
    by (metis "2.prems"(2) height_bal_tree)
qed simp

text "To verify our upper bound is sharp, we compare it to the height of artificially constructed
minimally filled (=slim) trees."

fun slim_node::"nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a btree" where
  "slim_node k c 0 = Leaf"|
  "slim_node k c (Suc n) = (Node (replicate k ((slim_node k c n),c)) (slim_node k c n))"

value "let k = (2::nat) in map (\<lambda>x. nodes x * k) (map (slim_node k (1::nat)) [0,1,2,3,4])"
value "let k = (2::nat) in map (\<lambda>x. ((k+1::nat)^(x)-1)) [0,1,2,3,4]"


lemma height_slim_node: "height (slim_node k a h) = h"
  apply(induction k a h rule: full_node.induct)
   apply (auto simp add: set_replicate_conv_if)
  done

lemma bal_slim_node: "bal (slim_node k a h)"
  apply(induction k a h rule: full_node.induct)
   apply auto
  done

lemma order_slim_node: "order k (slim_node k a h)"
  apply(induction k a h rule: full_node.induct)
   apply auto
  done

lemma slim_nodes_sharp: "nodes (slim_node k a h) * k = bound k h"
  apply(induction k a h rule: slim_node.induct)
   apply (auto simp add: height_slim_node algebra_simps sum_list_replicate compow_id_point)
  done

lemma lower_bound_sharp_node:
  "t = slim_node k a h \<Longrightarrow> height t = h \<and> order k t \<and> bal t \<and> bound k h = nodes t * k"
  by (simp add: bal_slim_node height_slim_node order_slim_node slim_nodes_sharp)

(* TODO results for root_order/bal *)
text "Since BTrees have special roots, we need to show the overall nodes seperately"

lemma nodes_root_height_lower_bound:
  assumes "root_order k t"
    and "bal t"
  shows "2*((k+1)^(height t - 1) - 1) + (of_bool (t \<noteq> Leaf))*k  \<le> nodes t * k"
proof (cases t)
  case (Node ts t)
  let ?sub_height = "((k + 1) ^ height t - 1)"
  from Node have "?sub_height \<le> length ts * ?sub_height"
    using assms
    by (simp add: Suc_leI)
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using sum_list_replicate
    by simp
  also have "\<dots> = sum_list (map (\<lambda>x. ?sub_height) (subtrees ts))"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> \<le> sum_list (map (\<lambda>t. nodes t * k) (subtrees ts))"
    using Node
      sum_list_mono[of "subtrees ts" "\<lambda>x. (k+1)^(height t) - 1" "\<lambda>x. nodes x * k"]
      nodes_height_lower_bound assms
    by fastforce
  also have "\<dots> = sum_list (map nodes (subtrees ts)) * k"
    using sum_list_mult_const[of nodes k "subtrees ts"] by simp
  finally have "sum_list (map nodes (subtrees ts))*k \<ge> ?sub_height"
    by simp

  moreover have "(nodes t)*k \<ge> ?sub_height"
    using Node assms nodes_height_lower_bound
    by auto
  ultimately have "(nodes (Node ts t))*k \<ge> 
        ?sub_height
        + ?sub_height + k"
    unfolding nodes.simps add_mult_distrib
    by linarith
  then show ?thesis
    using Node assms(2) height_bal_tree by fastforce
qed simp

lemma nodes_root_height_upper_bound: 
  assumes "root_order k t"
    and "bal t"
  shows "nodes t * (2*k) \<le> (2*k+1)^(height t) - 1"
proof(cases t)
  case (Node ts t)
  let ?sub_height = "((2 * k + 1) ^ height t - 1)"
  have "sum_list (map nodes (subtrees ts)) * (2*k) =
        sum_list (map (\<lambda>t. nodes t * (2 * k)) (subtrees ts))"
    using sum_list_mult_const by metis
  also have "\<dots> \<le> sum_list (map (\<lambda>x.?sub_height) (subtrees ts))"
    using Node
      sum_list_mono[of "subtrees ts" "\<lambda>x. nodes x * (2*k)"  "\<lambda>x. (2*k+1)^(height t) - 1"]
      nodes_height_upper_bound assms
    by fastforce
  also have "\<dots> = sum_list (replicate (length ts) ?sub_height)"
    using map_replicate_const[of ?sub_height "subtrees ts"] length_map
    by simp
  also have "\<dots> = (length ts)*(?sub_height)"
    using sum_list_replicate by simp
  also have "\<dots> \<le> (2*k)*?sub_height"
    using assms Node
    by simp
  finally have "sum_list (map nodes (subtrees ts))*(2*k) \<le> ?sub_height*(2*k)"
    by simp
  moreover have "(nodes t)*(2*k) \<le> ?sub_height"
    using Node assms nodes_height_upper_bound
    by auto
  ultimately have "(nodes (Node ts t))*(2*k) \<le> 
         2*k
        + ?sub_height * (2*k)
        + ?sub_height"
    unfolding nodes.simps add_mult_distrib
    by linarith
  also have "\<dots> =  2*k + (2*k)*((2 * k + 1) ^ height t) - 2*k + (2 * k + 1) ^ height t - 1"
    by (simp add: diff_mult_distrib2 mult.assoc mult.commute)
  also have "\<dots> = (2*k)*((2 * k + 1) ^ height t) + (2 * k + 1) ^ height t - 1"
    by simp
  also have "\<dots> = (2*k+1)^(Suc(height t)) - 1"
    by simp
  finally show ?thesis
    by (metis Node assms(2) height_bal_tree)
qed simp

lemma root_order_imp_divmuleq: "root_order k t \<Longrightarrow> (nodes t * k) div k = nodes t"
  using root_order.elims(2) by fastforce

lemma nodes_root_height_lower_bound_simp:
  assumes "root_order k t"
    and "bal t"
    and "k > 0"
  shows "(2*((k+1)^(height t - 1) - 1)) div k + (of_bool (t \<noteq> Leaf)) \<le> nodes t"
proof (cases t)
  case Node
  have "(2*((k+1)^(height t - 1) - 1)) div k + (of_bool (t \<noteq> Leaf)) = 
(2*((k+1)^(height t - 1) - 1) + (of_bool (t \<noteq> Leaf))*k) div k"
    using Node assms
    using div_plus_div_distrib_dvd_left[of k k "(2 * Suc k ^ (height t - Suc 0) - Suc (Suc 0))"]
    by (auto simp add: algebra_simps simp del: height_btree.simps)
  also have "\<dots> \<le> (nodes t * k) div k"
    using nodes_root_height_lower_bound[OF assms(1,2)] div_le_mono
    by blast
  also have "\<dots> = nodes t"
    using root_order_imp_divmuleq[OF assms(1)]
    by simp
  finally show ?thesis .
qed simp

lemma nodes_root_height_upper_bound_simp:
  assumes "root_order k t"
    and "bal t"
  shows "nodes t \<le> ((2*k+1)^(height t) - 1) div (2*k)"
proof -
  have "nodes t = (nodes t * (2*k)) div (2*k)"
    using root_order_imp_divmuleq[OF assms(1)]
    by simp
  also have "\<dots> \<le> ((2*k+1)^(height t) - 1) div (2*k)"
    using div_le_mono nodes_root_height_upper_bound[OF assms] by blast
  finally show ?thesis .
qed

definition "full_tree = full_node"

fun slim_tree where
  "slim_tree k c 0 = Leaf" |
  "slim_tree k c (Suc h) = Node [(slim_node k c h, c)] (slim_node k c h)"

lemma lower_bound_sharp:
  "k > 0 \<Longrightarrow> t = slim_tree k a h \<Longrightarrow> height t = h \<and> root_order k t \<and> bal t \<and> nodes t * k = 2*((k+1)^(height t - 1) - 1) + (of_bool (t \<noteq> Leaf))*k"
  apply (cases h)
  using slim_nodes_sharp[of k a]
   apply (auto simp add: algebra_simps bal_slim_node height_slim_node order_slim_node)
  done

lemma upper_bound_sharp:
  "k > 0 \<Longrightarrow> t = full_tree k a h \<Longrightarrow> height t = h \<and> root_order k t \<and> bal t \<and> ((2*k+1)^(height t) - 1) = nodes t * (2*k)"
  unfolding full_tree_def
  using order_impl_root_order[of k t]
  by (simp add: bal_full_node height_full_node order_full_node full_btrees_sharp)


end