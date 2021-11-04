theory BTree_Set
  imports BTree
    "HOL-Data_Structures.Set_Specs"
begin

section "Set interpretation"

subsection "Auxiliary functions"

fun split_half:: "('a btree\<times>'a) list \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)" where
  "split_half xs = (take (length xs div 2) xs, drop (length xs div 2) xs)"


lemma drop_not_empty: "xs \<noteq> [] \<Longrightarrow> drop (length xs div 2) xs \<noteq> []"
  apply(induction xs)
   apply(auto split!: list.splits)
  done

lemma split_half_not_empty: "length xs \<ge> 1 \<Longrightarrow> \<exists>ls sub sep rs. split_half xs = (ls,(sub,sep)#rs)"
  using drop_not_empty
  by (metis (no_types, hide_lams) drop0 drop_eq_Nil eq_snd_iff hd_Cons_tl le_trans not_one_le_zero split_half.simps)

subsection "The split function locale"

text "Here, we abstract away the inner workings of the split function
      for B-tree operations."

(* TODO what if we define a function "list_split" that returns
 a split list for mapping arbitrary f (separators) and g (subtrees)
s.th. f :: 'a \<Rightarrow> ('b::linorder) and g :: 'a \<Rightarrow> 'a btree
this would allow for key,pointer pairs to be inserted into the tree *)
(* TODO what if the keys are the pointers? *)
locale split =
  fixes split ::  "('a btree\<times>'a::linorder) list \<Rightarrow> 'a \<Rightarrow> (('a btree\<times>'a) list \<times> ('a btree\<times>'a) list)"
  assumes split_req:
    "\<lbrakk>split xs p = (ls,rs)\<rbrakk> \<Longrightarrow> xs = ls @ rs"
    "\<lbrakk>split xs p = (ls@[(sub,sep)],rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> sep < p"
    "\<lbrakk>split xs p = (ls,(sub,sep)#rs); sorted_less (separators xs)\<rbrakk> \<Longrightarrow> p \<le> sep"
begin

lemmas split_conc = split_req(1)
lemmas split_sorted = split_req(2,3)


lemma [termination_simp]:"(ls, (sub, sep) # rs) = split ts y \<Longrightarrow>
      size sub < Suc (size_list (\<lambda>x. Suc (size (fst x))) ts  + size l)"
  using split_conc[of ts y ls "(sub,sep)#rs"] by auto


fun invar_inorder where "invar_inorder k t = (bal t \<and> root_order k t)"

definition "empty_btree = Leaf"

subsection "Membership"

fun isin:: "'a btree \<Rightarrow> 'a \<Rightarrow> bool" where
  "isin (Leaf) y = False" |
  "isin (Node ts t) y = (
      case split ts y of (_,(sub,sep)#rs) \<Rightarrow> (
          if y = sep then
             True
          else
             isin sub y
      )
   | (_,[]) \<Rightarrow> isin t y
  )"

subsection "Insertion"

text "The insert function requires an auxiliary data structure
and auxiliary invariant functions."

datatype 'b up\<^sub>i = T\<^sub>i "'b btree" | Up\<^sub>i "'b btree" 'b "'b btree"

fun order_up\<^sub>i where
  "order_up\<^sub>i k (T\<^sub>i sub) = order k sub" |
  "order_up\<^sub>i k (Up\<^sub>i l a r) = (order k l \<and> order k r)"

fun root_order_up\<^sub>i where
  "root_order_up\<^sub>i k (T\<^sub>i sub) = root_order k sub" |
  "root_order_up\<^sub>i k (Up\<^sub>i l a r) = (order k l \<and> order k r)"


fun height_up\<^sub>i where
  "height_up\<^sub>i (T\<^sub>i t) = height t" |
  "height_up\<^sub>i (Up\<^sub>i l a r) = max (height l) (height r)"

fun bal_up\<^sub>i where
  "bal_up\<^sub>i (T\<^sub>i t) = bal t" |
  "bal_up\<^sub>i (Up\<^sub>i l a r) = (height l = height r \<and> bal l \<and> bal r)"

fun inorder_up\<^sub>i where
  "inorder_up\<^sub>i (T\<^sub>i t) = inorder t" |
  "inorder_up\<^sub>i (Up\<^sub>i l a r) = inorder l @ [a] @ inorder r"


text "The following function merges two nodes and returns separately split nodes
   if an overflow occurs"

fun node\<^sub>i:: "nat \<Rightarrow> ('a btree \<times> 'a) list \<Rightarrow> 'a btree \<Rightarrow> 'a up\<^sub>i" where
  "node\<^sub>i k ts t = (
  if length ts \<le> 2*k then T\<^sub>i (Node ts t)
  else (
    case split_half ts of (ls, (sub,sep)#rs) \<Rightarrow>
      Up\<^sub>i (Node ls sub) sep (Node rs t)
    )
  )"


fun ins:: "nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a up\<^sub>i" where
  "ins k x Leaf = (Up\<^sub>i Leaf x Leaf)" |
  "ins k x (Node ts t) = (
  case split ts x of
    (ls,(sub,sep)#rs) \<Rightarrow>
      (if sep = x then
        T\<^sub>i (Node ts t)
      else
        (case ins k x sub of
          Up\<^sub>i l a r \<Rightarrow>
             node\<^sub>i k (ls @ (l,a)#(r,sep)#rs) t |
          T\<^sub>i a \<Rightarrow>
            T\<^sub>i (Node (ls @ (a,sep) # rs) t))) |
    (ls, []) \<Rightarrow>
      (case ins k x t of
         Up\<^sub>i l a r \<Rightarrow>
           node\<^sub>i k (ls@[(l,a)]) r |
         T\<^sub>i a \<Rightarrow>
           T\<^sub>i (Node ls a)
  )
)"



fun tree\<^sub>i::"'a up\<^sub>i \<Rightarrow> 'a btree" where
  "tree\<^sub>i (T\<^sub>i sub) = sub" |
  "tree\<^sub>i (Up\<^sub>i l a r) = (Node [(l,a)] r)"

fun insert::"nat \<Rightarrow> 'a \<Rightarrow> 'a btree \<Rightarrow> 'a btree" where
  "insert k x t = tree\<^sub>i (ins k x t)"

subsection "Deletion"

text "The following deletion method is inspired by Bayer (70) and Fielding (??).
Rather than stealing only a single node from the neighbour,
the neighbour is fully merged with the potentially underflowing node.
If the resulting node is still larger than allowed, the merged node is split
again, using the rules known from insertion splits.
If the resulting node has admissable size, it is simply kept in the tree."

fun rebalance_middle_tree where
  "rebalance_middle_tree k ls Leaf sep rs Leaf = (
  Node (ls@(Leaf,sep)#rs) Leaf
)" |
  "rebalance_middle_tree k ls (Node mts mt) sep rs (Node tts tt) = (
  if length mts \<ge> k \<and> length tts \<ge> k then
    Node (ls@(Node mts mt,sep)#rs) (Node tts tt)
  else (
    case rs of [] \<Rightarrow> (
      case node\<^sub>i k (mts@(mt,sep)#tts) tt of
       T\<^sub>i u \<Rightarrow>
        Node ls u |
       Up\<^sub>i l a r \<Rightarrow>
        Node (ls@[(l,a)]) r) |
    (Node rts rt,rsep)#rs \<Rightarrow> (
      case node\<^sub>i k (mts@(mt,sep)#rts) rt of
      T\<^sub>i u \<Rightarrow>
        Node (ls@(u,rsep)#rs) (Node tts tt) |
      Up\<^sub>i l a r \<Rightarrow>
        Node (ls@(l,a)#(r,rsep)#rs) (Node tts tt))
))"

text "Deletion"

text "All trees are merged with the right neighbour on underflow.
Obviously for the last tree this would not work since it has no right neighbour.
Therefore this tree, as the only exception, is merged with the left neighbour.
However since we it does not make a difference, we treat the situation
as if the second to last tree underflowed."

fun rebalance_last_tree where
  "rebalance_last_tree k ts t = (
case last ts of (sub,sep) \<Rightarrow>
   rebalance_middle_tree k (butlast ts) sub sep [] t
)"

text "Rather than deleting the minimal key from the right subtree,
we remove the maximal key of the left subtree.
This is due to the fact that the last tree can easily be accessed
and the left neighbour is way easier to access than the right neighbour,
it resides in the same pair as the separating element to be removed."



fun split_max where
  "split_max k (Node ts t) = (case t of Leaf \<Rightarrow> (
  let (sub,sep) = last ts in
    (Node (butlast ts) sub, sep)
)|
_ \<Rightarrow>
case split_max k t of (sub, sep) \<Rightarrow>
  (rebalance_last_tree k ts sub, sep)
)"

fun del where
  "del k x Leaf = Leaf" |
  "del k x (Node ts t) = (
  case split ts x of
    (ls,[]) \<Rightarrow>
     rebalance_last_tree k ls (del k x t)
  | (ls,(sub,sep)#rs) \<Rightarrow> (
      if sep \<noteq> x then
        rebalance_middle_tree k ls (del k x sub) sep rs t
      else if sub = Leaf then
        Node (ls@rs) t
      else let (sub_s, max_s) = split_max k sub in
        rebalance_middle_tree k ls sub_s max_s rs t
  )
)"

fun reduce_root where
  "reduce_root Leaf = Leaf" |
  "reduce_root (Node ts t) = (case ts of
   [] \<Rightarrow> t |
   _ \<Rightarrow> (Node ts t)
)"


fun delete where "delete k x t = reduce_root (del k x t)"


text "An invariant for intermediate states at deletion.
In particular we allow for an underflow to 0 subtrees."

fun almost_order where
  "almost_order k Leaf = True" |
  "almost_order k (Node ts t) = (
  (length ts \<le> 2*k) \<and>
  (\<forall>s \<in> set (subtrees ts). order k s) \<and>
   order k t
)"


text "A recursive property of the \"spine\" we want to walk along for splitting
    off the maximum of the left subtree."

fun nonempty_lasttreebal where
  "nonempty_lasttreebal Leaf = True" |
  "nonempty_lasttreebal (Node ts t) = (
    (\<exists>ls tsub tsep. ts = (ls@[(tsub,tsep)]) \<and> height tsub = height t) \<and>
     nonempty_lasttreebal t
  )"

subsection "Proofs of functional correctness"

lemma split_set:
  assumes "split ts z = (ls,(a,b)#rs)"
  shows "(a,b) \<in> set ts"
    and "(x,y) \<in> set ls \<Longrightarrow> (x,y) \<in> set ts"
    and "(x,y) \<in> set rs \<Longrightarrow> (x,y) \<in> set ts"
    and "set ls \<union> set rs \<union> {(a,b)} = set ts"
    and "\<exists>x \<in> set ts. b \<in> Basic_BNFs.snds x"
  using split_conc assms by fastforce+

lemma split_length:
  "split ts x = (ls, rs) \<Longrightarrow> length ls + length rs = length ts"
  by (auto dest: split_conc)


text "Isin proof"

thm isin_simps
  (* copied from comment in List_Ins_Del *)
lemma sorted_ConsD: "sorted_less (y # xs) \<Longrightarrow> x \<le> y \<Longrightarrow> x \<notin> set xs"
  by (auto simp: sorted_Cons_iff)

lemma sorted_snocD: "sorted_less (xs @ [y]) \<Longrightarrow> y \<le> x \<Longrightarrow> x \<notin> set xs"
  by (auto simp: sorted_snoc_iff)


lemmas isin_simps2 = sorted_lems sorted_ConsD sorted_snocD
  (*-----------------------------*)

lemma isin_sorted: "sorted_less (xs@a#ys) \<Longrightarrow>
  (x \<in> set (xs@a#ys)) = (if x < a then x \<in> set xs else x \<in> set (a#ys))"
  by (auto simp: isin_simps2)

(* lift to split *)


lemma isin_sorted_split:
  assumes "sorted_less (inorder (Node ts t))"
    and "split ts x = (ls, rs)"
  shows "x \<in> set (inorder (Node ts t)) = (x \<in> set (inorder_list rs @ inorder t))"
proof (cases ls)
  case Nil
  then have "ts = rs"
    using assms by (auto dest!: split_conc)
  then show ?thesis by simp
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.simps(3) rev_exhaust surj_pair)
  then have "sep < x"
    using split_req(2)[of ts x ls' sub sep rs]
    using sorted_inorder_separators[OF assms(1)]
    using assms
    by simp
  then show ?thesis
    using assms(1) split_conc[OF assms(2)] ls_tail_split
    using isin_sorted[of "inorder_list ls' @ inorder sub" sep "inorder_list rs @ inorder t" x]
    by auto
qed

lemma isin_sorted_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (inorder (Node ts t))"
    and "sep \<noteq> x"
  shows "x \<in> set (inorder_list ((sub,sep)#rs) @ inorder t) = (x \<in> set (inorder sub))"
proof -
  from assms have "x < sep"
  proof -
    from assms have "sorted_less (separators ts)"
      by (simp add: sorted_inorder_separators)
    then show ?thesis
      using split_req(3)
      using assms
      by fastforce
  qed
  moreover have "sorted_less (inorder_list ((sub,sep)#rs) @ inorder t)"
    using assms sorted_wrt_append split_conc
    by fastforce
  ultimately show ?thesis
    using isin_sorted[of "inorder sub" "sep" "inorder_list rs @ inorder t" x]
    by simp
qed


theorem isin_set_inorder: "sorted_less (inorder t) \<Longrightarrow> isin t x = (x \<in> set (inorder t))"
proof(induction t x rule: isin.induct)
  case (2 ts t x)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs"
    using split_conc by auto
  show ?case
  proof (cases rs)
    case Nil
    then have "isin (Node ts t) x = isin t x"
      by (simp add: list_split)
    also have "\<dots> = (x \<in> set (inorder t))"
      using "2.IH"(1) list_split Nil
      using "2.prems" sorted_inorder_induct_last by auto
    also have "\<dots> = (x \<in> set (inorder (Node ts t)))"
      using isin_sorted_split[of ts t x ls rs]
      using "2.prems" list_split list_conc Nil
      by simp
    finally show ?thesis .
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis
        using list_conc Cons a_split list_split
        by auto
    next
      case False
      then have "isin (Node ts t) x = isin sub x"
        using list_split Cons a_split False
        by auto
      also have "\<dots> = (x \<in> set (inorder sub))"
        using "2.IH"(2)
        using "2.prems" False a_split list_conc list_split local.Cons sorted_inorder_induct_subtree by fastforce
      also have "\<dots> = (x \<in> set (inorder (Node ts t)))"
        using isin_sorted_split[OF "2.prems" list_split]
        using isin_sorted_split_right "2.prems" list_split Cons a_split False
        by simp
      finally show ?thesis  .
    qed
  qed
qed auto




(* TODO way to use this for custom case distinction? *)
lemma node\<^sub>i_cases: "length xs \<le> k \<or> (\<exists>ls sub sep rs. split_half xs = (ls,(sub,sep)#rs))"
proof -
  have "\<not> length xs \<le> k \<Longrightarrow> length xs \<ge> 1"
    by linarith
  then show ?thesis
    using split_half_not_empty
    by blast
qed


lemma root_order_tree\<^sub>i: "root_order_up\<^sub>i (Suc k) t = root_order (Suc k) (tree\<^sub>i t)"
  apply (cases t)
   apply auto
  done

lemma node\<^sub>i_root_order:
  assumes "length ts > 0"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set (subtrees ts). order k x"
    and "order k t"
  shows "root_order_up\<^sub>i k (node\<^sub>i k ts t)"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by (simp add: node\<^sub>i.simps)
next
  case False
  then obtain ls sub sep rs where split_half_ts:
    "take (length ts div 2) ts = ls"
    "drop (length ts div 2) ts = (sub,sep)#rs"
    using split_half_not_empty[of ts]
    by auto
  then have length_rs: "length rs = length ts - (length ts div 2) - 1"
    using length_drop
    by (metis One_nat_def add_diff_cancel_right' list.size(4))
  also have "\<dots> \<le> 4*k - ((4*k + 1) div 2)"
    using assms(2) by simp
  also have "\<dots> = 2*k"
    by auto
  finally have "length rs \<le> 2*k"
    by simp
  moreover have "length rs \<ge> k"
    using False length_rs by simp
  moreover have "set ((sub,sep)#rs) \<subseteq> set ts"
    by (metis split_half_ts(2) set_drop_subset)
  ultimately have o_r: "order k sub" "order k (Node rs t)"
    using split_half_ts assms by auto
  moreover have "length ls \<ge> k"
    using length_take assms split_half_ts False
    by auto
  moreover have  "length ls \<le> 2*k"
    using assms(2) split_half_ts
    by auto
  ultimately have o_l: "order k (Node ls sub)"
    using set_take_subset assms split_half_ts
    by fastforce
  from o_r o_l show ?thesis
    by (simp add: node\<^sub>i.simps False split_half_ts)
qed

lemma node\<^sub>i_order_helper:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set (subtrees ts). order k x"
    and "order k t"
  shows "case (node\<^sub>i k ts t) of T\<^sub>i t \<Rightarrow> order k t | _ \<Rightarrow> True"
proof (cases "length ts \<le> 2*k")
  case True
  then show ?thesis
    using assms
    by (simp add: node\<^sub>i.simps)
next
  case False
  then obtain sub sep rs where
    "drop (length ts div 2) ts = (sub,sep)#rs"
    using split_half_not_empty[of ts]
    by auto
  then show ?thesis
    using assms by (simp add: node\<^sub>i.simps)
qed


lemma node\<^sub>i_order:
  assumes "length ts \<ge> k"
    and "length ts \<le> 4*k+1"
    and "\<forall>x \<in> set (subtrees ts). order k x"
    and "order k t"
  shows "order_up\<^sub>i k (node\<^sub>i k ts t)"

  apply(cases "node\<^sub>i k ts t")
  using node\<^sub>i_root_order node\<^sub>i_order_helper assms apply fastforce
  apply (metis node\<^sub>i_root_order assms(2,3,4) le0 length_greater_0_conv
      list.size(3) node\<^sub>i.simps order_up\<^sub>i.simps(2) root_order_up\<^sub>i.simps(2) up\<^sub>i.distinct(1))
  done

(* explicit proof *)
lemma ins_order:
  "order k t \<Longrightarrow> order_up\<^sub>i k (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_res: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ls@rs = ts"
    using split_conc
    by simp

  show ?case
  proof (cases rs)
    case Nil
    then have "order_up\<^sub>i k (ins k x t)"
      using 2 split_res
      by simp
    then show ?thesis
      using Nil 2 split_app split_res Nil node\<^sub>i_order
      by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)"
      by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis
        using 2 a_prod Cons split_res
        by simp
    next
      case False
      then have "order_up\<^sub>i k (ins k x sub)"
        using "2.IH"(2) "2.prems" a_prod local.Cons split_app split_res by auto
      then show ?thesis
        using 2 split_app Cons length_append node\<^sub>i_order a_prod split_res
        by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps simp add: order_impl_root_order)
    qed
  qed
qed simp


(* notice this is almost a duplicate of ins_order *)
lemma ins_root_order:
  assumes "root_order k t"
  shows "root_order_up\<^sub>i k (ins k x t)"
proof(cases t)
  case (Node ts t)
  then obtain ls rs where split_res: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ls@rs = ts"
    using split_conc
    by fastforce

  show ?thesis
  proof (cases rs)
    case Nil
    then have "order_up\<^sub>i k (ins k x t)" using Node assms split_res
      by (simp add: ins_order)
    then show ?thesis
      using Nil Node split_app split_res assms node\<^sub>i_root_order
      by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps simp add: order_impl_root_order)
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)"
      by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis using assms Node a_prod Cons split_res
        by simp
    next
      case False
      then have "order_up\<^sub>i k (ins k x sub)"
        using Node a_prod assms ins_order local.Cons split_app by auto
      then show ?thesis
        using assms split_app Cons length_append Node node\<^sub>i_root_order a_prod split_res
        by (auto split!: up\<^sub>i.splits simp del: node\<^sub>i.simps simp add: order_impl_root_order)
    qed
  qed
qed simp



lemma height_list_split: "height_up\<^sub>i (Up\<^sub>i (Node ls a) b (Node rs t)) = height (Node (ls@(a,b)#rs) t) "
  by (induction ls) (auto simp add: max.commute)

lemma node\<^sub>i_height: "height_up\<^sub>i (node\<^sub>i k ts t) = height (Node ts t)"
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls, (sub, sep) # rs)"
    by (meson node\<^sub>i_cases)
  then have "node\<^sub>i k ts t = Up\<^sub>i (Node ls (sub)) sep (Node rs t)"
    using False by simp
  then show ?thesis
    using split_half_ts
    by (metis append_take_drop_id fst_conv height_list_split snd_conv split_half.elims)
qed simp



lemma bal_up\<^sub>i_tree: "bal_up\<^sub>i t = bal (tree\<^sub>i t)"
  apply(cases t)
   apply auto
  done

lemma bal_list_split: "bal (Node (ls@(a,b)#rs) t) \<Longrightarrow> bal_up\<^sub>i (Up\<^sub>i (Node ls a) b (Node rs t))"
  by (auto simp add: image_constant_conv)

lemma node\<^sub>i_bal:
  assumes "bal (Node ts t)"
  shows "bal_up\<^sub>i (node\<^sub>i k ts t)"
  using assms
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where
    split_half_ts: "split_half ts = (ls, (sub, sep) # rs)"
    by (meson node\<^sub>i_cases)
  then have "bal (Node (ls@(sub,sep)#rs) t)"
    using assms append_take_drop_id[where n="length ts div 2" and xs=ts]
    by auto
  then show ?thesis
    using split_half_ts assms False
    by (auto simp del: bal.simps bal_up\<^sub>i.simps dest!: bal_list_split[of ls sub sep rs t])
qed simp

lemma height_up\<^sub>i_merge: "height_up\<^sub>i (Up\<^sub>i l a r) = height t \<Longrightarrow> height (Node (ls@(t,x)#rs) tt) = height (Node (ls@(l,a)#(r,x)#rs) tt)"
  by simp

lemma ins_height: "height_up\<^sub>i (ins k x t) = height t"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_list: "split ts x = (ls,rs)"
    by (meson surj_pair)
  then have split_append: "ls@rs = ts"
    using split_conc
    by auto
  then show ?case
  proof (cases rs)
    case Nil
    then have height_sub: "height_up\<^sub>i (ins k x t) = height t"
      using 2 by (simp add: split_list)
    then show ?thesis
    proof (cases "ins k x t")
      case (T\<^sub>i a)
      then have "height (Node ts t) = height (Node ts a)"
        using height_sub
        by simp
      then show ?thesis
        using T\<^sub>i Nil split_list split_append
        by simp
    next
      case (Up\<^sub>i l a r)
      then have "height (Node ls t) = height (Node (ls@[(l,a)]) r)"
        using height_btree_order height_sub by (induction ls) auto
      then show ?thesis using 2 Nil split_list Up\<^sub>i split_append
        by (simp del: node\<^sub>i.simps add: node\<^sub>i_height)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_split: "a = (sub,sep)"
      by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis
        using Cons a_split 2 split_list
        by (simp del: height_btree.simps)
    next
      case False
      then have height_sub: "height_up\<^sub>i (ins k x sub) = height sub"
        by (metis "2.IH"(2) a_split Cons split_list)
      then show ?thesis
      proof (cases "ins k x sub")
        case (T\<^sub>i a)
        then have "height a = height sub"
          using height_sub by auto
        then have "height (Node (ls@(sub,sep)#rs) t) = height (Node (ls@(a,sep)#rs) t)"
          by auto
        then show ?thesis
          using T\<^sub>i height_sub False Cons 2 split_list a_split split_append
          by (auto simp add: image_Un max.commute finite_set_ins_swap)
      next
        case (Up\<^sub>i l a r)
        then have "height (Node (ls@(sub,sep)#list) t) = height (Node (ls@(l,a)#(r,sep)#list) t)"
          using height_up\<^sub>i_merge height_sub
          by fastforce
        then show ?thesis
          using Up\<^sub>i False Cons 2 split_list a_split split_append
          by (auto simp del: node\<^sub>i.simps simp add: node\<^sub>i_height image_Un max.commute finite_set_ins_swap)
      qed
    qed
  qed
qed simp


(* the below proof is overly complicated as a number of lemmas regarding height are missing *)
lemma ins_bal: "bal t \<Longrightarrow> bal_up\<^sub>i (ins k x t)"
proof(induction k x t rule: ins.induct)
  case (2 k x ts t)
  then obtain ls rs where split_res: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have split_app: "ls@rs = ts"
    using split_conc
    by fastforce

  show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
    proof (cases "ins k x t")
      case (T\<^sub>i a)
      then have "bal (Node ls a)" unfolding bal.simps
        by (metis "2.IH"(1) "2.prems" append_Nil2 bal.simps(2) bal_up\<^sub>i.simps(1) height_up\<^sub>i.simps(1) ins_height local.Nil split_app split_res)
      then show ?thesis
        using Nil T\<^sub>i 2 split_res
        by simp
    next
      case (Up\<^sub>i l a r)
      then have
        "(\<forall>x\<in>set (subtrees (ls@[(l,a)])). bal x)"
        "(\<forall>x\<in>set (subtrees ls). height r = height x)"
        using 2 Up\<^sub>i Nil split_res split_app
        by simp_all (metis height_up\<^sub>i.simps(2) ins_height max_def)
      then show ?thesis unfolding ins.simps
        using Up\<^sub>i Nil 2 split_res
        by (simp del: node\<^sub>i.simps add: node\<^sub>i_bal)
    qed
  next
    case (Cons a list)
    then obtain sub sep where a_prod: "a  = (sub, sep)" by (cases a)
    then show ?thesis
    proof (cases "x = sep")
      case True
      then show ?thesis
        using a_prod 2 split_res Cons by simp
    next
      case False
      then have "bal_up\<^sub>i (ins k x sub)" using 2 split_res
        using a_prod local.Cons split_app by auto
      show ?thesis
      proof (cases "ins k x sub")
        case (T\<^sub>i x1)
        then have  "height x1 = height t"
          by (metis "2.prems" a_prod add_diff_cancel_left' bal_split_left(1) bal_split_left(2) height_bal_tree height_up\<^sub>i.simps(1) ins_height local.Cons plus_1_eq_Suc split_app)
        then show ?thesis
          using split_app Cons T\<^sub>i 2 split_res a_prod
          by auto
      next
        case (Up\<^sub>i l a r)
          (* The only case where explicit reasoning is required - likely due to the insertion of 2 elements in the list *)
        then have
          "\<forall>x \<in> set (subtrees (ls@(l,a)#(r,sep)#list)). bal x"
          using Up\<^sub>i split_app Cons 2 \<open>bal_up\<^sub>i (ins k x sub)\<close> by auto
        moreover have "\<forall>x \<in> set (subtrees (ls@(l,a)#(r,sep)#list)). height x = height t"
          using False Up\<^sub>i split_app Cons 2 \<open>bal_up\<^sub>i (ins k x sub)\<close> ins_height split_res a_prod
          apply auto
          by (metis height_up\<^sub>i.simps(2) sup.idem sup_nat_def)
        ultimately show ?thesis using Up\<^sub>i Cons 2 split_res a_prod
          by (simp del: node\<^sub>i.simps add: node\<^sub>i_bal)
      qed
    qed
  qed
qed simp

(* ins acts as ins_list wrt inorder *)

(* "simple enough" to be automatically solved *)
lemma node\<^sub>i_inorder: "inorder_up\<^sub>i (node\<^sub>i k ts t) = inorder (Node ts t)"
  apply(cases "length ts \<le> 2*k")
   apply (auto split!: list.splits)
    (* we want to only transform in one direction here.. *)
  supply R = sym[OF append_take_drop_id, of "map _ ts" "(length ts div 2)"]
  thm R
  apply(subst R)
  apply (simp del: append_take_drop_id add: take_map drop_map)
  done

corollary node\<^sub>i_inorder_simps:
  "node\<^sub>i k ts t = T\<^sub>i t' \<Longrightarrow> inorder t' = inorder (Node ts t)"
  "node\<^sub>i k ts t = Up\<^sub>i l a r \<Longrightarrow> inorder l @ a # inorder r = inorder (Node ts t)"
   apply (metis inorder_up\<^sub>i.simps(1) node\<^sub>i_inorder)
  by (metis append_Cons inorder_up\<^sub>i.simps(2) node\<^sub>i_inorder self_append_conv2)


lemma ins_sorted_inorder: "sorted_less (inorder t) \<Longrightarrow> (inorder_up\<^sub>i (ins k (x::('a::linorder)) t)) = ins_list x (inorder t)"
  apply(induction k x t rule: ins.induct)
  using split_axioms apply (auto split!: prod.splits list.splits up\<^sub>i.splits simp del: node\<^sub>i.simps
      simp add:  node\<^sub>i_inorder node\<^sub>i_inorder_simps)
    (* from here on we prefer an explicit proof, showing how to apply the IH  *)
  oops


(* specialize ins_list_sorted since it is cumbersome to express
 "inorder_list ts" as "xs @ [a]" and always having to use the implicit properties of split*)

lemma ins_list_split:
  assumes "split ts x = (ls, rs)"
    and "sorted_less (inorder (Node ts t))"
  shows "ins_list x (inorder (Node ts t)) = inorder_list ls @ ins_list x (inorder_list rs @ inorder t)"
proof (cases ls)
  case Nil
  then show ?thesis
    using assms by (auto dest!: split_conc)
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.distinct(1) rev_exhaust surj_pair)
  moreover have "sep < x"
    using split_req(2)[of ts x ls' sub sep rs]
    using sorted_inorder_separators
    using assms(1) assms(2) ls_tail_split
    by auto
  moreover have "sorted_less (inorder_list ls)"
    using assms sorted_wrt_append split_conc by fastforce
  ultimately show ?thesis using assms(2) split_conc[OF assms(1)]
    using ins_list_sorted[of "inorder_list ls' @ inorder sub" sep]
    by auto
qed

lemma ins_list_split_right_general:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (inorder_list ts)"
    and "sep \<noteq> x"
  shows "ins_list x (inorder_list ((sub,sep)#rs) @ zs) = ins_list x (inorder sub) @ sep # inorder_list rs @ zs"
proof -
  from assms have "x < sep"
  proof -
    from assms have "sorted_less (separators ts)"
      by (simp add: sorted_inorder_list_separators)
    then show ?thesis
      using split_req(3)
      using assms
      by fastforce
  qed
  moreover have "sorted_less (inorder_pair (sub,sep))"
    by (metis (no_types, lifting) assms(1) assms(2) concat.simps(2) concat_append list.simps(9) map_append sorted_wrt_append split_conc)
  ultimately show ?thesis
    using ins_list_sorted[of "inorder sub" "sep"]
    by auto
qed

(* this fits the actual use cases better *)
corollary ins_list_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (inorder (Node ts t))"
    and "sep \<noteq> x"
  shows "ins_list x (inorder_list ((sub,sep)#rs) @ inorder t) = ins_list x (inorder sub) @ sep # inorder_list rs @ inorder t"
  using assms sorted_wrt_append split.ins_list_split_right_general split_axioms by fastforce


(* a simple lemma, missing from the standard as of now *)
lemma ins_list_idem_eq_isin: "sorted_less xs \<Longrightarrow> x \<in> set xs \<longleftrightarrow> (ins_list x xs = xs)"
  apply(induction xs)
   apply auto
  done

lemma ins_list_contains_idem: "\<lbrakk>sorted_less xs; x \<in> set xs\<rbrakk> \<Longrightarrow> (ins_list x xs = xs)"
  using ins_list_idem_eq_isin by auto


declare node\<^sub>i.simps [simp del]
declare node\<^sub>i_inorder [simp add]

lemma ins_inorder: "sorted_less (inorder t) \<Longrightarrow> (inorder_up\<^sub>i (ins k x t)) = ins_list x (inorder t)"
proof(induction k x t rule: ins.induct)
  case (1 k x)
  then show ?case by auto
next
  case (2 k x ts t)
  then obtain ls rs where list_split: "split ts x = (ls,rs)"
    by (cases "split ts x")
  then have list_conc: "ts = ls@rs"
    using split.split_conc split_axioms by blast
  then show ?case
  proof (cases rs)
    case Nil
    then show ?thesis
    proof (cases "ins k x t")
      case (T\<^sub>i a)
      then have IH:"inorder a = ins_list x (inorder t)"
        using "2.IH"(1) "2.prems" list_split local.Nil sorted_inorder_induct_last
        by auto

      have "inorder_up\<^sub>i (ins k x (Node ts t)) = inorder_list ls @ inorder a"
        using list_split T\<^sub>i Nil by (auto simp add: list_conc)
      also have "\<dots> = inorder_list ls @ (ins_list x (inorder t))"
        by (simp add: IH)
      also have "\<dots> = ins_list x (inorder (Node ts t))"
        using ins_list_split
        using "2.prems" list_split Nil by auto
      finally show ?thesis .
    next
      case (Up\<^sub>i l a r)
      then have IH:"inorder_up\<^sub>i (Up\<^sub>i l a r) = ins_list x (inorder t)"
        using "2.IH"(1) "2.prems" list_split local.Nil sorted_inorder_induct_last by auto

      have "inorder_up\<^sub>i (ins k x (Node ts t)) = inorder_list ls @ inorder_up\<^sub>i (Up\<^sub>i l a r)"
        using list_split Up\<^sub>i Nil by (auto simp add: list_conc)
      also have "\<dots> = inorder_list ls @ ins_list x (inorder t)"
        using IH by simp
      also have "\<dots> = ins_list x (inorder (Node ts t))"
        using ins_list_split
        using "2.prems" list_split local.Nil by auto
      finally show ?thesis .
    qed
  next
    case (Cons h list)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)

    then have sorted_inorder_sub: "sorted_less (inorder sub)"
      using "2.prems" list_conc local.Cons sorted_inorder_induct_subtree
      by fastforce
    then show ?thesis
    proof(cases "x = sep")
      case True
      then have "x \<in> set (inorder (Node ts t))"
        using list_conc h_split Cons by simp
      then have "ins_list x (inorder (Node ts t)) = inorder (Node ts t)"
        using "2.prems" ins_list_contains_idem by blast
      also have "\<dots> = inorder_up\<^sub>i (ins k x (Node ts t))"
        using list_split h_split Cons True by auto
      finally show ?thesis by simp
    next
      case False
      then show ?thesis
      proof (cases "ins k x sub")
        case (T\<^sub>i a)
        then have IH:"inorder a = ins_list x (inorder sub)"
          using "2.IH"(2) "2.prems" list_split Cons sorted_inorder_sub h_split False
          by auto
        have "inorder_up\<^sub>i (ins k x (Node ts t)) = inorder_list ls @ inorder a @ sep # inorder_list list @ inorder t"
          using h_split False list_split T\<^sub>i Cons by simp
        also have "\<dots> = inorder_list ls @ ins_list x (inorder sub) @ sep # inorder_list list @ inorder t"
          using IH by simp
        also have "\<dots> = ins_list x (inorder (Node ts t))"
          using ins_list_split ins_list_split_right
          using list_split "2.prems" Cons h_split False by auto
        finally show ?thesis .
      next
        case (Up\<^sub>i l a r)
        then have IH:"inorder_up\<^sub>i (Up\<^sub>i l a r) = ins_list x (inorder sub)"
          using "2.IH"(2) False h_split list_split local.Cons sorted_inorder_sub
          by auto
        have "inorder_up\<^sub>i (ins k x (Node ts t)) = inorder_list ls @ inorder l @ a # inorder r  @ sep # inorder_list list @ inorder t"
          using h_split False list_split Up\<^sub>i Cons by simp
        also have "\<dots> = inorder_list ls @ ins_list x (inorder sub) @ sep # inorder_list list @ inorder t"
          using IH by simp
        also have "\<dots> = ins_list x (inorder (Node ts t))"
          using ins_list_split ins_list_split_right
          using list_split "2.prems" Cons h_split False by auto
        finally show ?thesis .
      qed
    qed
  qed
qed

declare node\<^sub>i.simps [simp add]
declare node\<^sub>i_inorder [simp del]


thm ins.induct
thm btree.induct

(* wrapped up insert invariants *)

lemma tree\<^sub>i_bal: "bal_up\<^sub>i u \<Longrightarrow> bal (tree\<^sub>i u)"
  apply(cases u)
   apply(auto)
  done

lemma tree\<^sub>i_order: "\<lbrakk>k > 0; root_order_up\<^sub>i k u\<rbrakk> \<Longrightarrow> root_order k (tree\<^sub>i u)"
  apply(cases u)
   apply(auto simp add: order_impl_root_order)
  done

lemma tree\<^sub>i_inorder: "inorder_up\<^sub>i u = inorder (tree\<^sub>i u)"
  apply (cases u)
   apply auto
  done

lemma insert_bal: "bal t \<Longrightarrow> bal (insert k x t)"
  using ins_bal
  by (simp add: tree\<^sub>i_bal)

lemma insert_order: "\<lbrakk>k > 0; root_order k t\<rbrakk> \<Longrightarrow> root_order k (insert k x t)"
  using ins_root_order
  by (simp add: tree\<^sub>i_order)


lemma insert_inorder: "sorted_less (inorder t) \<Longrightarrow> inorder (insert k x t) = ins_list x (inorder t)"
  using ins_inorder
  by (simp add: tree\<^sub>i_inorder)

text "Deletion proofs"

thm list.simps



lemma rebalance_middle_tree_height:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "height (rebalance_middle_tree k ls sub sep rs t) = height (Node (ls@(sub,sep)#rs) t)"
proof (cases "height t")
  case 0
  then have "t = Leaf" "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis by simp
next
  case (Suc nat)
  then obtain tts tt where t_node: "t = Node tts tt"
    using height_Leaf by (cases t) simp
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) simp
  then show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      then have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt) = height (Node (mts@(mt,sep)#tts) tt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = max (height t) (height sub)"
        by (metis assms(1) height_up\<^sub>i.simps(2) height_list_split sub_node t_node)
      finally have height_max: "height_up\<^sub>i (node\<^sub>i k (mts @ (mt, sep) # tts) tt) = max (height t) (height sub)" by simp
      then show ?thesis
      proof (cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
        case (T\<^sub>i u)
        then have "height u = max (height t) (height sub)" using height_max by simp
        then have "height (Node ls u) = height (Node (ls@[(sub,sep)]) t)"
          by (induction ls) (auto simp add: max.commute)
        then show ?thesis using Nil False T\<^sub>i
          by (simp add: sub_node t_node)
      next
        case (Up\<^sub>i l a r)
        then have "height (Node (ls@[(sub,sep)]) t) =  height (Node (ls@[(l,a)]) r)"
          using assms(1) height_max by (induction ls) auto
        then show ?thesis
          using Up\<^sub>i Nil sub_node t_node by auto
      qed
    next
      case (Cons a list)
      then obtain rsub rsep where a_split: "a = (rsub, rsep)"
        by (cases a)
      then obtain rts rt where r_node: "rsub = Node rts rt"
        using assms(2) Cons height_Leaf Suc by (cases rsub) simp_all

      then have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt) = height (Node (mts@(mt,sep)#rts) rt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = max (height rsub) (height sub)"
        by (metis r_node height_up\<^sub>i.simps(2) height_list_split max.commute sub_node)
      finally have height_max: "height_up\<^sub>i (node\<^sub>i k (mts @ (mt, sep) # rts) rt) = max (height rsub) (height sub)" by simp
      then show ?thesis
      proof (cases "node\<^sub>i k (mts@(mt,sep)#rts) rt")
        case (T\<^sub>i u)
        then have "height u = max (height rsub) (height sub)"
          using height_max by simp
        then show ?thesis
          using T\<^sub>i False Cons r_node a_split sub_node t_node by auto
      next
        case (Up\<^sub>i l a r)
        then have height_max: "max (height l) (height r) = max (height rsub) (height sub)"
          using height_max by auto
        then show ?thesis
          using Cons a_split r_node Up\<^sub>i sub_node t_node by auto
      qed
    qed
  qed (simp add: sub_node t_node)
qed


lemma rebalance_last_tree_height:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "height (rebalance_last_tree k ts t) = height (Node ts t)"
  using rebalance_middle_tree_height assms by auto

lemma split_max_height:
  assumes "split_max k t = (sub,sep)"
    and "nonempty_lasttreebal t"
    and "t \<noteq> Leaf"
  shows "height sub = height t"
  using assms
proof(induction t arbitrary: k sub sep)
  case Node1: (Node tts tt)
  then obtain ls tsub tsep where tts_split: "tts = ls@[(tsub,tsep)]" by auto
  then show ?case
  proof (cases tt)
    case Leaf
    then have "height (Node (ls@[(tsub,tsep)]) tt) = max (height (Node ls tsub)) (Suc (height tt))"
      using height_btree_last height_btree_order by metis
    moreover have "split_max k (Node tts tt) = (Node ls tsub, tsep)"
      using Leaf Node1 tts_split by auto
    ultimately show ?thesis
      using Leaf Node1 height_Leaf max_def by auto
  next
    case Node2: (Node l a)
    then obtain subsub subsep where sub_split: "split_max k tt = (subsub,subsep)" by (cases "split_max k tt")
    then have "height subsub = height tt" using Node1 Node2 by auto
    moreover have "split_max k (Node tts tt) = (rebalance_last_tree k tts subsub, subsep)"
      using Node1 Node2 tts_split sub_split by auto
    ultimately show ?thesis using rebalance_last_tree_height Node1 Node2 by auto
  qed
qed auto

lemma order_bal_nonempty_lasttreebal: "\<lbrakk>k > 0; root_order k t; bal t\<rbrakk> \<Longrightarrow> nonempty_lasttreebal t"
proof(induction k t rule: order.induct)
  case (2 k ts t)
  then have "length ts > 0" by auto
  then obtain ls tsub tsep where ts_split: "ts = (ls@[(tsub,tsep)])"
    by (metis eq_fst_iff length_greater_0_conv snoc_eq_iff_butlast)
  moreover have "height tsub = height t"
    using "2.prems"(3) ts_split by auto
  moreover have "nonempty_lasttreebal t" using 2 order_impl_root_order by auto
  ultimately show ?case by simp
qed simp

lemma bal_sub_height: "bal (Node (ls@a#rs) t) \<Longrightarrow> (case rs of [] \<Rightarrow> True | (sub,sep)#_ \<Rightarrow> height sub = height t)"
  by (cases rs) (auto)

lemma del_height: "\<lbrakk>k > 0; root_order k t; bal t\<rbrakk> \<Longrightarrow> height (del k x t) = height t"
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split ts x = (ls, list)" by (cases "split ts x")
  then show ?case
  proof(cases list)
    case Nil
    then have "height (del k x t) = height t"
      using 2 list_split order_bal_nonempty_lasttreebal
      by (simp add: order_impl_root_order)
    moreover obtain lls sub sep where "ls = lls@[(sub,sep)]"
      using split_conc 2 list_split Nil
      by (metis append_Nil2 nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal)
    moreover have "Node ls t = Node ts t" using split_conc Nil list_split by auto
    ultimately show ?thesis
      using rebalance_last_tree_height 2 list_split Nil split_conc
      by (auto simp add: max.assoc sup_nat_def max_def)
  next
    case (Cons a rs)
    then have rs_height: "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t" (* notice the difference if rsub and t are switched *)
      using "2.prems"(3) bal_sub_height list_split split_conc by blast
    from Cons obtain sub sep where a_split: "a = (sub,sep)" by (cases a)
    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" |
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      have height_t_sub: "height t = height sub"
        using "2.prems"(3) a_split list_split local.Cons split.split_set(1) split_axioms by fastforce
      have height_t_del: "height (del k x sub) = height t"
        by (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) list_split local.Cons order_impl_root_order root_order.simps(2) sep_n_x some_child_sub(1) split_set(1))
      then have "height (rebalance_middle_tree k ls (del k x sub) sep rs t) = height (Node (ls@((del k x sub),sep)#rs) t)"
        using rs_height rebalance_middle_tree_height by simp
      also have "\<dots> = height (Node (ls@(sub,sep)#rs) t)"
        using height_t_sub "2.prems" height_t_del
        by auto
      also have "\<dots> = height (Node ts t)"
        using 2 a_split sep_n_x list_split Cons split_set(1) split_conc
        by auto
      finally show ?thesis
        using sep_n_x Cons a_split list_split 2
        by simp
    next
      case sep_x_Leaf
      then have "height (Node ts t) = height (Node (ls@rs) t)"
        using bal_split_last(2) "2.prems"(3) a_split list_split Cons split_conc
        by metis
      then show ?thesis
        using a_split list_split Cons sep_x_Leaf 2 by auto
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by blast
      obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) a_split bal.simps(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) some_child_sub(1) split_set(1) split_max_height sub_node)
      then have "height (rebalance_middle_tree k ls sub_s max_s rs t) = height (Node (ls@(sub_s,sep)#rs) t)"
        using rs_height rebalance_middle_tree_height by simp
      also have "\<dots> = height (Node ts t)"
        using 2 a_split sep_x_Node list_split Cons split_set(1) \<open>height sub_s = height t\<close>
        by (auto simp add: split_conc[of ts])
      finally show ?thesis using sep_x_Node Cons a_split list_split 2 sub_node sub_split
        by auto
    qed
  qed
qed simp

(* proof for inorders *)

(* note: this works (as it should, since there is not even recursion involved)
  automatically. *yay* *)
lemma rebalance_middle_tree_inorder:
  assumes "height t = height sub"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
  shows "inorder (rebalance_middle_tree k ls sub sep rs t) = inorder (Node (ls@(sub,sep)#rs) t)"
  apply(cases sub; cases t)
  using assms
     apply (auto
      split!: btree.splits up\<^sub>i.splits list.splits
      simp del: node\<^sub>i.simps
      simp add: node\<^sub>i_inorder_simps
      )
  done

lemma rebalance_last_tree_inorder:
  assumes "height t = height sub"
    and "ts = list@[(sub,sep)]"
  shows "inorder (rebalance_last_tree k ts t) = inorder (Node ts t)"
  using rebalance_middle_tree_inorder assms by auto

lemma butlast_inorder_app_id: "xs = xs' @ [(sub,sep)] \<Longrightarrow> inorder_list xs' @ inorder sub @ [sep] = inorder_list xs"
  by simp

lemma split_max_inorder:
  assumes "nonempty_lasttreebal t"
    and "t \<noteq> Leaf"
  shows "inorder_pair (split_max k t) = inorder t"
  using assms
proof (induction k t rule: split_max.induct)
  case (1 k ts t)
  then show ?case
  proof (cases t)
    case Leaf
    then have "ts = butlast ts @ [last ts]"
      using "1.prems"(1) by auto
    moreover obtain sub sep where "last ts = (sub,sep)"
      by fastforce
    ultimately show ?thesis
      using Leaf
      apply (auto split!: prod.splits btree.splits)
      by (simp add: butlast_inorder_app_id)
  next
    case (Node tts tt)
    then have IH: "inorder_pair (split_max k t) = inorder t"
      using "1.IH" "1.prems"(1) by auto
    obtain sub sep where split_sub_sep: "split_max k t = (sub,sep)"
      by fastforce
    then have height_sub: "height sub = height t"
      by (metis "1.prems"(1) Node btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height)
    have "inorder_pair (split_max k (Node ts t)) = inorder (rebalance_last_tree k ts sub) @ [sep]"
      using Node 1 split_sub_sep by auto
    also have "\<dots> = inorder_list ts @ inorder sub @ [sep]"
      using rebalance_last_tree_inorder height_sub "1.prems"
      by (auto simp del: rebalance_last_tree.simps)
    also have "\<dots> = inorder (Node ts t)"
      using IH split_sub_sep by simp
    finally show ?thesis .
  qed
qed simp


lemma height_bal_subtrees_merge: "\<lbrakk>height (Node as a) = height (Node bs b); bal (Node as a); bal (Node bs b)\<rbrakk>
 \<Longrightarrow> \<forall>x \<in> set (subtrees as) \<union> {a}. height x = height b"
  by (metis Suc_inject Un_iff bal.simps(2) height_bal_tree singletonD)

lemma bal_list_merge:
  assumes "bal_up\<^sub>i (Up\<^sub>i (Node as a) x (Node bs b))"
  shows "bal (Node (as@(a,x)#bs) b)"
proof -
  have "\<forall>x\<in>set (subtrees (as @ (a, x) # bs)). bal x"
    using subtrees_split assms by auto
  moreover have "bal b"
    using assms by auto
  moreover have "\<forall>x\<in>set (subtrees as) \<union> {a} \<union> set (subtrees bs). height x = height b"
    using assms height_bal_subtrees_merge
    unfolding bal_up\<^sub>i.simps
    by blast
  ultimately show ?thesis
    by auto
qed

lemma node\<^sub>i_bal_up\<^sub>i:
  assumes "bal_up\<^sub>i (node\<^sub>i k ts t)"
  shows "bal (Node ts t)"
  using assms
proof(cases "length ts \<le> 2*k")
  case False
  then obtain ls sub sep rs where split_list: "split_half ts = (ls, (sub,sep)#rs)"
    using node\<^sub>i_cases by blast
  then have "node\<^sub>i k ts t = Up\<^sub>i (Node ls sub) sep (Node rs t)"
    using False by auto
  moreover have "ts = ls@(sub,sep)#rs"
    by (metis append_take_drop_id fst_conv local.split_list snd_conv split_half.elims)
  ultimately show ?thesis
    using bal_list_merge[of ls sub sep rs t] assms
    by (simp del: bal.simps bal_up\<^sub>i.simps)
qed simp

lemma node\<^sub>i_bal_simp: "bal_up\<^sub>i (node\<^sub>i k ts t) = bal (Node ts t)"
  using node\<^sub>i_bal node\<^sub>i_bal_up\<^sub>i by blast

lemma rebalance_middle_tree_bal: "bal (Node (ls@(sub,sep)#rs) t) \<Longrightarrow> bal (rebalance_middle_tree k ls sub sep rs t)"
proof (cases t)
  case t_node: (Node tts tt)
  assume assms: "bal (Node (ls @ (sub, sep) # rs) t)"
  then obtain mts mt where sub_node: "sub = Node mts mt"
    by (cases sub) (auto simp add: t_node)
  have sub_heights: "height sub = height t" "bal sub" "bal t"
    using assms by auto
  show ?thesis
  proof (cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then show ?thesis
      using t_node sub_node assms
      by (auto simp del: bal.simps)
  next
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt) = height (Node (mts@(mt,sep)#tts) tt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = Suc (height tt)"
        by (metis height_bal_tree height_up\<^sub>i.simps(2) height_list_split max.idem sub_heights(1) sub_heights(3) sub_node t_node)
      also have "\<dots> = height t"
        using height_bal_tree sub_heights(3) t_node by fastforce
      finally have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt) = height t" by simp
      moreover have "bal_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#tts) tt)"
        by (metis bal_list_merge bal_up\<^sub>i.simps(2) node\<^sub>i_bal sub_heights(1) sub_heights(2) sub_heights(3) sub_node t_node)
      ultimately show ?thesis
        apply (cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
        using assms Nil sub_node t_node by auto
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t" "bal rsub"
        using assms Cons by auto
      then obtain rts rt where r_node: "rsub = (Node rts rt)"
        apply(cases rsub) using t_node by simp
      have "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt) = height (Node (mts@(mt,sep)#rts) rt)"
        using node\<^sub>i_height by blast
      also have "\<dots> = Suc (height rt)"
        by (metis Un_iff  \<open>height rsub = height t\<close> assms bal.simps(2) bal_split_last(1) height_bal_tree height_up\<^sub>i.simps(2) height_list_split list.set_intros(1) Cons max.idem r_node r_split set_append some_child_sub(1) sub_heights(1) sub_node)
      also have "\<dots> = height rsub"
        using height_bal_tree r_node rsub_height(2) by fastforce
      finally have 1: "height_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt) = height rsub" .
      moreover have 2: "bal_up\<^sub>i (node\<^sub>i k (mts@(mt,sep)#rts) rt)"
        by (metis bal_list_merge bal_up\<^sub>i.simps(2) node\<^sub>i_bal r_node rsub_height(1) rsub_height(2) sub_heights(1) sub_heights(2) sub_node)
      ultimately show ?thesis
      proof (cases "node\<^sub>i k (mts@(mt,sep)#rts) rt")
        case (T\<^sub>i u)
        then have "bal (Node (ls@(u,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_btree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False T\<^sub>i
          by (auto simp del: node\<^sub>i.simps bal.simps)
      next
        case (Up\<^sub>i l a r)
        then have "bal (Node (ls@(l,a)#(r,rsep)#rs) t)"
          using 1 2 Cons assms t_node subtrees_split sub_heights r_split rsub_height
          unfolding bal.simps by (auto simp del: height_btree.simps)
        then show ?thesis
          using Cons assms t_node sub_node r_split r_node False Up\<^sub>i
          by (auto simp del: node\<^sub>i.simps bal.simps)
      qed
    qed
  qed
qed (simp add: height_Leaf)


lemma rebalance_last_tree_bal: "\<lbrakk>bal (Node ts t); ts \<noteq> []\<rbrakk> \<Longrightarrow> bal (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_bal append_butlast_last_id[of ts]
  apply(cases "last ts")
  apply(auto simp del: bal.simps rebalance_middle_tree.simps)
  done


lemma split_max_bal:
  assumes "bal t"
    and "t \<noteq> Leaf"
    and "nonempty_lasttreebal t"
  shows "bal (fst (split_max k t))"
  using assms
proof(induction k t rule: split_max.induct)
  case (1 k ts t)
  then show ?case
  proof (cases t)
    case Leaf
    then obtain sub sep where last_split: "last ts = (sub,sep)"
      using 1 by auto
    then have "height sub = height t" using 1 by auto
    then have "bal (Node (butlast ts) sub)" using 1 last_split by auto
    then show ?thesis using 1 Leaf last_split by auto
  next
    case (Node tts tt)
    then obtain sub sep where t_split: "split_max k t = (sub,sep)" by (cases "split_max k t")
    then have "height sub = height t" using 1 Node
      by (metis btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height)
    moreover have "bal sub"
      using "1.IH" "1.prems"(1) "1.prems"(3) Node t_split by fastforce
    ultimately have "bal (Node ts sub)"
      using 1 t_split Node by auto
    then show ?thesis
      using rebalance_last_tree_bal t_split Node 1
      by (auto simp del: bal.simps rebalance_middle_tree.simps)
  qed
qed simp

lemma del_bal:
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
  shows "bal (del k x t)"
  using assms
proof(induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls rs where list_split: "split ts x = (ls,rs)"
    by (cases "split ts x")
  then show ?case
  proof (cases rs)
    case Nil
    then have "bal (del k x t)" using 2 list_split
      by (simp add: order_impl_root_order)
    moreover have "height (del k x t) = height t"
      using 2 del_height by (simp add: order_impl_root_order)
    moreover have "ts \<noteq> []" using 2 by auto
    ultimately have "bal (rebalance_last_tree k ts (del k x t))"
      using 2 Nil order_bal_nonempty_lasttreebal rebalance_last_tree_bal
      by simp
    then have "bal (rebalance_last_tree k ls (del k x t))"
      using list_split split_conc Nil by fastforce
    then show ?thesis
      using 2 list_split Nil
      by auto
  next
    case (Cons r rs)
    then obtain sub sep where r_split: "r = (sub,sep)" by (cases r)
    then have sub_height: "height sub = height t" "bal sub"
      using 2 Cons list_split split_set(1) by fastforce+
    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" |
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      then have "bal (del k x sub)" "height (del k x sub) = height sub" using sub_height
         apply (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) list_split local.Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_set(1))
        by (metis "2.prems"(1) "2.prems"(2) list_split Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) del_height split_set(1) sub_height(2))
      moreover have "bal (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) list_split Cons r_split split_conc by blast
      ultimately have "bal (Node (ls@(del k x sub,sep)#rs) t)"
        using bal_substitute_subtree[of ls sub sep rs t "del k x sub"] by metis
      then have "bal (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using rebalance_middle_tree_bal[of ls "del k x sub" sep rs t k] by metis
      then show ?thesis
        using 2 list_split Cons r_split sep_n_x by auto
    next
      case sep_x_Leaf
      moreover have "bal (Node (ls@rs) t)"
        using bal_split_last(1) list_split split_conc r_split
        by (metis "2.prems"(3) Cons)
      ultimately show ?thesis
        using 2 list_split Cons r_split by auto
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      then obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height sub"
        using split_max_height
        by (metis "2.prems"(1) "2.prems"(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_set(1) sub_height(2) sub_node)
      moreover have "bal sub_s"
        using split_max_bal
        by (metis "2.prems"(1) "2.prems"(2) btree.distinct(1) fst_conv list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_set(1) sub_height(2) sub_node sub_split)
      moreover have "bal (Node (ls@(sub,sep)#rs) t)"
        using "2.prems"(3) list_split Cons r_split split_conc by blast
      ultimately have "bal (Node (ls@(sub_s,sep)#rs) t)"
        using bal_substitute_subtree[of ls sub sep rs t "sub_s"] by metis
      then have "bal (Node (ls@(sub_s,max_s)#rs) t)"
        using bal_substitute_separator by metis
      then have "bal (rebalance_middle_tree k ls sub_s max_s rs t)"
        using rebalance_middle_tree_bal[of ls sub_s max_s rs t k] by metis
      then show ?thesis
        using 2 list_split Cons r_split sep_x_Node sub_node sub_split by auto
    qed
  qed
qed simp


lemma rebalance_middle_tree_order:
  assumes "almost_order k sub"
    and "\<forall>s \<in> set (subtrees (ls@rs)). order k s" "order k t"
    and "case rs of (rsub,rsep) # list \<Rightarrow> height rsub = height t | [] \<Rightarrow> True"
    and "length (ls@(sub,sep)#rs) \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_middle_tree k ls sub sep rs t)"
proof(cases t)
  case Leaf
  then have "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis using Leaf assms by auto
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto)
  then show ?thesis
  proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then have "order k sub" using assms
      by (simp add: sub_node)
    then show ?thesis
      using True t_node sub_node assms by auto
  next
    case False
    then show ?thesis
    proof (cases rs)
      case Nil
      have "order_up\<^sub>i k (node\<^sub>i k (mts@(mt,sep)#tts) tt)"
        using node\<^sub>i_order[of k "mts@(mt,sep)#tts" tt] assms(1,3) t_node sub_node
        by (auto simp del: order_up\<^sub>i.simps node\<^sub>i.simps)
      then show ?thesis
        apply(cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
        using assms t_node sub_node False Nil apply (auto simp del: node\<^sub>i.simps)
        done
    next
      case (Cons r rs)
      then obtain rsub rsep where r_split: "r = (rsub,rsep)" by (cases r)
      then have rsub_height: "height rsub = height t"
        using assms Cons by auto
      then obtain rts rt where r_node: "rsub = (Node rts rt)"
        apply(cases rsub) using t_node by simp
      have "order_up\<^sub>i k (node\<^sub>i k (mts@(mt,sep)#rts) rt)"
        using node\<^sub>i_order[of k "mts@(mt,sep)#rts" rt] assms(1,2) t_node sub_node r_node r_split Cons
        by (auto simp del: order_up\<^sub>i.simps node\<^sub>i.simps)
      then show ?thesis
        apply(cases "node\<^sub>i k (mts@(mt,sep)#rts) rt")
        using assms t_node sub_node False Cons r_split r_node apply (auto simp del: node\<^sub>i.simps)
        done
    qed
  qed
qed

(* we have to proof the order invariant once for an underflowing last tree *)
lemma rebalance_middle_tree_last_order:
  assumes "almost_order k t"
    and  "\<forall>s \<in> set (subtrees (ls@(sub,sep)#rs)). order k s"
    and "rs = []"
    and "length (ls@(sub,sep)#rs) \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_middle_tree k ls sub sep rs t)"
proof (cases t)
  case Leaf
  then have "sub = Leaf" using height_Leaf assms by auto
  then show ?thesis using Leaf assms by auto
next
  case t_node: (Node tts tt)
  then obtain mts mt where sub_node: "sub = Node mts mt"
    using assms by (cases sub) (auto)
  then show ?thesis
  proof(cases "length mts \<ge> k \<and> length tts \<ge> k")
    case True
    then have "order k sub" using assms
      by (simp add: sub_node)
    then show ?thesis
      using True t_node sub_node assms by auto
  next
    case False
    have "order_up\<^sub>i k (node\<^sub>i k (mts@(mt,sep)#tts) tt)"
      using node\<^sub>i_order[of k "mts@(mt,sep)#tts" tt] assms t_node sub_node
      by (auto simp del: order_up\<^sub>i.simps node\<^sub>i.simps)
    then show ?thesis
      apply(cases "node\<^sub>i k (mts@(mt,sep)#tts) tt")
      using assms t_node sub_node False Nil apply (auto simp del: node\<^sub>i.simps)
      done
  qed
qed

lemma rebalance_last_tree_order:
  assumes "ts = ls@[(sub,sep)]"
    and "\<forall>s \<in> set (subtrees (ts)). order k s" "almost_order k t"
    and "length ts \<le> 2*k"
    and "height sub = height t"
  shows "almost_order k (rebalance_last_tree k ts t)"
  using rebalance_middle_tree_last_order assms by auto

lemma split_max_order:
  assumes "order k t"
    and "t \<noteq> Leaf"
    and "nonempty_lasttreebal t"
  shows "almost_order k (fst (split_max k t))"
  using assms
proof(induction k t rule: split_max.induct)
  case (1 k ts t)
  then obtain ls sub sep where ts_not_empty: "ts = ls@[(sub,sep)]"
    by auto
  then show ?case
  proof (cases t)
    case Leaf
    then show ?thesis using ts_not_empty 1 by auto
  next
    case (Node)
    then obtain s_sub s_max where sub_split: "split_max k t = (s_sub, s_max)"
      by (cases "split_max k t")
    moreover have "height sub = height s_sub"
      by (metis "1.prems"(3) Node Pair_inject append1_eq_conv btree.distinct(1) nonempty_lasttreebal.simps(2) split_max_height sub_split ts_not_empty)
    ultimately have "almost_order k (rebalance_last_tree k ts s_sub)"
      using rebalance_last_tree_order[of ts ls sub sep k s_sub]
        1 ts_not_empty Node sub_split
      by force
    then show ?thesis
      using Node 1 sub_split by auto
  qed
qed simp


lemma del_order:
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
  shows "almost_order k (del k x t)"
  using assms
proof (induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls list where list_split: "split ts x = (ls, list)" by (cases "split ts x")
  then show ?case
  proof (cases list)
    case Nil
    then have "almost_order k (del k x t)" using 2 list_split
      by (simp add: order_impl_root_order)
    moreover obtain lls lsub lsep where ls_split: "ls = lls@[(lsub,lsep)]"
      using 2 Nil list_split
      by (metis append_Nil2 nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal split_conc)
    moreover have "height t = height (del k x t)" using del_height 2
      by (simp add: order_impl_root_order)
    moreover have "length ls = length ts"
      using Nil list_split
      by (auto dest: split_length)
    ultimately have "almost_order k (rebalance_last_tree k ls (del k x t))"
      using rebalance_last_tree_order[of ls lls lsub lsep k "del k x t"]
      by (metis "2.prems"(2) "2.prems"(3) Un_iff append_Nil2 bal.simps(2) list_split Nil root_order.simps(2) singletonI split_conc subtrees_split)
    then show ?thesis
      using 2 list_split Nil by auto
  next
    case (Cons r rs)

    from Cons obtain sub sep where r_split: "r = (sub,sep)" by (cases r)

    have inductive_help:
      "case rs of [] \<Rightarrow> True | (rsub,rsep)#_ \<Rightarrow> height rsub = height t"
      "\<forall>s\<in>set (subtrees (ls @ rs)). order k s"
      "Suc (length (ls @ rs)) \<le> 2 * k"
      "order k t"
      using Cons r_split "2.prems" list_split split_set
      by (auto dest: split_conc split!: list.splits)

    consider (sep_n_x) "sep \<noteq> x" |
      (sep_x_Leaf) "sep = x \<and> sub = Leaf" |
      (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      then have "almost_order k (del k x sub)" using 2 list_split Cons r_split order_impl_root_order
        by (metis bal.simps(2) root_order.simps(2) some_child_sub(1) split_set(1))
      moreover have "height (del k x sub) = height t"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) list_split Cons order_impl_root_order r_split root_order.simps(2) some_child_sub(1) del_height split_set(1))
      ultimately have "almost_order k (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using rebalance_middle_tree_order[of k "del k x sub" ls rs t sep]
        using inductive_help
        using Cons r_split sep_n_x list_split by auto
      then show ?thesis using 2 Cons r_split sep_n_x list_split by auto
    next
      case sep_x_Leaf
      then have "almost_order k (Node (ls@rs) t)" using inductive_help by auto
      then show ?thesis using 2 Cons r_split sep_x_Leaf list_split by auto
    next
      case sep_x_Node
      then obtain sts st where sub_node: "sub = Node sts st" by auto
      then obtain sub_s max_s where sub_split: "split_max k sub = (sub_s, max_s)"
        by (cases "split_max k sub")
      then have "height sub_s = height t" using split_max_height
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) list_split Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_set(1) sub_node)
      moreover have "almost_order k sub_s" using split_max_order
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) btree.distinct(1) fst_conv list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order r_split root_order.simps(2) some_child_sub(1) split_set(1)  sub_node sub_split)
      ultimately have "almost_order k (rebalance_middle_tree k ls sub_s max_s rs t)"
        using rebalance_middle_tree_order[of k sub_s ls rs t max_s] inductive_help
        by auto
      then show ?thesis
        using 2 Cons r_split list_split sep_x_Node sub_split by auto
    qed
  qed
qed simp

(* sortedness of delete by inorder *)
(* generalize del_list_sorted since its cumbersome to express inorder_list ts as xs @ [a]
note that the proof scheme is almost identical to ins_list_sorted
 *)
thm del_list_sorted

lemma del_list_split:
  assumes "split ts x = (ls, rs)"
    and "sorted_less (inorder (Node ts t))"
  shows "del_list x (inorder (Node ts t)) = inorder_list ls @ del_list x (inorder_list rs @ inorder t)"
proof (cases ls)
  case Nil
  then show ?thesis
    using assms by (auto dest!: split_conc)
next
  case Cons
  then obtain ls' sub sep where ls_tail_split: "ls = ls' @ [(sub,sep)]"
    by (metis list.distinct(1) rev_exhaust surj_pair)
  moreover have "sep < x"
    using split_req(2)[of ts x ls' sub sep rs]
    using assms(1) assms(2) ls_tail_split sorted_inorder_separators
    by blast
  moreover have "sorted_less (inorder_list ls)"
    using assms sorted_wrt_append split_conc by fastforce
  ultimately show ?thesis using assms(2) split_conc[OF assms(1)]
    using del_list_sorted[of "inorder_list ls' @ inorder sub" sep]
    by auto
qed

(* del sorted requires sortedness of the full list so we need to change the right specialization a bit *)

lemma del_list_split_right:
  assumes "split ts x = (ls, (sub,sep)#rs)"
    and "sorted_less (inorder (Node ts t))"
    and "sep \<noteq> x"
  shows "del_list x (inorder_list ((sub,sep)#rs) @ inorder t) = del_list x (inorder sub) @ sep # inorder_list rs @ inorder t"
proof -
  from assms have "x < sep"
  proof -
    from assms have "sorted_less (separators ts)"
      using sorted_inorder_separators by blast
    then show ?thesis
      using split_req(3)
      using assms
      by fastforce
  qed
  moreover have "sorted_less (inorder sub @ sep # inorder_list rs @ inorder t)"
    using assms sorted_wrt_append[where xs="inorder_list ls"]
    by (auto dest!: split_conc)
  ultimately show ?thesis
    using del_list_sorted[of "inorder sub" "sep"]
    by auto
qed

thm del_list_idem

lemma del_inorder:
  assumes "k > 0"
    and "root_order k t"
    and "bal t"
    and "sorted_less (inorder t)"
  shows "inorder (del k x t) = del_list x (inorder t)"
  using assms
proof (induction k x t rule: del.induct)
  case (2 k x ts t)
  then obtain ls rs where list_split: "split ts x = (ls, rs)"
    by (meson surj_pair)
  then have list_conc: "ts = ls @ rs"
    using split.split_conc split_axioms by blast
  show ?case
  proof (cases rs)
    case Nil
    then have IH: "inorder (del k x t) = del_list x (inorder t)"
      by (metis "2.IH"(1) "2.prems" bal.simps(2) list_split order_impl_root_order root_order.simps(2) sorted_inorder_induct_last)
    have "inorder (del k x (Node ts t)) = inorder (rebalance_last_tree k ts (del k x t))"
      using list_split Nil list_conc by auto
    also have "\<dots> = inorder_list ts @ inorder (del k x t)"
    proof -
      obtain ts' sub sep where ts_split: "ts = ts' @ [(sub, sep)]"
        by (meson "2.prems"(1) "2.prems"(2) "2.prems"(3) nonempty_lasttreebal.simps(2) order_bal_nonempty_lasttreebal)
      then have "height sub = height t"
        using "2.prems"(3) by auto
      moreover have "height t = height (del k x t)"
        by (metis "2.prems"(1) "2.prems"(2) "2.prems"(3) bal.simps(2) del_height order_impl_root_order root_order.simps(2))
      ultimately show ?thesis
        using rebalance_last_tree_inorder
        using ts_split by auto
    qed
    also have "\<dots> = inorder_list ts @ del_list x (inorder t)"
      using IH by blast
    also have "\<dots> = del_list x (inorder (Node ts t))"
      using "2.prems"(4) list_conc list_split Nil del_list_split
      by auto
    finally show ?thesis .
  next
    case (Cons h rs)
    then obtain sub sep where h_split: "h = (sub,sep)"
      by (cases h)
    then have node_sorted_split:
      "sorted_less (inorder (Node (ls@(sub,sep)#rs) t))"
      "root_order k (Node (ls@(sub,sep)#rs) t)"
      "bal (Node (ls@(sub,sep)#rs) t)"
      using "2.prems" h_split list_conc Cons by blast+
    consider (sep_n_x) "sep \<noteq> x" | (sep_x_Leaf) "sep = x \<and> sub = Leaf" |  (sep_x_Node) "sep = x \<and> (\<exists>ts t. sub = Node ts t)"
      using btree.exhaust by blast
    then show ?thesis
    proof cases
      case sep_n_x
      then have IH: "inorder (del k x sub) = del_list x (inorder sub)"
        by (metis "2.IH"(2) "2.prems"(1) "2.prems"(2) bal.simps(2) bal_split_left(1) h_split list_split local.Cons node_sorted_split(1) node_sorted_split(3) order_impl_root_order root_order.simps(2) some_child_sub(1) sorted_inorder_induct_subtree split_set(1))
      from sep_n_x have "inorder (del k x (Node ts t)) = inorder (rebalance_middle_tree k ls (del k x sub) sep rs t)"
        using list_split Cons h_split by auto
      also have "\<dots> = inorder (Node (ls@(del k x sub, sep)#rs) t)"
      proof -
        have "height t = height (del k x sub)"
          using del_height
          using order_impl_root_order "2.prems"
          by (auto simp add: order_impl_root_order Cons list_conc h_split)
        moreover have "case rs of [] \<Rightarrow> True | (rsub, rsep) # list \<Rightarrow> height rsub = height t"
          using "2.prems"(3) bal_sub_height list_conc Cons by blast
        ultimately show ?thesis
          using rebalance_middle_tree_inorder
          by simp
      qed
      also have "\<dots> = inorder_list ls @ del_list x (inorder sub) @ sep # inorder_list rs @ inorder t"
        using IH by simp
      also have "\<dots> = del_list x (inorder (Node ts t))"
        using del_list_split[of ts x ls "(sub,sep)#rs" t]
        using del_list_split_right[of ts x ls sub sep rs t]
        using list_split list_conc h_split Cons "2.prems"(4) sep_n_x
        by auto
      finally show ?thesis .
    next
      case sep_x_Leaf
      then have "del_list x (inorder (Node ts t)) = inorder (Node (ls@rs) t)"
        using list_conc h_split Cons
        using del_list_split[OF list_split "2.prems"(4)]
        by simp
      also have "\<dots> = inorder (del k x (Node ts t))"
        using list_split sep_x_Leaf list_conc h_split Cons
        by auto
      finally show ?thesis by simp
    next
      case sep_x_Node
      obtain ssub ssep where split_split: "split_max k sub = (ssub, ssep)"
        by fastforce
      from sep_x_Node have "x = sep"
        by simp
      then have "del_list x (inorder (Node ts t)) = inorder_list ls @ inorder sub @ inorder_list rs @ inorder t"
        using list_split list_conc h_split Cons "2.prems"(4)
        using del_list_split[OF list_split "2.prems"(4)]
        using del_list_sorted1[of "inorder sub" sep "inorder_list rs @ inorder t" x]
          sorted_wrt_append
        by auto
      also have "\<dots> = inorder_list ls @ inorder_pair (split_max k sub) @ inorder_list rs @ inorder t"
        using sym[OF split_max_inorder[of sub k]]
        using order_bal_nonempty_lasttreebal[of k sub] "2.prems"
          list_conc h_split Cons sep_x_Node
        by (auto simp del: split_max.simps simp add: order_impl_root_order)
      also have "\<dots> = inorder_list ls @ inorder ssub @ ssep # inorder_list rs @ inorder t"
        using split_split by auto
      also have "\<dots> = inorder (rebalance_middle_tree k ls ssub ssep rs t)"
      proof -
        have "height t = height ssub"
          using split_max_height
          by (metis "2.prems"(1,2,3) bal.simps(2) btree.distinct(1) h_split list_split local.Cons order_bal_nonempty_lasttreebal order_impl_root_order root_order.simps(2) sep_x_Node some_child_sub(1) split_set(1) split_split)
        moreover have "case rs of [] \<Rightarrow> True | (rsub, rsep) # list \<Rightarrow> height rsub = height t"
          using "2.prems"(3) bal_sub_height list_conc local.Cons
          by blast
        ultimately show ?thesis
          using rebalance_middle_tree_inorder
          by auto
      qed
      also have "\<dots> = inorder (del k x (Node ts t))"
        using list_split sep_x_Node list_conc h_split Cons split_split
        by auto
      finally show ?thesis by simp
    qed
  qed
qed auto

lemma reduce_root_order: "\<lbrakk>k > 0; almost_order k t\<rbrakk> \<Longrightarrow> root_order k (reduce_root t)"
  apply(cases t)
   apply(auto split!: list.splits simp add: order_impl_root_order)
  done

lemma reduce_root_bal: "bal (reduce_root t) = bal t"
  apply(cases t)
   apply(auto split!: list.splits)
  done


lemma reduce_root_inorder: "inorder (reduce_root t) = inorder t"
  apply (cases t)
   apply (auto split!: list.splits)
  done


lemma delete_order: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> root_order k (delete k x t)"
  using del_order
  by (simp add: reduce_root_order)

lemma delete_bal: "\<lbrakk>k > 0; bal t; root_order k t\<rbrakk> \<Longrightarrow> bal (delete k x t)"
  using del_bal
  by (simp add: reduce_root_bal)

lemma delete_inorder: "\<lbrakk>k > 0; bal t; root_order k t; sorted_less (inorder t)\<rbrakk> \<Longrightarrow> inorder (delete k x t) = del_list x (inorder t)"
  using del_inorder
  by (simp add: reduce_root_inorder)

(* TODO (opt) runtime wrt runtime of split *)

(* we are interested in a) number of comparisons b) number of fetches c) number of writes *)
(* a) is dependent on t_split, the remainder is not (we assume the number of fetches and writes
for split fun is 0 *)


(* TODO simpler induction schemes /less boilerplate isabelle/src/HOL/ex/Induction_Schema *)

subsection "Set specification by inorder"


interpretation S_ordered: Set_by_Ordered where
  empty = empty_btree and
  insert = "insert (Suc k)" and
  delete = "delete (Suc k)" and
  isin = "isin" and
  inorder = "inorder"   and
  inv = "invar_inorder (Suc k)"
proof (standard, goal_cases)
  case (2 s x)
  then show ?case
    by (simp add: isin_set_inorder)
next
  case (3 s x)
  then show ?case using insert_inorder
    by simp
next
  case (4 s x)
  then show ?case using delete_inorder
    by auto
next
  case (6 s x)
  then show ?case using insert_order insert_bal
    by auto
next
  case (7 s x)
  then show ?case using delete_order delete_bal
    by auto
qed (simp add: empty_btree_def)+


(* if we remove this, it is not possible to remove the simp rules in subsequent contexts... *)
declare node\<^sub>i.simps[simp del]

end


end
