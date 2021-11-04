subsection "Splay Tree Analysis"

theory Splay_Tree_Analysis
imports
  Splay_Tree_Analysis_Base
  Amortized_Framework
begin

subsubsection "Analysis of splay"

definition A_splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> real" where
"A_splay a t = T_splay a t + \<Phi>(splay a t) - \<Phi> t"

text\<open>The following lemma is an attempt to prove a generic lemma that covers
both zig-zig cases. However, the lemma is not as nice as one would like.
Hence it is used only once, as a demo. Ideally the lemma would involve
function @{const A_splay}, but that is impossible because this involves @{const splay}
and thus depends on the ordering. We would need a truly symmetric version of @{const splay}
that takes the ordering as an explicit argument. Then we could define
all the symmetric cases by one final equation
@{term"splay2 less t = splay2 (not o less) (mirror t)"}.
This would simplify the code and the proofs.\<close>

lemma zig_zig: fixes lx x rx lb b rb a ra u lb1 lb2
defines [simp]: "X == Node lx (x) rx" defines[simp]: "B == Node lb b rb"
defines [simp]: "t == Node B a ra" defines [simp]: "A' == Node rb a ra"
defines [simp]: "t' == Node lb1 u (Node lb2 b A')"
assumes hyps: "lb \<noteq> \<langle>\<rangle>" and IH: "T_splay x lb + \<Phi> lb1 + \<Phi> lb2 - \<Phi> lb \<le> 2 * \<phi> lb - 3 * \<phi> X + 1" and
 prems: "size lb = size lb1 + size lb2 + 1" "X \<in> subtrees lb"
shows "T_splay x lb + \<Phi> t' - \<Phi> t \<le> 3 * (\<phi> t - \<phi> X)"
proof -
  define B' where [simp]: "B' = Node lb2 b A'"
  have "T_splay x lb + \<Phi> t' - \<Phi> t = T_splay x lb + \<Phi> lb1 + \<Phi> lb2 - \<Phi> lb + \<phi> B' + \<phi> A' - \<phi> B"
    using prems
    by(auto simp: A_splay_def size_if_splay algebra_simps in_set_tree_if split: tree.split)
  also have "\<dots> \<le> 2 * \<phi> lb + \<phi> B' + \<phi> A' - \<phi> B - 3 * \<phi> X + 1"
    using IH prems(2) by(auto simp: algebra_simps)
  also have "\<dots> \<le> \<phi> lb + \<phi> B' + \<phi> A' - 3 * \<phi> X + 1" by(simp)
  also have "\<dots> \<le> \<phi> B' + 2 * \<phi> t - 3 * \<phi> X "
    using prems ld_ld_1_less[of "size1 lb" "size1 A'"]
    by(simp add: size_if_splay)
  also have "\<dots> \<le> 3 * \<phi> t - 3 * \<phi> X"
    using prems by(simp add: size_if_splay)
  finally show ?thesis by simp
qed

lemma A_splay_ub: "\<lbrakk> bst t; Node l x r : subtrees t \<rbrakk>
  \<Longrightarrow> A_splay x t \<le> 3 * (\<phi> t - \<phi>(Node l x r)) + 1"
proof(induction x t rule: splay.induct)
  case 1 thus ?case by simp
next
  case 2 thus ?case by (auto simp: A_splay_def)
next
  case 4 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 5 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 7 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 10 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 12 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case 13 hence False by(fastforce dest: in_set_tree_if) thus ?case ..
next
  case (3 x b A B CD)
  (* A readable proof *)
  let ?t = "\<langle>\<langle>A, x, B\<rangle>, b, CD\<rangle>"
  let ?t' = "\<langle>A, x, \<langle>B, b, CD\<rangle>\<rangle>"
  have *: "l = A \<and> r = B" using "3.prems" by(fastforce dest: in_set_tree_if)
  have "A_splay x ?t = 1 + \<Phi> ?t' - \<Phi> ?t" using "3.hyps" by (simp add: A_splay_def)
  also have "\<dots> = 1 + \<phi> ?t' + \<phi> \<langle>B, b, CD\<rangle>  - \<phi> ?t - \<phi> \<langle>A, x, B\<rangle>" by(simp)
  also have "\<dots> = 1 + \<phi> \<langle>B, b, CD\<rangle> - \<phi> \<langle>A, x, B\<rangle>" by(simp)
  also have "\<dots> \<le>  1 + \<phi> ?t - \<phi>(Node A x B)"
    using log_le_cancel_iff[of 2 "size1(Node B b CD)" "size1 ?t"] by (simp)
  also have "\<dots> \<le> 1 + 3 * (\<phi> ?t - \<phi>(Node A x B))"
    using log_le_cancel_iff[of 2 "size1(Node A x B)" "size1 ?t"] by (simp)
  finally show ?case using * by simp
next
  case (9 b x AB C D)
  (* An automatic proof *)
  let ?A = "\<langle>AB, b, \<langle>C, x, D\<rangle>\<rangle>"
  have "x \<notin> set_tree AB" using "9.prems"(1) by auto
  with 9 show ?case using
    log_le_cancel_iff[of 2 "size1(Node AB b C)" "size1 ?A"]
    log_le_cancel_iff[of 2 "size1(Node C x D)" "size1 ?A"]
    by (auto simp: A_splay_def algebra_simps simp del:log_le_cancel_iff)
next
  case (6 x a b A B C)
  hence *: "\<langle>l, x, r\<rangle> \<in> subtrees A" by(fastforce dest: in_set_tree_if)
  obtain A1 a' A2 where sp: "splay x A = Node A1 a' A2"
    using splay_not_Leaf[OF \<open>A \<noteq> Leaf\<close>] by blast
  let ?X = "Node l x r" let ?AB = "Node A a B"  let ?ABC = "Node ?AB b C"
  let ?A' = "Node A1 a' A2"
  let ?BC = "Node B b C"  let ?A2BC = "Node A2 a ?BC" let ?A1A2BC = "Node A1 a' ?A2BC"
  have 0: "\<phi> ?A1A2BC = \<phi> ?ABC" using sp by(simp add: size_if_splay)
  have 1: "\<Phi> ?A1A2BC - \<Phi> ?ABC = \<Phi> A1 + \<Phi> A2 + \<phi> ?A2BC + \<phi> ?BC - \<Phi> A - \<phi> ?AB"
    using 0 by (simp)
  have "A_splay x ?ABC = T_splay x A + 1 + \<Phi> ?A1A2BC - \<Phi> ?ABC"
    using "6.hyps" sp by(simp add: A_splay_def)
  also have "\<dots> = T_splay x A + 1 + \<Phi> A1 + \<Phi> A2 + \<phi> ?A2BC + \<phi> ?BC - \<Phi> A - \<phi> ?AB"
    using 1 by simp
  also have "\<dots> = T_splay x A + \<Phi> ?A' - \<phi> ?A' - \<Phi> A + \<phi> ?A2BC + \<phi> ?BC - \<phi> ?AB + 1"
    by(simp)
  also have "\<dots> = A_splay x A + \<phi> ?A2BC + \<phi> ?BC - \<phi> ?AB - \<phi> ?A' + 1"
    using sp by(simp add: A_splay_def)
  also have "\<dots> \<le> 3 * \<phi> A + \<phi> ?A2BC + \<phi> ?BC - \<phi> ?AB - \<phi> ?A' - 3 * \<phi> ?X + 2"
    using "6.IH" "6.prems"(1) * by(simp)
  also have "\<dots> = 2 * \<phi> A + \<phi> ?A2BC + \<phi> ?BC - \<phi> ?AB - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> < \<phi> A + \<phi> ?A2BC + \<phi> ?BC - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> < \<phi> ?A2BC + 2 * \<phi> ?ABC - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 A" "size1 ?BC"]
    by(simp add: size_if_splay)
  also have "\<dots> < 3 * \<phi> ?ABC - 3 * \<phi> ?X + 1"
    using sp by(simp add: size_if_splay)
  finally show ?case by simp
next
  case (8 a x b B A C)
  hence *: "\<langle>l, x, r\<rangle> \<in> subtrees B" by(fastforce dest: in_set_tree_if)
  obtain B1 b' B2 where sp: "splay x B = Node B1 b' B2"
     using splay_not_Leaf[OF \<open>B \<noteq> Leaf\<close>] by blast
  let ?X = "Node l x r" let ?AB = "Node A a B"  let ?ABC = "Node ?AB b C"
  let ?B' = "Node B1 b' B2"
  let ?AB1 = "Node A a B1"  let ?B2C = "Node B2 b C" let ?AB1B2C = "Node ?AB1 b' ?B2C"
  have 0: "\<phi> ?AB1B2C = \<phi> ?ABC" using sp by(simp add: size_if_splay)
  have 1: "\<Phi> ?AB1B2C - \<Phi> ?ABC = \<Phi> B1 + \<Phi> B2 + \<phi> ?AB1 + \<phi> ?B2C - \<Phi> B - \<phi> ?AB"
    using 0 by (simp)
  have "A_splay x ?ABC = T_splay x B + 1 + \<Phi> ?AB1B2C - \<Phi> ?ABC"
    using "8.hyps" sp by(simp add: A_splay_def)
  also have "\<dots> = T_splay x B + 1 + \<Phi> B1 + \<Phi> B2 + \<phi> ?AB1 + \<phi> ?B2C - \<Phi> B - \<phi> ?AB"
    using 1 by simp
  also have "\<dots> = T_splay x B + \<Phi> ?B' - \<phi> ?B' - \<Phi> B + \<phi> ?AB1 + \<phi> ?B2C - \<phi> ?AB + 1"
    by simp
  also have "\<dots> = A_splay x B + \<phi> ?AB1 + \<phi> ?B2C - \<phi> ?AB - \<phi> ?B' + 1"
    using sp by (simp add: A_splay_def)
  also have "\<dots> \<le> 3 * \<phi> B + \<phi> ?AB1 + \<phi> ?B2C - \<phi> ?AB - \<phi> ?B' - 3 * \<phi> ?X + 2"
    using "8.IH" "8.prems"(1) * by(simp)
  also have "\<dots> = 2 * \<phi> B + \<phi> ?AB1 + \<phi> ?B2C - \<phi> ?AB - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> < \<phi> B + \<phi> ?AB1 + \<phi> ?B2C - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> < \<phi> B + 2 * \<phi> ?ABC - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?AB1" "size1 ?B2C"]
    by(simp add: size_if_splay)
  also have "\<dots> < 3 * \<phi> ?ABC - 3 * \<phi> ?X + 1" by(simp)
  finally show ?case by simp
next
  case (11 b x c C A D)
  hence *: "\<langle>l, x, r\<rangle> \<in> subtrees C" by(fastforce dest: in_set_tree_if)
  obtain C1 c' C2 where sp: "splay x C = Node C1 c' C2"
    using splay_not_Leaf[OF \<open>C \<noteq> Leaf\<close>] by blast
  let ?X = "Node l x r" let ?CD = "Node C c D"  let ?ACD = "Node A b ?CD"
  let ?C' = "Node C1 c' C2"
  let ?C2D = "Node C2 c D"  let ?AC1 = "Node A b C1"
  have "A_splay x ?ACD = A_splay x C + \<phi> ?C2D + \<phi> ?AC1 - \<phi> ?CD - \<phi> ?C' + 1"
    using "11.hyps" sp
    by(auto simp: A_splay_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> C + \<phi> ?C2D + \<phi> ?AC1 - \<phi> ?CD - \<phi> ?C' - 3 * \<phi> ?X + 2"
    using "11.IH" "11.prems"(1) * by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> C + \<phi> ?C2D + \<phi> ?AC1 - \<phi> ?CD - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> C + \<phi> ?C2D + \<phi> ?AC1 - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> C + 2 * \<phi> ?ACD - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?C2D" "size1 ?AC1"]
    by(simp add: size_if_splay algebra_simps)
  also have "\<dots> \<le> 3 * \<phi> ?ACD - 3 * \<phi> ?X + 1" by(simp)
  finally show ?case by simp
next
  case (14 a x b CD A B)
  hence 0: "x \<notin> set_tree B \<and> x \<notin> set_tree A"
    using "14.prems"(1) \<open>b<x\<close> by(auto)
  hence 1: "x \<in> set_tree CD" using "14.prems" \<open>b<x\<close> \<open>a<x\<close> by (auto)
  obtain C c D where sp: "splay x CD = Node C c D"
    using splay_not_Leaf[OF \<open>CD \<noteq> Leaf\<close>] by blast
  from zig_zig[of CD x D C l r _ b B a A] 14 sp 0
  show ?case by(auto simp: A_splay_def size_if_splay algebra_simps)
(* The explicit version:
  have "A_splay x ?A = A_splay x ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' + 1"
    using "14.prems" 1 sp
    by(auto simp: A_splay_def size_if_splay algebra_simps split: tree.split)
  also have "\<dots> \<le> 3 * \<phi> ?R + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - \<phi> ?R' - 3 * \<phi> ?X + 2"
    using 14 0 by(auto simp: algebra_simps)
  also have "\<dots> = 2 * \<phi> rb + \<phi> ?B' + \<phi> ?A' - \<phi> ?B - 3 * \<phi> ?X + 2"
    using sp by(simp add: size_if_splay)
  also have "\<dots> \<le> \<phi> ?R + \<phi> ?B' + \<phi> ?A' - 3 * \<phi> ?X + 2" by(simp)
  also have "\<dots> \<le> \<phi> ?B' + 2 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp ld_ld_1_less[of "size1 ?R" "size1 ?A'"]
    by(simp add: size_if_splay algebra_simps)
  also have "\<dots> \<le> 3 * \<phi> ?A - 3 * \<phi> ?X + 1"
    using sp by(simp add: size_if_splay)
  finally show ?case by simp
*)
qed

lemma A_splay_ub2: assumes "bst t" "x : set_tree t"
shows "A_splay x t \<le> 3 * (\<phi> t - 1) + 1"
proof -
  from assms(2) obtain l r where N: "Node l x r : subtrees t"
    by (metis set_treeE)
  have "A_splay x t \<le> 3 * (\<phi> t - \<phi>(Node l x r)) + 1" by(rule A_splay_ub[OF assms(1) N])
  also have "\<dots> \<le> 3 * (\<phi> t - 1) + 1" by(simp add: field_simps)
  finally show ?thesis .
qed

lemma A_splay_ub3: assumes "bst t" shows "A_splay x t \<le> 3 * \<phi> t + 1"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: A_splay_def)
next
  assume "t \<noteq> Leaf"
  from ex_in_set_tree[OF this assms] obtain x' where
    a': "x' \<in> set_tree t"  "splay x' t = splay x t"  "T_splay x' t = T_splay x t"
    by blast
  show ?thesis using A_splay_ub2[OF assms a'(1)] by(simp add: A_splay_def a')
qed


subsubsection "Analysis of insert"

lemma amor_insert: assumes "bst t"
shows "T_insert x t + \<Phi>(Splay_Tree.insert x t) - \<Phi> t \<le> 4 * log 2 (size1 t) + 3" (is "?l \<le> ?r")
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: T_insert_def)
next
  assume "t \<noteq> Leaf"
  then obtain l e r where [simp]: "splay x t = Node l e r"
    by (metis tree.exhaust splay_Leaf_iff)
  let ?t = "real(T_splay x t)"
  let ?Plr = "\<Phi> l + \<Phi> r"  let ?Ps = "\<Phi> t"
  let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
  have opt: "?t + \<Phi> (splay x t) - ?Ps  \<le> 3 * log 2 (real (size1 t)) + 1"
    using A_splay_ub3[OF \<open>bst t\<close>, simplified A_splay_def, of x] by (simp)
  from less_linear[of e x]
  show ?thesis
  proof (elim disjE)
    assume "e=x"
    have nneg: "log 2 (1 + real (size t)) \<ge> 0" by simp
    thus ?thesis using \<open>t \<noteq> Leaf\<close> opt \<open>e=x\<close>
      apply(simp add: T_insert_def algebra_simps) using nneg by arith
  next
    let ?L = "log 2 (real(size1 l) + 1)"
    assume "e < x" hence "e \<noteq> x" by simp
    hence "?l = (?t + ?Plr - ?Ps) + ?L + ?LR + 1"
      using  \<open>t \<noteq> Leaf\<close> \<open>e<x\<close> by(simp add: T_insert_def)
    also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr + 1"
      using opt size_splay[of x t,symmetric] by(simp)
    also have "?L \<le> log 2 ?slr" by(simp)
    also have "?LR \<le> log 2 ?slr + 1"
    proof -
      have "?LR \<le> log 2 (2 * ?slr)" by (simp add:)
      also have "\<dots> \<le> log 2 ?slr + 1"
        by (simp add: log_mult del:distrib_left_numeral)
      finally show ?thesis .
    qed
    finally show ?thesis using size_splay[of x t,symmetric] by (simp)
  next
    let ?R = "log 2 (2 + real(size r))"
    assume "x < e" hence "e \<noteq> x" by simp
    hence "?l = (?t + ?Plr - ?Ps) + ?R + ?LR + 1"
      using \<open>t \<noteq> Leaf\<close> \<open>x < e\<close> by(simp add: T_insert_def)
    also have "?t + ?Plr - ?Ps \<le> 2 * log 2 ?slr + 1"
      using opt size_splay[of x t,symmetric] by(simp)
    also have "?R \<le> log 2 ?slr" by(simp)
    also have "?LR \<le> log 2 ?slr + 1"
    proof -
      have "?LR \<le> log 2 (2 * ?slr)" by (simp add:)
      also have "\<dots> \<le> log 2 ?slr + 1"
        by (simp add: log_mult del:distrib_left_numeral)
      finally show ?thesis .
    qed
    finally show ?thesis using size_splay[of x t, symmetric] by simp
  qed
qed


subsubsection "Analysis of delete"

definition A_splay_max :: "'a::linorder tree \<Rightarrow> real" where
"A_splay_max t = T_splay_max t + \<Phi>(splay_max t) - \<Phi> t"

lemma A_splay_max_ub: "t \<noteq> Leaf \<Longrightarrow> A_splay_max t \<le> 3 * (\<phi> t - 1) + 1"
proof(induction t rule: splay_max.induct)
  case 1 thus ?case by (simp)
next
  case (2 A)
  thus ?case using one_le_log_cancel_iff[of 2 "size1 A + 1"]
    by (simp add: A_splay_max_def del: one_le_log_cancel_iff)
next
  case (3 l b rl c rr)
  show ?case
  proof cases
    assume "rr = Leaf"
    thus ?thesis
      using one_le_log_cancel_iff[of 2 "1 + size1 rl"]
        one_le_log_cancel_iff[of 2 "1 + size1 l + size1 rl"]
        log_le_cancel_iff[of 2 "size1 l + size1 rl" "1 + size1 l + size1 rl"]
     by (auto simp: A_splay_max_def field_simps
           simp del: log_le_cancel_iff one_le_log_cancel_iff)
  next
    assume "rr \<noteq> Leaf"
    then obtain l' u r' where sp: "splay_max rr = Node l' u r'"
      using splay_max_Leaf_iff tree.exhaust by blast
    hence 1: "size rr = size l' + size r' + 1"
      using size_splay_max[of rr,symmetric] by(simp)
    let ?C = "Node rl c rr"  let ?B = "Node l b ?C"
    let ?B' = "Node l b rl"  let ?C' = "Node ?B' c l'"
    have "A_splay_max ?B = A_splay_max rr + \<phi> ?B' + \<phi> ?C' - \<phi> rr - \<phi> ?C + 1" using "3.prems" sp 1
      by(auto simp add: A_splay_max_def)
    also have "\<dots> \<le> 3 * (\<phi> rr - 1) + \<phi> ?B' + \<phi> ?C' - \<phi> rr - \<phi> ?C + 2"
      using 3 \<open>rr \<noteq> Leaf\<close> by auto
    also have "\<dots> = 2 * \<phi> rr + \<phi> ?B' + \<phi> ?C' - \<phi> ?C - 1" by simp
    also have "\<dots> \<le> \<phi> rr + \<phi> ?B' + \<phi> ?C' - 1" by simp
    also have "\<dots> \<le> 2 * \<phi> ?B + \<phi> ?C' - 2"
      using ld_ld_1_less[of "size1 ?B'" "size1 rr"] by(simp add:)
    also have "\<dots> \<le> 3 * \<phi> ?B - 2" using 1 by simp
    finally show ?case by simp
  qed
qed

lemma A_splay_max_ub3: "A_splay_max t \<le> 3 * \<phi> t + 1"
proof cases
  assume "t = Leaf" thus ?thesis by(simp add: A_splay_max_def)
next
  assume "t \<noteq> Leaf"
  show ?thesis using A_splay_max_ub[OF \<open>t \<noteq> Leaf\<close>] by(simp)
qed

lemma amor_delete: assumes "bst t"
shows "T_delete a t + \<Phi>(Splay_Tree.delete a t) - \<Phi> t \<le> 6 * log 2 (size1 t) + 3"
proof (cases t)
  case Leaf thus ?thesis by(simp add: Splay_Tree.delete_def T_delete_def)
next
  case [simp]: (Node ls x rs)
  then obtain l e r where sp[simp]: "splay a (Node ls x rs) = Node l e r"
    by (metis tree.exhaust splay_Leaf_iff)
  let ?t = "real(T_splay a t)"
  let ?Plr = "\<Phi> l + \<Phi> r"  let ?Ps = "\<Phi> t"
  let ?slr = "real(size1 l) + real(size1 r)" let ?LR = "log 2 (1 + ?slr)"
  let ?lslr = "log 2 (real (size ls) + (real (size rs) + 2))"
  have "?lslr \<ge> 0" by simp
  have opt: "?t + \<Phi> (splay a t) - ?Ps  \<le> 3 * log 2 (real (size1 t)) + 1"
    using A_splay_ub3[OF \<open>bst t\<close>, simplified A_splay_def, of a]
    by (simp add: field_simps)
  show ?thesis
  proof (cases "e=a")
    case False thus ?thesis
      using opt apply(simp add: Splay_Tree.delete_def T_delete_def field_simps)
      using \<open>?lslr \<ge> 0\<close> by arith
  next
    case [simp]: True
    show ?thesis
    proof (cases l)
      case Leaf
      have 1: "log 2 (real (size r) + 2) \<ge> 0" by(simp)
      show ?thesis
        using Leaf opt apply(simp add: Splay_Tree.delete_def T_delete_def field_simps)
        using 1 \<open>?lslr \<ge> 0\<close> by arith
    next
      case (Node ll y lr)
      then obtain l' y' r' where [simp]: "splay_max (Node ll y lr) = Node l' y' r'"
      using splay_max_Leaf_iff tree.exhaust by blast
      have "bst l" using bst_splay[OF \<open>bst t\<close>, of a] by simp
      have "\<Phi> r' \<ge> 0" apply (induction r') by (auto)
      have optm: "real(T_splay_max l) + \<Phi> (splay_max l) - \<Phi> l  \<le> 3 * \<phi> l + 1"
        using A_splay_max_ub3[of l, simplified A_splay_max_def] by (simp add: field_simps Node)
      have 1: "log 2 (2+(real(size l')+real(size r))) \<le> log 2 (2+(real(size l)+real(size r)))"
        using size_splay_max[of l] Node by simp
      have 2: "log 2 (2 + (real (size l') + real (size r'))) \<ge> 0" by simp
      have 3: "log 2 (size1 l' + size1 r) \<le> log 2 (size1 l' + size1 r') + log 2 ?slr"
        apply simp using 1 2 by arith
      have 4: "log 2 (real(size ll) + (real(size lr) + 2)) \<le> ?lslr"
        using size_if_splay[OF sp] Node by simp
      show ?thesis using add_mono[OF opt optm] Node 3
        apply(simp add: Splay_Tree.delete_def T_delete_def field_simps)
        using 4 \<open>\<Phi> r' \<ge> 0\<close> by arith
    qed
  qed
qed


subsubsection "Overall analysis"

fun U where
"U Empty [] = 1" |
"U (Splay _) [t] = 3 * log 2 (size1 t) + 1" |
"U (Insert _) [t] = 4 * log 2 (size1 t) + 3" |
"U (Delete _) [t] = 6 * log 2 (size1 t) + 3"

interpretation Amortized
where arity = arity and exec = exec and inv = bst
and cost = cost and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case (1 ss f) show ?case
  proof (cases f)
    case Empty thus ?thesis using 1 by auto
  next
    case (Splay a)
    then obtain t where "ss = [t]" "bst t" using 1 by auto
    with Splay bst_splay[OF \<open>bst t\<close>, of a] show ?thesis
      by (auto split: tree.split)
  next
    case (Insert a)
    then obtain t where "ss = [t]" "bst t" using 1 by auto
    with bst_splay[OF \<open>bst t\<close>, of a] Insert show ?thesis
      by (auto simp: splay_bstL[OF \<open>bst t\<close>] splay_bstR[OF \<open>bst t\<close>] split: tree.split)
  next
    case (Delete a)
    then obtain t where "ss = [t]" "bst t" using 1 by auto
    with 1 Delete show ?thesis by(simp add: bst_delete)
  qed
next
  case (2 t) thus ?case by (induction t) auto
next
  case (3 ss f)
  show ?case (is "?l \<le> ?r")
  proof(cases f)
    case Empty thus ?thesis using 3(2) by(simp add: A_splay_def)
  next
    case (Splay a)
    then obtain t where "ss = [t]" "bst t" using 3 by auto
    thus ?thesis using Splay A_splay_ub3[OF \<open>bst t\<close>] by(simp add: A_splay_def)
  next
    case [simp]: (Insert a)
    then obtain t where [simp]: "ss = [t]" and "bst t" using 3 by auto
    thus ?thesis using amor_insert[of t a] by auto
  next
    case [simp]: (Delete a)
    then obtain t where [simp]: "ss = [t]" and "bst t" using 3 by auto
    thus ?thesis using amor_delete[of t a] by auto
  qed
qed

end
