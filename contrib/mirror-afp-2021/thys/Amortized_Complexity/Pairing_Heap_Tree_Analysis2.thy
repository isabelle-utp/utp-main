(* Author: Hauke Brinkop and Tobias Nipkow *)

section \<open>Pairing Heaps\<close>

subsection \<open>Binary Tree Representation\<close>

theory Pairing_Heap_Tree_Analysis2
imports  
  Pairing_Heap.Pairing_Heap_Tree
  Amortized_Framework
  Priority_Queue_ops_merge
  Lemmas_log
begin

text
\<open>Verification of logarithmic bounds on the amortized complexity of pairing heaps.
As in \cite{FredmanSST86,Brinkop}, except that the treatment of @{const pass\<^sub>1} is simplified.
TODO: convert the other Pairing Heap analyses to this one.\<close>

fun len :: "'a tree \<Rightarrow> nat" where 
  "len Leaf = 0"
| "len (Node _ _ r) = 1 + len r"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
  "\<Phi> Leaf = 0"
| "\<Phi> (Node l x r) = log 2 (size (Node l x r)) + \<Phi> l + \<Phi> r"

lemma link_size[simp]: "size (link hp) = size hp" 
  by (cases hp rule: link.cases) simp_all

lemma size_pass\<^sub>1: "size (pass\<^sub>1 hp) = size hp" 
  by (induct hp rule: pass\<^sub>1.induct) simp_all

lemma size_pass\<^sub>2: "size (pass\<^sub>2 hp) = size hp" 
  by (induct hp rule: pass\<^sub>2.induct) simp_all

lemma size_merge: 
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> size (merge h1 h2) = size h1 + size h2"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>_insert: "is_root hp \<Longrightarrow> \<Phi> (insert x hp) - \<Phi> hp \<le> log 2  (size hp + 1)"
  by (simp split: tree.splits)

lemma \<Delta>\<Phi>_merge:
  assumes "h1 = Node hs1 x1 Leaf" "h2 = Node hs2 x2 Leaf" 
  shows "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (size h1 + size h2) + 1" 
proof -
  let ?hs = "Node hs1 x1 (Node hs2 x2 Leaf)"
  have "\<Phi> (merge h1 h2) = \<Phi> (link ?hs)" using assms by simp
  also have "\<dots> = \<Phi> hs1 + \<Phi> hs2 + log 2 (size hs1 + size hs2 + 1) + log 2 (size hs1 + size hs2 + 2)"
    by (simp add: algebra_simps)
  also have "\<dots> = \<Phi> hs1 + \<Phi> hs2 + log 2 (size hs1 + size hs2 + 1) + log 2 (size h1 + size h2)"
     using assms by simp
  finally have "\<Phi> (merge h1 h2) = \<dots>" .
  have "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 =
   log 2 (size hs1 + size hs2 + 1) + log 2 (size h1 + size h2)
   - log 2 (size hs1 + 1) - log 2 (size hs2 + 1)"
     using assms by (simp add: algebra_simps)
  also have "\<dots> \<le> log 2 (size h1 + size h2) + 1"
    using ld_le_2ld[of "size hs1" "size hs2"] assms by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma \<Delta>\<Phi>_pass1: "\<Phi> (pass\<^sub>1 hs) - \<Phi> hs  \<le> 2 * log 2 (size hs + 1) - len hs + 2"
proof (induction hs rule: pass\<^sub>1.induct)
  case (1 hs1 x hs2 y hs)
  let ?h = "Node hs1 x (Node hs2 y hs)"
  let ?n1 = "size hs1"
  let ?n2 = "size hs2" let ?m = "size hs"
  have "\<Phi> (pass\<^sub>1 ?h) - \<Phi> ?h = \<Phi> (pass\<^sub>1 hs) + log 2 (?n1+?n2+1) - \<Phi> hs - log 2 (?n2+?m+1)" 
    by (simp add: size_pass\<^sub>1 algebra_simps)
  also have "\<dots> \<le> log 2 (?n1+?n2+1) - log 2 (?n2+?m+1) + 2 * log 2 (?m + 1) - len hs + 2" 
    using "1.IH" by (simp)
  also have "\<dots> \<le> 2 * log 2 (?n1+?n2+?m+2) - log 2 (?n2+?m+1) + log 2 (?m + 1) - len hs" 
        using ld_sum_inequality [of "?n1+?n2+1" "?m + 1"] by(simp)
  also have "\<dots> \<le> 2 * log 2 (?n1+?n2+?m+2) - len hs" by simp
  also have "\<dots> = 2 * log 2 (size ?h) - len ?h + 2" by simp
  also have "\<dots> \<le> 2 * log 2 (size ?h + 1) - len ?h + 2" by simp
  finally show ?case .
qed simp_all

lemma \<Delta>\<Phi>_pass2: "hs \<noteq> Leaf \<Longrightarrow> \<Phi> (pass\<^sub>2 hs) - \<Phi> hs \<le> log 2 (size hs)"
proof (induction hs)
  case (Node hs1 x hs)
  thus ?case 
  proof (cases hs)
    case 1: (Node hs2 y r)
    let ?h = "Node hs1 x hs"
    obtain hs3 a where 2: "pass\<^sub>2 hs = Node hs3 a Leaf" 
      using pass\<^sub>2_struct 1 by force
    hence 3: "size hs = size \<dots>" using size_pass\<^sub>2 by metis
    have link: "\<Phi>(link(Node hs1 x (pass\<^sub>2 hs))) - \<Phi> hs1 - \<Phi> (pass\<^sub>2 hs) =
          log 2 (size hs1 + size hs + 1) + log 2 (size hs1 + size hs) - log 2 (size hs)"
      using 2 3 by (simp add: algebra_simps)
    have "\<Phi> (pass\<^sub>2 ?h) - \<Phi> ?h =
        \<Phi> (link (Node hs1 x (pass\<^sub>2 hs))) - \<Phi> hs1 - \<Phi> hs - log 2 (size hs1 + size hs + 1)"
      by (simp)
    also have "\<dots> = \<Phi> (pass\<^sub>2 hs) - \<Phi> hs + log 2 (size hs1 + size hs) - log 2 (size hs)"
      using link by linarith
    also have "\<dots> \<le> log 2 (size hs1 + size hs)"
      using Node.IH(2) 1 by simp
    also have "\<dots> \<le> log 2 (size ?h)" using 1 by simp
    finally show ?thesis .
  qed simp
qed simp

corollary \<Delta>\<Phi>_pass2': "\<Phi> (pass\<^sub>2 hs) - \<Phi> hs \<le> log 2 (size hs + 1)"
proof cases
  assume "hs = Leaf" thus ?thesis by simp
next
  assume "hs \<noteq> Leaf"
  hence "log 2 (size hs) \<le> log 2 (size hs + 1)" using eq_size_0 by fastforce
  then show ?thesis using \<Delta>\<Phi>_pass2[OF \<open>hs \<noteq> Leaf\<close>] by linarith
qed

lemma \<Delta>\<Phi>_del_min:
  "\<Phi> (del_min (Node hs x Leaf)) - \<Phi> (Node hs x Leaf) 
  \<le> 2 * log 2 (size hs + 1) - len hs + 2"
proof -
  have "\<Phi> (del_min (Node hs x Leaf)) - \<Phi> (Node hs x Leaf) =
        \<Phi> (pass\<^sub>2 (pass\<^sub>1 hs)) - (log 2 (1 + real (size hs)) + \<Phi> hs)" by simp
  also have "\<dots> \<le> \<Phi> (pass\<^sub>1 hs) - \<Phi> hs"
    using \<Delta>\<Phi>_pass2' [of "pass\<^sub>1 hs"] by(simp add: size_pass\<^sub>1)
  also have "\<dots> \<le> 2 * log 2 (size hs + 1) - len hs + 2" by(rule \<Delta>\<Phi>_pass1)
  finally show ?thesis .
qed

lemma is_root_merge:
  "is_root h1 \<Longrightarrow> is_root h2 \<Longrightarrow> is_root (merge h1 h2)"
by (simp split: tree.splits)

lemma is_root_insert: "is_root h \<Longrightarrow> is_root (insert x h)"
by (simp split: tree.splits)

lemma is_root_del_min:
  assumes "is_root h" shows "is_root (del_min h)"
proof (cases h)
  case [simp]: (Node hs1 x hs)
  have "hs = Leaf" using assms by simp
  thus ?thesis 
  proof (cases hs1)
    case (Node hs2 y hs')
    then obtain la a ra where "pass\<^sub>1 hs1 = Node a la ra" 
      using pass\<^sub>1_struct by blast
    moreover obtain lb b where "pass\<^sub>2 \<dots> = Node b lb Leaf"
      using pass\<^sub>2_struct by blast
    ultimately show ?thesis using assms by simp
  qed simp
qed simp

lemma pass\<^sub>1_len: "len (pass\<^sub>1 h) \<le> len h"
by (induct h rule: pass\<^sub>1.induct) simp_all

fun exec :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> 'a tree" where
"exec Empty [] = Leaf" | 
"exec Del_min [h] = del_min h" |
"exec (Insert x) [h] = insert x h" |
"exec Merge [h1,h2] = merge h1 h2"

fun T_pass\<^sub>1 :: "'a tree \<Rightarrow> nat" where
"T_pass\<^sub>1 (Node _ _ (Node _ _ hs')) = T_pass\<^sub>1 hs' + 1" |
"T_pass\<^sub>1 h = 1"

fun T_pass\<^sub>2 :: "'a tree \<Rightarrow> nat" where
  "T_pass\<^sub>2 Leaf = 1"
| "T_pass\<^sub>2 (Node _ _ hs) = T_pass\<^sub>2 hs + 1"

fun T_del_min :: "('a::linorder) tree \<Rightarrow> nat" where
"T_del_min Leaf = 1" |
"T_del_min (Node hs _ _) = T_pass\<^sub>2 (pass\<^sub>1 hs) + T_pass\<^sub>1 hs + 1"

fun T_insert :: "'a \<Rightarrow> 'a tree \<Rightarrow> nat" where
"T_insert a h = 1"

fun T_merge :: "'a tree \<Rightarrow> 'a tree \<Rightarrow> nat" where
"T_merge h1 h2 = 1"

lemma A_del_min: assumes "is_root h"
shows "T_del_min h + \<Phi>(del_min h) - \<Phi> h \<le> 2 * log 2 (size h + 1) + 5"
proof (cases h)
  case [simp]: (Node hs1 x hs)
  have "T_pass\<^sub>2 (pass\<^sub>1 hs1) + real(T_pass\<^sub>1 hs1) \<le> real(len hs1) + 2"
    by (induct hs1 rule: pass\<^sub>1.induct) simp_all
  moreover have "\<Phi> (del_min h) - \<Phi> h \<le> 2 * log 2 (size h + 1) - len hs1 + 2"
  proof -
    have "\<Phi> (del_min h) - \<Phi> h \<le> 2 * log 2 (size hs1 + 1) - len hs1 + 2"
      using  \<Delta>\<Phi>_del_min[of "hs1" "x"] assms by simp
    also have "\<dots> \<le> 2 * log 2 (size h + 1) - len hs1 + 2" by fastforce
    finally show ?thesis .
  qed
  ultimately show ?thesis by(simp)
qed simp

lemma A_insert: "is_root h \<Longrightarrow> T_insert a h + \<Phi>(insert a h) - \<Phi> h \<le> log 2 (size h + 1) + 1"
by(drule \<Delta>\<Phi>_insert) simp

lemma A_merge: assumes "is_root h1" "is_root h2"
shows "T_merge h1 h2 + \<Phi>(merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (size h1 + size h2 + 1) + 2"
proof (cases h1)
  case Leaf thus ?thesis by (cases h2) auto
next
  case h1: Node
  show ?thesis
  proof (cases h2)
    case Leaf thus ?thesis using h1 by simp
  next
    case h2: Node
    have "\<Phi> (merge h1 h2) - \<Phi> h1 - \<Phi> h2 \<le> log 2 (real (size h1 + size h2)) + 1"
      apply(rule \<Delta>\<Phi>_merge) using h1 h2 assms by auto
    also have "\<dots> \<le> log 2 (size h1 + size h2 + 1) + 1" by (simp add: h1)
    finally show ?thesis by(simp add: algebra_simps)
  qed
qed

fun cost :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> nat" where
  "cost Empty [] = 1"
| "cost Del_min [h] = T_del_min h"
| "cost (Insert a) [h] = T_insert a h"
| "cost Merge [h1,h2] = T_merge h1 h2"

fun U :: "'a :: linorder op \<Rightarrow> 'a tree list \<Rightarrow> real" where
  "U Empty [] = 1"
| "U (Insert a) [h] = log 2 (size h + 1) + 1"
| "U Del_min [h] = 2 * log 2 (size h + 1) + 5"
| "U Merge [h1,h2] = log 2 (size h1 + size h2 + 1) + 2"

interpretation Amortized
where arity = arity and exec = exec and cost = cost and inv = is_root 
and \<Phi> = \<Phi> and U = U
proof (standard, goal_cases)
  case (1 _ f) thus ?case using is_root_insert is_root_del_min is_root_merge
    by (cases f) (auto simp: numeral_eq_Suc)
next
  case (2 s) show ?case by (induct s) simp_all
next
  case (3 ss f) show ?case 
  proof (cases f)
    case Empty with 3 show ?thesis by(auto)
  next
    case Insert
    then obtain h where "ss = [h]" "is_root h" using 3 by auto
    thus ?thesis using Insert \<Delta>\<Phi>_insert 3 by auto
  next
    case Del_min
    then obtain h where [simp]: "ss = [h]" using 3 by auto
    show ?thesis using A_del_min[of h] 3 Del_min by simp
  next
    case Merge
    then obtain h1 h2 where "ss = [h1,h2]" "is_root h1" "is_root h2"
      using 3 by (auto simp: numeral_eq_Suc)
    with A_merge[of h1 h2] Merge show ?thesis by simp
  qed
qed

end
