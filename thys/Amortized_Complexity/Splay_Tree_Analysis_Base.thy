section "Splay Tree"

subsection "Basics"

theory Splay_Tree_Analysis_Base
imports
  Lemmas_log
  Splay_Tree.Splay_Tree
begin

declare size1_size[simp]

abbreviation "\<phi> t == log 2 (size1 t)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l a r) = \<phi> (Node l a r) + \<Phi> l + \<Phi> r"

fun T_splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"T_splay x Leaf = 1" |
"T_splay x (Node AB b CD) =
  (case cmp x b of
   EQ \<Rightarrow> 1 |
   LT \<Rightarrow> (case AB of
          Leaf \<Rightarrow> 1 |
          Node A a B \<Rightarrow>
            (case cmp x a of EQ \<Rightarrow> 1 |
             LT \<Rightarrow> if A = Leaf then 1 else T_splay x A + 1 |
             GT \<Rightarrow> if B = Leaf then 1 else T_splay x B + 1)) |
   GT \<Rightarrow> (case CD of
          Leaf \<Rightarrow> 1 |
          Node C c D \<Rightarrow>
            (case cmp x c of EQ \<Rightarrow> 1 |
             LT \<Rightarrow> if C = Leaf then 1 else T_splay x C + 1 |
             GT \<Rightarrow> if D = Leaf then 1 else T_splay x D + 1)))"

lemma T_splay_simps[simp]:
  "T_splay a (Node l a r) = 1"
  "x<b \<Longrightarrow> T_splay x (Node Leaf b CD) = 1"
  "a<b \<Longrightarrow> T_splay a (Node (Node A a B) b CD) = 1"
  "x<a \<Longrightarrow> x<b \<Longrightarrow> T_splay x (Node (Node A a B) b CD) =
   (if A = Leaf then 1 else T_splay x A + 1)"
  "x<b \<Longrightarrow> a<x \<Longrightarrow> T_splay x (Node (Node A a B) b CD) =
   (if B = Leaf then 1 else T_splay x B + 1)"
  "b<x \<Longrightarrow> T_splay x (Node AB b Leaf) = 1"
  "b<a \<Longrightarrow> T_splay a (Node AB b (Node C a D)) = 1"
  "b<x \<Longrightarrow> x<c \<Longrightarrow> T_splay x (Node AB b (Node C c D)) =
  (if C=Leaf then 1 else T_splay x C + 1)"
  "b<x \<Longrightarrow> c<x \<Longrightarrow> T_splay x (Node AB b (Node C c D)) =
  (if D=Leaf then 1 else T_splay x D + 1)"
by auto

declare T_splay.simps(2)[simp del]

definition T_insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"T_insert x t = 1 + (if t = Leaf then 0 else T_splay x t)"

fun T_splay_max :: "'a::linorder tree \<Rightarrow> nat" where
"T_splay_max Leaf = 1" |
"T_splay_max (Node A a Leaf) = 1" |
"T_splay_max (Node A a (Node B b C)) = (if C=Leaf then 1 else T_splay_max C + 1)"

definition T_delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"T_delete x t =
  1 + (if t = Leaf then 0
   else T_splay x t +
     (case splay x t of
        Node l a r \<Rightarrow> if x \<noteq> a then 0 else if l = Leaf then 0 else T_splay_max l))"

lemma ex_in_set_tree: "t \<noteq> Leaf \<Longrightarrow> bst t \<Longrightarrow>
  \<exists>x' \<in> set_tree t. splay x' t = splay x t \<and> T_splay x' t = T_splay x t"
proof(induction x t rule: splay.induct)
  case (6 x b c A)
  hence "splay x A \<noteq> Leaf" by simp
  then obtain A1 u A2 where [simp]: "splay x A = Node A1 u A2"
    by (metis tree.exhaust)
  have "b < c" "bst A" using "6.prems" by auto
  from "6.IH"[OF \<open>A \<noteq> Leaf\<close> \<open>bst A\<close>]
  obtain x' where "x' \<in> set_tree A" "splay x' A = splay x A" "T_splay x' A = T_splay x A"
    by blast
  moreover hence "x'<b" using "6.prems"(2) by auto
  ultimately show ?case using \<open>x<c\<close> \<open>x<b\<close> \<open>b<c\<close> \<open>bst A\<close> by force
next
  case (8 a x c B)
  hence "splay x B \<noteq> Leaf" by simp
  then obtain B1 u B2 where [simp]: "splay x B = Node B1 u B2"
    by (metis tree.exhaust)
  have "a < c" "bst B" using "8.prems" by auto
  from "8.IH"[OF \<open>B \<noteq> Leaf\<close> \<open>bst B\<close>]
  obtain x' where "x' \<in> set_tree B" "splay x' B = splay x B" "T_splay x' B = T_splay x B"
    by blast
  moreover hence "a<x' & x'<c" using "8.prems"(2) by simp
  ultimately show ?case using \<open>x<c\<close> \<open>a<x\<close> \<open>a<c\<close> \<open>bst B\<close> by force
next
  case (11 b x c C)
  hence "splay x C \<noteq> Leaf" by simp
  then obtain C1 u C2 where [simp]: "splay x C = Node C1 u C2"
    by (metis tree.exhaust)
  have "b < c" "bst C" using "11.prems" by auto
  from "11.IH"[OF \<open>C \<noteq> Leaf\<close> \<open>bst C\<close>]
  obtain x' where "x' \<in> set_tree C" "splay x' C = splay x C" "T_splay x' C = T_splay x C"
    by blast
  moreover hence "b<x' & x'<c" using "11.prems" by simp
  ultimately show ?case using \<open>b<x\<close> \<open>x<c\<close> \<open>b<c\<close> \<open>bst C\<close> by force
next
  case (14 a x c D)
  hence "splay x D \<noteq> Leaf" by simp
  then obtain D1 u D2 where [simp]: "splay x D = Node D1 u D2"
    by (metis tree.exhaust)
  have "a < c" "bst D" using "14.prems" by auto
  from "14.IH"[OF \<open>D \<noteq> Leaf\<close> \<open>bst D\<close>]
  obtain x' where "x' \<in> set_tree D" "splay x' D = splay x D" "T_splay x' D = T_splay x D"
    by blast
  moreover hence "c<x'" using "14.prems"(2) by simp
  ultimately show ?case using \<open>a<x\<close> \<open>c<x\<close> \<open>a<c\<close> \<open>bst D\<close> by force
qed (auto simp: le_less)


datatype 'a op = Empty | Splay 'a | Insert 'a | Delete 'a

fun arity :: "'a::linorder op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity (Splay x) = 1" |
"arity (Insert x) = 1" |
"arity (Delete x) = 1"

fun exec :: "'a::linorder op \<Rightarrow> 'a tree list \<Rightarrow> 'a tree" where
"exec Empty [] = Leaf" |
"exec (Splay x) [t] = splay x t" |
"exec (Insert x) [t] = Splay_Tree.insert x t" |
"exec (Delete x) [t] = Splay_Tree.delete x t"

fun cost :: "'a::linorder op \<Rightarrow> 'a tree list \<Rightarrow> nat" where
"cost Empty [] = 1" |
"cost (Splay x) [t] = T_splay x t" |
"cost (Insert x) [t] = T_insert x t" |
"cost (Delete x) [t] = T_delete x t"

end
