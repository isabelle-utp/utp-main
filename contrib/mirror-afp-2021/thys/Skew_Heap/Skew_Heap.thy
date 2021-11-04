section "Skew Heap"

theory Skew_Heap
imports
  "HOL-Library.Tree_Multiset"
  "HOL-Library.Pattern_Aliases"
  "HOL-Data_Structures.Heaps"
begin

unbundle pattern_aliases

text\<open>Skew heaps~\cite{SleatorT-SIAM86} are possibly the simplest functional
priority queues that have logarithmic (albeit amortized) complexity.

The implementation below could be generalized to separate the elements from
their priorities.\<close>

subsection "Merge"

function merge :: "('a::linorder) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"merge Leaf t = t" |
"merge t Leaf = t" |
"merge (Node l1 a1 r1 =: t1) (Node l2 a2 r2 =: t2) =
   (if a1 \<le> a2 then Node (merge t2 r1) a1 l1
    else Node (merge t1 r2) a2 l2)" 
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma merge_code: "merge t1 t2 =
  (case t1 of
   Leaf \<Rightarrow> t2 |
   Node l1 a1 r1 \<Rightarrow> (case t2 of
     Leaf \<Rightarrow> t1 |
     Node l2 a2 r2 \<Rightarrow> 
       (if a1 \<le> a2
        then Node (merge t2 r1) a1 l1
        else Node (merge t1 r2) a2 l2)))"
by(auto split: tree.split)

text\<open>An alternative version that always walks to the Leaf of both heaps:\<close>
function merge2 :: "('a::linorder) tree \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"merge2 Leaf Leaf = Leaf" |
"merge2 Leaf (Node l2 a2 r2) = Node (merge2 r2 Leaf) a2 l2" |
"merge2 (Node l1 a1 r1) Leaf = Node (merge2 r1 Leaf) a1 l1" |
"merge2 (Node l1 a1 r1) (Node l2 a2 r2) =
   (if a1 \<le> a2
    then Node (merge2 (Node l2 a2 r2) r1) a1 l1
    else Node (merge2 (Node l1 a1 r1) r2) a2 l2)"
by pat_completeness auto
termination
by (relation "measure (\<lambda>(x, y). size x + size y)") auto

lemma size_merge: "size(merge t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: merge.induct) auto

lemma size_merge2: "size(merge2 t1 t2) = size t1 + size t2"
by(induction t1 t2 rule: merge2.induct) auto

lemma mset_merge: "mset_tree (merge t1 t2) = mset_tree t1 + mset_tree t2"
by (induction t1 t2 rule: merge.induct) (auto simp add: ac_simps)

lemma set_merge: "set_tree (merge t1 t2) = set_tree t1 \<union> set_tree t2"
by (metis mset_merge set_mset_tree set_mset_union)

lemma heap_merge:
  "\<lbrakk> heap t1;  heap t2 \<rbrakk> \<Longrightarrow> heap (merge t1 t2)"
by (induction t1 t2 rule: merge.induct)(auto simp: ball_Un set_merge)

interpretation skew_heap: Heap_Merge
where merge = merge
proof(standard, goal_cases)
  case 1 thus ?case by(simp add: mset_merge)
next
  case 2 thus ?case by(simp add: heap_merge)
qed


end
