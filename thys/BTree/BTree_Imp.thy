theory BTree_Imp
  imports
    BTree
    Partially_Filled_Array
    Basic_Assn
begin

section "Imperative B-tree Definition"

text "The heap data type definition. Anything stored on the heap always contains data,
leafs are represented as None."

datatype 'a btnode =
  Btnode "('a btnode ref option*'a) pfarray" "'a btnode ref option"

text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option*'a) pfarray" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec last :: "'a::heap btnode \<Rightarrow> 'a btnode ref option" where
  [sep_dflt_simps]: "last (Btnode _ t) = t"

term arrays_update

text \<open>Encoding to natural numbers, as required by Imperative/HOL\<close>
  (* Note: should also work using the package "Deriving" *)
fun
  btnode_encode :: "'a::heap btnode \<Rightarrow> nat"
  where
    "btnode_encode (Btnode ts t) = to_nat (ts, t)"

instance btnode :: (heap) heap
  apply (rule heap_class.intro)
   apply (rule countable_classI [of "btnode_encode"])
   apply (metis btnode_encode.elims from_nat_to_nat fst_conv snd_conv)
  ..

text "The refinement relationship to abstract B-trees."

fun btree_assn :: "nat \<Rightarrow> 'a::heap btree \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "btree_assn k Leaf None = emp" |
  "btree_assn k (Node ts t) (Some a) = 
 (\<exists>\<^sub>A tsi ti tsi'.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * btree_assn k t ti
    * is_pfa (2*k) tsi' tsi
    * list_assn ((btree_assn k) \<times>\<^sub>a id_assn) ts tsi'
    )" |
  "btree_assn _ _ _ = false"

text "With the current definition of deletion, we would
also need to directly reason on nodes and not only on references
to them."

fun btnode_assn :: "nat \<Rightarrow> 'a::heap btree \<Rightarrow> 'a btnode \<Rightarrow> assn" where
  "btnode_assn k (Node ts t) (Btnode tsi ti) = 
 (\<exists>\<^sub>A tsi'.
      btree_assn k t ti
    * is_pfa (2*k) tsi' tsi
    * list_assn ((btree_assn k) \<times>\<^sub>a id_assn) ts tsi'
    )" |
  "btnode_assn _ _ _ = false"

abbreviation "blist_assn k \<equiv> list_assn ((btree_assn k) \<times>\<^sub>a id_assn)"

end