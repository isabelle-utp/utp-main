theory Partially_Filled_Array
  imports
    "Refine_Imperative_HOL.IICF_Array_List"
    Array_SBlit
begin

section "Partially Filled Arrays"

text \<open>An array that is only partially filled.
The number of actual elements contained is kept in a second element.
This represents a weakened version of the array\_list from IICF.\<close>

type_synonym 'a pfarray = "'a array_list"


subsection "Operations on Partly Filled Arrays"


definition is_pfa where
  "is_pfa c l \<equiv> \<lambda>(a,n). \<exists>\<^sub>A l'. a \<mapsto>\<^sub>a l' *  \<up>(c = length l' \<and> n \<le> c \<and> l = (take n l'))"


lemma is_pfa_prec[safe_constraint_rules]: "precise (is_pfa c)"
  unfolding is_pfa_def[abs_def]
  apply(rule preciseI)
  apply(simp split: prod.splits) 
  using preciseD snga_prec by fastforce

definition pfa_init where
  "pfa_init cap v n \<equiv> do {
  a \<leftarrow> Array.new cap v;
  return (a,n)
}"

lemma pfa_init_rule[sep_heap_rules]: "n \<le> N \<Longrightarrow> < emp > pfa_init N x n <is_pfa N (replicate n x)>"
  by (sep_auto simp: pfa_init_def is_pfa_def)

definition pfa_empty where
  "pfa_empty cap \<equiv> pfa_init cap default 0"



lemma pfa_empty_rule[sep_heap_rules]: "< emp > pfa_empty N <is_pfa N []>"
  by (sep_auto simp: pfa_empty_def is_pfa_def)


definition "pfa_length \<equiv> arl_length"

lemma pfa_length_rule[sep_heap_rules]: "
  <is_pfa c l a> 
    pfa_length a
  <\<lambda>r. is_pfa c l a * \<up>(r=length l)>"
  by (sep_auto simp: pfa_length_def arl_length_def is_pfa_def)


definition "pfa_capacity \<equiv> \<lambda>(a,n). Array.len a
"


lemma pfa_capacity_rule[sep_heap_rules]: "
  <is_pfa c l a> 
    pfa_capacity a
  <\<lambda>r. is_pfa c l a * \<up>(c=r)>"
  by (sep_auto simp: pfa_capacity_def arl_length_def is_pfa_def)



definition "pfa_is_empty \<equiv> arl_is_empty"

lemma pfa_is_empty_rule[sep_heap_rules]: "
  <is_pfa c l a> 
    pfa_is_empty a
  <\<lambda>r. is_pfa c l a * \<up>(r\<longleftrightarrow>(l=[]))>"
  by (sep_auto simp: pfa_is_empty_def arl_is_empty_def is_pfa_def)



definition "pfa_append \<equiv> \<lambda>(a,n) x. do {
  Array.upd n x a;
  return (a,n+1)
}"

lemma pfa_append_rule[sep_heap_rules]: "
   n < c  \<Longrightarrow>
    < is_pfa c l (a,n) > 
      pfa_append (a,n) x 
    <\<lambda>(a',n'). is_pfa c (l@[x]) (a',n') * \<up>(a' = a \<and> n' = n+1) >"  
  by (sep_auto 
      simp: pfa_append_def arl_append_def is_pfa_def take_update_last neq_Nil_conv
      split: prod.splits nat.split)


definition "pfa_last \<equiv> arl_last"


lemma pfa_last_rule[sep_heap_rules]: "
  l\<noteq>[] \<Longrightarrow>
  <is_pfa c l a> 
    pfa_last a
  <\<lambda>r. is_pfa c l a * \<up>(r=last l)>"
  by (sep_auto simp: pfa_last_def arl_last_def is_pfa_def last_take_nth_conv)


definition pfa_butlast :: "'a::heap pfarray \<Rightarrow> 'a pfarray Heap" where
  "pfa_butlast \<equiv> \<lambda>(a,n).
    return (a,n-1)
  "


lemma pfa_butlast_rule[sep_heap_rules]: "
  <is_pfa c l (a,n)> 
    pfa_butlast (a,n)
  <\<lambda>(a',n'). is_pfa c (butlast l) (a',n') * \<up>(a' = a)>"
  by (sep_auto 
      split: prod.splits
      simp: pfa_butlast_def is_pfa_def butlast_take)  


definition "pfa_get \<equiv> arl_get"

lemma pfa_get_rule[sep_heap_rules]: "
  i < length l \<Longrightarrow>
  < is_pfa c l a> 
    pfa_get a i
  <\<lambda>r. is_pfa c l a * \<up>((l!i) = r)>"
  by (sep_auto simp: is_pfa_def pfa_get_def arl_get_def  split: prod.split)


definition "pfa_set \<equiv> arl_set"

lemma pfa_set_rule[sep_heap_rules]: "
    i<length l \<Longrightarrow>
    <is_pfa c l a> 
      pfa_set a i x
    <\<lambda>a'. is_pfa c (l[i:=x]) a' * \<up>(a' = a)>"
  by (sep_auto simp: pfa_set_def arl_set_def is_pfa_def split: prod.split)





definition pfa_shrink :: "nat \<Rightarrow> 'a::heap pfarray \<Rightarrow> 'a pfarray Heap" where
  "pfa_shrink k \<equiv> \<lambda>(a,n).
  return (a,k)
"


lemma pfa_shrink_rule[sep_heap_rules]: "
   k \<le> length l \<Longrightarrow>
    < is_pfa c l (a,n) > 
      pfa_shrink k (a,n)
    <\<lambda>(a',n'). is_pfa c (take k l) (a',n') * \<up>(n' = k \<and> a'=a) >"  
  by (sep_auto 
      simp: pfa_shrink_def is_pfa_def min.absorb1
      split: prod.splits nat.split)


definition pfa_shrink_cap :: "nat \<Rightarrow> 'a::heap pfarray \<Rightarrow> 'a pfarray Heap" where
  "pfa_shrink_cap k \<equiv> \<lambda>(a,n). do {
  a' \<leftarrow> array_shrink a k;
  return (a',min k n)
}
"

lemma pfa_shrink_cap_rule_preserve[sep_heap_rules]: "
   \<lbrakk>n \<le> k; k \<le> c\<rbrakk> \<Longrightarrow>
    < is_pfa c l (a,n) > 
      pfa_shrink_cap k (a,n)
    <\<lambda>a'. is_pfa k l a' >\<^sub>t"
  by (sep_auto 
      simp: pfa_shrink_cap_def is_pfa_def min.absorb1 min.absorb2
      split: prod.splits nat.split)



lemma pfa_shrink_cap_rule: "
   \<lbrakk>k \<le> c\<rbrakk> \<Longrightarrow>
    < is_pfa c l a > 
      pfa_shrink_cap k a
    <\<lambda>a'. is_pfa k (take k l) a' >\<^sub>t"  
  by (sep_auto 
      simp: pfa_shrink_cap_def is_pfa_def min.absorb1 min.absorb2
      split: prod.splits nat.split dest: mod_starD)


definition "array_ensure a s x \<equiv> do {
    l\<leftarrow>Array.len a;
    if l\<ge>s then 
      return a
    else do {
      a'\<leftarrow>Array.new s x;
      blit a 0 a' 0 l;
      return a'
    }
  }"

lemma array_ensure_rule[sep_heap_rules]:
  shows "
      < a\<mapsto>\<^sub>ala > 
        array_ensure a s x 
      <\<lambda>a'. a'\<mapsto>\<^sub>a (la @ replicate (s-length la) x)>\<^sub>t"
  unfolding array_ensure_def
  by sep_auto

(* Ensure a certain capacity *)
definition pfa_ensure :: "'a::{heap,default} pfarray \<Rightarrow> nat \<Rightarrow> 'a pfarray Heap" where
  "pfa_ensure \<equiv> \<lambda>(a,n) k. do {
  a' \<leftarrow> array_ensure a k default;
  return (a',n)
}
"

lemma pfa_ensure_rule[sep_heap_rules]: "
    < is_pfa c l (a,n) > 
      pfa_ensure (a,n) k
    <\<lambda>(a',n'). is_pfa (max c k) l (a',n') * \<up>(n' = n \<and> c \<ge> n)>\<^sub>t"  
  by (sep_auto 
      simp: pfa_ensure_def is_pfa_def)


definition "pfa_copy \<equiv> arl_copy"


lemma pfa_copy_rule[sep_heap_rules]:
  "< is_pfa c l a >
   pfa_copy a
   <\<lambda>r. is_pfa c l a * is_pfa c l r>\<^sub>t"  
  by (sep_auto simp: pfa_copy_def arl_copy_def is_pfa_def)

definition pfa_blit :: "'a::heap pfarray \<Rightarrow> nat \<Rightarrow> 'a::heap pfarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "pfa_blit \<equiv> \<lambda>(src,sn) si (dst,dn) di l. blit src si dst di l"


lemma min_nat: "min a (a+b) = (a::nat)"
  by auto


lemma pfa_blit_rule[sep_heap_rules]:
  assumes LEN: "si+len \<le> sn" "di \<le> dn" "di+len \<le> dc"
  shows
    "< is_pfa sc src (srci,sn)
      * is_pfa dc dst (dsti,dn) >
    pfa_blit (srci,sn) si (dsti,dn) di len
    <\<lambda>_. is_pfa sc src (srci,sn)
      * is_pfa dc (take di dst @ take len (drop si src) @ drop (di+len) dst) (dsti,max (di+len) dn)
    >"
  using LEN apply(sep_auto simp add: min_nat is_pfa_def pfa_blit_def min.commute min.absorb1 heap: blit_rule)
   apply (simp add: min.absorb1 take_drop)
  apply (simp add: drop_take max_def)
  done

definition pfa_drop :: "('a::heap) pfarray \<Rightarrow> nat \<Rightarrow> 'a pfarray \<Rightarrow> 'a pfarray Heap" where
  "pfa_drop \<equiv> \<lambda>(src,sn) si (dst,dn). do {
   blit src si dst 0 (sn-si);
   return (dst,(sn-si))
}
"


lemma pfa_drop_rule[sep_heap_rules]:
  assumes LEN: "k \<le> sn" "(sn-k) \<le> dc"
  shows
    "< is_pfa sc src (srci,sn)
      * is_pfa dc dst (dsti,dn) >
    pfa_drop (srci,sn) k (dsti,dn)
    <\<lambda>(dsti',dn'). is_pfa sc src (srci,sn)
      * is_pfa dc (drop k src) (dsti',dn')
      * \<up>(dsti' = dsti)
    >"
  using LEN apply (sep_auto simp add: drop_take is_pfa_def pfa_drop_def dest!: mod_starD heap: pfa_blit_rule)
  done


definition "pfa_append_grow \<equiv> \<lambda>(a,n) x. do {
  l \<leftarrow> pfa_capacity (a,n);
  a' \<leftarrow> if l = n 
  then array_grow a (l+1) x
  else Array.upd n x a;
  return (a',n+1)
}"



lemma pfa_append_grow_full_rule[sep_heap_rules]: "n = c \<Longrightarrow>
     <is_pfa c l (a,n)>
  array_grow a (c+1) x
      <\<lambda>a'. is_pfa (c+1) (l@[x]) (a',n+1)>\<^sub>t"
  apply(sep_auto simp add: is_pfa_def 
      heap del: array_grow_rule)
  apply(vcg heap del: array_grow_rule heap add: array_grow_rule[of l "(Suc (length l))" a x])
   apply simp
  apply(rule ent_ex_postI[where ?x="l@[x]"])
  apply sep_auto
  done


lemma pfa_append_grow_less_rule: "n < c \<Longrightarrow>
 <is_pfa c l (a,n)>
    Array.upd n x a
<\<lambda>a'. is_pfa c (l@[x]) (a',n+1)>\<^sub>t"
  apply(sep_auto simp add: is_pfa_def take_update_last)
  done

lemma pfa_append_grow_rule[sep_heap_rules]: "
  <is_pfa c l (a,n)>
  pfa_append_grow (a,n) x 
  <\<lambda>(a',n'). is_pfa (if c = n then c+1 else c) (l@[x]) (a',n') * \<up>(n'=n+1 \<and> c \<ge> n)>\<^sub>t"
  apply(subst pfa_append_grow_def)
  apply(rule hoare_triple_preI)
  apply (sep_auto
      heap add: pfa_append_grow_full_rule pfa_append_grow_less_rule)
   apply(sep_auto simp add: is_pfa_def)
  apply(sep_auto simp add: is_pfa_def)
  done

(* This definition has only one access to the array length *)
definition "pfa_append_grow' \<equiv> \<lambda>(a,n) x. do {
  a' \<leftarrow> pfa_ensure (a,n) (n+1);
  a'' \<leftarrow> pfa_append a' x;
  return a''
}"

lemma pfa_append_grow'_rule[sep_heap_rules]: "
  <is_pfa c l (a,n)>
  pfa_append_grow' (a,n) x 
  <\<lambda>(a',n'). is_pfa (max (n+1) c) (l@[x]) (a',n') * \<up>(n'=n+1 \<and> c \<ge> n)>\<^sub>t"
  unfolding pfa_append_grow'_def
  by (sep_auto simp add: max_def)


definition "pfa_insert \<equiv> \<lambda>(a,n) i x. do {
  a' \<leftarrow> array_shr a i 1;
  a'' \<leftarrow> Array.upd i x a;
  return (a'',n+1)
}"


lemma list_update_last: "length ls = Suc i \<Longrightarrow> ls[i:=x] = (take i ls)@[x]"
  by (metis append_eq_conv_conj length_Suc_rev_conv list_update_length)

lemma pfa_insert_rule[sep_heap_rules]:
  "\<lbrakk>i \<le> n; n < c\<rbrakk> \<Longrightarrow>
  <is_pfa c l (a,n)>
  pfa_insert (a,n) i x 
  <\<lambda>(a',n'). is_pfa c (take i l@x#drop i l) (a',n') * \<up>(n' = n+1 \<and> a=a')>"
  unfolding pfa_insert_def is_pfa_def 
  by (sep_auto simp add: list_update_append1 list_update_last
      Suc_diff_le drop_take min_def)

definition pfa_insert_grow ::  "'a::{heap,default} pfarray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a pfarray Heap" 
  where "pfa_insert_grow \<equiv> \<lambda>(a,n) i x. do {
  a' \<leftarrow> pfa_ensure (a,n) (n+1);
  a'' \<leftarrow> pfa_insert a' i x;
  return a''
}"

lemma pfa_insert_grow_rule: 
  "i \<le> n \<Longrightarrow>
  <is_pfa c l (a,n)>
  pfa_insert_grow (a,n) i x 
  <\<lambda>(a',n'). is_pfa (max c (n+1)) (take i l@x#drop i l) (a',n') * \<up>(n'=n+1 \<and> c \<ge> n)>\<^sub>t"
  unfolding pfa_insert_grow_def  
  by (sep_auto heap add: pfa_insert_rule[of i n "max c (Suc n)"])


definition pfa_extend where
  "pfa_extend \<equiv> \<lambda> (a,n) (b,m). do{
  blit b 0 a n m;
  return (a,n+m)
}"

lemma pfa_extend_rule: 
  "n+m \<le> c \<Longrightarrow>
  <is_pfa c l1 (a,n) * is_pfa d l2 (b,m)>
  pfa_extend (a,n) (b,m) 
  <\<lambda>(a',n'). is_pfa c (l1@l2) (a',n') * \<up>(a' = a \<and> n'=n+m) * is_pfa d l2 (b,m)>\<^sub>t"
  unfolding pfa_extend_def  
  by (sep_auto simp add: is_pfa_def min.absorb1 min.absorb2 heap add: blit_rule)


definition pfa_extend_grow where
  "pfa_extend_grow \<equiv> \<lambda> (a,n) (b,m). do{
  a' \<leftarrow> array_ensure a (n+m) default;
  blit b 0 a' n m;
  return (a',n+m)
}"

lemma pfa_extend_grow_rule: 
  "<is_pfa c l1 (a,n) * is_pfa d l2 (b,m)>
  pfa_extend_grow (a,n) (b,m) 
  <\<lambda>(a',n'). is_pfa (max c (n+m)) (l1@l2) (a',n') * \<up>(n'=n+m \<and> c \<ge> n) * is_pfa d l2 (b,m)>\<^sub>t"
  unfolding pfa_extend_grow_def  
  by (sep_auto simp add: is_pfa_def min.absorb1 min.absorb2 heap add: blit_rule)

definition pfa_append_extend_grow where
  "pfa_append_extend_grow \<equiv> \<lambda> (a,n) x (b,m). do{
  a' \<leftarrow> array_ensure a (n+m+1) default;
  a'' \<leftarrow> Array.upd n x a';
  blit b 0 a'' (n+1) m;
  return (a'',n+m+1)
}"

lemma pfa_append_extend_grow_rule: 
  "<is_pfa c l1 (a,n) * is_pfa d l2 (b,m)>
  pfa_append_extend_grow (a,n) x (b,m) 
  <\<lambda>(a',n'). is_pfa (max c (n+m+1)) (l1@x#l2) (a',n') * \<up>(n'=n+m+1 \<and> c \<ge> n) * is_pfa d l2 (b,m)>\<^sub>t"
  unfolding pfa_append_extend_grow_def  
  by (sep_auto simp add: list_update_last is_pfa_def min.absorb1 min.absorb2 heap add: blit_rule)


definition "pfa_delete \<equiv> \<lambda>(a,n) i. do {
  array_shl a (i+1) 1;
  return (a,n-1)
}"

lemma pfa_delete_rule[sep_heap_rules]:
  "i < n \<Longrightarrow>
  <is_pfa c l (a,n)>
  pfa_delete (a,n) i
  <\<lambda>(a',n'). is_pfa c (take i l@drop (i+1) l) (a',n') * \<up>(n' = n-1 \<and> a=a')>"
  unfolding pfa_delete_def is_pfa_def 
  apply (sep_auto simp add: drop_take min_def)
  by (metis Suc_diff_Suc diff_zero dual_order.strict_trans2 le_less_Suc_eq zero_le)



end