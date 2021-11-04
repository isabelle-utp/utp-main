theory BTree_ImpSplit
  imports
    BTree_ImpSet
    BTree_Split
    Imperative_Loops
begin

section "Imperative split operations"

text "So far, we have only given a functional specification of a possible split.
      We will now provide imperative split functions that refine the functional specification.
      However, rather than tracing the execution of the abstract specification,
      the imperative versions are implemented using while-loops."


subsection "Linear split"

text "The linear split is the most simple split function for binary trees.
      It serves a good example on how to use while-loops in Imperative/HOL
      and how to prove Hoare-Triples about its application using loop invariants."

definition lin_split :: "('a::heap \<times> 'b::{heap,linorder}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "lin_split \<equiv> \<lambda> (a,n) p. do {
  
  i \<leftarrow> heap_WHILET 
    (\<lambda>i. if i<n then do {
      (_,s) \<leftarrow> Array.nth a i;
      return (s<p)
    } else return False) 
    (\<lambda>i. return (i+1)) 
    0;
       
  return i
}"


lemma lin_split_rule: "
< is_pfa c xs (a,n)>
 lin_split (a,n) p
 <\<lambda>i. is_pfa c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p) \<and> (i<n \<longrightarrow> snd (xs!i)\<ge>p))>\<^sub>t"
  unfolding lin_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>i. n - i)"
      and I = "\<lambda>i. is_pfa c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p))"
      and b = "\<lambda>i. i<n \<and> snd (xs!i) < p"
      and Q="\<lambda>i. is_pfa c xs (a,n) * \<up>(i\<le>n \<and> (\<forall>j<i. snd (xs!j) < p) \<and> (i<n \<longrightarrow> snd (xs!i)\<ge>p))"
      ]
  thm R

  apply (sep_auto  decon: R simp: less_Suc_eq is_pfa_def) []
       apply (metis nth_take snd_eqD)
      apply (metis nth_take snd_eqD)
     apply (sep_auto simp: is_pfa_def less_Suc_eq)+
      apply (metis nth_take)
    apply(sep_auto simp: is_pfa_def)
  apply (metis le_simps(3) less_Suc_eq less_le_trans nth_take)
  apply(sep_auto simp: is_pfa_def)+
  done

subsection "Binary split"

text "To obtain an efficient B-Tree implementation, we prefer a binary split
function.
To explore the searching procedure
and the resulting proof, we first implement the split on singleton arrays."

definition bin'_split :: "'b::{heap,linorder} array_list \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "bin'_split \<equiv> \<lambda>(a,n) p. do {
  (low',high') \<leftarrow> heap_WHILET 
    (\<lambda>(low,high). return (low < high)) 
    (\<lambda>(low,high). let mid = ((low  + high) div 2) in
     do {
      s \<leftarrow> Array.nth a mid;
      if p < s then
         return (low, mid)
      else if p > s then
         return (mid+1, high)
      else return (mid,mid)
     }) 
    (0::nat,n);
  return low'
}"


thm sorted_wrt_nth_less

(* alternative: replace (\<forall>j<l. xs!j < p) by (l > 0 \<longrightarrow> xs!(l-1) < p)*)
lemma bin'_split_rule: "
sorted_less xs \<Longrightarrow>
< is_pfa c xs (a,n)>
 bin'_split (a,n) p
 <\<lambda>l. is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (l<n \<longrightarrow> xs!l\<ge>p)) >\<^sub>t"
  unfolding bin'_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>(l,h). h-l)"
      and I = "\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l\<le>h \<and> h \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (h<n \<longrightarrow> xs!h\<ge>p))"
      and b = "\<lambda>(l,h). l<h"
      and Q="\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. xs!j < p) \<and> (l<n \<longrightarrow> xs!l\<ge>p))"
      ]
  thm R

  apply (sep_auto decon: R simp: less_Suc_eq is_pfa_def) []
  subgoal for l' aa l'a aaa ba j
  proof -
    assume 0: "n \<le> length l'a"
    assume a: "l'a ! ((aa + n) div 2) < p"
    moreover assume "aa < n"
    ultimately have b: "((aa+n)div 2) < n"
      by linarith
    then have "(take n l'a) ! ((aa + n) div 2) < p"
      using a by auto
    moreover assume "sorted_less (take n l'a)"
    ultimately have "\<And>j. j < (aa+n)div 2 \<Longrightarrow> (take n l'a) ! j < (take n l'a) ! ((aa + n) div 2)"
      using
        sorted_wrt_nth_less[where ?P="(<)" and xs="(take n l'a)" and ?j="((aa + n) div 2)"]
        a b "0" by auto
    moreover fix j assume "j < (aa+n) div 2"
    ultimately show "l'a ! j < p" using "0" b
      using \<open>take n l'a ! ((aa + n) div 2) < p\<close> dual_order.strict_trans by auto
  qed
  subgoal for l' aa b l'a aaa ba j
  proof -
    assume t0: "n \<le> length l'a"
    assume t1: "aa < b"
    assume a: "l'a ! ((aa + b) div 2) < p"
    moreover assume "b \<le> n"
    ultimately have b: "((aa+b)div 2) < n" using t1
      by linarith
    then have "(take n l'a) ! ((aa + b) div 2) < p"
      using a by auto
    moreover assume "sorted_less (take n l'a)"
    ultimately have "\<And>j. j < (aa+b)div 2 \<Longrightarrow> (take n l'a) ! j < (take n l'a) ! ((aa + b) div 2)"
      using
        sorted_wrt_nth_less[where ?P="(<)" and xs="(take n l'a)" and ?j="((aa + b) div 2)"]
        a b t0 by auto
    moreover fix j assume "j < (aa+b) div 2"
    ultimately show "l'a ! j < p" using t0 b
      using \<open>take n l'a ! ((aa + b) div 2) < p\<close> dual_order.strict_trans by auto
  qed
     apply sep_auto
      apply (metis le_less nth_take)
     apply (metis le_less nth_take)
    apply sep_auto
  subgoal for l' aa l'a aaa ba j
  proof -
    assume t0: "aa < n"
    assume t1: " n \<le> length l'a"
    assume t4: "sorted_less (take n l'a)"
    assume t5: "j < (aa + n) div 2"
    have "(aa+n) div 2 < n" using t0 by linarith
    then have "(take n l'a) ! j < (take n l'a) ! ((aa + n) div 2)"
      using t0 sorted_wrt_nth_less[where xs="take n l'a" and ?j="((aa + n) div 2)"]
        t1 t4 t5 by auto
    then show ?thesis
      using \<open>(aa + n) div 2 < n\<close> t5 by auto
  qed
  subgoal for l' aa b l'a aaa ba j
  proof -
    assume t0: "aa < b"
    assume t1: " n \<le> length l'a"
    assume t3: "b \<le> n"
    assume t4: "sorted_less (take n l'a)"
    assume t5: "j < (aa + b) div 2"
    have "(aa+b) div 2 < n" using t3 t0 by linarith
    then have "(take n l'a) ! j < (take n l'a) ! ((aa + b) div 2)"
      using t0 sorted_wrt_nth_less[where xs="take n l'a" and ?j="((aa + b) div 2)"]
        t1 t4 t5 by auto
    then show ?thesis
      using \<open>(aa + b) div 2 < n\<close> t5 by auto
  qed
    apply (metis nth_take order_mono_setup.refl)
   apply sep_auto
  apply (sep_auto simp add: is_pfa_def)
  done

text "Then, using the same loop invariant, a binary split for B-tree-like arrays
is derived in a straightforward manner."


definition bin_split :: "('a::heap \<times> 'b::{heap,linorder}) pfarray \<Rightarrow> 'b \<Rightarrow> nat Heap"
  where
    "bin_split \<equiv> \<lambda>(a,n) p. do {
  (low',high') \<leftarrow> heap_WHILET 
    (\<lambda>(low,high). return (low < high)) 
    (\<lambda>(low,high). let mid = ((low  + high) div 2) in
     do {
      (_,s) \<leftarrow> Array.nth a mid;
      if p < s then
         return (low, mid)
      else if p > s then
         return (mid+1, high)
      else return (mid,mid)
     }) 
    (0::nat,n);
  return low'
}"


thm nth_take

lemma nth_take_eq: "take n ls = take n ls' \<Longrightarrow> i < n \<Longrightarrow> ls!i = ls'!i"
  by (metis nth_take)

lemma map_snd_sorted_less: "\<lbrakk>sorted_less (map snd xs); i < j; j < length xs\<rbrakk>
       \<Longrightarrow> snd (xs ! i) < snd (xs ! j)"
  by (metis (mono_tags, hide_lams) length_map less_trans nth_map sorted_wrt_iff_nth_less)

lemma map_snd_sorted_lesseq: "\<lbrakk>sorted_less (map snd xs); i \<le> j; j < length xs\<rbrakk>
       \<Longrightarrow> snd (xs ! i) \<le> snd (xs ! j)"
  by (metis eq_iff less_imp_le map_snd_sorted_less order.not_eq_order_implies_strict)

lemma bin_split_rule: "
sorted_less (map snd xs) \<Longrightarrow>
< is_pfa c xs (a,n)>
 bin_split (a,n) p
 <\<lambda>l. is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. snd(xs!j) < p) \<and> (l<n \<longrightarrow> snd(xs!l)\<ge>p)) >\<^sub>t"
  (* this works in principle, as demonstrated above *)
  unfolding bin_split_def

  supply R = heap_WHILET_rule''[where 
      R = "measure (\<lambda>(l,h). h-l)"
      and I = "\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l\<le>h \<and> h \<le> n \<and> (\<forall>j<l. snd (xs!j) < p) \<and> (h<n \<longrightarrow> snd (xs!h)\<ge>p))"
      and b = "\<lambda>(l,h). l<h"
      and Q="\<lambda>(l,h). is_pfa c xs (a,n) * \<up>(l \<le> n \<and> (\<forall>j<l. snd (xs!j) < p) \<and> (l<n \<longrightarrow> snd (xs!l)\<ge>p))"
      ]
  thm R

  apply (sep_auto decon: R simp: less_Suc_eq is_pfa_def) []

      apply(auto dest!: sndI nth_take_eq[of n _ _ "(_ + _) div 2"])[]
     apply(auto dest!: sndI nth_take_eq[of n _ _ "(_ + _) div 2"])[]
    apply (sep_auto dest!: sndI )
  subgoal for ls i ls' _ _ j
    using map_snd_sorted_lesseq[of "take n ls'" j "(i + n) div 2"] 
      less_mult_imp_div_less apply(auto)[]
    done
  subgoal for ls i j ls' _ _ j'
    using map_snd_sorted_lesseq[of "take n ls'" j' "(i + j) div 2"] 
      less_mult_imp_div_less apply(auto)[]
    done
    apply sep_auto
  subgoal for ls i ls' _ _ j
    using map_snd_sorted_less[of "take n ls'" j "(i + n) div 2"] 
      less_mult_imp_div_less
    apply(auto)[]
    done
  subgoal for ls i j ls' _ _ j'
    using map_snd_sorted_less[of "take n ls'" j' "(i + j) div 2"] 
      less_mult_imp_div_less
    apply(auto)[]
    done
    apply (metis le_less nth_take_eq)
   apply sep_auto
  apply (sep_auto simp add: is_pfa_def)
  done


subsection "Refinement of an abstract split"

text "We provide a certain abstract split function
that is particularly easy to analyse. The idea of this function is due to Peter Lammich."

definition "abs_split xs x = (takeWhile (\<lambda>(_,s). s<x) xs, dropWhile (\<lambda>(_,s). s<x) xs)"

interpretation btree_abs_search: split abs_split
  unfolding abs_split_def sym[OF linear_split_alt]
  by unfold_locales

text \<open>Any function that yields the heap rule
we have obtained for bin\_split and lin\_split also
refines this abstract split.\<close>

locale imp_split_smeq =
  fixes split_fun :: "('a::{heap,default,linorder} btnode ref option \<times> 'a) array \<times> nat \<Rightarrow> 'a \<Rightarrow> nat Heap"
  assumes split_rule: "sorted_less (separators xs) \<Longrightarrow> 
 <is_pfa c xs (a, n)>
   split_fun (a, n) (p::'a)
  <\<lambda>r. is_pfa c xs (a, n) *
                 \<up> (r \<le> n \<and>
                   (\<forall>j<r. snd (xs ! j) < p) \<and>
                   (r < n \<longrightarrow> p \<le> snd (xs ! r)))>\<^sub>t"
begin


lemma abs_split_full: "\<forall>(_,s) \<in> set xs. s < p \<Longrightarrow> abs_split xs p = (xs,[])"
  by (simp add: abs_split_def)


lemma abs_split_split:
  assumes "n < length xs" 
    and "(\<forall>(_,s) \<in> set (take n xs). s < p)"
    and " (case (xs!n) of (_,s) \<Rightarrow> \<not>(s < p))"
  shows "abs_split xs p = (take n xs, drop n xs)"
  using assms  apply (auto simp add: abs_split_def)
   apply (metis (mono_tags, lifting) id_take_nth_drop old.prod.case takeWhile_eq_all_conv takeWhile_tail)
  by (metis (no_types, lifting) Cons_nth_drop_Suc case_prod_conv dropWhile.simps(2) dropWhile_append2 id_take_nth_drop)


lemma split_rule_abs_split: 
  shows
    "sorted_less (separators ts) \<Longrightarrow> <
    is_pfa c tsi (a,n)
  * list_assn (A \<times>\<^sub>a id_assn) ts tsi> 
    split_fun (a,n) p 
  <\<lambda>i. 
    is_pfa c tsi (a,n)
    * list_assn (A \<times>\<^sub>a id_assn) ts tsi
    * \<up>(split_relation ts (abs_split ts p) i)>\<^sub>t"
  apply(rule hoare_triple_preI)
  apply (sep_auto heap: split_rule dest!: mod_starD id_assn_list
      simp add: list_assn_prod_map split_ismeq)
    apply(auto simp add: is_pfa_def)
proof -

  fix h l' assume heap_init:
    "h \<Turnstile> a \<mapsto>\<^sub>a l'"
    "map snd ts = (map snd (take n l'))"
    "n \<le> length l'"


  show full_thm: "\<forall>j<n. snd (l' ! j) < p \<Longrightarrow>
       split_relation ts (abs_split ts p) n"
  proof -
    assume sm_list: "\<forall>j<n. snd (l' ! j) < p"
    then have "\<forall>j < length (map snd (take n l')). ((map snd (take n l'))!j) < p"
      by simp
    then have "\<forall>j<length (map snd ts). ((map snd ts)!j) < p"
      using heap_init by simp
    then have "\<forall>(_,s) \<in> set ts. s < p"
      by (metis case_prod_unfold in_set_conv_nth length_map nth_map)
    then have "abs_split ts p = (ts, [])"
      using abs_split_full[of ts p] by simp
    then show "split_relation ts (abs_split ts p) n"
      using split_relation_length
      by (metis heap_init(2) heap_init(3) length_map length_take min.absorb2)

  qed
  then show "\<forall>j<n. snd (l' ! j) < p \<Longrightarrow>
       p \<le> snd (take n l' ! n) \<Longrightarrow>
       split_relation ts (abs_split ts p) n"
    by simp

  show part_thm: "\<And>x. x < n \<Longrightarrow>
       \<forall>j<x. snd (l' ! j) < p \<Longrightarrow>
       p \<le> snd (l' ! x) \<Longrightarrow> split_relation ts (abs_split ts p) x"
  proof -
    fix x assume x_sm_len: "x < n"
    moreover assume sm_list: "\<forall>j<x. snd (l' ! j) < p"
    ultimately have "\<forall>j<x. ((map snd l') ! j) < p"
      using heap_init
      by auto
    then have "\<forall>j<x. ((map snd ts)!j) < p"
      using heap_init  x_sm_len
      by auto
    moreover have x_sm_len_ts: "x < n"
      using heap_init x_sm_len by auto
    ultimately have "\<forall>(_,x) \<in> set (take x ts). x < p"
      by (auto simp add: in_set_conv_nth  min.absorb2)+
    moreover assume "p \<le> snd (l' ! x)"
    then have "case l'!x of (_,s) \<Rightarrow> \<not>(s < p)"
      by (simp add: case_prod_unfold)
    then have "case ts!x of (_,s) \<Rightarrow> \<not>(s < p)"
      using heap_init x_sm_len x_sm_len_ts
      by (metis (mono_tags, lifting) case_prod_unfold length_map length_take min.absorb2 nth_take snd_map_help(2))
    ultimately have "abs_split ts p = (take x ts, drop x ts)"
      using x_sm_len_ts abs_split_split[of x ts p] heap_init
      by (metis length_map length_take min.absorb2)
    then show "split_relation ts (abs_split ts p) x"
      using x_sm_len_ts 
      by (metis append_take_drop_id heap_init(2) heap_init(3) length_map length_take less_imp_le_nat min.absorb2 split_relation_alt)
  qed
qed


sublocale imp_split abs_split split_fun
  apply(unfold_locales)
  apply(sep_auto heap: split_rule_abs_split)
  done

end

subsection "Obtaining executable code"

text "In order to obtain fully defined functions,
we need to plug our split function implementations
into the locales we introduced previously."

interpretation btree_imp_linear_split: imp_split_smeq lin_split
  apply unfold_locales
  apply(sep_auto heap: lin_split_rule)
  done


text "Obtaining actual code turns out to be slightly more difficult
  due to the use of locales. However, we successfully obtain
the B-tree insertion and membership query with binary search splitting."

global_interpretation btree_imp_binary_split: imp_split_smeq bin_split
  defines btree_isin = btree_imp_binary_split.isin
    and btree_ins = btree_imp_binary_split.ins
    and btree_insert = btree_imp_binary_split.insert
    and btree_empty = btree_imp_binary_split.empty
  apply unfold_locales
  apply(sep_auto heap: bin_split_rule)
  done

thm btree_imp_binary_split.ins.simps
declare btree_imp_binary_split.ins.simps[code] btree_imp_binary_split.isin.simps[code]

export_code btree_empty btree_isin btree_insert checking SML Scala
export_code btree_empty btree_isin btree_insert in SML module_name BTreeInsert
export_code btree_empty btree_isin btree_insert in Scala module_name BTreeInsert

end

