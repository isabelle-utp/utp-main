section \<open>Extra theorems on prefixes of Lists and their coinductive counterparts\<close>

theory MorePrefix
  imports MoreCoinductiveList2 (* for notation and lemmas like infinite_small_llength *)
begin

subsection \<open> Reasoning about prefixes \<close>
lemma head_prefixes [simp]:
  "prefixes list ! 0 = []"
  by (metis hd_conv_nth hd_prefixes prefixes_not_Nil)

lemma non_head_prefixes [simp]:
  assumes "n < length p" shows "(prefixes p ! Suc n) \<noteq> []"
proof -
  have "0 < length (prefixes p)" "Suc n < length (prefixes p)" by (auto simp: assms)
  then show ?thesis by (metis Zero_not_Suc distinct_prefixes head_prefixes nth_eq_iff_index_eq)
qed

lemma last_prefixes:
  assumes "i < length p"
  shows "last (tl (prefixes p) ! i) = p ! i"
  using assms
proof(induct p arbitrary:i)
  case (Cons a p i)
  show ?case proof(cases i)
    case (Suc nat)
    with Cons have "p ! nat = last (tl (prefixes p) ! nat)" "nat < length p" by auto
    then show ?thesis unfolding Suc by(auto simp:nth_tl)
  qed auto
qed force

lemma take_1_prefixes[simp]:
  "take (Suc 0) (prefixes list) = [[]]"
  by (simp add: take_Suc)

lemma map_last_prefixes [simp]:
  shows "map last (tl (prefixes p)) = p"
  unfolding list_eq_iff_nth_eq
  using last_prefixes by auto

lemma ltake_zero[simp]: "ltake (enat (0::nat)) lst = LNil"
  (* nitpick finds a counterexample in Isabelle2021*)
  by (simp add: zero_enat_def)

lemma ltakes_one_iterates:
  "ltake (enat (Suc 0)) (iterates f p) = LCons p LNil"
  by (metis One_nat_def iterates_lmap ltake_eSuc_LCons ltake_zero one_eSuc one_enat_def zero_enat_def)

lemma ltakes_suc_iterates[simp]:
  "ltake (enat (Suc n)) (iterates f p) = LCons p (ltake (enat n) (iterates f (f p)))"
  by (induct n,force simp:ltakes_one_iterates,metis eSuc_enat iterates.code ltake_eSuc_LCons)

lemma prefixes_nth_take[simp]:
  assumes "i \<le> length p"
  shows "prefixes p ! i = take i p"
  using assms proof(induct p arbitrary:i)
  case (Cons a p i) thus ?case by (cases i, auto)
qed auto

lemma tl_prefixes_idx:
  assumes "i < length p"
  shows "tl (prefixes p) ! i = take (Suc i) p"
  using assms by(induct p,auto)

lemma list_of_lappend_llist_of[simp]:
  assumes "lfinite q"
  shows "list_of (lappend (llist_of p) q) = append p (list_of q)"
  using assms by(induct p,auto)

lemma nth_prefixes:
  "n < length p \<Longrightarrow> \<not> Suc n < length p \<Longrightarrow> tl (prefixes p) ! n = p"
  by(induct p arbitrary:n,auto)

lemma take_Suc_prefix:
  "prefix (take n p) (take (Suc n) p)"
proof(induct p arbitrary:n)
  case (Cons a p n)
  then show ?case by(cases n,auto)
qed auto

lemma nth_prefixes_is_prefix:
  "n < length p  \<Longrightarrow> prefix ((prefixes p) ! n) ((prefixes p) ! Suc n)"
  by(induct "length p" n arbitrary:p rule:diff_induct,auto simp:take_Suc_prefix)

lemma nth_prefixes_is_prefix_tl:
  "Suc n < length p  \<Longrightarrow> prefix (tl (prefixes p) ! n) (tl (prefixes p) ! Suc n)"
  by (cases p) (auto simp:nth_prefixes_is_prefix take_Suc_prefix)

lemma prefix_same_length_eq:
  shows "(prefix a b \<and> length a = length b) \<longleftrightarrow> a = b"
  by (metis prefix_length_le prefix_length_prefix prefix_order.antisym prefix_order.order_refl)

lemma prefix_takeI:
  assumes "prefix a b" "n \<ge> length a"
  shows "prefix a (take n b)"
  using assms 
  by (smt (verit) prefix_length_prefix length_take min.absorb2 nat_le_linear take_all take_is_prefix)

thm prefix_length_prefix (* compare to *)
lemma lprefix_llength_lprefix:
  assumes "lprefix a c" "lprefix b c" "llength a \<le> llength b"
  shows "lprefix a b"
  using assms
  by (metis dual_order.antisym lprefix_down_linear lprefix_llength_eq_imp_eq lprefix_llength_le)

thm prefix_takeI (* compare to *)
lemma lprefix_ltakeI:
  assumes "lprefix a b" "llength a \<le> n"
  shows "lprefix a (ltake n b)"
  by (smt (verit, best) dual_order.antisym lappend_eq_lappend_conv lappend_ltake_ldrop llength_ltake
                        assms lprefix_conv_lappend lprefix_down_linear lprefix_llength_le min_def)

abbreviation augment_list where
  "augment_list \<sigma> p \<equiv> p @ [\<sigma> p]"

lemma length_augment_list:
  "length ((augment_list f ^^ n) p) = n + length p"
  by(induct n,auto)

lemma augment_list_nonempty:
  assumes "p\<noteq>[]" shows "(augment_list f ^^ i) p \<noteq> []"
  using assms by(cases i,auto)

lemma augment_list_Suc_prefix:
  "prefix ((augment_list f ^^ n) p) ((augment_list f ^^ Suc n) p)"
  by(cases n,auto simp:take_Suc_prefix)

lemma augment_list_prefix:
  "n \<le> m \<Longrightarrow> prefix ((augment_list f ^^ n) p) ((augment_list f ^^ m) p)"
proof(induct "m-n" arbitrary:m n)
  case (Suc x)
  hence [simp]:"Suc (x + n) = m" by auto
  from Suc.hyps(2) 
    prefix_order.order.trans[OF Suc.hyps(1)[of "x + n" n] augment_list_Suc_prefix[of "x+n" f p]]
  show ?case by auto
qed auto

lemma augment_list_nonsense[dest]:
assumes "(augment_list \<sigma> ^^ n) p = []"
shows "n=0" "p=[]"
using assms by(induct n,auto)

lemma prefix_augment:
  shows "prefix p ((augment_list s ^^ n) p)"
  by (induct n,auto simp:prefix_def)


end