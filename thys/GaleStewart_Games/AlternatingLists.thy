section \<open> Alternating lists \<close>

text \<open>In lists where even and odd elements play different roles, it helps to define functions to
      take out the even elements. We defined the function (l)alternate on (coinductive) lists to
      do exactly this, and define certain properties.\<close>

theory AlternatingLists
  imports MoreCoinductiveList2 (* for notation and lemmas like infinite_small_llength *)
begin

text \<open>The functions ``alternate" and ``lalternate" are our main workhorses:
      they take every other item, so every item at even indices.\<close>

fun alternate where
  "alternate Nil = Nil" |
  "alternate (Cons x xs) = Cons x (alternate (tl xs))"

text \<open>``lalternate" takes every other item from a co-inductive list.\<close>
primcorec lalternate :: "'a llist \<Rightarrow> 'a llist"
  where
    "lalternate xs = (case xs of LNil \<Rightarrow> LNil |
                                 (LCons x xs) \<Rightarrow> LCons x (lalternate (ltl xs)))"

lemma lalternate_ltake:
  "ltake (enat n) (lalternate xs) = lalternate (ltake (2*n) xs)"
proof(induct n arbitrary:xs)
  case 0
  then show ?case by (metis LNil_eq_ltake_iff enat_defs(1) lalternate.ctr(1) lnull_def mult_zero_right)
next
  case (Suc n)
  hence lt:"ltake (enat n) (lalternate (ltl (ltl xs))) = lalternate (ltake (enat (2 * n)) (ltl (ltl xs)))".
  show ?case
  proof(cases "lalternate xs")
    case LNil
    then show ?thesis by(metis lalternate.disc(2) lnull_def ltake_LNil)
  next
    case (LCons x21 x22)
    thus ?thesis unfolding ltake_ltl mult_Suc_right add_2_eq_Suc
      using eSuc_enat lalternate.code lalternate.ctr(1) lhd_LCons_ltl llist.sel(1)
      by (smt (z3) lt ltake_ltl llist.simps(3) llist.simps(5) ltake_eSuc_LCons)
  qed
qed

lemma lalternate_llist_of[simp]:
  "lalternate (llist_of xs) = llist_of (alternate xs)"
proof(induct "alternate xs" arbitrary:xs)
  case Nil
  then show ?case
    by (metis alternate.elims lalternate.ctr(1) list.simps(3) llist_of.simps(1) lnull_llist_of)
next
  case (Cons a xs)
  then show ?case by(cases xs,auto simp: lalternate.ctr)
qed

lemma lalternate_finite_helper: (* The other direction is proved later, added as SIMP rule *)
  assumes "lfinite (lalternate xs)"
  shows "lfinite xs"
using assms proof(induct "lalternate xs" arbitrary:xs rule:lfinite_induct)
  case LNil
  then show ?case unfolding lalternate.code[of xs] by(cases xs;auto)
next
  case (LCons xs)
  then show ?case unfolding lalternate.code[of xs] by(cases "xs";cases "ltl xs";auto)
qed

lemma alternate_list_of: (* Note that this only holds for finite lists,
                    as the other direction is left undefined with arguments (not just undefined) *)
  assumes "lfinite xs"
  shows "alternate (list_of xs) = list_of (lalternate xs)"
  using assms by (metis lalternate_llist_of list_of_llist_of llist_of_list_of)

lemma alternate_length:
  "length (alternate xs) = (1+length xs) div 2"
  by (induct xs rule:induct_list012;simp)

lemma lalternate_llength:
  "llength (lalternate xs) * 2 = (1+llength xs) \<or> llength (lalternate xs) * 2 = llength xs"
proof(cases "lfinite xs")
  case True
  let ?xs = "list_of xs"
  have "length (alternate ?xs) = (1+length ?xs) div 2" using alternate_length by auto
  hence "length (alternate ?xs) * 2 = (1+length ?xs) \<or> length (alternate ?xs) * 2 = length ?xs"
    by auto
  then show ?thesis using alternate_list_of[OF True] lalternate_llist_of True
    length_list_of_conv_the_enat[OF True] llist_of_list_of[OF True]
    by (metis llength_llist_of numeral_One of_nat_eq_enat of_nat_mult of_nat_numeral plus_enat_simps(1))
next
  case False
  have "\<not> lfinite (lalternate xs)" using False lalternate_finite_helper by auto
  hence l1:"llength (lalternate xs) = \<infinity>" by(rule not_lfinite_llength)
  from False have l2:"llength xs = \<infinity>" using not_lfinite_llength by auto
  show ?thesis using l1 l2 by (simp add: mult_2_right)
qed

lemma lalternate_finite[simp]:
  shows "lfinite (lalternate xs) = lfinite xs"
proof(cases "lfinite xs")
  case True
  then show ?thesis
  proof(cases "lfinite (lalternate xs)")
    case False
    hence False using not_lfinite_llength[OF False] True[unfolded lfinite_conv_llength_enat]
                      lalternate_llength[of xs]
                by (auto simp:one_enat_def numeral_eq_enat)
    thus ?thesis by metis
  qed auto
next
  case False
  then show ?thesis using lalternate_finite_helper by blast
qed

lemma nth_alternate:
  assumes "2*n < length xs"
  shows "alternate xs ! n = xs ! (2 * n)"
  using assms proof (induct xs arbitrary:n rule:induct_list012)
  case (3 x y zs)
  then show ?case proof(cases n)
    case (Suc nat)
    show ?thesis using "3.hyps"(1) "3.prems" Suc by force
  qed simp
qed auto

lemma lnth_lalternate:
  assumes "2*n < llength xs"
  shows "lalternate xs $ n = xs $ (2 * n)"
proof -
  let ?xs = "ltake (2*Suc n) xs"
  have "lalternate ?xs $ n = ?xs $ (2 * n)"
    using assms alternate_list_of[of "ltake (2*Suc n) xs"] nth_alternate[of n "list_of ?xs"]
    by (smt (z3) Suc_1 Suc_mult_less_cancel1 enat_ord_simps(2) infinite_small_llength lalternate_ltake length_list_of lessI llength_eq_enat_lfiniteD llength_ltake' ltake_all not_less nth_list_of numeral_eq_enat the_enat.simps times_enat_simps(1))
  thus ?thesis
    by (metis Suc_1 Suc_mult_less_cancel1 enat_ord_simps(2) lalternate_ltake lessI lnth_ltake)
qed

lemma lnth_lalternate2[simp]:
  assumes "n < llength (lalternate xs)"
  shows "lalternate xs $ n = xs $ (2 * n)"
proof -
  from assms have "2*enat n < llength xs"
    by (metis enat_numeral lalternate_ltake leI linorder_neq_iff llength_ltake' ltake_all times_enat_simps(1))
  from lnth_lalternate[OF this] show ?thesis.
qed

end