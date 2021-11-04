section \<open>Coinductive lists\<close>

theory MoreCoinductiveList2
  imports Parity_Game.MoreCoinductiveList (* for notation and lemmas like infinite_small_llength *)
begin

lemma ltake_infinity[simp]: "ltake \<infinity> x = x" by (simp add: ltake_all)

lemma coinductive_eq_iff_lnth_eq:
  "a = b \<longleftrightarrow> (llength a = llength b \<and> (\<forall> n. enat n < llength a \<longrightarrow> a $ n = b $ n))"
proof
  assume "llength a = llength b \<and> (\<forall>n. enat n < llength a \<longrightarrow> a $ n = b $ n)"
  hence len:"llength a = llength b"
    and lnth:"enat n < llength a \<Longrightarrow> a $ n = b $ n" for n by auto
  show "a = b" proof(cases "llength a")
    case (enat nat)
    hence leq:"llist_of (list_of (ltake nat a)) = a" "llist_of (list_of (ltake nat b)) = b"
      by (auto simp add: len llength_eq_enat_lfiniteD ltake_all)
    with lnth_llist_of lnth
    have [intro]:"i < length (list_of (ltake (enat nat) a)) \<Longrightarrow> ltake (enat nat) a $ i = ltake (enat nat) b $ i" for i 
      by (metis enat_ord_code(4) enat_ord_simps(2) lfinite_ltake llength_llist_of llist_of_list_of)
    from len have [intro]:"length (list_of (ltake (enat nat) a)) = length (list_of (ltake (enat nat) b))"
      by (simp add: length_list_of_conv_the_enat)
    have "list_of (ltake nat a) = list_of (ltake nat b)" by(subst list_eq_iff_nth_eq, auto)
    then show ?thesis using leq by metis
  next
    case infinity
    hence inf:"\<not> lfinite a" "\<not> lfinite b" using len llength_eq_infty_conv_lfinite by auto
    from lnth[unfolded infinity] have "(($) a) = (($) b)" by auto
    then show ?thesis using inf[THEN inf_llist_lnth] by metis
  qed
qed auto

lemma coinductive_eq_I:
  assumes "(llength a = llength b \<and> (\<forall> n. enat n < llength a \<longrightarrow> a $ n = b $ n))"
  shows "a = b"
  using coinductive_eq_iff_lnth_eq assms by auto
text \<open>Our co-inductive lists will have Option types in them, so we can return None for out of bounds.\<close>
definition lnth_option where
  "lnth_option xs i \<equiv> if enat i < llength xs then xs $ i else None"

lemma enat_times_less:
  "enat c * enat lst < y * enat c \<Longrightarrow> lst < y"
by (cases y;auto)

lemma llist_eq_lcons:
  assumes "a \<noteq> LNil" "b \<noteq> LNil" "lhd a = lhd b" "ltl a = ltl b"
  shows "a = b"
using assms by(cases a;cases b;auto)

end