theory FilteredList
  imports MoreCoinductiveList2
begin

subsection \<open>More on filtered lists\<close>

text \<open>We will reason about (co-inductive) lists with distinct elements.
      However, for our setting, this 'distinct' property only holds on the list after filtering.
      For this reason, we need some additional lemmas.\<close>

text \<open>Taking a sublist preserves distinctness after filtering.\<close>
lemma ldistinct_lfilter_ltake[intro]:
  assumes "ldistinct (lfilter P xs)"
  shows "ldistinct (lfilter P (ltake x xs))"
  using assms
  by(induct xs,force,force
    ,(* sledgehammer found this gem to prove the inductive step via lfilter_lappend_lfinite!
        We will use this strategy ourselves later on *)
     metis lappend_ltake_ldrop ldistinct_lappend lfilter_lappend_lfinite lfinite_LConsI lfinite_ltake)

text \<open>The function lfind is used in multiple proofs, all are introduced to prove ltake_lfilter.\<close>
definition lfind where "lfind P lst = (LEAST i. P (lst $ i))"

lemma lfilter_lfind:
  assumes "lfilter P lst \<noteq> LNil"
  shows "P (lst $ lfind P lst)" (is ?g1)
        "P (lst $ y) \<Longrightarrow> lfind P lst \<le> y" (is "?a \<Longrightarrow> ?g2")
        "lfind P lst < llength lst" (is ?g3)
proof -
  let ?I = "{n. enat n < llength lst \<and> P (lst $ n)}"
  let ?xs = lst
  from assms[unfolded lfilter_conv_lnths] lset_LNil
  have "lset (lnths lst {n. enat n < llength lst \<and> P (lst $ n)}) \<noteq> {}" by auto
  hence "{?xs $ i |i. enat i < llength ?xs \<and> i \<in> ?I} \<noteq> {}" using lset_lnths[of ?xs ?I] by metis
  then obtain i where p:"P (lst $ i)" "i < llength lst" by auto
  from p show ?g1 using LeastI lfind_def by metis
  from p show "?a \<Longrightarrow> ?g2" using Least_le lfind_def by metis
  from p show ?g3 using Least_le lfind_def by (metis enat_ord_simps(1) le_less_trans)
qed

lemma ltake_lfind_lset:
  assumes "x \<in> lset (ltake (enat (lfind P lst)) lst)"
  shows "\<not> P x"
proof(cases "lfilter P (ltake (enat (lfind P lst)) lst) = LNil")
  case True
  then show ?thesis using assms unfolding lfilter_eq_LNil by auto
next
  case False
  from assms[unfolded in_lset_conv_lnth] obtain n where
    n:"enat n < llength (ltake (enat (lfind P lst)) lst)" "ltake (enat (lfind P lst)) lst $ n = x"
    by blast
  { assume a:"P x"
      (* The idea of this {block} is that the element n must come after (lfind P lst) by lfilter_lfind(2)
     but this contradicts n(1).
     However, in the last step when writing this proof, sledgehammer found one that didn't use
       any of my previous steps, so here's a one-liner: *)
    from n Coinductive_List.lset_ltake False a enat_ord_simps(1) leD lfilter_empty_conv lfilter_lfind(2,3) llength_ltake' lnth_ltake subset_eq
    have False by metis
  }
  then show ?thesis by blast
qed

lemma ltake_lfind_conv:
  assumes "lfilter P lst \<noteq> LNil"
  shows "ltake (lfind P lst) lst = ltakeWhile (Not o P) lst" (is "?t1 = ?t2")
        "ldrop (lfind P lst) lst = ldropWhile (Not o P) lst" (is "?t3 = ?t4")
proof -
  have lfin:"lfinite ?t1" by simp
  have [simp]:"min (enat (lfind P lst)) (llength lst) = (lfind P lst)"
    using lfilter_lfind(3)[OF assms] by (metis min.strict_order_iff)
  have l1:"llength ?t1 = lfind P lst" by simp
  from ltake_lfind_lset ltakeWhile_all
  have t:"ltakeWhile (Not o P) ?t1 = ?t1" unfolding o_def by metis
  have inset:"lset (ltake (enat (lfind P lst)) lst) \<subseteq> {x. (Not \<circ> P) x}"
    using ltake_lfind_lset[of _ P lst] by auto (* for use in ltakeWhile_lappend2 *)
  have isnull:"ltakeWhile (Not \<circ> P) (ldrop (enat (lfind P lst)) lst) = LNil"
    apply(cases "ldrop (enat (lfind P lst)) lst")
    using lfilter_lfind(1)[OF assms] lhd_ldrop[OF lfilter_lfind(3)[OF assms]]
    by auto
  have "ltakeWhile (Not o P) ?t1 = ltakeWhile (Not o P) (lappend ?t1 ?t3)"
    unfolding ltakeWhile_lappend2[OF inset] isnull lappend_LNil2 t..
  hence leneq:"llength ?t1 = llength ?t2" using t l1 lappend_ltake_ldrop by metis
  have "lappend ?t1 ?t3 = lappend ?t2 ?t4" 
     unfolding lappend_ltakeWhile_ldropWhile[of "Not \<circ> P" lst]
               lappend_ltake_ldrop[of "lfind P lst" lst]
     by simp
  from this[unfolded lappend_eq_lappend_conv[OF leneq]] lfin
  show "?t1 = ?t2" "?t3 = ?t4" by auto
qed

lemma lfilter_hdtl:
  assumes "lfilter P lst \<noteq> LNil"
  shows "\<exists> n. LCons (lhd (lfilter P lst)) LNil = lfilter P (ltake (enat n) lst) \<and>
              ltl (lfilter P lst) = lfilter P (ldrop (enat n) lst)"
proof(standard,standard)
  note * = lfilter_lfind[OF assms]
  let ?n = "Suc (lfind P lst)"
  let ?ltake = "ltake (enat ?n) lst"
  have ltake:"lappend (ltakeWhile (Not \<circ> P) ?ltake) (ldropWhile (Not \<circ> P) ?ltake) = ?ltake"
      (is "lappend ?ltw ?ldw = _")
      using lappend_ltakeWhile_ldropWhile by blast
  have "llength ?ldw \<le> 1"
      unfolding ldropWhile_lappend ltake_Suc_conv_snoc_lnth[OF *(3)]
      using ltake_lfind_lset[of _ P lst] by (auto intro:* simp:one_eSuc)
  hence null:"lnull (ltl (ldropWhile (Not \<circ> P) ?ltake))"
      unfolding llength_eq_0[symmetric] llength_ltl
      by (metis dual_order.order_iff_strict enat_ile epred_0 epred_1 iless_Suc_eq le_zero_eq one_eSuc one_enat_def)
  have e:"enat (lfind P lst) < enat (Suc (lfind P lst))" by auto
    from * have "P (?ltake $ lfind P lst)" using lnth_ltake[OF e] by metis
  hence nonnull:"\<not> lnull (lfilter P ?ltake)" unfolding lnull_lfilter
      by (metis "*"(3) e in_lset_conv_lnth leI llength_ltake' ltake_all)

  show a:"LCons (lhd (lfilter P lst)) LNil = lfilter P ?ltake" (is "?lhs = ?rhs")
  proof -
    have "lhd (lfilter P ?ltake) = lhd (lfilter P lst)"
      by(rule lprefix_lhdD[OF lprefix_lfilterI[OF ltake_is_lprefix] nonnull])
    hence h:"lhd ?lhs = lhd ?rhs" by simp
    have "ltl ?rhs = LNil" 
      unfolding ltl_lfilter using null by (metis lfilter_LNil llist.collapse(1))
    hence t:"ltl ?lhs = ltl ?rhs" by simp
    have flt:"?rhs \<noteq> LNil" using nonnull by fastforce
    show ?thesis by(rule llist_eq_lcons[of ?lhs ?rhs,OF _ flt h t],auto)
  qed

  from lappend_ltake_ldrop[of ?n lst] lappend_ltakeWhile_ldropWhile[of "Not \<circ> P" lst]
  have "lappend (ltake ?n lst) (ldrop ?n lst) = lappend (ltakeWhile (Not \<circ> P) lst) (ldropWhile (Not \<circ> P) lst)"
    by auto
  from ltake_lfind_conv(2)[OF assms]
  have "ltl (ldropWhile (Not \<circ> P) lst) = ldrop (enat (Suc (lfind P lst))) lst"
    unfolding ldrop_eSuc_conv_ltl eSuc_enat[symmetric] by simp
  thus "ltl (lfilter P lst) = lfilter P (ldrop (enat ?n) lst)" unfolding ltl_lfilter by metis
qed

lemma ltake_lfilter:
  shows "\<exists> n. ltake (enat x) (lfilter P lst) = lfilter P (ltake (enat n) lst) \<and> ldrop (enat x) (lfilter P lst) = lfilter P (ldrop (enat n) lst)"
proof(induct x)
  case 0
  then show ?case by (metis LNil_eq_ltake_iff ldrop_enat ldropn_0 lfilter_code(1) zero_enat_def)
next
  let ?fP = "lfilter P"
  case (Suc x)
  then obtain n where n:"ltake (enat x) (?fP lst) = ?fP (ltake (enat n) lst)"
    "ldrop (enat x) (lfilter P lst) = lfilter P (ldrop (enat n) lst)" by blast
  consider "lfilter P (ldrop (enat n) lst) \<noteq> LNil \<and> x < llength (?fP lst)" |
    "lfilter P (ldrop (enat n) lst) = LNil" | "x \<ge> llength (?fP lst)" by force
  then show ?case proof(cases)
    case 1
    hence *:"lfilter P (ldrop (enat n) lst) \<noteq> LNil" "enat x < llength (lfilter P lst)" by auto
    from lappend_ltake_ldrop have "lst = lappend (ltake (enat n) lst) (ldrop (enat n) lst)" by metis
    from lfilter_hdtl[OF *(1)] obtain delta where
      delta:"LCons (lhd (?fP (ldrop (enat n) lst))) LNil = ?fP (ltake (enat delta) (ldrop (enat n) lst))"
      "ltl (lfilter P (ldrop (enat n) lst)) = lfilter P (ldrop (enat delta) (ldrop (enat n) lst))" by blast
    have "ltake (enat (Suc x)) (?fP lst) = lappend (?fP (ltake (enat n) lst)) (LCons (?fP lst $ x) LNil)"
      using n ltake_Suc_conv_snoc_lnth * by metis
    also have "?fP lst $ x = ?fP lst $ (the_enat x)" by auto
    also have "\<dots> = lhd (ldrop x (?fP lst))" using lhd_ldrop[symmetric] *(2) by metis
    also have "\<dots> = lhd (?fP (ldrop (enat n) lst))" using n by metis
    also note delta(1)
    finally have take_part:"ltake (enat (Suc x)) (?fP lst) = ?fP (ltake (enat (n + delta)) lst)"
      using ltake_plus_conv_lappend
      by (metis infinite_small_llength lfilter_lappend_lfinite llength_ltake' ltake_all min.strict_order_iff not_less plus_enat_simps(1))
    have "ldrop (enat (Suc x)) (?fP lst) = ltl (ldrop x (?fP lst))" by (simp add: ltl_ldropn ldrop_eSuc_ltl ldrop_enat)
    also have "ldrop x (?fP lst) = ?fP (ldrop (enat n) lst)" using n by metis
    also note delta(2)
    also have "lfilter P (ldrop (enat delta) (ldrop (enat n) lst)) = lfilter P (ldrop (enat delta + enat n) lst)"
      by simp
    also have "(enat delta + enat n) = enat (n + delta)" by simp
    finally have drop_part:"ldrop (enat (Suc x)) (?fP lst) = ?fP (ldrop (enat (n + delta)) lst)".
    from take_part drop_part show ?thesis by blast
  next
  case 2
    note * = 2 lappend_ltake_ldrop[of "enat n" lst] Suc_llength infinite_small_llength
             lappend_LNil2 leI lfilter_lappend_lfinite llength_ltake' min.strict_order_iff n
    have take_part:"ltake (enat (Suc x)) (?fP lst) = ?fP (ltake (enat n) lst)"
      using * by (smt (z3) ltake_all)
    from 2 have drop_part:"ldrop (enat (Suc x)) (?fP lst) = ?fP (ldrop (enat n) lst)"
      using * by (smt (z3) ldrop_all)
    from take_part drop_part show ?thesis by blast
  next
  case 3
    then show ?thesis using n dual_order.order_iff_strict eSuc_enat iless_Suc_eq le_less_trans ltake_all ldrop_all
         by metis
  qed 
qed

lemma filter_obtain_two:
  assumes "i < j" "j < length (filter P lst)"
  shows "\<exists> i2 j2. i2 < j2 \<and> j2 < length lst \<and> lst ! i2 = filter P lst ! i \<and> lst ! j2 = filter P lst ! j"
  using assms
proof(induct lst arbitrary: i j)
  case (Cons a lst)
  then obtain jprev where jprev:"j = Suc jprev" using lessE by metis
  show ?case proof(cases "P a")
    case True
    hence lnth[simp]:"length (filter P (a # lst)) = Suc (length (filter P lst))" by auto
    show ?thesis proof(cases i)
      case 0
      from jprev True Cons(3) have "jprev < length (filter P lst) " by auto
      from nth_mem[OF this]
      have "filter P lst ! jprev \<in> set lst" by auto
      from this[unfolded in_set_conv_nth] obtain j2 where
        "j2<length lst" "lst ! j2 = filter P lst ! jprev" by blast
      hence "0 < Suc j2" "Suc j2 < length (a # lst)"
        "(a # lst) ! 0 = filter P (a # lst) ! i"
        "(a # lst) ! Suc j2 = filter P (a # lst) ! j" using 0 True jprev by auto
      then show ?thesis by blast
    next
      case (Suc nat)
      then obtain jprev where jprev:"j = Suc jprev" using Cons lessE by metis
      hence "nat < jprev" "jprev < length (filter P lst)" using Cons Suc lnth by auto
      from Cons(1)[OF this] obtain i2 j2 where "i2 < j2" "j2 < length lst"
        "lst ! i2 = filter P lst ! nat" "lst ! j2 = filter P lst ! jprev" by blast
      hence "Suc i2 < Suc j2" "Suc j2 < length (a # lst)"
        "(a # lst) ! Suc i2 = filter P (a # lst) ! Suc nat"
        "(a # lst) ! Suc j2 = filter P (a # lst) ! Suc jprev" using lnth by auto
      then show ?thesis unfolding jprev[symmetric] Suc[symmetric] by blast
    qed
  next
    case False
    hence [simp]: "filter P (a # lst) = filter P lst" by auto
    from Cons(1)[OF Cons(2)] Cons(3)[unfolded this]
    obtain i2 j2 where "i2 < j2" "j2 < length lst"
      "lst ! i2 = filter P lst ! i" "lst ! j2 = filter P lst ! j" by blast
    hence "Suc i2 < Suc j2" "Suc j2 < length (a # lst)"
      "(a # lst) ! Suc i2 = filter P (a # lst) ! i"
      "(a # lst) ! Suc j2 = filter P (a # lst) ! j" by (auto simp:False) 
    then show ?thesis by blast
  qed
qed auto

lemma ldistinct_lfilterI:
  assumes "\<And> i j. i < llength lst \<Longrightarrow> j < llength lst \<Longrightarrow> lst $ i = lst $ j \<Longrightarrow> P (lst $ i) \<Longrightarrow> i = j"
  shows "ldistinct (lfilter P lst)"
proof -
{ fix i j
  assume *: "enat i < llength (lfilter P lst)"
            "enat j < llength (lfilter P lst)"
            "lfilter P lst $ i = lfilter P lst $ j"
            "i < j"
  hence "lfilter P lst $ i \<in> lset (lfilter P lst)"
    unfolding in_lset_conv_lnth by auto
  with lset_lfilter
  have P:"P (lfilter P lst $ i)" by auto
  let ?maxij = "Suc (max i j)"
  from ltake_lfilter obtain maxij where
    maxij:"ltake ?maxij (lfilter P lst) = lfilter P (ltake (enat maxij) lst)"
    by blast
  let ?lst = "ltake (enat maxij) lst"
  have "lfinite ?lst" by auto
  define flst where "flst = list_of ?lst"
  hence flst:"llist_of flst = ?lst" by auto
  let ?flst = "llist_of flst"
  from * P
    have "enat i < llength (lfilter P ?flst)"
         "enat j < llength (lfilter P ?flst)"
         "lfilter P ?flst $ i = lfilter P ?flst $ j"
    and P2:"P (lfilter P ?lst $ i)"
    unfolding maxij[symmetric] flst by (auto simp add: lnth_ltake)
  hence "i < length (filter P flst)"
        "j < length (filter P flst)"
    and eq_ij: "filter P flst ! i = filter P flst ! j"
    unfolding llength_llist_of lfilter_llist_of lnth_llist_of by auto
  with filter_obtain_two[OF *(4) this(2)] obtain i2 j2
    where "i2 < length flst" "j2 < length flst"
          "flst ! i2 = filter P flst ! i"
          "flst ! j2 = filter P flst ! j"
          and ineq:"i2<j2"
    by auto
  hence "i2 < llength ?flst" "j2 < llength ?flst" "?flst $ i2 = ?flst $ j2" "?flst $ i2 = lfilter P ?flst $ i" "i2<j2" 
    unfolding llength_llist_of lfilter_llist_of lnth_llist_of eq_ij by auto
  hence "enat i2 < llength lst" "enat j2 < llength lst" "lst $ i2 = lst $ j2" "P (lst $ i2)"
    using P2 unfolding flst by (auto simp add: lnth_ltake)
  from assms[OF this]
  have False using ineq by auto
}
thus ?thesis unfolding ldistinct_conv_lnth by (smt (z3) le_cases3 less_le)
qed

lemma ldistinct_lfilterE:
  assumes "ldistinct (lfilter P lst)" "e = lst $ i" "e = lst $ j"
          "i < llength lst" "j < llength lst" "P e"
  shows "i = j"
proof -
  let ?maxij = "Suc (max i j)"
  let ?lst = "ltake (enat ?maxij) lst"
  have jle:"j < length (list_of (ltake (enat (Suc (max i j))) lst))" using assms(4,5)
    apply(subst length_list_of_conv_the_enat,force)
    by(cases "llength lst", auto simp:min_enat2_conv_enat min_enat1_conv_enat)
  have ile:"i < length (list_of (ltake (enat (Suc (max i j))) lst))" using assms(4,5)
    apply(subst length_list_of_conv_the_enat,force)
    by(cases "llength lst", auto simp:min_enat2_conv_enat min_enat1_conv_enat)
  have "enat i < ?maxij" "enat j < ?maxij" by auto
  from this[THEN lnth_ltake,of lst] assms
  have "ldistinct (lfilter P ?lst)" "e = ?lst $ i" "e = ?lst $ j" by auto
  hence d:"distinct (filter P (list_of ?lst))"
       "(list_of ?lst) ! j = e" "(list_of ?lst) ! i = e"
    using lfilter_llist_of[of P "list_of ?lst"] by auto
  show ?thesis by(rule distinct_filterD[OF d(1) jle ile assms(6) d(2,3)])
qed

lemma ldistinct_lfilter_conv:
  "ldistinct (lfilter P lst) = (\<forall> i j. i < llength lst \<longrightarrow> j < llength lst \<longrightarrow> P (lst $ i) \<longrightarrow> lst $ i = lst $ j \<longrightarrow> i = j)"
proof
  show "ldistinct (lfilter P lst) \<Longrightarrow> \<forall>i j. enat i < llength lst \<longrightarrow> enat j < llength lst \<longrightarrow> P (lst $ i) \<longrightarrow> lst $ i = lst $ j \<longrightarrow> i = j" 
    by (auto simp add: ldistinct_lfilterE)
  show "\<forall>i j. enat i < llength lst \<longrightarrow> enat j < llength lst \<longrightarrow> P (lst $ i) \<longrightarrow> lst $ i = lst $ j \<longrightarrow> i = j \<Longrightarrow> ldistinct (lfilter P lst) "
    using ldistinct_lfilterI by blast
qed

end