section \<open>Utilties\<close>

theory Util
  imports
    Main
    "HOL-Library.Sublist"
    "HOL-Library.Permutation"

begin

abbreviation swap_events where
  "swap_events i j t \<equiv> take i t @ [t ! j, t ! i] @ take (j - (i+1)) (drop (i+1) t) @ drop (j+1) t"

lemma swap_neighbors_2:
  shows
    "i+1 < length t \<Longrightarrow> swap_events i (i+1) t = (t[i := t ! (i+1)])[i+1 := t ! i]"
proof (induct i arbitrary: t)
  case 0
  then show ?case 
    by (metis One_nat_def Suc_eq_plus1 add_lessD1 append.left_neutral append_Cons cancel_comm_monoid_add_class.diff_cancel drop_update_cancel length_list_update numeral_One take_0 take_Cons_numeral upd_conv_take_nth_drop zero_less_Suc)
next
  case (Suc n)
  let ?t = "tl t"
  have "t = hd t # ?t"
    by (metis Suc.prems hd_Cons_tl list.size(3) not_less_zero)
  moreover have "swap_events n (n+1) ?t = (?t[n := ?t ! (n+1)])[n+1 := ?t ! n]" 
    by (metis Suc.hyps Suc.prems Suc_eq_plus1 length_tl less_diff_conv)
  ultimately show ?case 
    by (metis Suc_eq_plus1 append_Cons diff_self_eq_0 drop_Suc_Cons list_update_code(3) nth_Cons_Suc take_Suc_Cons)
qed

lemma swap_identical_length:
  assumes
    "i < j" and
    "j < length t"
  shows
    "length t = length (swap_events i j t)"
proof -
  have "length (take i t @ [t ! j, t ! i] @ take (j - (i+1)) (drop (i+1) t))
      = length (take i t) + length [t ! j, t ! i] + length (take (j - (i+1)) (drop (i+1) t))"
    by simp
  then have "... = j+1" 
    using assms(1) assms(2) by auto
  then show ?thesis using assms(2) by auto
qed

lemma swap_identical_heads:
  assumes
    "i < j" and
    "j < length t"
  shows
    "take i t = take i (swap_events i j t)"
  using assms by auto

lemma swap_identical_tails:
  assumes
    "i < j" and
    "j < length t"
  shows
    "drop (j+1) t = drop (j+1) (swap_events i j t)"
proof -
  have "length (take i t @ [t ! j, t ! i] @ take (j - (i+1)) (drop (i+1) t))
      = length (take i t) + length [t ! j, t ! i] + length (take (j - (i+1)) (drop (i+1) t))"
    by simp
  then have "... = j+1" 
    using assms(1) assms(2) by auto
  then show ?thesis 
    by (metis \<open>length (take i t @ [t ! j, t ! i] @ take (j - (i + 1)) (drop (i + 1) t)) = length (take i t) + length [t ! j, t ! i] + length (take (j - (i + 1)) (drop (i + 1) t))\<close> append.assoc append_eq_conv_conj)
qed

lemma swap_neighbors:
  shows
    "i+1 < length l \<Longrightarrow> (l[i := l ! (i+1)])[i+1 := l ! i] = take i l @ [l ! (i+1), l ! i] @ drop (i+2) l"
proof (induct i arbitrary: l)
  case 0
  then show ?case 
    by (metis One_nat_def add.left_neutral add_lessD1 append_Cons append_Nil drop_update_cancel length_list_update one_add_one plus_1_eq_Suc take0 take_Suc_Cons upd_conv_take_nth_drop zero_less_two)
next
  case (Suc n)
  let ?l = "tl l"
  have "(l[Suc n := l ! (Suc n + 1)])[Suc n + 1 := l ! Suc n] = hd l # (?l[n := ?l ! (n+1)])[n+1 := ?l ! n]"
    by (metis Suc.prems add.commute add_less_same_cancel2 list.collapse list.size(3) list_update_code(3) not_add_less2 nth_Cons_Suc plus_1_eq_Suc)
  have "n + 1 < length ?l" using Suc.prems by auto
  then have "(?l[n := ?l ! (n+1)])[n+1 := ?l ! n] = take n ?l @ [?l ! (n+1), ?l ! n] @ drop (n+2) ?l"
    using Suc.hyps by simp
  then show ?case
    by (cases l) auto
qed

lemma swap_events_perm:
  assumes
    "i < j" and
    "j < length t"
  shows
    "perm (swap_events i j t) t"
proof -
  have swap: "swap_events i j t
      = take i t @ [t ! j, t ! i] @ (take (j - (i+1)) (drop (i+1) t)) @ (drop (j+1) t)"
    by auto
  have reg: "t = take i t @ (take ((j+1) - i) (drop i t)) @ drop (j+1) t" 
    by (metis add_diff_inverse_nat add_lessD1 append.assoc append_take_drop_id assms(1) less_imp_add_positive less_not_refl take_add)
  have "perm (take i t) (take i t)" by simp
  moreover have "perm (drop (j+1) t) (drop (j+1) t)" by simp
  moreover have "perm ([t ! j, t ! i] @ (take (j - (i+1)) (drop (i+1) t))) (take ((j+1) - i) (drop i t))"
  proof -
    let ?l = "take (j - (i+1)) (drop (i+1) t)"
    have "take ((j+1) - i) (drop i t) = t ! i # ?l @ [t ! j]"
    proof -
      have f1: "Suc (j - Suc i) = j - i"
        by (meson Suc_diff_Suc assms(1))
      have f2: "i < length t"
        using assms(1) assms(2) by linarith
      have f3: "j - (i + 1) + (i + 1) = j"
        by (meson assms(1) discrete le_add_diff_inverse2)
      then have "drop (j - (i + 1)) (drop (i + 1) t) = drop j t"
        by (metis drop_drop)
      then show ?thesis
        using f3 f2 f1 by (metis (no_types) Cons_nth_drop_Suc Suc_diff_le Suc_eq_plus1 assms(1) assms(2) hd_drop_conv_nth length_drop less_diff_conv nat_less_le take_Suc_Cons take_hd_drop)
    qed
    then show ?thesis using mset_eq_perm by fastforce
  qed
  ultimately show ?thesis using swap reg 
    by (metis append.assoc perm_append1 perm_append2)
qed

lemma sum_eq_if_same_subterms:
  fixes
    i :: nat
  shows
    "\<forall>k. i \<le> k \<and> k < j \<longrightarrow> f k = f' k \<Longrightarrow> sum f {i..<j} = sum f' {i..<j}"
  by auto

lemma filter_neq_takeWhile:
  assumes
    "filter ((\<noteq>) a) l \<noteq> takeWhile ((\<noteq>) a) l"
  shows
    "\<exists>i j. i < j \<and> j < length l \<and> l ! i = a \<and> l ! j \<noteq> a" (is ?P)
proof (rule ccontr)
  assume "~ ?P"
  then have asm: "\<forall>i j. i < j \<and> j < length l \<longrightarrow> l ! i \<noteq> a \<or> l ! j = a" (is ?Q) by simp
  then have "filter ((\<noteq>) a) l = takeWhile ((\<noteq>) a) l"
  proof (cases "a : set l")
    case False
    then have "\<forall>i. i < length l \<longrightarrow> l ! i \<noteq> a" by auto
    then show ?thesis 
      by (metis (mono_tags, lifting) False filter_True takeWhile_eq_all_conv)
  next
    case True
    then have ex_j: "\<exists>j. j < length l \<and> l ! j = a" 
      by (simp add: in_set_conv_nth)
    let ?j = "Min {j. j < length l \<and> l ! j = a}"
    have fin_j: "finite {j. j < length l \<and> l ! j = a}" 
      using finite_nat_set_iff_bounded by blast
    moreover have "{j. j < length l \<and> l ! j = a} \<noteq> empty" using ex_j by blast
    ultimately have "?j < length l" 
      using Min_less_iff by blast
    have tail_all_a: "\<forall>j. j < length l \<and> j \<ge> ?j \<longrightarrow> l ! j = a"
    proof (rule allI, rule impI)
      fix j
      assume "j < length l \<and> j \<ge> ?j"
      moreover have "\<lbrakk> ?Q; j < length l \<and> j \<ge> ?j \<rbrakk> \<Longrightarrow> \<forall>k. k \<ge> ?j \<and> k \<le> j \<longrightarrow> l ! j = a"
      proof (induct "j - ?j")
        case 0
        then have "j = ?j" using 0 by simp
        then show ?case 
          using Min_in \<open>{j. j < length l \<and> l ! j = a} \<noteq> {}\<close> fin_j by blast
      next
        case (Suc n)
        then have "\<forall>k. k \<ge> ?j \<and> k < j \<longrightarrow> l ! j = a" 
          by (metis (mono_tags, lifting) Min_in \<open>{j. j < length l \<and> l ! j = a} \<noteq> {}\<close> fin_j le_eq_less_or_eq mem_Collect_eq)
        then show ?case 
          using Suc.hyps(2) by auto
      qed
      ultimately show "l ! j = a" using asm by blast
    qed
    moreover have head_all_not_a: "\<forall>i. i < ?j \<longrightarrow> l ! i \<noteq> a" using asm calculation 
      by (metis (mono_tags, lifting) Min_le \<open>Min {j. j < length l \<and> l ! j = a} < length l\<close> fin_j leD less_trans mem_Collect_eq)
    ultimately have "takeWhile ((\<noteq>) a) l = take ?j l"
    proof -
      have "length (takeWhile ((\<noteq>) a) l) = ?j" 
      proof -
        have "length (takeWhile ((\<noteq>) a) l) \<le> ?j" (is ?S)
        proof (rule ccontr)
          assume "\<not> ?S"
          then have "l ! ?j \<noteq> a" 
            by (metis (mono_tags, lifting) not_le_imp_less nth_mem set_takeWhileD takeWhile_nth)
          then show False 
            using \<open>Min {j. j < length l \<and> l ! j = a} < length l\<close> tail_all_a by blast
        qed
        moreover have "length (takeWhile ((\<noteq>) a) l) \<ge> ?j" (is ?T)
        proof (rule ccontr)
          assume "\<not> ?T"
          then have "\<exists>j. j < ?j \<and> l ! j = a" 
            by (metis (mono_tags, lifting) \<open>Min {j. j < length l \<and> l ! j = a} < length l\<close> calculation le_less_trans not_le_imp_less nth_length_takeWhile)
          then show False 
            using head_all_not_a by blast
        qed
        ultimately show ?thesis by simp
      qed
      moreover have "length (take ?j l) = ?j" 
        by (metis calculation takeWhile_eq_take)
      ultimately show ?thesis 
        by (metis takeWhile_eq_take)

    qed
    moreover have "filter ((\<noteq>) a) l = take ?j l"
    proof -
      have "filter ((\<noteq>) a) l = filter ((\<noteq>) a) (take ?j l) @ filter ((\<noteq>) a) (drop ?j l)" 
        by (metis append_take_drop_id filter_append)
      moreover have "filter ((\<noteq>) a) (take ?j l) = take ?j l" using head_all_not_a 
        by (metis \<open>takeWhile ((\<noteq>) a) l = take (Min {j. j < length l \<and> l ! j = a}) l\<close> filter_id_conv set_takeWhileD)
      moreover have "filter ((\<noteq>) a) (drop ?j l) = []"
      proof -
        have "\<forall>j. j \<ge> ?j \<and> j < length l \<longrightarrow> l ! j = drop ?j l ! (j - ?j)" 
          by simp
        then have "\<forall>j. j < length l - ?j \<longrightarrow> drop ?j l ! j = a" using tail_all_a 
          by (metis (no_types, lifting) Groups.add_ac(2) \<open>Min {j. j < length l \<and> l ! j = a} < length l\<close> less_diff_conv less_imp_le_nat not_add_less2 not_le nth_drop)
        then show ?thesis
        proof -
          obtain aa :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a" where
            "\<forall>x0 x1. (\<exists>v2. v2 \<in> set x1 \<and> x0 v2) = (aa x0 x1 \<in> set x1 \<and> x0 (aa x0 x1))"
            by moura
          then have f1: "\<forall>as p. aa p as \<in> set as \<and> p (aa p as) \<or> filter p as = []"
            by (metis (full_types) filter_False)
          obtain nn :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
            f2: "\<forall>x0 x1. (\<exists>v2<length x0. x0 ! v2 = x1) = (nn x0 x1 < length x0 \<and> x0 ! nn x0 x1 = x1)"
          by moura
          { assume "drop (Min {n. n < length l \<and> l ! n = a}) l ! nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) = a"
            then have "filter ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l) = [] \<or> \<not> nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) < length (drop (Min {n. n < length l \<and> l ! n = a}) l) \<or> drop (Min {n. n < length l \<and> l ! n = a}) l ! nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) \<noteq> aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)"
              using f1 by (metis (full_types)) }
          moreover
          { assume "\<not> nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) < length l - Min {n. n < length l \<and> l ! n = a}"
            then have "\<not> nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) < length (drop (Min {n. n < length l \<and> l ! n = a}) l) \<or> drop (Min {n. n < length l \<and> l ! n = a}) l ! nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) \<noteq> aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)"
              by simp }
          ultimately have "filter ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l) = [] \<or> \<not> nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) < length (drop (Min {n. n < length l \<and> l ! n = a}) l) \<or> drop (Min {n. n < length l \<and> l ! n = a}) l ! nn (drop (Min {n. n < length l \<and> l ! n = a}) l) (aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)) \<noteq> aa ((\<noteq>) a) (drop (Min {n. n < length l \<and> l ! n = a}) l)"
            using \<open>\<forall>j<length l - Min {j. j < length l \<and> l ! j = a}. drop (Min {j. j < length l \<and> l ! j = a}) l ! j = a\<close> by blast
          then show ?thesis
            using f2 f1 by (meson in_set_conv_nth)
        qed
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
  then show False using assms by simp
qed

lemma util_exactly_one_element:
  assumes
    "m \<notin> set l" and
    "l' = l @ [m]"
  shows
    "\<exists>!j. j < length l' \<and> l' ! j = m" (is ?P)
proof -
  have "\<forall>j. j < length l' - 1 \<longrightarrow> l' ! j \<noteq> m" 
    by (metis assms(1) assms(2) butlast_snoc length_butlast nth_append nth_mem)
  then have one_j: "\<forall>j. j < length l' \<and> l' ! j = m \<longrightarrow> j = (length l' - 1)"
    by (metis (no_types, hide_lams) diff_Suc_1 lessE)
  show ?thesis
  proof (rule ccontr)
    assume "~ ?P"
    then obtain i j where "i \<noteq> j" "i < length l'" "j < length l'"
                          "l' ! i = m" "l' ! j = m"
      using assms by auto
    then show False using one_j by blast
  qed
qed

lemma exists_one_iff_filter_one:
  shows
    "(\<exists>!j. j < length l \<and> l ! j = a) \<longleftrightarrow> length (filter ((=) a) l) = 1"
proof (rule iffI)
  assume "\<exists>!j. j < length l \<and> l ! j = a"
  then obtain j where "j < length l" "l ! j = a"
    by blast
  moreover have "\<forall>k. k \<noteq> j \<and> k < length l \<longrightarrow> l ! k \<noteq> a" 
    using \<open>\<exists>!j. j < length l \<and> l ! j = a\<close> \<open>j < length l\<close> \<open>l ! j = a\<close> by blast
  moreover have "l = take j l @ [l ! j] @ drop (j+1) l" 
    by (metis Cons_eq_appendI Cons_nth_drop_Suc Suc_eq_plus1 append_self_conv2 append_take_drop_id calculation(1) calculation(2))
  moreover have "filter ((=) a) (take j l) = []"
  proof -
    have "\<forall>k. k < length (take j l) \<longrightarrow> (take j l) ! k \<noteq> a" 
      using calculation(3) by auto
    then show ?thesis 
      by (metis (full_types) filter_False in_set_conv_nth)
  qed
  moreover have "filter ((=) a) (drop (j+1) l) = []"
  proof -
    have "\<forall>k. k < length (drop (j+1) l) \<longrightarrow> (drop (j+1) l) ! k \<noteq> a" 
      using calculation(3) by auto
    then show ?thesis
      by (metis (full_types) filter_False in_set_conv_nth)
  qed
  ultimately show "length (filter ((=) a) l) = 1" 
    by (metis (mono_tags, lifting) One_nat_def Suc_eq_plus1 append_Cons append_self_conv2 filter.simps(2) filter_append list.size(3) list.size(4))
next
  assume asm: "length (filter ((=) a) l) = 1"
  then have "filter ((=) a) l = [a]"
  proof -
    let ?xs = "filter ((=) a) l"
    have "length ?xs = 1"
      using asm by blast
    then show ?thesis 
      by (metis (full_types) Cons_eq_filterD One_nat_def length_0_conv length_Suc_conv)
  qed
  then have "\<exists>j. j < length l \<and> l ! j = a" 
    by (metis (full_types) filter_False in_set_conv_nth list.discI)
  then obtain j where j: "j < length l" "l ! j = a" by blast
  moreover have "\<forall>k. k < length l \<and> k \<noteq> j \<longrightarrow> l ! k \<noteq> a"
  proof (rule allI, rule impI)
    fix k
    assume assm: "k < length l \<and> k \<noteq> j"
    show "l ! k \<noteq> a"
    proof (rule ccontr)
      assume lka: "\<not> l ! k \<noteq> a"
      show False
      proof (cases "k < j")
        let ?xs = "take (k+1) l"
        let ?ys = "drop (k+1) l"
        case True
        then have "length (filter ((=) a) ?xs) > 0" 
          by (metis (full_types, hide_lams) add.commute assm discrete filter_empty_conv length_greater_0_conv length_take less_add_one lka min.absorb2 nth_mem nth_take)
        moreover have "length (filter ((=) a) ?ys) > 0"
        proof -
          have "?ys ! (j - (k+1)) = l ! j" 
            using True assm by auto
          moreover have "j - (k+1) < length ?ys" 
            using True \<open>j < length l\<close> by auto
          ultimately show ?thesis 
            by (metis (full_types) \<open>l ! j = a\<close> filter_empty_conv length_greater_0_conv nth_mem)
        qed
        moreover have "?xs @ ?ys = l" 
          using append_take_drop_id by blast
        ultimately have "length (filter ((=) a) l) > 1" 
          by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 asm filter_append length_append less_add_eq_less less_one nat_neq_iff)
        then show False using asm by simp
      next
        let ?xs = "take (j+1) l"
        let ?ys = "drop (j+1) l"
        case False
        then have "length (filter ((=) a) ?xs) > 0" 
          by (metis (full_types, hide_lams) add.commute j discrete filter_empty_conv length_greater_0_conv length_take less_add_one min.absorb2 nth_mem nth_take)
        moreover have "length (filter ((=) a) ?ys) > 0"
        proof -
          have "?ys ! (k - (j+1)) = l ! k" 
            using False assm by auto
          moreover have "k - (j+1) < length ?ys" 
            using False assm by auto
          ultimately show ?thesis 
            by (metis (full_types) filter_empty_conv length_greater_0_conv lka nth_mem)
        qed
        moreover have "?xs @ ?ys = l" 
          using append_take_drop_id by blast
        ultimately have "length (filter ((=) a) l) > 1" 
          by (metis (no_types, lifting) One_nat_def Suc_eq_plus1 asm filter_append length_append less_add_eq_less less_one nat_neq_iff)
        then show False using asm by simp
      qed
    qed
  qed
  ultimately show "\<exists>!j. j < length l \<and> l ! j = a" by blast
qed

end
