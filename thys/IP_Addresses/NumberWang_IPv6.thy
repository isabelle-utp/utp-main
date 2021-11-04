theory NumberWang_IPv6
imports 
  Word_Lib.Word_Lemmas
  Word_Lib.Word_Syntax
  Word_Lib.Reversed_Bit_Lists
begin

section\<open>Helper Lemmas for Low-Level Operations on Machine Words\<close>
text\<open>Needed for IPv6 Syntax\<close>

lemma length_drop_bl: "length (dropWhile Not (to_bl (of_bl bs))) \<le> length bs"
proof -
  have length_takeWhile_Not_replicate_False:
    "length (takeWhile Not (replicate n False @ ls)) = n + length (takeWhile Not ls)"
  for n ls by(subst takeWhile_append2) simp+
  show ?thesis by(simp add: word_rep_drop dropWhile_eq_drop length_takeWhile_Not_replicate_False)
qed

lemma bl_drop_leading_zeros: 
      "(of_bl:: bool list \<Rightarrow> 'a::len word) (dropWhile Not bs) =
       (of_bl:: bool list \<Rightarrow> 'a::len word) bs"
by(induction bs) simp_all


lemma bl_length_drop_bound: assumes "length (dropWhile Not bs) \<le> n"
  shows "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs))) \<le> n"
proof -
  have bl_length_drop_twice: 
      "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) (dropWhile Not bs)))) =
       length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs)))"
    by(simp add: bl_drop_leading_zeros)
  from length_drop_bl
  have *: "length (dropWhile Not (to_bl ((of_bl:: bool list \<Rightarrow> 'a::len word) bs))) \<le> length (dropWhile Not bs)"
   apply(rule dual_order.trans)
   apply(subst bl_length_drop_twice)
   ..
  show ?thesis
  apply(rule order.trans, rule *)
  using assms by(simp)
qed

lemma length_drop_mask_outer: fixes ip::"'a::len word"
  shows "LENGTH('a) - n' = len \<Longrightarrow> length (dropWhile Not (to_bl (ip AND (mask n << n') >> n'))) \<le> len"
  apply(subst word_and_mask_shiftl)
  apply(subst shiftl_shiftr1)
   apply(simp; fail)
  apply(simp)
  apply(subst and_mask)
  apply(simp add: word_size)
  apply(simp add: length_drop_mask)
  done
lemma length_drop_mask_inner: fixes ip::"'a::len word"
  shows "n \<le> LENGTH('a) - n' \<Longrightarrow> length (dropWhile Not (to_bl (ip AND (mask n << n') >> n'))) \<le> n"
  apply(subst word_and_mask_shiftl)
  apply(subst shiftl_shiftr3)
   apply(simp; fail)
  apply(simp)
  apply(simp add: word_size)
  apply(simp add: mask_twice)
  apply(simp add: length_drop_mask)
  done


lemma mask128: "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF = (mask 128 :: 'a::len word)"
  by (simp add: mask_eq)


(*-------------- things for ipv6 syntax round trip property two ------------------*)

(*n small, m large*)
lemma helper_masked_ucast_generic:
  fixes b::"16 word"
  assumes "n + 16 \<le> m" and "m < 128"
  shows "((ucast:: 16 word \<Rightarrow> 128 word) b << n) && (mask 16 << m) = 0"
proof -
  have "x < 2 ^ (m - n)" if mnh2: "x < 0x10000"
    for x::"128 word"
  proof -
    from assms(1) have mnh3: "16 \<le> m - n" by fastforce
    have power_2_16_nat: "(16::nat) \<le> n \<Longrightarrow> (65535::nat) < 2 ^ n" if a:"16 \<le> n"for n
    proof -
      have power2_rule: "a \<le> b \<Longrightarrow> (2::nat)^a \<le> 2 ^ b" for a b by fastforce
      show ?thesis
       apply(subgoal_tac "65536 \<le> 2 ^ n")
        apply(subst Nat.less_eq_Suc_le)
        apply(simp; fail)
       apply(subgoal_tac "(65536::nat) = 2^16")
        subgoal using power2_rule \<open>16 \<le> n\<close> by presburger
       by(simp)
    qed
    have "65536 = unat (65536::128 word)" by auto
    moreover from mnh2 have "unat x <  unat (65536::128 word)" by(rule Word.unat_mono)
    ultimately have x: "unat x < 65536" by simp
    with mnh3 have "unat x < 2 ^ (m - n)" 
      apply(rule_tac b=65535 in Orderings.order_class.order.strict_trans1)
       apply(simp_all)
      using power_2_16_nat apply blast
      done
    with assms(2) show ?thesis by(subst word_less_nat_alt) simp
  qed
  hence mnhelper2: "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) < 2 ^ (m - n)"
    apply(subgoal_tac "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) < 2^(LENGTH(16))")
     apply(simp; fail)
    by(rule of_bl_length_less) simp+
  have mnhelper3: "(of_bl::bool list \<Rightarrow> 128 word) (to_bl b) * 2 ^ n < 2 ^ m"
    apply(rule div_lt_mult)
     apply(rule word_less_two_pow_divI)
       using assms by(simp_all add: mnhelper2 p2_gt_0)

  from assms show ?thesis
    apply(subst ucast_bl)+
    apply(subst shiftl_of_bl)
    apply(subst of_bl_append)
    apply simp
    apply(subst word_and_mask_shiftl)
    apply(subst shiftr_div_2n_w)
     subgoal by(simp add: word_size; fail)
    apply(subst word_div_less)
     subgoal by(rule mnhelper3)
    apply simp
    done
qed


lemma unat_of_bl_128_16_less_helper:
  fixes b::"16 word"
  shows "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2^16"
proof -
  from word_bl_Rep' have 1: "length (to_bl b) = 16" by simp
  have "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2^(length (to_bl b))"
    by(fact unat_of_bl_length)
  with 1 show ?thesis by auto
qed
lemma unat_of_bl_128_16_le_helper: "unat ((of_bl:: bool list \<Rightarrow> 128 word) (to_bl (b::16 word))) \<le> 65535"
proof -
  from unat_of_bl_128_16_less_helper[of b] have
    "unat ((of_bl:: bool list \<Rightarrow> 128 word) (to_bl b)) < 65536" by simp 
  from Suc_leI[OF this] show ?thesis by simp
qed


(*reverse*)
 lemma helper_masked_ucast_reverse_generic:
   fixes b::"16 word"
   assumes "m + 16 \<le> n" and "n \<le> 128 - 16"
   shows "((ucast:: 16 word \<Rightarrow> 128 word) b << n) && (mask 16 << m) = 0"
 proof -

   have power_less_128_helper: "2 ^ n * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) < 2 ^ LENGTH(128)"
     if n: "n \<le> 128 - 16" for n
   proof -
     have help_mult: "n \<le> l \<Longrightarrow> 2 ^ n * x < 2 ^ l \<longleftrightarrow> x < 2 ^ (l - n)" for x::nat and l
       by (simp add: nat_mult_power_less_eq semiring_normalization_rules(7))
     from n show ?thesis
       apply(subst help_mult)
        subgoal by (simp)
       apply(rule order_less_le_trans)
        apply(rule unat_of_bl_128_16_less_helper)
       apply(rule Power.power_increasing)
        apply(simp_all)
       done
   qed

   have *: "2 ^ m * (2 ^ (n - m) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b))) = 
            2 ^ n * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b))"
   proof(cases "unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) = 0")
   case True thus ?thesis by simp
   next
   case False
    have help_mult: "x \<noteq> 0 \<Longrightarrow> b * (c * x) = a * (x::nat)  \<longleftrightarrow> b * c = a" for x a b c by simp
    from assms show ?thesis
     apply(subst help_mult[OF False])
     apply(subst Power.monoid_mult_class.power_add[symmetric])
     apply(simp)
     done
   qed

  from assms have "unat ((2 ^ n)::128 word) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) mod 2 ^ LENGTH(128) =
        2 ^ m * (2 ^ (n - m) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) mod 2 ^ LENGTH(128))"
     apply(subst nat_mod_eq')
      subgoal apply(subst unat_power_lower)
       subgoal by(simp; fail)
      subgoal by (rule power_less_128_helper) simp
      done
     apply(subst nat_mod_eq')
      subgoal by(rule power_less_128_helper) simp
     apply(subst unat_power_lower)
      apply(simp; fail)
     apply(simp only: *)
     done
   hence ex_k: "\<exists>k. unat ((2 ^ n)::128 word) * unat ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b)) mod 2 ^ LENGTH(128) = 2 ^ m * k"
     by blast

   hence aligned: "is_aligned ((of_bl::bool list \<Rightarrow> 128 word) (to_bl b) << n) m"
     unfolding is_aligned_iff_dvd_nat
     unfolding dvd_def
     unfolding shiftl_t2n
     unfolding Word.unat_word_ariths(2)
     by assumption

   from assms have of_bl_to_bl_shift_mask: "((of_bl::bool list \<Rightarrow> 128 word) (to_bl b) << n) && mask (16 + m) = 0"
    using is_aligned_mask is_aligned_shiftl by force (*sledgehammer*)

   show ?thesis
    apply(subst ucast_bl)+
    apply(subst word_and_mask_shiftl)
    apply(subst aligned_shiftr_mask_shiftl)
     subgoal by (fact aligned)
    subgoal by (fact of_bl_to_bl_shift_mask)
    done
qed


lemma helper_masked_ucast_equal_generic:
  fixes b::"16 word"
  assumes "n \<le> 128 - 16"
  shows "ucast (((ucast:: 16 word \<Rightarrow> 128 word) b << n) && (mask 16 << n) >> n) = b"
proof -
  have ucast_mask: "(ucast:: 16 word \<Rightarrow> 128 word) b && mask 16 = ucast b" 
    by transfer (simp flip: take_bit_eq_mask)
  from assms have "ucast (((ucast:: 16 word \<Rightarrow> 128 word) b && mask (128 - n) && mask 16) && mask (128 - n)) = b"
    by (auto simp add: nth_ucast word_size intro: word_eqI)
  thus ?thesis
  apply(subst word_and_mask_shiftl)
  apply(subst shiftl_shiftr3)
   apply(simp; fail)
  apply(simp)
  apply(subst shiftl_shiftr3)
    apply(simp_all add: word_size and.assoc)
  done
qed

end
