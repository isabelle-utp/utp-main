(*
    File:     Miscellaneous_Groups.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Miscellaneous group facts\<close>

theory Miscellaneous_Groups
  imports Set_Multiplication
begin

text \<open>As the name suggests, this section contains several smaller lemmas about groups.\<close>

(* Manuel Eberl *)
lemma (in subgroup) nat_pow_closed [simp,intro]: "a \<in> H \<Longrightarrow> pow G a (n::nat) \<in> H"
  by (induction n) (auto simp: nat_pow_def)

(* Manuel Eberl *)
lemma nat_pow_modify_carrier: "a [^]\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> b = a [^]\<^bsub>G\<^esub> (b::nat)"
  by (simp add: nat_pow_def)

lemma (in group) subgroup_card_dvd_group_ord:
  assumes "subgroup H G"
  shows "card H dvd order G"
  using Coset.group.lagrange[of G H] assms group_axioms by (metis dvd_triv_right)

lemma (in group) subgroup_card_eq_order:
  assumes "subgroup H G"
  shows "card H = order (G\<lparr>carrier := H\<rparr>)"
  unfolding order_def by simp

lemma (in group) finite_subgroup_card_neq_0:
  assumes "subgroup H G" "finite H"
  shows "card H \<noteq> 0"
  using subgroup_nonempty assms by auto

lemma (in group) subgroup_order_dvd_group_order:
  assumes "subgroup H G"
  shows "order (G\<lparr>carrier := H\<rparr>) dvd order G"
  by (metis subgroup_card_dvd_group_ord[of H] assms subgroup_card_eq_order)

lemma (in group) sub_subgroup_dvd_card:
  assumes "subgroup H G" "subgroup J G" "J \<subseteq> H"
  shows "card J dvd card H"
  by (metis subgroup_incl[of J H] subgroup_card_eq_order[of H]
            group.subgroup_card_dvd_group_ord[of "(G\<lparr>carrier := H\<rparr>)" J] assms
            subgroup.subgroup_is_group[of H G] group_axioms)

lemma (in group) inter_subgroup_dvd_card:
  assumes "subgroup H G" "subgroup J G"
  shows "card (H \<inter> J) dvd card H"
  using subgroups_Inter_pair[of H J] assms sub_subgroup_dvd_card[of H "H \<inter> J"] by blast

lemma (in group) subgroups_card_coprime_inter_card_one:
  assumes "subgroup H G" "subgroup J G" "coprime (card H) (card J)"
  shows "card (H \<inter> J) = 1"
proof -
  from assms inter_subgroup_dvd_card have "is_unit (card (H \<inter> J))" unfolding coprime_def
    by (meson Int_lower2 sub_subgroup_dvd_card subgroup_Int)
  then show ?thesis by simp
qed

lemma (in group) coset_neq_imp_empty_inter:
  assumes "subgroup H G" "a \<in> carrier G" "b \<in> carrier G"
  shows "H #> a \<noteq> H #> b \<Longrightarrow> (H #> a) \<inter> (H #> b) = {}"
  by (metis Int_emptyI assms repr_independence)

lemma (in comm_group) subgroup_is_comm_group:
  assumes "subgroup H G"
  shows "comm_group (G\<lparr>carrier := H\<rparr>)" unfolding comm_group_def
proof
  interpret H: subgroup H G by fact
  interpret H: submonoid H G using H.subgroup_is_submonoid .
  show "Group.group (G\<lparr>carrier := H\<rparr>)" by blast
  show "comm_monoid (G\<lparr>carrier := H\<rparr>)" using submonoid_is_comm_monoid H.submonoid_axioms by blast
qed

lemma (in group) pow_int_mod_ord:
  assumes [simp]:"a \<in> carrier G" "ord a \<noteq> 0"
  shows "a [^] (n::int) = a [^] (n mod ord a)"
proof -
  obtain q r where d: "q = n div ord a" "r = n mod ord a" "n = q * ord a + r"
    using mod_div_decomp by blast
  hence "a [^] n = (a [^] int (ord a)) [^] q \<otimes> a [^] r"
    using assms(1) int_pow_mult int_pow_pow
    by (metis mult_of_nat_commute)
  also have "\<dots> = \<one> [^] q \<otimes> a [^] r"
    by (simp add: int_pow_int)
  also have "\<dots> = a [^] r" by simp
  finally show ?thesis using d(2) by blast
qed

lemma (in group) pow_nat_mod_ord:
  assumes [simp]:"a \<in> carrier G" "ord a \<noteq> 0"
  shows "a [^] (n::nat) = a [^] (n mod ord a)"
proof -
  obtain q r where d: "q = n div ord a" "r = n mod ord a" "n = q * ord a + r"
    using mod_div_decomp by blast
  hence "a [^] n = (a [^] ord a) [^] q \<otimes> a [^] r"
    using assms(1) nat_pow_mult nat_pow_pow by presburger
  also have "\<dots> = \<one> [^] q \<otimes> a [^] r" by auto
  also have "\<dots> = a [^] r" by simp
  finally show ?thesis using d(2) by blast
qed

lemma (in group) ord_min:
  assumes "m \<ge> 1" "x \<in> carrier G" "x [^] m = \<one>"
  shows   "ord x \<le> m"
  using assms pow_eq_id by auto

(* Manuel Eberl *)
lemma (in group) bij_betw_mult_left[intro]:
  assumes [simp]: "x \<in> carrier G"
  shows "bij_betw (\<lambda>y. x \<otimes> y) (carrier G) (carrier G)"
  by (intro bij_betwI[where ?g = "\<lambda>y. inv x \<otimes> y"])
     (auto simp: m_assoc [symmetric])

(* Manuel Eberl *)
lemma (in subgroup) inv_in_iff:
  assumes "x \<in> carrier G" "group G"
  shows   "inv x \<in> H \<longleftrightarrow> x \<in> H"
proof safe
  assume "inv x \<in> H"
  hence "inv (inv x) \<in> H" by blast
  also have "inv (inv x) = x"
    by (intro group.inv_inv) (use assms in auto)
  finally show "x \<in> H" .
qed auto

(* Manuel Eberl *)
lemma (in subgroup) mult_in_cancel_left:
  assumes "y \<in> carrier G" "x \<in> H" "group G"
  shows   "x \<otimes> y \<in> H \<longleftrightarrow> y \<in> H"
proof safe
  assume "x \<otimes> y \<in> H"
  hence "inv x \<otimes> (x \<otimes> y) \<in> H"
    using assms by blast
  also have "inv x \<otimes> (x \<otimes> y) = y"
    using assms by (simp add: \<open>x \<otimes> y \<in> H\<close> group.inv_solve_left')
  finally show "y \<in> H" .
qed (use assms in auto)

(* Manuel Eberl *)
lemma (in subgroup) mult_in_cancel_right:
  assumes "x \<in> carrier G" "y \<in> H" "group G"
  shows   "x \<otimes> y \<in> H \<longleftrightarrow> x \<in> H"
proof safe
  assume "x \<otimes> y \<in> H"
  hence "(x \<otimes> y) \<otimes> inv y \<in> H"
    using assms by blast
  also have "(x \<otimes> y) \<otimes> inv y = x"
    using assms by (simp add: \<open>x \<otimes> y \<in> H\<close> group.inv_solve_right')
  finally show "x \<in> H" .
qed (use assms in auto)

lemma (in group) (* Manuel Eberl *)
  assumes "x \<in> carrier G" and "x [^] n = \<one>" and "n > 0"
  shows   ord_le: "ord x \<le> n" and ord_pos: "ord x > 0"
proof -
  have "ord x dvd n"
    using pow_eq_id[of x n] assms by auto
  thus "ord x \<le> n" "ord x > 0"
    using assms by (auto intro: dvd_imp_le)
qed

lemma (in group) ord_conv_Least: (* Manuel Eberl *)
  assumes "x \<in> carrier G" "\<exists>n::nat > 0. x [^] n = \<one>"
  shows   "ord x = (LEAST n::nat. 0 < n \<and> x [^] n = \<one>)"
proof (rule antisym)
  show "ord x \<le> (LEAST n::nat. 0 < n \<and> x [^] n = \<one>)"
    using assms LeastI_ex[OF assms(2)] by (intro ord_le) auto
  show "ord x \<ge> (LEAST n::nat. 0 < n \<and> x [^] n = \<one>)"
    using assms by (intro Least_le) (auto intro: pow_ord_eq_1 ord_pos)
qed

lemma (in group) ord_conv_Gcd: (* Manuel Eberl *)
  assumes "x \<in> carrier G"
  shows   "ord x = Gcd {n. x [^] n = \<one>}"
  by (rule sym, rule Gcd_eqI) (use assms in \<open>auto simp: pow_eq_id\<close>)

lemma (in group) subgroup_ord_eq:
  assumes "subgroup H G" "x \<in> H"
  shows "group.ord (G\<lparr>carrier := H\<rparr>) x = ord x"
  using nat_pow_consistent ord_def group.ord_def[of "(G\<lparr>carrier := H\<rparr>)" x]
        subgroup.subgroup_is_group[of H G] assms by simp

lemma (in group) ord_FactGroup:
  assumes "subgroup P G" "group (G Mod P)"
  shows "order (G Mod P) * card P = order G"
  using lagrange[of P] FactGroup_def[of G P] assms order_def[of "(G Mod P)"] by fastforce

lemma (in group) one_is_same:
  assumes "subgroup H G"
  shows "\<one>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> = \<one>"
  by simp

lemma (in group) kernel_FactGroup:
  assumes "P \<lhd> G"
  shows "kernel G (G Mod P) (\<lambda>x. P #> x) = P"
proof(rule equalityI; rule subsetI)
  fix x
  assume "x \<in> kernel G (G Mod P) ((#>) P)"
  then have "P #> x = \<one>\<^bsub>G Mod P\<^esub>" "x \<in> carrier G" unfolding kernel_def by simp+
  with coset_join1[of P x] show "x \<in> P" using assms unfolding normal_def by simp
next
  fix x
  assume x:"x \<in> P"
  then have xc: "x \<in> carrier G" using assms subgroup.subset unfolding normal_def by fast
  from x have "P #> x = P" using assms
    by (simp add: normal_imp_subgroup subgroup.rcos_const) 
  thus "x \<in> kernel G (G Mod P) ((#>) P)" unfolding kernel_def using xc by simp
qed

lemma (in group) sub_subgroup_coprime:
  assumes "subgroup H G" "subgroup J G" "coprime (card H) (card J)"
  and "subgroup sH G" "subgroup sJ G" "sH \<subseteq> H" "sJ \<subseteq> J"
shows "coprime (card sH) (card sJ)"
  using assms by (meson coprime_divisors sub_subgroup_dvd_card)

lemma (in group) pow_eq_nat_mod:
  assumes "a \<in> carrier G" "a [^] n = a [^] m"
  shows "n mod (ord a) = m mod (ord a)"
proof -
  from assms have "a [^] (n - m) = \<one>" using pow_eq_div2 by blast
  hence "ord a dvd n - m" using assms(1) pow_eq_id by blast
  thus ?thesis
    by (metis assms mod_eq_dvd_iff_nat nat_le_linear pow_eq_div2 pow_eq_id)
qed

lemma (in group) pow_eq_int_mod:
  fixes n m::int
  assumes "a \<in> carrier G" "a [^] n = a [^] m"
  shows "n mod (ord a) = m mod (ord a)"
proof -
  from assms have "a [^] (n - m) = \<one>" using int_pow_closed int_pow_diff r_inv by presburger
  hence "ord a dvd n - m" using assms(1) int_pow_eq_id by blast
  thus ?thesis by (meson mod_eq_dvd_iff)
qed

end