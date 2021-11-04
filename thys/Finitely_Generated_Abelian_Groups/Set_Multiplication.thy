(*
    File:     Set_Multiplication.thy
    Author:   Joseph Thommes, TU München
*)
section \<open>Set Multiplication\<close>

theory Set_Multiplication
  imports "HOL-Algebra.Algebra"
begin

text \<open>This theory/section is of auxiliary nature and is mainly used to establish a connection
between the set multiplication and the multiplication of subgroups via the \<open>IDirProd\<close> (although this
particular notion is introduced later). However, as in every section of this entry, there are some
lemmas that do not have any further usage in this entry, but are of interest just by themselves.\<close>

lemma (in group) set_mult_union:
  "A <#> (B \<union> C) = (A <#> B) \<union> (A <#> C)"
  unfolding set_mult_def by auto

lemma (in group) set_mult_card_single_el_eq:
  assumes "J \<subseteq> carrier G" "x \<in> carrier G"
  shows "card (l_coset G x J) = card J" unfolding l_coset_def
proof -
  have "card ((\<otimes>) x ` J) = card J"
    using inj_on_cmult[of x] card_image[of "(\<otimes>) x" J] assms inj_on_subset[of "(\<otimes>) x" "carrier G" J]
    by blast
  moreover have "(\<Union>y\<in>J. {x \<otimes> y}) = (\<otimes>) x ` J" using image_def[of "(\<otimes>) x" J] by blast
  ultimately show "card (\<Union>h\<in>J. {x \<otimes> h}) = card J" by presburger
qed

text \<open>We find an upper bound for the cardinality of a set product.\<close>

lemma (in group) set_mult_card_le:
  assumes "finite H" "H \<subseteq> carrier G" "J \<subseteq> carrier G"
  shows "card (H <#> J) \<le> card H * card J"
  using assms
proof (induction "card H" arbitrary: H)
  case 0
  then have "H = {}" by force
  then show ?case using set_mult_def[of G H J] by simp
next
  case (Suc n)
  then obtain a where a_def: "a \<in> H" by fastforce
  then have c_n: "card (H - {a}) = n" using Suc by force
  then have "card ((H - {a}) <#> J) \<le> card (H - {a}) * card J" using Suc by blast
  moreover have "card ({a} <#> J) = card J"
    using Suc(4, 5) a_def set_mult_card_single_el_eq[of J a] l_coset_eq_set_mult[of G a J] by auto
  moreover have "H <#> J = (H - {a} <#> J) \<union> ({a} <#> J)" using set_mult_def[of G _ J] a_def by auto
  moreover have "card (H - {a}) * card J + card J = Suc n * card J" using c_n mult_Suc by presburger
  ultimately show ?case using card_Un_le[of "H - {a} <#> J" "{a} <#> J"] c_n \<open>Suc n = card H\<close> by auto
qed

lemma (in group) set_mult_finite:
  assumes "finite H" "finite J" "H \<subseteq> carrier G" "J \<subseteq> carrier G"
  shows "finite (H <#> J)"
  using assms set_mult_def[of G H J] by auto

text \<open>The next lemma allows us to later to derive that two finite subgroups $J$ and $H$ are complementary
if and only if their product has the cardinality $|J| \cdot |H|$.\<close>

lemma (in group) set_mult_card_eq_impl_empty_inter:
  assumes "finite H" "finite J" "H \<subseteq> carrier G" "J \<subseteq> carrier G" "card (H <#> J) = card H * card J"
  shows "\<And>a b. \<lbrakk>a \<in> H; b \<in> H; a \<noteq> b\<rbrakk> \<Longrightarrow> ((\<otimes>) a ` J) \<inter> ((\<otimes>) b ` J) = {}"
  using assms
proof (induction H rule: finite_induct)
  case empty
  then show ?case by fast
next
  case step: (insert x H)
  from step have x_c: "x \<in> carrier G" by simp
  from step have H_c: "H \<subseteq> carrier G" by simp
  from set_mult_card_single_el_eq[of J x] have card_x: "card ({x} <#> J) = card J"
    using \<open>J \<subseteq> carrier G\<close> x_c l_coset_eq_set_mult by metis
  moreover have ins: "(insert x H) <#> J = (H <#> J) \<union> ({x} <#> J)"
    using set_mult_def[of G _ J] by auto
  ultimately have "card (H <#> J) \<ge> card H * card J"
    using card_Un_le[of "H <#> J" "{x} <#> J"] \<open>card (insert x H <#> J) = card (insert x H) * card J\<close>
    by (simp add: step.hyps(1) step.hyps(2))
  then have card_eq:"card (H <#> J) = card H * card J"
    using set_mult_card_le[of H J] step H_c by linarith
  then have ih: "\<And>a b. \<lbrakk>a \<in> H; b \<in> H; a \<noteq> b\<rbrakk> \<Longrightarrow> ((\<otimes>) a ` J) \<inter> ((\<otimes>) b ` J) = {}"
    using step H_c by presburger

  have "card (insert x H) * card J = card H * card J + card J" using \<open>x \<notin> H\<close> using step by simp
  then have "({x} <#> J) \<inter> (H <#> J) = {}"
    using card_eq card_x ins card_Un_Int[of "H <#> J" "{x} <#> J"] step set_mult_finite by auto
  then have "\<And>a. a \<in> H \<Longrightarrow> (\<Union>y\<in>J. {a \<otimes> y}) \<inter> (\<Union>y\<in>J. {x \<otimes> y}) = {}" 
    using set_mult_def[of G _ J] by blast
  then have "\<And>a b. \<lbrakk>a \<in> (insert x H); b \<in> (insert x H); a \<noteq> b\<rbrakk> \<Longrightarrow> ((\<otimes>) a ` J) \<inter> ((\<otimes>) b ` J) = {}"
    using \<open>x \<notin> H\<close> ih by blast
  then show ?case using step by algebra
qed

lemma (in group) set_mult_card_eq_impl_empty_inter':
  assumes "finite H" "finite J" "H \<subseteq> carrier G" "J \<subseteq> carrier G" "card (H <#> J) = card H * card J"
  shows "\<And>a b. \<lbrakk>a \<in> H; b \<in> H; a \<noteq> b\<rbrakk> \<Longrightarrow> (l_coset G a J) \<inter> (l_coset G b J) = {}"
  unfolding l_coset_def
  using set_mult_card_eq_impl_empty_inter image_def[of "(\<otimes>) _" J] assms by blast

lemma (in comm_group) set_mult_comm:
  assumes "H \<subseteq> carrier G" "J \<subseteq> carrier G"
  shows "(H <#> J) = (J <#> H)"
  unfolding set_mult_def
proof -
  have 1: "\<And>a b. \<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> {a \<otimes> b} = {b \<otimes> a}" using m_comm by simp
  then have "\<And>a b.\<lbrakk>a \<in> H; b \<in> J\<rbrakk> \<Longrightarrow> {a \<otimes> b} = {b \<otimes> a}" using assms by auto
  moreover have "\<And>a b.\<lbrakk>b \<in> H; a \<in> J\<rbrakk> \<Longrightarrow> {a \<otimes> b} = {b \<otimes> a}" using assms 1 by auto
  ultimately show "(\<Union>h\<in>H. \<Union>k\<in>J. {h \<otimes> k}) = (\<Union>k\<in>J. \<Union>h\<in>H. {k \<otimes> h})"  by fast
qed

lemma (in group) set_mult_one_imp_inc:
  assumes "\<one> \<in> A" "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "B \<subseteq> (B <#> A)"
proof
  fix x
  assume "x \<in> B"
  thus "x \<in> (B <#> A)" using assms unfolding set_mult_def by force
qed

text \<open>In all cases, we know that the product of two sets is always contained in the subgroup
generated by them.\<close>
lemma (in group) set_mult_subset_generate:
  assumes "A \<subseteq> carrier G" "B \<subseteq> carrier G"
  shows "A <#> B \<subseteq> generate G (A \<union> B)"
proof
  fix x
  assume "x \<in> A <#> B"
  then obtain a b where ab: "a \<in> A" "b \<in> B" "x = a \<otimes> b" unfolding set_mult_def by blast
  then have "a \<in> generate G (A \<union> B)" "b \<in> generate G (A \<union> B)"
    using generate.incl[of _ "A \<union> B" G] by simp+
  thus "x \<in> generate G (A \<union> B)" using ab generate.eng by metis
qed

text \<open>In the case of subgroups, the set product is just the subgroup generated by both
of the subgroups.\<close>

lemma (in comm_group) set_mult_eq_generate_subgroup:
  assumes "subgroup H G" "subgroup J G"
  shows "generate G (H \<union> J) = H <#> J" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R"
  proof
    fix x
    assume "x \<in> ?L"
    then show "x \<in> ?R"
    proof(induction rule: generate.induct)
      case one
      have "\<one> \<otimes> \<one> = \<one>" using nat_pow_one[of 2] by simp
      thus ?case
        using assms subgroup.one_closed[OF assms(1)]
              subgroup.one_closed[OF assms(2)] set_mult_def[of G H J] by fastforce
    next
      case (incl x)
      have H1: "\<one> \<in> H" using assms subgroup.one_closed by auto
      have J1: "\<one> \<in> J" using assms subgroup.one_closed by auto
      have lx: "x \<otimes> \<one> = x" using r_one[of x] incl subgroup.subset assms by blast
      have rx: "\<one> \<otimes> x = x" using l_one[of x] incl subgroup.subset assms by blast
      show ?case
      proof (cases "x \<in> H")
        case True
        then show ?thesis using set_mult_def J1 lx by fastforce
      next
        case False
        then show ?thesis using set_mult_def H1 rx incl by fastforce
      qed
    next
      case (inv h)
      then have inv_in:"(inv h) \<in> H \<union> J" (is "?iv \<in> H \<union> J")
        using assms subgroup.m_inv_closed[of _ G h] by (cases "h \<in> H"; blast)
      have H1: "\<one> \<in> H" using assms subgroup.one_closed by auto
      have J1: "\<one> \<in> J" using assms subgroup.one_closed by auto
      have lx: "?iv \<otimes> \<one> = ?iv" using r_one[of "?iv"] subgroup.subset inv_in assms by blast
      have rx: "\<one> \<otimes> ?iv = ?iv" using l_one[of "?iv"] incl subgroup.subset inv_in assms by blast
      show ?case 
      proof (cases "?iv \<in> H")
        case True
        then show ?thesis using set_mult_def[of G H J] J1 lx by fastforce
      next
        case False
        then show ?thesis using set_mult_def[of G H J] H1 rx inv_in by fastforce
      qed
    next
      case (eng h g)
      from eng(3) obtain a b where aH: "a \<in> H" and bJ: "b \<in> J" and h_def: "h = a \<otimes> b"
        using set_mult_def[of G H J] by fast
      have a_carr: "a \<in> carrier G" by (metis subgroup.mem_carrier assms(1) aH)
      have b_carr: "b \<in> carrier G" by (metis subgroup.mem_carrier assms(2) bJ)
      from eng(4) obtain c d where cH: "c \<in> H" and dJ: "d \<in> J" and g_def: "g = c \<otimes> d"
        using set_mult_def[of G H J] by fast
      have c_carr: "c \<in> carrier G" by (metis subgroup.mem_carrier assms(1) cH)
      have d_carr: "d \<in> carrier G" by (metis subgroup.mem_carrier assms(2) dJ)
      then have "h \<otimes> g = (a \<otimes> c) \<otimes> (b \<otimes> d)"
        using a_carr b_carr c_carr d_carr g_def h_def m_assoc m_comm by force
      moreover have "a \<otimes> c \<in> H" using assms(1) aH cH subgroup.m_closed by fast
      moreover have "b \<otimes> d \<in> J" using assms(2) bJ dJ subgroup.m_closed by fast
      ultimately show ?case using set_mult_def by fast
    qed
  qed
next
  show "?R \<subseteq> ?L" using set_mult_subset_generate[of H J] subgroup.subset assms by blast
qed

end