section \<open>An ordinal partition theorem by Jean A. Larson\<close>

text \<open>Jean A. Larson,
     A short proof of a partition theorem for the ordinal $\omega^\omega$.
     \emph{Annals of Mathematical Logic}, 6:129–145, 1973.\<close>

theory Omega_Omega
  imports "HOL-Library.Product_Lexorder" Erdos_Milner

begin

abbreviation "list_of \<equiv> sorted_list_of_set"

subsection \<open>Cantor normal form for ordinals below @{term "\<omega>\<up>\<omega>"}\<close>

text \<open>Unlike @{term Cantor_sum}, there is no list of ordinal exponents,
which are instead taken as consecutive. We obtain an order-isomorphism between @{term "\<omega>\<up>\<omega>"}
and increasing lists of natural numbers (ordered lexicographically).\<close>

fun omega_sum_aux  where
  Nil: "omega_sum_aux 0 _ = 0"
| Suc: "omega_sum_aux (Suc n) [] = 0"
| Cons: "omega_sum_aux (Suc n) (m#ms) = (\<omega>\<up>n) * (ord_of_nat m) + omega_sum_aux n ms"

abbreviation omega_sum where "omega_sum ms \<equiv> omega_sum_aux (length ms) ms"

text \<open>A normal expansion has no leading zeroes\<close>
primrec normal:: "nat list \<Rightarrow> bool" where
  normal_0: "normal [] = True"
| normal_Suc: "normal (m#ms) = (m > 0)"

lemma omega_sum_0_iff [simp]: "normal ns \<Longrightarrow> omega_sum ns = 0 \<longleftrightarrow> ns = []"
  by (induction ns) auto

lemma Ord_omega_sum_aux [simp]: "Ord (omega_sum_aux k ms)"
  by (induction rule: omega_sum_aux.induct) auto

lemma Ord_omega_sum: "Ord (omega_sum ms)"
  by simp

lemma omega_sum_less_\<omega>\<omega> [intro]: "omega_sum ms < \<omega>\<up>\<omega>"
proof (induction ms)
  case Nil
  then show ?case
    by (auto simp: zero_less_Limit)
next
  case (Cons m ms)
  have "\<omega> \<up> (length ms) * ord_of_nat m \<in> elts (\<omega> \<up> Suc (length ms))"
    using Ord_mem_iff_lt by auto
  then have "\<omega>\<up>(length ms) * ord_of_nat m \<in> elts (\<omega>\<up>\<omega>)"
    using Ord_ord_of_nat oexp_mono_le omega_nonzero ord_of_nat_le_omega by blast
  with Cons show ?case
    by (auto simp: mult_succ OrdmemD oexp_less indecomposableD indecomposable_\<omega>_power)
qed

lemma omega_sum_aux_less: "omega_sum_aux k ms < \<omega> \<up> k"
proof (induction rule: omega_sum_aux.induct)
  case (3 n m ms)
  have " \<omega>\<up>n * ord_of_nat m + \<omega>\<up>n < \<omega>\<up>n * \<omega>"
    by (metis Ord_ord_of_nat \<omega>_power_succ_gtr mult_succ oexp_succ ord_of_nat.simps(2))
  with 3 show ?case
    using dual_order.strict_trans by force
qed auto

lemma omega_sum_less: "omega_sum ms < \<omega> \<up> (length ms)"
  by (rule omega_sum_aux_less)

lemma omega_sum_ge: "m \<noteq> 0 \<Longrightarrow> \<omega> \<up> (length ms) \<le> omega_sum (m#ms)"
  apply clarsimp
  by (metis Ord_ord_of_nat add_le_cancel_left0 le_mult Nat.neq0_conv ord_of_eq_0_iff vsubsetD)

lemma omega_sum_length_less:
  assumes "length ms < length ns" "normal ns"
  shows "omega_sum ms < omega_sum ns"
proof (cases ns)
  case Nil
  then show ?thesis
    using assms by auto
next
  case (Cons n ns')
  have "\<omega> \<up> length ms \<le> \<omega> \<up> length ns'"
    using assms local.Cons by (simp add: oexp_mono_le)
  then have "\<not> omega_sum (n#ns') \<le> omega_sum ms"
    using omega_sum_ge [of n ns'] omega_sum_less [of ms] \<open>normal ns\<close> local.Cons by auto
  then show ?thesis
    by (metis Ord_linear2 Ord_omega_sum local.Cons)
qed

lemma omega_sum_length_leD:
  assumes "omega_sum ms \<le> omega_sum ns" "normal ms"
  shows "length ms \<le> length ns"
  by (meson assms leD leI omega_sum_length_less)


lemma omega_sum_less_eqlen_iff_cases [simp]:
  assumes "length ms = length ns"
   shows "omega_sum (m#ms) < omega_sum (n#ns)
          \<longleftrightarrow> m<n \<or> m=n \<and> omega_sum ms < omega_sum ns"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  have "\<not> Suc n < Suc m"
    using omega_sum_less [of ms] omega_sum_less [of ns] L assms mult_nat_less_add_less by fastforce
  then have "m\<le>n"
    by auto
  with L assms show ?rhs
    by auto
next
  assume ?rhs
  then show ?lhs
    by (auto simp: mult_nat_less_add_less omega_sum_aux_less assms)
qed

lemma omega_sum_lex_less_iff_cases:
   "((length ms, omega_sum (m#ms)), (length ns, omega_sum (n#ns))) \<in> less_than <*lex*> VWF
   \<longleftrightarrow> length ms < length ns
            \<or> length ms = length ns \<and> m<n
            \<or> m=n \<and> ((length ms, omega_sum ms), (length ns, omega_sum ns)) \<in> less_than <*lex*> VWF"
  using omega_sum_less_eqlen_iff_cases by force

lemma omega_sum_less_iff_cases:
  assumes "m > 0" "n > 0"
  shows "omega_sum (m#ms) < omega_sum (n#ns)
          \<longleftrightarrow> length ms < length ns
            \<or> length ms = length ns \<and> m<n
            \<or> length ms = length ns \<and> m=n \<and> omega_sum ms < omega_sum ns"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then have "length ms \<le> length ns"
    using omega_sum_length_leD [OF less_imp_le [OF L]] by (simp add: \<open>m > 0\<close>)
  moreover have "m\<le>n" if "length ms = length ns"
    using L omega_sum_less_eqlen_iff_cases that by auto
  ultimately show ?rhs
    using L by auto
next
  assume ?rhs
  moreover
  have "omega_sum (m # ms) < omega_sum (n # ns)"
    if "length ms < length ns"
    using that by (metis Suc_mono \<open>n > 0\<close> length_Cons normal_Suc omega_sum_length_less)
  ultimately show ?lhs
    using omega_sum_less_eqlen_iff_cases by force
qed

lemma omega_sum_less_iff:
  "((length ms, omega_sum ms), (length ns, omega_sum ns)) \<in> less_than <*lex*> VWF
   \<longleftrightarrow> (ms,ns) \<in> lenlex less_than"
proof (induction ms arbitrary: ns)
  case Nil
  then show ?case
    by auto
next
  case (Cons m ms)
  then show ?case
  proof (induction ns)
    case (Cons n ns')
    show ?case
      using omega_sum_lex_less_iff_cases [of ms m ns' n] Cons.prems
      by (simp add: Cons_lenlex_iff lenlex_length order.not_eq_order_implies_strict nat_less_le)
  qed auto
qed

lemma eq_omega_sum_less_iff:
  assumes "length ms = length ns"
  shows "(omega_sum ms, omega_sum ns) \<in> VWF \<longleftrightarrow> (ms,ns) \<in> lenlex less_than"
  by (metis assms in_lex_prod less_not_refl less_than_iff omega_sum_less_iff)

lemma eq_omega_sum_eq_iff:
  assumes "length ms = length ns"
  shows "omega_sum ms = omega_sum ns \<longleftrightarrow> ms=ns"
proof
  assume "omega_sum ms = omega_sum ns"
  then have "(omega_sum ms, omega_sum ns) \<notin> VWF" "(omega_sum ns, omega_sum ms) \<notin> VWF"
    by auto
  then obtain "(ms,ns) \<notin> lenlex less_than" "(ns,ms) \<notin> lenlex less_than"
    using assms eq_omega_sum_less_iff by metis
  moreover have "total (lenlex less_than)"
    by (simp add: total_lenlex total_less_than)
  ultimately show "ms=ns"
    by (meson UNIV_I total_on_def)
qed auto

lemma inj_omega_sum: "inj_on omega_sum {l. length l = n}"
  unfolding inj_on_def using eq_omega_sum_eq_iff by fastforce

lemma Ex_omega_sum: "\<gamma> \<in> elts (\<omega>\<up>n) \<Longrightarrow> \<exists>ns. \<gamma> = omega_sum ns \<and> length ns = n"
proof (induction n arbitrary: \<gamma>)
  case 0
  then show ?case
    by (rule_tac x="[]" in exI) auto
next
  case (Suc n)
  then obtain k::nat where k: "\<gamma> \<in> elts (\<omega> \<up> n * k)"
       and kmin: "\<And>k'. k'<k \<Longrightarrow> \<gamma> \<notin> elts (\<omega> \<up> n * k')"
    by (metis Ord_ord_of_nat elts_mult_\<omega>E oexp_succ ord_of_nat.simps(2))
  show ?case
  proof (cases k)
    case (Suc k')
    then obtain \<delta> where \<delta>: "\<gamma> = (\<omega> \<up> n * k') + \<delta>"
      by (metis lessI mult_succ ord_of_nat.simps(2) k kmin mem_plus_V_E)
    then have \<delta>in: "\<delta> \<in> elts (\<omega> \<up> n)"
      using Suc k mult_succ by auto
    then obtain ns where ns: "\<delta> = omega_sum ns" and len: "length ns = n"
      using Suc.IH by auto
    moreover have "omega_sum ns < \<omega>\<up>n"
      using OrdmemD ns \<delta>in by auto
    ultimately show ?thesis
      by (rule_tac x="k'#ns" in exI) (simp add: \<delta>)
  qed (use k in auto)
qed

lemma omega_sum_drop [simp]: "omega_sum (dropWhile (\<lambda>n. n=0) ns) = omega_sum ns"
  by (induction ns) auto

lemma normal_drop [simp]: "normal (dropWhile (\<lambda>n. n=0) ns)"
  by (induction ns) auto

lemma omega_sum_\<omega>\<omega>:
  assumes "\<gamma> \<in> elts (\<omega>\<up>\<omega>)"
  obtains ns where "\<gamma> = omega_sum ns" "normal ns"
proof -
  obtain ms where "\<gamma> = omega_sum ms"
    using assms Ex_omega_sum by (auto simp: oexp_Limit elts_\<omega>)
  show thesis
  proof
    show "\<gamma> = omega_sum (dropWhile (\<lambda>n. n=0) ms)"
      by (simp add: \<open>\<gamma> = omega_sum ms\<close>)
    show "normal (dropWhile (\<lambda>n. n=0) ms)"
      by auto
  qed
qed

definition Cantor_\<omega>\<omega> :: "V \<Rightarrow> nat list"
  where "Cantor_\<omega>\<omega> \<equiv> \<lambda>x. SOME ns. x = omega_sum ns \<and> normal ns"

lemma
  assumes "\<gamma> \<in> elts (\<omega>\<up>\<omega>)"
  shows Cantor_\<omega>\<omega>: "omega_sum (Cantor_\<omega>\<omega> \<gamma>) = \<gamma>"
    and normal_Cantor_\<omega>\<omega>: "normal (Cantor_\<omega>\<omega> \<gamma>)"
  by (metis (mono_tags, lifting) Cantor_\<omega>\<omega>_def assms omega_sum_\<omega>\<omega> someI)+


subsection \<open>Larson's set $W(n)$\<close>

definition WW :: "nat list set"
  where "WW \<equiv> {l. strict_sorted l}"

fun into_WW :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "into_WW k [] = []"
| "into_WW k (n#ns) = (k+n) # into_WW (Suc (k+n)) ns"

fun from_WW :: "nat \<Rightarrow> nat list \<Rightarrow> nat list" where
  "from_WW k [] = []"
| "from_WW k (n#ns) = (n - k) # from_WW (Suc n) ns"

lemma from_into_WW [simp]: "from_WW k (into_WW k ns) = ns"
  by (induction ns arbitrary: k) auto

lemma inj_into_WW: "inj (into_WW k)"
  by (metis from_into_WW injI)

lemma into_from_WW_aux:
  "\<lbrakk>strict_sorted ns; \<forall>n\<in>list.set ns. k \<le> n\<rbrakk> \<Longrightarrow> into_WW k (from_WW k ns) = ns"
  by (induction ns arbitrary: k) (auto simp: Suc_leI)

lemma into_from_WW [simp]: "strict_sorted ns \<Longrightarrow> into_WW 0 (from_WW 0 ns) = ns"
  by (simp add: into_from_WW_aux)

lemma into_WW_imp_ge: "y \<in> List.set (into_WW x ns) \<Longrightarrow> x \<le> y"
  by (induction ns arbitrary: x) fastforce+

lemma strict_sorted_into_WW: "strict_sorted (into_WW x ns)"
  by (induction ns arbitrary: x) (auto simp: dest: into_WW_imp_ge)

lemma length_into_WW: "length (into_WW x ns) = length ns"
  by (induction ns arbitrary: x) auto

lemma WW_eq_range_into: "WW = range (into_WW 0)"
  by (metis (mono_tags, hide_lams) WW_def equalityI image_subset_iff into_from_WW mem_Collect_eq rangeI strict_sorted_into_WW subset_iff)

lemma into_WW_lenlex_iff: "(into_WW k ms, into_WW k ns) \<in> lenlex less_than \<longleftrightarrow> (ms, ns) \<in> lenlex less_than"
proof (induction ms arbitrary: ns k)
  case Nil
  then show ?case
    by simp (metis length_0_conv length_into_WW)
next
  case (Cons m ms)
  then show ?case
    by (induction ns) (auto simp: Cons_lenlex_iff length_into_WW)
qed

lemma wf_llt [simp]: "wf (lenlex less_than)"
  by blast

lemma trans_llt [simp]: "trans (lenlex less_than)"
  by blast

lemma total_llt [simp]: "total_on A (lenlex less_than)"
  by (meson UNIV_I total_lenlex total_less_than total_on_def)

lemma omega_sum_1_less:
  assumes "(ms,ns) \<in> lenlex less_than" shows "omega_sum (1#ms) < omega_sum (1#ns)"
proof -
  have "omega_sum (1#ms) < omega_sum (1#ns)" if "length ms < length ns"
    using omega_sum_less_iff_cases that zero_less_one by blast
  then show ?thesis
    using assms by (auto simp: mult_succ simp flip: omega_sum_less_iff)
qed

lemma ordertype_WW_1: "ordertype WW (lenlex less_than) \<le> ordertype UNIV (lenlex less_than)"
  by (rule ordertype_mono) auto

lemma ordertype_WW_2: "ordertype UNIV (lenlex less_than) \<le> \<omega>\<up>\<omega>"
proof (rule ordertype_inc_le_Ord)
  show "range (\<lambda>ms. omega_sum (1#ms)) \<subseteq> elts (\<omega>\<up>\<omega>)"
    by (meson Ord_\<omega> Ord_mem_iff_lt Ord_oexp Ord_omega_sum image_subset_iff omega_sum_less_\<omega>\<omega>)
qed (use omega_sum_1_less in auto)

lemma ordertype_WW_3: "\<omega>\<up>\<omega> \<le> ordertype WW (lenlex less_than)"
proof -
  define \<pi> where "\<pi> \<equiv> into_WW 0 \<circ> Cantor_\<omega>\<omega>"
  have \<omega>\<omega>: "\<omega>\<up>\<omega> = tp (elts (\<omega>\<up>\<omega>))"
    by simp
  also have "\<dots> \<le> ordertype WW (lenlex less_than)"
  proof (rule ordertype_inc_le)
    fix \<alpha> \<beta>
    assume \<alpha>: "\<alpha> \<in> elts (\<omega>\<up>\<omega>)" and \<beta>: "\<beta> \<in> elts (\<omega>\<up>\<omega>)" and "(\<alpha>, \<beta>) \<in> VWF"
    then obtain *: "Ord \<alpha>" "Ord \<beta>" "\<alpha><\<beta>"
      by (metis Ord_in_Ord Ord_ordertype VWF_iff_Ord_less \<omega>\<omega>)
    then have "length (Cantor_\<omega>\<omega> \<alpha>) \<le> length (Cantor_\<omega>\<omega> \<beta>)"
      using \<alpha> \<beta> by (simp add: Cantor_\<omega>\<omega> normal_Cantor_\<omega>\<omega> omega_sum_length_leD)
    with \<alpha> \<beta> * have "(Cantor_\<omega>\<omega> \<alpha>, Cantor_\<omega>\<omega> \<beta>) \<in> lenlex less_than"
      by (auto simp: Cantor_\<omega>\<omega> simp flip: omega_sum_less_iff)
    then show "(\<pi> \<alpha>, \<pi> \<beta>) \<in> lenlex less_than"
      by (simp add: \<pi>_def into_WW_lenlex_iff)
  next
    show "\<pi> ` elts (\<omega>\<up>\<omega>) \<subseteq> WW"
      by (auto simp: \<pi>_def WW_def strict_sorted_into_WW)
  qed auto
  finally show "\<omega>\<up>\<omega> \<le> ordertype WW (lenlex less_than)" .
qed

lemma ordertype_WW: "ordertype WW (lenlex less_than) = \<omega>\<up>\<omega>"
  and ordertype_UNIV_\<omega>\<omega>: "ordertype UNIV (lenlex less_than) = \<omega>\<up>\<omega>"
  using ordertype_WW_1 ordertype_WW_2 ordertype_WW_3 by auto


lemma ordertype_\<omega>\<omega>:
  fixes F :: "nat \<Rightarrow> nat list set"
  assumes "\<And>j::nat. ordertype (F j) (lenlex less_than) = \<omega>\<up>j"
  shows "ordertype (\<Union>j. F j) (lenlex less_than) = \<omega>\<up>\<omega>"
proof (rule antisym)
  show "ordertype (\<Union> (range F)) (lenlex less_than) \<le> \<omega> \<up> \<omega>"
    by (metis ordertype_UNIV_\<omega>\<omega> ordertype_mono small top_greatest trans_llt wf_llt)
  have "\<And>n. \<omega> \<up> ord_of_nat n \<le> ordertype (\<Union> (range F)) (lenlex less_than)"
    by (metis TC_small Union_upper assms ordertype_mono rangeI trans_llt wf_llt)
  then show "\<omega> \<up> \<omega> \<le> ordertype (\<Union> (range F)) (lenlex less_than)"
    by (auto simp: oexp_\<omega>_Limit ZFC_in_HOL.SUP_le_iff elts_\<omega>)
qed



definition WW_seg :: "nat \<Rightarrow> nat list set"
  where "WW_seg n \<equiv> {l \<in> WW. length l = n}"

lemma WW_seg_subset_WW: "WW_seg n \<subseteq> WW"
  by (auto simp: WW_seg_def)

lemma WW_eq_UN_WW_seg: "WW = (\<Union> n. WW_seg n)"
  by (auto simp: WW_seg_def)

lemma ordertype_list_seg: "ordertype {l. length l = n} (lenlex less_than) = \<omega>\<up>n"
proof -
  have "bij_betw omega_sum {l. length l = n} (elts (\<omega>\<up>n))"
    unfolding WW_seg_def bij_betw_def
    by (auto simp: inj_omega_sum Ord_mem_iff_lt omega_sum_less dest: Ex_omega_sum)
  then show ?thesis
    by (force simp: ordertype_eq_iff simp flip: eq_omega_sum_less_iff)
qed

lemma ordertype_WW_seg: "ordertype (WW_seg n) (lenlex less_than) = \<omega>\<up>n"
  (is "ordertype ?W ?R = \<omega>\<up>n")
proof -
  have "ordertype {l. length l = n} ?R = ordertype ?W ?R"
  proof (subst ordertype_eq_ordertype)
    show "\<exists>f. bij_betw f {l. length l = n} ?W \<and> (\<forall>x\<in>{l. length l = n}. \<forall>y\<in>{l. length l = n}. ((f x, f y) \<in> lenlex less_than) = ((x, y) \<in> lenlex less_than))"
    proof (intro exI conjI)
      have "inj_on (into_WW 0) {l. length l = n}"
        by (metis from_into_WW inj_onI)
      then show "bij_betw (into_WW 0) {l. length l = n} ?W"
        by (auto simp: bij_betw_def WW_seg_def WW_eq_range_into length_into_WW)
    qed (simp add: into_WW_lenlex_iff)
  qed auto
  then show ?thesis
    using ordertype_list_seg by auto
qed


subsection \<open>Definitions required for the lemmas\<close>

subsubsection \<open>Larson's "$<$"-relation on ordered lists\<close>

instantiation list :: (ord)ord
begin

definition "xs < ys \<equiv> xs \<noteq> [] \<and> ys \<noteq> [] \<longrightarrow> last xs < hd ys" for xs ys :: "'a list"
definition "xs \<le> ys \<equiv> xs < ys \<or> xs = ys" for xs ys :: "'a list"

instance
  by standard

end

lemma less_Nil [simp]: "xs < []" "[] < xs"
  by (auto simp: less_list_def)

lemma less_sets_imp_list_less:
  assumes "list.set xs \<lless> list.set ys"
  shows "xs < ys"
  by (metis assms last_in_set less_list_def less_sets_def list.set_sel(1))

lemma less_sets_imp_sorted_list_of_set:
  assumes "A \<lless> B" "finite A" "finite B"
  shows "list_of A < list_of B"
  by (simp add: assms less_sets_imp_list_less)

lemma sorted_list_of_set_imp_less_sets:
  assumes "xs < ys" "sorted xs" "sorted ys"
  shows "list.set xs \<lless> list.set ys"
  using assms sorted_hd_le sorted_le_last
  by (force simp: less_list_def less_sets_def intro: order.trans)

lemma less_list_iff_less_sets:
  assumes "sorted xs" "sorted ys"
  shows "xs < ys \<longleftrightarrow> list.set xs \<lless> list.set ys"
  using assms sorted_hd_le sorted_le_last
  by (force simp: less_list_def less_sets_def intro: order.trans)

lemma sorted_trans:
  assumes "xs < ys" "ys < zs" "sorted ys" "ys \<noteq> []" shows "xs < zs"
  using assms unfolding less_list_def
  by (metis dual_order.strict_trans last_in_set leD neqE sorted_hd_le)

lemma strict_sorted_imp_append_less:
  assumes "strict_sorted (xs @ ys)"
  shows "xs < ys"
  using assms by (simp add: less_list_def sorted_wrt_append strict_sorted_sorted_wrt)

lemma strict_sorted_append_iff:
  "strict_sorted (xs @ ys) \<longleftrightarrow> xs < ys \<and> strict_sorted xs \<and> strict_sorted ys" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (auto simp: sorted_wrt_append strict_sorted_sorted_wrt less_list_def)
next
  assume R: ?rhs
  then have "\<And>x y. \<lbrakk>x \<in> list.set xs; y \<in> list.set ys\<rbrakk> \<Longrightarrow> x < y"
    using less_setsD sorted_list_of_set_imp_less_sets strict_sorted_imp_sorted by blast
  with R show ?lhs
    by (auto simp: sorted_wrt_append strict_sorted_sorted_wrt)
qed

lemma singleton_less_list_iff: "sorted xs \<Longrightarrow> [n] < xs \<longleftrightarrow> {..n} \<inter> list.set xs = {}"
  apply (simp add: less_list_def set_eq_iff)
  by (metis empty_iff less_le_trans list.set(1) list.set_sel(1) not_le sorted_hd_le)

lemma less_last_iff: "xs@[x] < ys \<longleftrightarrow> [x] < ys"
  by (simp add: less_list_def)

lemma less_Cons_iff: "NO_MATCH [] ys \<Longrightarrow> xs < y#ys \<longleftrightarrow> xs < [y]"
  by (simp add: less_list_def)

lemma less_hd_imp_less: "xs < [hd ys] \<Longrightarrow> xs < ys"
  by (simp add: less_list_def)

lemma last_less_imp_less: "[last xs] < ys \<Longrightarrow> xs < ys"
  by (simp add: less_list_def)

lemma strict_sorted_concat_I:
  assumes
    "\<And>x. x \<in> list.set xs \<Longrightarrow> strict_sorted x"
    "\<And>n. Suc n < length xs \<Longrightarrow> xs!n < xs!Suc n"
  assumes "xs \<in> lists (- {[]})"
  shows "strict_sorted (concat xs)"
  using assms
proof (induction xs)
  case (Cons x xs)
  then have "x < concat xs"
    apply (simp add: less_list_def)
    by (metis Compl_iff hd_concat insertI1 length_greater_0_conv length_pos_if_in_set list.sel(1) lists.cases nth_Cons_0)
  with Cons show ?case
    by (force simp: strict_sorted_append_iff)
qed auto


subsection \<open>Nash Williams for lists\<close>

subsubsection \<open>Thin sets of lists\<close>

inductive initial_segment :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "initial_segment xs (xs@ys)"

definition thin :: "'a list set \<Rightarrow> bool"
  where "thin A \<equiv> \<not> (\<exists>x y. x \<in> A \<and> y \<in> A \<and> x \<noteq> y \<and> initial_segment x y)"

lemma initial_segment_ne:
  assumes "initial_segment xs ys" "xs \<noteq> []"
  shows "ys \<noteq> [] \<and> hd ys = hd xs"
  using assms by (auto elim!: initial_segment.cases)

lemma take_initial_segment:
  assumes "initial_segment xs ys" "k \<le> length xs"
  shows "take k xs = take k ys"
  by (metis append_eq_conv_conj assms initial_segment.cases min_def take_take)

lemma initial_segment_length_eq:
  assumes "initial_segment xs ys" "length xs = length ys"
  shows "xs = ys"
  using assms initial_segment.cases by fastforce

lemma initial_segment_Nil [simp]: "initial_segment [] ys"
  by (simp add: initial_segment.simps)

lemma initial_segment_Cons [simp]: "initial_segment (x#xs) (y#ys) \<longleftrightarrow> x=y \<and> initial_segment xs ys"
  by (metis append_Cons initial_segment.simps list.inject)

lemma init_segment_iff_initial_segment:
  assumes "strict_sorted xs" "strict_sorted ys"
  shows "init_segment (list.set xs) (list.set ys) \<longleftrightarrow> initial_segment xs ys" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain S' where S': "list.set ys = list.set xs \<union> S'" "list.set xs \<lless> S'"
    by (auto simp: init_segment_def)
  then have "finite S'"
    by (metis List.finite_set finite_Un)
  have "ys = xs @ list_of S'"
    using S' \<open>strict_sorted xs\<close>
  proof (induction xs)
    case Nil
    with \<open>strict_sorted ys\<close> show ?case
      by auto
  next
    case (Cons a xs)
    with \<open>finite S'\<close> have "ys = a # xs @ list_of S'"
      by (metis List.finite_set \<open>finite S'\<close> append_Cons assms(2) sorted_list_of_set_Un sorted_list_of_set_set_of)
    then show ?case
      by (auto simp: Cons)
  qed
  then show ?rhs
    using initial_segment.intros by blast
next
  assume ?rhs
  then show ?lhs
  proof cases
    case (1 ys)
    with assms(2) show ?thesis
      using sorted_list_of_set_imp_less_sets strict_sorted_imp_sorted
      by (auto simp: init_segment_def strict_sorted_append_iff)
  qed
qed

theorem Nash_Williams_WW:
  fixes h :: "nat list \<Rightarrow> nat"
  assumes "infinite M" and h: "h ` {l \<in> A. List.set l \<subseteq> M} \<subseteq> {..<2}" and "thin A" "A \<subseteq> WW"
  obtains i N where "i < 2" "infinite N" "N \<subseteq> M" "h ` {l \<in> A. List.set l \<subseteq> N} \<subseteq> {i}"
proof -
  define AM where "AM \<equiv> {l \<in> A. List.set l \<subseteq> M}"
  have "thin_set (list.set ` A)"
    using \<open>thin A\<close> \<open>A \<subseteq> WW\<close> unfolding thin_def thin_set_def WW_def
    by (auto simp: subset_iff init_segment_iff_initial_segment)
  then have "thin_set (list.set ` AM)"
    by (simp add: AM_def image_subset_iff thin_set_def)
  then have "Ramsey (list.set ` AM) 2"
    using Nash_Williams_2 by metis
  moreover have "(h \<circ> list_of) \<in> list.set ` AM \<rightarrow> {..<2}"
    unfolding AM_def
  proof clarsimp
    fix l
    assume "l \<in> A" "list.set l \<subseteq> M"
    then have "strict_sorted l"
      using WW_def \<open>A \<subseteq> WW\<close> by blast
    then show "h (list_of (list.set l)) < 2"
      using h \<open>l \<in> A\<close> \<open>list.set l \<subseteq> M\<close> by auto
  qed
  ultimately obtain N i where N: "N \<subseteq> M" "infinite N" "i<2"
    and "\<And>j. \<lbrakk>j<2; i\<noteq>j\<rbrakk> \<Longrightarrow> (h \<circ> list_of) -` {j} \<inter> (list.set ` AM) \<inter> Pow N = {}"
    unfolding Ramsey_def by (metis \<open>infinite M\<close>)
  then have N_disjoint: "(h \<circ> list_of) -` {1-i} \<inter> (list.set ` AM) \<inter> Pow N = {}"
    by (metis One_nat_def diff_less_Suc not_less_eq numeral_2_eq_2 zero_less_diff)
  have "h ` {l \<in> A. list.set l \<subseteq> N} \<subseteq> {i}"
  proof clarify
    fix l
    assume "l \<in> A" and "list.set l \<subseteq> N"
    then have "h l < 2"
      using h \<open>N \<subseteq> M\<close> by force
    with \<open>i<2\<close> have "h l \<noteq> Suc 0 - i \<Longrightarrow> h l = i"
      by (auto simp: eval_nat_numeral less_Suc_eq)
    moreover have "strict_sorted l"
      using \<open>A \<subseteq> WW\<close> \<open>l \<in> A\<close> unfolding WW_def by blast
    moreover have "h (list_of (list.set l)) = 1 - i \<longrightarrow> \<not> (list.set l \<subseteq> N)"
      using N_disjoint \<open>N \<subseteq> M\<close> \<open>l \<in> A\<close> by (auto simp: AM_def)
    ultimately
    show "h l = i"
      using N \<open>N \<subseteq> M\<close> \<open>l \<in> A\<close> \<open>list.set l \<subseteq> N\<close>
      by (auto simp: vimage_def set_eq_iff AM_def WW_def subset_iff)
  qed
  then show thesis
    using that \<open>i<2\<close> N by auto
qed

subsection \<open>Specialised functions on lists\<close>

lemma mem_lists_non_Nil: "xss \<in> lists (- {[]}) \<longleftrightarrow> (\<forall>x \<in> list.set xss. x \<noteq> [])"
  by auto

fun acc_lengths :: "nat \<Rightarrow> 'a list list \<Rightarrow> nat list"
  where "acc_lengths acc [] = []"
      | "acc_lengths acc (l#ls) = (acc + length l) # acc_lengths (acc + length l) ls"

lemma length_acc_lengths [simp]: "length (acc_lengths acc ls) = length ls"
  by (induction ls arbitrary: acc) auto

lemma acc_lengths_eq_Nil_iff [simp]: "acc_lengths acc ls = [] \<longleftrightarrow> ls = []"
  by (metis length_0_conv length_acc_lengths)

lemma set_acc_lengths:
  assumes "ls \<in> lists (- {[]})" shows "list.set (acc_lengths acc ls) \<subseteq> {acc<..}"
  using assms by (induction ls rule: acc_lengths.induct) fastforce+

text \<open>Useful because @{text acc_lengths.simps} will later be deleted from the simpset.\<close>
lemma hd_acc_lengths [simp]: "hd (acc_lengths acc (l#ls)) = acc + length l"
  by simp

lemma last_acc_lengths [simp]:
  "ls \<noteq> [] \<Longrightarrow> last (acc_lengths acc ls) = acc + sum_list (map length ls)"
by (induction acc ls rule: acc_lengths.induct) auto

lemma nth_acc_lengths [simp]:
  "\<lbrakk>ls \<noteq> []; k < length ls\<rbrakk> \<Longrightarrow> acc_lengths acc ls ! k = acc + sum_list (map length (take (Suc k) ls))"
  by (induction acc ls arbitrary: k rule: acc_lengths.induct) (fastforce simp: less_Suc_eq nth_Cons')+

lemma acc_lengths_plus: "acc_lengths (m+n) as = map ((+)m) (acc_lengths n as)"
  by (induction n as arbitrary: m rule: acc_lengths.induct) (auto simp: add.assoc)

lemma acc_lengths_shift: "NO_MATCH 0 acc \<Longrightarrow> acc_lengths acc as = map ((+)acc) (acc_lengths 0 as)"
  by (metis acc_lengths_plus add.comm_neutral)

lemma length_concat_acc_lengths:
  "ls \<noteq> [] \<Longrightarrow> k + length (concat ls) \<in> list.set (acc_lengths k ls)"
  by (metis acc_lengths_eq_Nil_iff last_acc_lengths last_in_set length_concat)

lemma strict_sorted_acc_lengths:
  assumes "ls \<in> lists (- {[]})" shows "strict_sorted (acc_lengths acc ls)"
  using assms
proof (induction ls rule: acc_lengths.induct)
  case (2 acc l ls)
  then have "strict_sorted (acc_lengths (acc + length l) ls)"
    using "2" by auto
  then show ?case
    using set_acc_lengths "2.prems" by auto
qed auto

lemma acc_lengths_append:
  "acc_lengths acc (xs @ ys)
   = acc_lengths acc xs @ acc_lengths (acc + sum_list (map length xs)) ys"
by (induction acc xs rule: acc_lengths.induct) (auto simp: add.assoc)


declare acc_lengths.simps [simp del]

lemma length_concat_ge:
  assumes "as \<in> lists (- {[]})"
  shows "length (concat as) \<ge> length as"
  using assms
proof (induction as)
  case (Cons a as)
  then have "length a \<ge> Suc 0" "\<And>l. l \<in> list.set as \<Longrightarrow> length l \<ge> Suc 0"
    by (auto simp: Suc_leI)
  then show ?case
    using Cons.IH by force
qed auto


fun interact :: "'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list"
  where
  "interact [] ys = concat ys"
| "interact xs [] = concat xs"
| "interact (x#xs) (y#ys) = x @ y @ interact xs ys"

lemma (in monoid_add) length_interact:
  "length (interact xs ys) = sum_list (map length xs) + sum_list (map length ys)"
  by (induction rule: interact.induct) (auto simp: length_concat)

lemma length_interact_ge:
  assumes "xs \<in> lists (- {[]})" "ys \<in> lists (- {[]})"
  shows "length (interact xs ys) \<ge> length xs + length ys"
  by (metis mem_lists_non_Nil add_mono assms length_concat length_concat_ge length_interact)

lemma set_interact [simp]:
  shows "list.set (interact xs ys) = list.set (concat xs) \<union> list.set (concat ys)"
by (induction rule: interact.induct) auto

lemma interact_eq_Nil_iff [simp]:
  assumes "xs \<in> lists (- {[]})" "ys \<in> lists (- {[]})"
  shows "interact xs ys = [] \<longleftrightarrow> xs=[] \<and> ys=[]"
  using length_interact_ge [OF assms]  by fastforce

lemma interact_sing [simp]: "interact [x] ys = x @ concat ys"
  by (metis (no_types) concat.simps(2) interact.simps neq_Nil_conv)

lemma hd_interact: "\<lbrakk>xs \<noteq> []; hd xs \<noteq> []\<rbrakk> \<Longrightarrow> hd (interact xs ys) = hd (hd xs)"
  by (metis concat.simps(2) hd_append2 interact.simps(2) interact.simps(3) list.exhaust list.sel(1))

lemma acc_lengths_concat_injective:
  assumes "concat as' = concat as" "acc_lengths n as' = acc_lengths n as"
  shows "as' = as"
  using assms
proof (induction as arbitrary: n as')
  case Nil
  then show ?case
    by (metis acc_lengths_eq_Nil_iff)
next
  case (Cons a as)
  then obtain a' bs where "as' = a'#bs"
    by (metis Suc_length_conv length_acc_lengths)
  with Cons show ?case
    by (simp add: acc_lengths.simps)
qed

lemma acc_lengths_interact_injective:
  assumes "interact as' bs' = interact as bs" "acc_lengths a as' = acc_lengths a as" "acc_lengths b bs' = acc_lengths b bs"
  shows "as' = as \<and> bs' = bs"
  using assms
proof (induction as bs arbitrary: a b as' bs' rule: interact.induct)
  case (1 cs)
  then have "as' = []"
    by (metis acc_lengths_eq_Nil_iff)
  with 1 show ?case
    using acc_lengths_concat_injective by auto
next
  case (2 c cs)
  then show ?case
    by (metis acc_lengths_concat_injective acc_lengths_eq_Nil_iff interact.simps(2) list.exhaust)
next
  case (3 x xs y ys)
  then obtain a' us b' vs where "as' = a'#us" "bs' = b'#vs"
    by (metis length_Suc_conv length_acc_lengths)
  with 3 show ?case
    by (auto simp: acc_lengths.simps)
qed


lemma strict_sorted_interact_I:
  assumes "length ys \<le> length xs" "length xs \<le> Suc (length ys)"
    "\<And>x. x \<in> list.set xs \<Longrightarrow> strict_sorted x"
    "\<And>y. y \<in> list.set ys \<Longrightarrow> strict_sorted y"
    "\<And>n. n < length ys \<Longrightarrow> xs!n < ys!n"
    "\<And>n. Suc n < length xs \<Longrightarrow> ys!n < xs!Suc n"
  assumes "xs \<in> lists (- {[]})" "ys \<in> lists (- {[]})"
  shows "strict_sorted (interact xs ys)"
  using assms
proof (induction rule: interact.induct)
  case (3 x xs y ys)
  then have "x < y"
    by force+
  moreover have "strict_sorted (interact xs ys)"
    using 3 by simp (metis Suc_less_eq nth_Cons_Suc)
  moreover have "y < interact xs ys"
  proof (clarsimp simp add: less_list_def)
    assume "y \<noteq> []" and ne: "interact xs ys \<noteq> []"
    then show "last y < hd (interact xs ys)"
      using 3
      apply simp
      by (metis dual_order.strict_trans1 hd_interact length_greater_0_conv less_list_def list.sel(1) lists.simps mem_lists_non_Nil nth_Cons' nth_mem)
  qed
  ultimately show ?case
    using 3 by (simp add: strict_sorted_append_iff less_list_def)
qed auto


subsection \<open>Forms and interactions\<close>

subsubsection \<open>Forms\<close>

inductive Form_Body :: "[nat, nat, nat list, nat list, nat list] \<Rightarrow> bool"
  where "Form_Body ka kb xs ys zs"
  if "length xs < length ys" "xs = concat (a#as)" "ys = concat (b#bs)"
          "a#as \<in> lists (- {[]})" "b#bs \<in> lists (- {[]})"
          "length (a#as) = ka" "length (b#bs) = kb"
          "c = acc_lengths 0 (a#as)"
          "d = acc_lengths 0 (b#bs)"
          "zs = concat [c, a, d, b] @ interact as bs"
          "strict_sorted zs"


inductive Form :: "[nat, nat list set] \<Rightarrow> bool"
  where "Form 0 {xs,ys}" if "length xs = length ys" "xs \<noteq> ys"
      | "Form (2*k-1) {xs,ys}" if "Form_Body k k xs ys zs" "k > 0"
      | "Form (2*k)   {xs,ys}" if "Form_Body (Suc k) k xs ys zs" "k > 0"

inductive_cases Form_0_cases_raw: "Form 0 u"

lemma Form_elim_upair:
  assumes "Form l U"
  obtains xs ys where "xs \<noteq> ys" "U = {xs,ys}" "length xs \<le> length ys"
  using assms
  by (elim Form.cases Form_Body.cases; metis dual_order.order_iff_strict less_not_refl)


lemma Form_Body_WW:
  assumes "Form_Body ka kb xs ys zs"
  shows "zs \<in> WW"
  by (rule Form_Body.cases [OF assms]) (auto simp: WW_def)

lemma Form_Body_nonempty:
  assumes "Form_Body ka kb xs ys zs"
  shows "length zs > 0"
  by (rule Form_Body.cases [OF assms]) auto

lemma Form_Body_length:
  assumes "Form_Body ka kb xs ys zs"
  shows "length xs < length ys"
  using Form_Body.cases assms by blast

lemma form_cases:
  fixes l::nat
  obtains (zero) "l = 0" | (nz) ka kb where "l = ka+kb - 1" "0 < kb" "kb \<le> ka" "ka \<le> Suc kb"
proof -
  have "l = 0 \<or> (\<exists>ka kb. l = ka+kb - 1 \<and> 0 < kb \<and> kb \<le> ka \<and> ka \<le> Suc kb)"
    by presburger
  then show thesis
    using nz zero by blast
qed

subsubsection \<open>Interactions\<close>

lemma interact:
  assumes "Form l U" "l>0"
  obtains ka kb xs ys zs where "l = ka+kb - 1" "U = {xs,ys}" "Form_Body ka kb xs ys zs" "0 < kb" "kb \<le> ka" "ka \<le> Suc kb"
  using form_cases [of l]
proof cases
  case zero
  then show ?thesis
    using Form_0_cases_raw assms that(1) by auto
next
  case (nz ka kb)
  obtain xs ys where xys: "xs \<noteq> ys" "U = {xs,ys}" "length xs \<le> length ys"
    using Form_elim_upair assms by blast
  show ?thesis
  proof (cases "ka = kb")
    case True
    show ?thesis
      using Form.cases [OF \<open>Form l U\<close>]
    proof cases
      case (2 k xs' ys' zs')
      then have "xs' = xs \<and> ys' = ys"
        by (metis Form_Body_length Set.doubleton_eq_iff leD xys(2) xys(3))
      moreover have "k = ka"
        using 2 True nz by presburger
      ultimately show ?thesis
        using 2 True nz(1) nz(4) that xys(1) by blast
    qed (use True nz in \<open>presburger+\<close>)
  next
    case False
    show ?thesis
      using Form.cases [OF \<open>Form l U\<close>]
    proof cases
      case (3 k xs' ys' zs')
      then have "xs' = xs \<and> ys' = ys"
        by (metis Form_Body_length Set.doubleton_eq_iff leD xys(2) xys(3))
      moreover have "k = kb"
        using 3 False nz
        by linarith 
      ultimately show ?thesis
        using 3 False nz \<open>xs \<noteq> ys\<close>
        by (metis le_SucE le_antisym that)
    qed (use False nz in \<open>presburger+\<close>)
  qed
qed


definition inter_scheme :: "nat \<Rightarrow> nat list set \<Rightarrow> nat list"
  where "inter_scheme l U \<equiv> 
           SOME zs. \<exists>k xs ys. l > 0 \<and>
                         (l = 2*k-1 \<and> U = {xs,ys} \<and> Form_Body k k xs ys zs
                        \<or> l = 2*k \<and> U = {xs,ys} \<and> Form_Body (Suc k) k xs ys zs)"


lemma inter_scheme:
  assumes "Form l U" "l>0"
  obtains ka kb xs ys where "l = ka+kb - 1" "U = {xs,ys}" "Form_Body ka kb xs ys (inter_scheme l U)" "0 < kb" "kb \<le> ka" "ka \<le> Suc kb"
  using interact [OF \<open>Form l U\<close>]
proof cases
  case 1
  with \<open>l > 0\<close> show ?case
    by auto
next
  case (2 ka kb xs ys zs)
  then have \<section>: "\<And>ka kb zs. \<not> Form_Body ka kb ys xs zs"
    using Form_Body_length less_asym' by blast
  have "Form_Body ka kb xs ys (inter_scheme l U)"
  proof (cases "ka = kb")
    case True
    with 2 have l: "\<forall>k. l \<noteq> k * 2"
      by presburger
    have [simp]: "\<And>k. kb + kb - Suc 0 = k * 2 - Suc 0 \<longleftrightarrow> k=kb"
      by auto
    show ?thesis
      unfolding inter_scheme_def using 2 l True
      by (auto simp add: \<section> \<open>l > 0\<close> Set.doubleton_eq_iff conj_disj_distribR ex_disj_distrib algebra_simps some_eq_ex)
  next
    case False
    with 2 have l: "\<forall>k. l \<noteq> k * 2 - Suc 0" and [simp]: "ka = Suc kb"
      by presburger+
    have [simp]: "\<And>k. kb + kb = k * 2 \<longleftrightarrow> k=kb"
      by auto
    show ?thesis
      unfolding inter_scheme_def using 2 l False
      by (auto simp add: \<section> \<open>l > 0\<close> Set.doubleton_eq_iff conj_disj_distribR ex_disj_distrib algebra_simps some_eq_ex)
  qed
  then show ?thesis
    by (simp add: 2 that)
qed


lemma inter_scheme_simple:
  assumes "Form l U" "l>0"
  shows "inter_scheme l U \<in> WW \<and> length (inter_scheme l U) > 0"
  using inter_scheme [OF assms] by (meson Form_Body_WW Form_Body_nonempty)

lemma inter_scheme_strict_sorted:
  assumes "Form l U" "l>0"
  shows "strict_sorted (inter_scheme l U)"
  using inter_scheme_simple [OF assms] by (auto simp: WW_def)

subsubsection \<open>Injectivity of interactions\<close>

proposition inter_scheme_injective:
  assumes "Form l U" "Form l U'" "l > 0" and eq: "inter_scheme l U' = inter_scheme l U"
  shows "U' = U"
proof -
  obtain ka kb xs ys 
    where l: "l = ka+kb - 1" and U: "U = {xs,ys}" 
      and FB: "Form_Body ka kb xs ys (inter_scheme l U)" and "0 < kb" "kb \<le> ka" "ka \<le> Suc kb"
    using assms inter_scheme by blast
  then obtain a as b bs c d
    where xs: "xs = concat (a#as)" and ys: "ys = concat (b#bs)"
      and len: "length (a#as) = ka" "length (b#bs) = kb"
      and c: "c = acc_lengths 0 (a#as)"
      and d: "d = acc_lengths 0 (b#bs)"
      and Ueq: "inter_scheme l U = concat [c, a, d, b] @ interact as bs"
    by (auto simp: Form_Body.simps)
  obtain ka' kb' xs' ys' 
    where l': "l = ka'+kb' - 1" and U': "U' = {xs',ys'}" 
      and FB': "Form_Body ka' kb' xs' ys' (inter_scheme l U')" and "0 < kb'" "kb' \<le> ka'" "ka' \<le> Suc kb'"
    using assms inter_scheme by blast
  then obtain a' as' b' bs' c' d'
    where xs': "xs' = concat (a'#as')" and ys': "ys' = concat (b'#bs')"
      and len': "length (a'#as') = ka'" "length (b'#bs') = kb'"
      and c': "c' = acc_lengths 0 (a'#as')"
      and d': "d' = acc_lengths 0 (b'#bs')"
      and Ueq': "inter_scheme l U' = concat [c', a', d', b'] @ interact as' bs'"
    using Form_Body.simps by auto
  have [simp]: "ka' = ka \<and> kb' = kb"
    using \<open>l > 0\<close> l l' \<open>ka \<le> Suc kb\<close> \<open>ka' \<le> Suc kb'\<close> \<open>kb \<le> ka\<close> \<open>kb' \<le> ka'\<close> le_SucE le_antisym mult_2 by linarith 
  have [simp]: "length c = length c'" "length d = length d'"
    using c c' d d' len' len by auto
  have c_off: "c' = c" "a' @ d' @ b' @ interact as' bs' = a @ d @ b @ interact as bs"
    using eq by (auto simp: Ueq Ueq')
  then have len_a: "length a' = length a"
    by (metis acc_lengths.simps(2) add.left_neutral c c' nth_Cons_0)
  with c_off have \<section>: "a' = a" "d' = d" "b' @ interact as' bs' = b @ interact as bs"
    by auto
  then have "length (interact as' bs') = length (interact as bs)"
    by (metis acc_lengths.simps(2) add_left_cancel append_eq_append_conv d d' list.inject)
  with \<section> have "b' = b" "interact as' bs' = interact as bs"
    by auto
  moreover have "acc_lengths 0 as' = acc_lengths 0 as"
    using \<open>a' = a\<close> \<open>c' = c\<close> by (simp add: c' c acc_lengths.simps acc_lengths_shift)
  moreover have "acc_lengths 0 bs' = acc_lengths 0 bs"
    using \<open>b' = b\<close> \<open>d' = d\<close> by (simp add: d' d acc_lengths.simps acc_lengths_shift)
  ultimately have "as' = as \<and> bs' = bs"
    using acc_lengths_interact_injective by blast
  then show ?thesis
    by (simp add: \<open>a' = a\<close> U U' \<open>b' = b\<close> xs xs' ys ys')
qed


lemma strict_sorted_interact_imp_concat:
    "strict_sorted (interact as bs) \<Longrightarrow> strict_sorted (concat as) \<and> strict_sorted (concat bs)"
proof (induction as bs rule: interact.induct)
  case (3 x xs y ys)
  show ?case
  proof (cases x)
    case Nil
    show ?thesis
    proof (cases y)
      case Nil
      then show ?thesis
        using "3" strict_sorted_append_iff by (auto simp: \<open>x = []\<close>)
    next
      case (Cons a list)
      with Nil 3 show ?thesis
        apply (simp add: strict_sorted_append_iff)
        by (metis (no_types, lifting) Un_iff set_interact sorted_wrt_append strict_sorted_append_iff strict_sorted_sorted_wrt)
    qed
  next
    case (Cons a list)
    have \<section>: "sorted_wrt (<) ((a # list) @ y @ interact xs ys)"
      by (metis (no_types) "3.prems" interact.simps(3) local.Cons strict_sorted_sorted_wrt)
    then have "list = [] \<or> concat xs = [] \<or> last list < hd (concat xs)"
      by (metis (full_types) Un_iff hd_in_set last_ConsR last_in_set list.simps(3) set_append set_interact sorted_wrt_append)
    then have "list < concat xs"
      using less_list_def by blast
    have "list < y"
      by (metis \<section> append.assoc last.simps less_list_def list.distinct(1) strict_sorted_append_iff strict_sorted_sorted_wrt)
    note Cons1 = Cons
    show ?thesis
    proof (cases y)
      case Nil
      then show ?thesis
        using 3 by (simp add: sorted_wrt_append strict_sorted_sorted_wrt)
    next
      case (Cons a' list')
      have "strict_sorted (list' @ concat ys)"
        apply (simp add: strict_sorted_sorted_wrt)
        by (metis "3.IH" "\<section>" Un_iff append_Cons local.Cons set_interact sorted_wrt_append strict_sorted.simps(2) strict_sorted_sorted_wrt)
      moreover have "y < concat ys"
        by (metis "\<section>" Un_iff hd_in_set last_in_set less_list_def set_interact sorted_wrt_append)
      ultimately show ?thesis
        using 3 \<open>list < concat xs\<close>
        by (auto simp: Cons1 strict_sorted_append_iff)
    qed
  qed
qed auto




lemma strict_sorted_interact_hd:
  "\<lbrakk>strict_sorted (interact cs ds); cs \<noteq> []; ds \<noteq> []; hd cs \<noteq> []; hd ds \<noteq> []\<rbrakk>
       \<Longrightarrow> hd (hd cs) < hd (hd ds)"
  by (metis Nil_is_append_conv hd_append2 hd_in_set interact.simps(3) list.exhaust_sel sorted_wrt_append strict_sorted_sorted_wrt)


text \<open>the lengths of the two lists can differ by one\<close>
proposition interaction_scheme_unique_aux:
  assumes eq: "concat as = concat as'" and ys': "concat bs = concat bs'"
    and ne: "as \<in> lists (- {[]})" "bs \<in> lists (- {[]})"
    and ss_zs: "strict_sorted (interact as bs)"
    and "length bs \<le> length as" "length as \<le> Suc (length bs)"
    and ne': "as' \<in> lists (- {[]})" "bs' \<in> lists (- {[]})"
    and ss_zs': "strict_sorted (interact as' bs')"
    and "length bs' \<le> length as'" "length as' \<le> Suc (length bs')"
    and "length as = length as'" "length bs = length bs'"
  shows "as = as' \<and> bs = bs'"
  using assms
proof (induction "length as" arbitrary: as bs as' bs')
  case 0 then show ?case
    by auto
next
  case (Suc k)
  show ?case
  proof (cases k)
    case 0
    then have "length as = Suc 0"
      using Suc.hyps(2) by auto
    then obtain a a' where "as = [a]" "as' = [a']"
      by (metis \<open>length as = length as'\<close> length_0_conv length_Suc_conv)
    with 0 show ?thesis
      using Suc.prems
      apply (simp add: le_Suc_eq)
      by (metis concat.simps length_0_conv length_Suc_conv self_append_conv)
  next
    case (Suc k')
    then obtain a cs b ds where eq: "as = a#cs" "bs = b#ds"
      using Suc.prems
      by (metis Suc.hyps(2) le0 list.exhaust list.size(3) not_less_eq_eq)
    have "length as' \<noteq> 0"
      using Suc.hyps(2) Suc.prems(1) Suc.prems(3) interact_eq_Nil_iff by auto
    then obtain a' cs' b' ds' where eq': "as' = a'#cs'" "bs' = b'#ds'"
      by (metis Suc.prems(14) eq(2) length_0_conv list.exhaust)
    obtain k: "k = length cs" "k \<le> Suc (length ds)"
      using eq \<open>Suc k = length as\<close> \<open>length bs \<le> length as\<close> \<open>length as \<le> Suc (length bs)\<close> by auto
    case (Suc k')
    obtain [simp]: "b \<noteq> []" "b' \<noteq> []" "a \<noteq> []" "a' \<noteq> []"
      using Suc.prems by (simp add: eq eq')
    then have "hd b' = hd b"
      using Suc.prems(2) by (metis concat.simps(2) eq'(2) eq(2) hd_append2)

    have ss_ab: "strict_sorted (concat as)" "strict_sorted (concat bs)"
      using strict_sorted_interact_imp_concat Suc.prems(5) by blast+
    have "a < b"
      by (metis eq Suc.prems(5) append.assoc interact.simps(3) strict_sorted_append_iff)
    have sw_ab: "sorted_wrt (<) (a @ b @ interact cs ds)"
      by (metis Suc.prems(5) eq interact.simps(3) strict_sorted_sorted_wrt)
    then have "hd b \<notin> list.set (concat cs)"
      by (metis Un_iff \<open>b \<noteq> []\<close> list.set_sel(1) not_less_iff_gr_or_eq set_interact sorted_wrt_append)
    have "b < concat cs"
      using eq \<open>strict_sorted (interact as bs)\<close>
      apply (simp add: strict_sorted_append_iff)
      by (metis Un_iff sw_ab last_in_set less_list_def list.set_sel(1) set_interact sorted_wrt_append)
    have "strict_sorted (a @ concat cs)"
      using eq(1) ss_ab(1) by force
    then have b_cs: "strict_sorted (b @ concat cs)"
      by (metis \<open>b < concat cs\<close> strict_sorted_append_iff strict_sorted_sorted_wrt sw_ab)
    have "list.set a = list.set (concat as) \<inter> {..< hd b}"
    proof -
      have "x \<in> list.set a"
        if "x < hd b" and "l \<in> list.set cs" and "x \<in> list.set l" for x l
        using b_cs sorted_hd_le strict_sorted_imp_sorted that by fastforce
      then show ?thesis
        using \<open>b \<noteq> []\<close> sw_ab by (force simp: strict_sorted_append_iff sorted_wrt_append eq)
    qed
    moreover
    have ss_ab': "strict_sorted (concat as')" "strict_sorted (concat bs')"
      using strict_sorted_interact_imp_concat Suc.prems(10) by blast+
    have "a' < b'"
      by (metis eq' Suc.prems(10) append.assoc interact.simps(3) strict_sorted_append_iff)
    have sw_ab': "sorted_wrt (<) (a' @ b' @ interact cs' ds')"
      by (metis Suc.prems(10) eq' interact.simps(3) strict_sorted_sorted_wrt)
    then have "hd b' \<notin> list.set (concat cs')"
      by (metis Un_iff \<open>b' \<noteq> []\<close> list.set_sel(1) not_less_iff_gr_or_eq set_interact sorted_wrt_append)
    have "b' < concat cs'"
      using eq' \<open>strict_sorted (interact as' bs')\<close>
      apply (simp add: strict_sorted_append_iff)
      by (metis Un_iff last_in_set less_list_def list.set_sel(1) set_interact sorted_wrt_append sw_ab')
    have "strict_sorted (a' @ concat cs')"
      using eq'(1) ss_ab'(1) by force
    then have b_cs': "strict_sorted (b' @ concat cs')"
      using \<open>b' < concat cs'\<close> eq'(2) ss_ab'(2) strict_sorted_append_iff by auto
    have "list.set a' = list.set (concat as') \<inter> {..< hd b'}"
    proof -
      have "x \<in> list.set a'"
        if "x < hd b'" and "l \<in> list.set cs'" and "x \<in> list.set l" for x l
        using b_cs' sorted_hd_le strict_sorted_imp_sorted that by fastforce
      then show ?thesis
        using \<open>b' \<noteq> []\<close> sw_ab' by (force simp: strict_sorted_append_iff sorted_wrt_append eq')
    qed
    ultimately have "a=a'"
      by (metis Suc.prems(1) \<open>hd b' = hd b\<close> sorted_wrt_append strict_sorted_equal strict_sorted_sorted_wrt sw_ab sw_ab')
    moreover
    have ccat_cs_cs': "concat cs = concat cs'"
      using Suc.prems(1) \<open>a = a'\<close> eq'(1) eq(1) by fastforce
    have "b=b'"
    proof (cases "ds = [] \<or> ds' = []")
      case True
      then show ?thesis
        using Suc.prems(14) Suc.prems(2) eq'(2) eq(2) by auto
    next
      case False
      then have "ds \<noteq> []" "ds' \<noteq> []"
        by auto
      have "strict_sorted b"
        by (metis Suc.prems(2) concat.simps(2) eq(2) ss_ab'(2) strict_sorted_append_iff)
      moreover
      have "cs \<noteq> []"
        using k local.Suc by auto

      then obtain "hd cs \<noteq> []" "hd ds \<noteq> []"
        using Suc.prems(3) Suc.prems(4) eq list.set_sel(1)
        by (simp add: \<open>ds \<noteq> []\<close> mem_lists_non_Nil)
      then have "concat cs \<noteq> []"
        using \<open>cs \<noteq> []\<close> hd_in_set by auto
      have "hd (concat cs) < hd (concat ds)"
        using strict_sorted_interact_hd
        by (metis \<open>cs \<noteq> []\<close> \<open>ds \<noteq> []\<close> \<open>hd cs \<noteq> []\<close> \<open>hd ds \<noteq> []\<close> hd_concat strict_sorted_append_iff strict_sorted_sorted_wrt sw_ab)
      then have "list.set b = list.set (concat bs) \<inter> {..< hd (concat cs)}"
        using ss_ab
        apply (auto simp: strict_sorted_append_iff eq)
        apply (metis \<open>b < concat cs\<close> \<open>concat cs \<noteq> []\<close> hd_in_set sorted_wrt_append strict_sorted_append_iff strict_sorted_sorted_wrt)
        by (metis strict_sorted_iff UN_I dual_order.strict_trans2 order.asym set_concat sorted_hd_le)
      moreover
      have "cs' \<noteq> []"
        using k local.Suc \<open>concat cs \<noteq> []\<close> ccat_cs_cs' by auto
      then obtain "hd cs' \<noteq> []" "hd ds' \<noteq> []"
        using Suc.prems(8,9) \<open>ds' \<noteq> []\<close> eq'(1) eq'(2) list.set_sel(1) by auto
      then have "concat cs' \<noteq> []"
        using \<open>cs' \<noteq> []\<close> hd_in_set by auto
      have "hd (concat cs') < hd (concat ds')"
        using strict_sorted_interact_hd
        by (metis \<open>cs' \<noteq> []\<close> \<open>ds' \<noteq> []\<close> \<open>hd cs' \<noteq> []\<close> \<open>hd ds' \<noteq> []\<close> hd_concat strict_sorted_append_iff strict_sorted_sorted_wrt sw_ab')
      then have "list.set b' = list.set (concat bs') \<inter> {..< hd (concat cs')}"
        using ss_ab'
        apply (auto simp: strict_sorted_append_iff eq')
         apply (meson strict_sorted_iff \<open>b' < concat cs'\<close> \<open>b' \<noteq> []\<close> \<open>concat cs' \<noteq> []\<close> dual_order.strict_trans2 less_list_def sorted_le_last)
        by (metis strict_sorted_iff UN_I dual_order.strict_trans2 order.asym set_concat sorted_hd_le)

      ultimately show "b = b'"
        by (metis Suc.prems(2) ccat_cs_cs' strict_sorted_append_iff strict_sorted_equal strict_sorted_sorted_wrt sw_ab')
    qed
    moreover
    have "cs = cs' \<and> ds = ds'"
    proof (rule Suc.hyps)
      show "k = length cs"
        using eq Suc.hyps(2) by auto[1]
      show "concat ds = concat ds'"
        using Suc.prems(2) \<open>b = b'\<close> eq'(2) eq(2) by auto
      show "strict_sorted (interact cs ds)"
        using eq Suc.prems(5) strict_sorted_append_iff by auto
      show "length ds \<le> length cs" "length cs \<le> Suc (length ds)"
        using eq Suc.hyps(2) Suc.prems(6) k by auto
      show "strict_sorted (interact cs' ds')"
        using eq' Suc.prems(10) strict_sorted_append_iff by auto
      show "length cs = length cs'"
        using Suc.hyps(2) Suc.prems(13) eq'(1) k(1) by force
    qed (use ccat_cs_cs' eq eq' Suc.prems in auto)
    ultimately show ?thesis
      by (simp add: \<open>a = a'\<close> \<open>b = b'\<close> eq eq')
  qed
qed


proposition Form_Body_unique:
  assumes "Form_Body ka kb xs ys zs" "Form_Body ka kb xs ys zs'" and "kb \<le> ka" "ka \<le> Suc kb"
  shows "zs' = zs"
proof -
  obtain a as b bs c d
      where xs: "xs = concat (a#as)" and ys: "ys = concat (b#bs)"
        and ne: "a#as \<in> lists (- {[]})" "b#bs \<in> lists (- {[]})"
        and len: "length (a#as) = ka" "length (b#bs) = kb"
        and c: "c = acc_lengths 0 (a#as)"
        and d: "d = acc_lengths 0 (b#bs)"
        and Ueq: "zs = concat [c, a, d, b] @ interact as bs"
        and ss_zs: "strict_sorted zs"
    using Form_Body.cases [OF assms(1)] by (metis (no_types))
  obtain a' as' b' bs' c' d'
      where xs': "xs = concat (a'#as')" and ys': "ys = concat (b'#bs')"
        and ne': "a'#as' \<in> lists (- {[]})" "b'#bs' \<in> lists (- {[]})"
        and len': "length (a'#as') = ka" "length (b'#bs') = kb"
        and c': "c' = acc_lengths 0 (a'#as')"
        and d': "d' = acc_lengths 0 (b'#bs')"
        and Ueq': "zs' = concat [c', a', d', b'] @ interact as' bs'"
        and ss_zs': "strict_sorted zs'"
    using Form_Body.cases [OF assms(2)] by (metis (no_types))
  have [simp]: "length c = length c'" "length d = length d'"
    using c c' d d' len' len by auto
  have "a < b"
    using ss_zs apply (simp add: Ueq strict_sorted_append_iff)
    by (metis strict_sorted_iff append.assoc d length_0_conv length_acc_lengths list.distinct(1) strict_sorted_append_iff sorted_trans)
  have "a' < b'"
    using ss_zs' apply (simp add: Ueq' strict_sorted_append_iff)
    by (metis strict_sorted_iff append.assoc d' length_0_conv length_acc_lengths list.distinct(1) strict_sorted_append_iff sorted_trans)
  have "a#as = a'#as' \<and> b#bs = b'#bs'"
  proof (rule interaction_scheme_unique_aux)
    show "concat (a # as) = concat (a' # as')"
      using xs xs' by blast
    show "concat (b # bs) = concat (b' # bs')"
      using ys ys' by blast
    show "a # as \<in> lists (- {[]})" "b # bs \<in> lists (- {[]})"
      using ne by auto
    show "strict_sorted (interact (a # as) (b # bs))"
      using ss_zs \<open>a < b\<close> apply (simp add: Ueq strict_sorted_append_iff)
      by (metis strict_sorted_iff append.assoc append.left_neutral strict_sorted_append_iff sorted_trans)
    show "length (b # bs) \<le> length (a # as)" "length (b' # bs') \<le> length (a' # as')"
      using \<open>kb \<le> ka\<close> len len' by auto
    show "length (a # as) \<le> Suc (length (b # bs))"
      using \<open>ka \<le> Suc kb\<close> len by linarith
    then show "length (a' # as') \<le> Suc (length (b' # bs'))"
      using len len' by fastforce
    show "a' # as' \<in> lists (- {[]})" "b' # bs' \<in> lists (- {[]})"
      using ne' by auto
    show "strict_sorted (interact (a' # as') (b' # bs'))"
      using ss_zs' \<open>a' < b'\<close> apply (simp add: Ueq' strict_sorted_append_iff)
      by (metis strict_sorted_iff append.assoc append.left_neutral strict_sorted_append_iff sorted_trans)
    show "length (a # as) = length (a' # as')"
      using len'(1) len(1) by blast
    show "length (b # bs) = length (b' # bs')"
      using len'(2) len(2) by blast
  qed
  then show ?thesis
    using Ueq Ueq' c c' d d' by blast
qed


lemma Form_Body_imp_inter_scheme:
  assumes "Form_Body ka kb xs ys zs" and "0 < kb" "kb \<le> ka" "ka \<le> Suc kb"
  shows "zs = inter_scheme ((ka+kb) - Suc 0) {xs,ys}"
proof -
  have "length xs < length ys"
    by (meson Form_Body_length assms(1))
  have [simp]: "a + a = b + b \<longleftrightarrow> a=b"  "a + a - Suc 0 = b + b - Suc 0 \<longleftrightarrow> a=b" for a b::nat
    by auto
  show ?thesis
  proof (cases "ka = kb")
    case True
    show ?thesis
      unfolding inter_scheme_def
      apply (rule some_equality [symmetric])
      using assms True mult_2 not_gr0 one_is_add apply fastforce
      using assms \<open>length xs < length ys\<close>
      apply (auto simp: True mult_2 Set.doubleton_eq_iff Form_Body_unique dest: Form_Body_length)
      by presburger
  next
    case False
    then have eq: "ka = Suc kb"
      using assms by linarith
    show ?thesis
      unfolding inter_scheme_def
      apply (rule some_equality [symmetric])
      using assms False mult_2 one_is_add eq apply fastforce
      using assms \<open>length xs < length ys\<close>
       apply (auto simp: eq mult_2 Set.doubleton_eq_iff Form_Body_unique dest: Form_Body_length)
      by presburger
  qed
qed


subsection \<open>For Lemma 3.8 AND PROBABLY 3.7\<close>

definition grab :: "nat set \<Rightarrow> nat \<Rightarrow> nat set \<times> nat set"
  where "grab N n \<equiv> (N \<inter> enumerate N ` {..<n}, N \<inter> {enumerate N n..})"

lemma grab_0 [simp]: "grab N 0 = ({}, N)"
  by (fastforce simp add: grab_def enumerate_0 Least_le)

lemma less_sets_grab:
  "infinite N \<Longrightarrow> fst (grab N n) \<lless> snd (grab N n)"
  by (auto simp: grab_def less_sets_def intro: enumerate_mono less_le_trans)

lemma finite_grab [iff]: "finite (fst (grab N n))"
  by (simp add: grab_def)

lemma card_grab [simp]:
  assumes "infinite N" shows "card (fst (grab N n)) = n"
proof -
  have "N \<inter> enumerate N ` {..<n} = enumerate N ` {..<n}"
    using assms by (auto simp: enumerate_in_set)
  with assms show ?thesis
    by (simp add: card_image grab_def strict_mono_enum strict_mono_imp_inj_on)
qed

lemma fst_grab_subset: "fst (grab N n) \<subseteq> N"
  using grab_def range_enum by fastforce

lemma snd_grab_subset: "snd (grab N n) \<subseteq> N"
  by (auto simp: grab_def)

lemma grab_Un_eq:
  assumes "infinite N" shows "fst (grab N n) \<union> snd (grab N n) = N"
proof
  show "N \<subseteq> fst (grab N n) \<union> snd (grab N n)"
    unfolding grab_def
    using assms enumerate_Ex le_less_linear strict_mono_enum strict_mono_less by fastforce
qed (simp add: grab_def)

lemma finite_grab_iff [simp]: "finite (snd (grab N n)) \<longleftrightarrow> finite N"
  by (metis finite_grab grab_Un_eq infinite_Un infinite_super snd_grab_subset)

lemma grab_eqD:
    "\<lbrakk>grab N n = (A,M); infinite N\<rbrakk>
    \<Longrightarrow> A \<lless> M \<and> finite A \<and> card A = n \<and> infinite M \<and> A \<subseteq> N \<and> M \<subseteq> N"
  using card_grab grab_def less_sets_grab finite_grab_iff by auto

lemma less_sets_fst_grab: "A \<lless> N \<Longrightarrow> A \<lless> fst (grab N n)"
  by (simp add: fst_grab_subset less_sets_weaken2)

text\<open>Possibly redundant, given @{term grab}\<close>
definition nxt where "nxt \<equiv> \<lambda>N. \<lambda>n::nat. N \<inter> {n<..}"

lemma infinite_nxtN: "infinite N \<Longrightarrow> infinite (nxt N n)"
  by (simp add: infinite_nat_greaterThan nxt_def)

lemma nxt_subset: "nxt N n \<subseteq> N"
  unfolding nxt_def by blast

lemma nxt_subset_greaterThan: "m \<le> n \<Longrightarrow> nxt N n \<subseteq> {m<..}"
  by (auto simp: nxt_def)

lemma nxt_subset_atLeast: "m \<le> n \<Longrightarrow> nxt N n \<subseteq> {m..}"
  by (auto simp: nxt_def)

lemma enum_nxt_ge: "infinite N \<Longrightarrow> a \<le> enum (nxt N a) n"
  by (simp add: atLeast_le_enum infinite_nxtN nxt_subset_atLeast)

lemma inj_enum_nxt: "infinite N \<Longrightarrow> inj_on (enum (nxt N a)) A"
  by (simp add: infinite_nxtN strict_mono_enum strict_mono_imp_inj_on)


subsection \<open>Larson's Lemma 3.11\<close>

text \<open>Again from Jean A. Larson,
     A short proof of a partition theorem for the ordinal $\omega^\omega$.
     \emph{Annals of Mathematical Logic}, 6:129–145, 1973.\<close>

lemma lemma_3_11:
  assumes "l > 0"
  shows "thin (inter_scheme l ` {U. Form l U})"
  using form_cases [of l]
proof cases
  case zero
  then show ?thesis
    using assms by auto
next
  case (nz ka kb)
  show ?thesis
    unfolding thin_def
  proof clarify
    fix U U'
    assume ne: "inter_scheme l U \<noteq> inter_scheme l U'" and init: "initial_segment (inter_scheme l U) (inter_scheme l U')"
    assume "Form l U"
    then obtain kp kq xs ys 
      where "l = kp+kq - 1" "U = {xs,ys}" and U: "Form_Body kp kq xs ys (inter_scheme l U)" and "0 < kq" "kq \<le> kp" "kp \<le> Suc kq"
      using assms inter_scheme by blast
    then have "kp = ka \<and> kq = kb"
      using nz by linarith
    then obtain a as b bs c d
      where xs: "xs = concat (a#as)" and ys: "ys = concat (b#bs)"
        and len: "length (a#as) = ka" "length (b#bs) = kb"
        and c: "c = acc_lengths 0 (a#as)"
        and d: "d = acc_lengths 0 (b#bs)"
        and Ueq: "inter_scheme l U = concat [c, a, d, b] @ interact as bs"
      using U by (auto simp: Form_Body.simps)
    assume "Form l U'"
    then obtain kp' kq' xs' ys' 
      where "l = kp'+kq' - 1" "U' = {xs',ys'}" and U': "Form_Body kp' kq' xs' ys' (inter_scheme l U')" and "0 < kq'" "kq' \<le> kp'" "kp' \<le> Suc kq'"
      using assms inter_scheme by blast
    then have "kp' = ka \<and> kq' = kb"
      using nz by linarith
    then obtain a' as' b' bs' c' d'
      where xs': "xs' = concat (a'#as')" and ys': "ys' = concat (b'#bs')"
        and len': "length (a'#as') = ka" "length (b'#bs') = kb"
        and c': "c' = acc_lengths 0 (a'#as')"
        and d': "d' = acc_lengths 0 (b'#bs')"
        and Ueq': "inter_scheme l U' = concat [c', a', d', b'] @ interact as' bs'"
      using U' by (auto simp: Form_Body.simps)
    have [simp]: "length bs' = length bs" "length as' = length as"
      using len len' by auto
    have "inter_scheme l U \<noteq> []" "inter_scheme l U' \<noteq> []"
      using Form_Body_nonempty U U' by auto
    define u1 where "u1 \<equiv> hd (inter_scheme l U)"
    have u1_eq': "u1 = hd (inter_scheme l U')"
      using \<open>inter_scheme l U \<noteq> []\<close> init u1_def initial_segment_ne by fastforce
    have au1: "u1 = length a"
      by (simp add: u1_def Ueq c acc_lengths.simps)
    have au1': "u1 = length a'"
      by (simp add: u1_eq' Ueq' c' acc_lengths.simps)
    have len_eqk: "length c' = ka" "length d' = kb" "length c' = ka" "length d' = kb"
      using c d len c' d' len' by auto
    have take: "take (ka + u1 + kb) (c @ a @ d @ l) = c @ a @ d"
               "take (ka + u1 + kb) (c' @ a' @ d' @ l) = c' @ a' @ d'" for l
      using c d c' d' len by (simp_all add: flip: au1 au1')
    have leU: "ka + u1 + kb \<le> length (inter_scheme l U)"
      using c d len by (simp add: au1 Ueq)
    then have "take (ka + u1 + kb) (inter_scheme l U) = take (ka + u1 + kb) (inter_scheme l U')"
      using take_initial_segment init by blast
    then have \<section>: "c @ a @ d = c' @ a' @ d'"
      by (metis Ueq Ueq' append.assoc concat.simps(2) take)
    have "length (inter_scheme l U) = ka + (c @ a @ d)!(ka-1) + kb + last d"
      by (simp add: Ueq c d length_interact nth_append flip: len)
    moreover have "length (inter_scheme l U') = ka + (c' @ a' @ d')!(ka-1) + kb + last d'"
      by (simp add: Ueq' c' d' length_interact nth_append flip: len')
    moreover have "last d = last d'"
      using "\<section>" c d d' len'(1) len_eqk(1) by auto
    ultimately have "length (inter_scheme l U) = length (inter_scheme l U')"
      by (simp add: \<section>)
    then show False
      using init initial_segment_length_eq ne by blast
  qed
qed


subsection \<open>Larson's Lemma 3.6\<close>

proposition lemma_3_6:
  fixes g :: "nat list set \<Rightarrow> nat"
  assumes g: "g \<in> [WW]\<^bsup>2\<^esup> \<rightarrow> {0,1}"
  obtains N j where "infinite N"
    and "\<And>k u. \<lbrakk>k > 0; u \<in> [WW]\<^bsup>2\<^esup>; Form k u; [enum N k] < inter_scheme k u; List.set (inter_scheme k u) \<subseteq> N\<rbrakk> \<Longrightarrow> g u = j k"
proof -
  define \<Phi> where "\<Phi> \<equiv> \<lambda>m::nat. \<lambda>M. infinite M \<and> m < Inf M"
  define \<Psi> where "\<Psi> \<equiv> \<lambda>l m n::nat. \<lambda>M N j. n > m \<and> N \<subseteq> M \<and> n \<in> M \<and> (\<forall>U. Form l U \<and> U \<subseteq> WW \<and> [n] < inter_scheme l U \<and> list.set (inter_scheme l U) \<subseteq> N \<longrightarrow> g U = j)"
  { fix l m::nat and M :: "nat set"
    assume "l > 0" "\<Phi> m M"
    let ?A = "inter_scheme l ` {U \<in> [WW]\<^bsup>2\<^esup>. Form l U}"
    define h where "h \<equiv> \<lambda>zs. g (inv_into {U \<in> [WW]\<^bsup>2\<^esup>. Form l U} (inter_scheme l) zs)"
    have "thin ?A"
      using \<open>l > 0\<close> lemma_3_11 by (simp add: thin_def)
    moreover
    have "?A \<subseteq> WW"
      using inter_scheme_simple \<open>0 < l\<close> by blast
    moreover
    have "h ` {l \<in> ?A. List.set l \<subseteq> M} \<subseteq> {..<2}"
      using g inv_into_into[of concl: "{U \<in> [WW]\<^bsup>2\<^esup>. Form l U}" "inter_scheme l"]
      by (force simp: h_def Pi_iff)
    ultimately
    obtain j N where "j < 2" "infinite N" "N \<subseteq> M" and hj: "h ` {l \<in> ?A. List.set l \<subseteq> N} \<subseteq> {j}"
      using \<open>\<Phi> m M\<close> unfolding \<Phi>_def by (blast intro: Nash_Williams_WW [of M])
    define n where "n \<equiv> Inf N"
    have "n > m"
      using \<open>\<Phi> m M\<close> \<open>infinite N\<close> unfolding n_def \<Phi>_def Inf_nat_def infinite_nat_iff_unbounded
      by (metis LeastI_ex \<open>N \<subseteq> M\<close> le_less_trans not_less not_less_Least subsetD)
    have "g U = j" if "Form l U" "U \<subseteq> WW" "[n] < inter_scheme l U" "list.set (inter_scheme l U) \<subseteq> N - {n}" for U
    proof -
      obtain xs ys where xys: "xs \<noteq> ys" "U = {xs,ys}"
        using Form_elim_upair \<open>Form l U\<close> by blast
      moreover have "inj_on (inter_scheme l) {U \<in> [WW]\<^bsup>2\<^esup>. Form l U}"
        by (metis (mono_tags, lifting) inter_scheme_injective \<open>0 < l\<close> inj_onI mem_Collect_eq)
      moreover have "g (inv_into {U \<in> [WW]\<^bsup>2\<^esup>. Form l U} (inter_scheme l) (inter_scheme l U)) = j"
        using hj that xys
        apply (simp add: h_def image_subset_iff image_iff)
        by (metis (no_types, lifting) Diff_subset doubleton_in_nsets_2 dual_order.trans)
      ultimately show ?thesis
        using that by auto
    qed
    moreover have "n < Inf (N - {n})"
      unfolding n_def
      by (metis Diff_iff Inf_nat_def Inf_nat_def1 \<open>infinite N\<close> finite.emptyI infinite_remove linorder_neqE_nat not_less_Least singletonI)
    moreover have "n \<in> M"
      by (metis Inf_nat_def1 \<open>N \<subseteq> M\<close> \<open>infinite N\<close> finite.emptyI n_def subsetD)
    ultimately have "\<Phi> n (N - {n}) \<and> \<Psi> l m n M (N - {n}) j"
      using \<open>\<Phi> m M\<close> \<open>infinite N\<close> \<open>N \<subseteq> M\<close> \<open>n > m\<close> by (auto simp: \<Phi>_def \<Psi>_def)
    then have "\<exists>n N j. \<Phi> n N \<and> \<Psi> l m n M N j"
      by blast
  } note * = this
  have base: "\<Phi> 0 {0<..}"
    unfolding \<Phi>_def by (metis infinite_Ioi Inf_nat_def1 greaterThan_iff greaterThan_non_empty)
  have step: "Ex (\<lambda>(n,N,j). \<Phi> n N \<and> \<Psi> l m n M N j)" if "\<Phi> m M" "l > 0" for m M l
    using * [of l m M] that by (auto simp: \<Phi>_def)
  define G where "G \<equiv> \<lambda>l m M. @(n,N,j). \<Phi> n N \<and> \<Psi> (Suc l) m n M N j"
  have G\<Phi>: "(\<lambda>(n,N,j). \<Phi> n N) (G l m M)" and G\<Psi>: "(\<lambda>(n,N,j). \<Psi> (Suc l) m n M N j) (G l m M)"
    if "\<Phi> m M" for l m M
    using step [OF that, of "Suc l"] by (force simp: G_def dest: some_eq_imp)+
  have G_increasing: "(\<lambda>(n,N,j). n > m \<and> N \<subseteq> M \<and> n \<in> M) (G l m M)"  if "\<Phi> m M" for l m M
    using G\<Psi> [OF that, of l] that by (simp add: \<Psi>_def split: prod.split_asm)
  define H where "H \<equiv> rec_nat (0,{0<..},0) (\<lambda>l (m,M,j). G l m M)"
  have H_simps: "H 0 = (0,{0<..},0)" "\<And>l. H (Suc l) = (case H l of (m,M,j) \<Rightarrow> G l m M)"
    by (simp_all add: H_def)
  have H\<Phi>: "(\<lambda>(n,N,j). \<Phi> n N) (H l)" for l
  proof (induction l)
    case 0
    with base show ?case
      by (auto simp: H_simps)
  next
    case (Suc l)
    with G\<Phi> show ?case
      by (force simp: H_simps split: prod.split prod.split_asm)
  qed
  define \<nu> where "\<nu> \<equiv> (\<lambda>l. case H l of (n,M,j) \<Rightarrow> n)"
  have H_inc: "\<nu> l \<ge> l" for l
  proof (induction l)
    case 0
    then show ?case
      by auto
  next
    case (Suc l)
    then show ?case
      using H\<Phi> G_increasing [of "\<nu> l"]
      apply (auto simp: H_simps \<nu>_def split: prod.split prod.split_asm)
      by (metis (mono_tags, lifting) Suc_leI Suc_le_mono case_prod_conv dual_order.trans)
  qed
  let ?N = "range \<nu>"
  define j where "j \<equiv> \<lambda>l. case H l of (n,M,j) \<Rightarrow> j"
  have H_increasing_Suc: "(case H k of (n, N, j') \<Rightarrow> N) \<supseteq> (case H (Suc k) of (n, N, j') \<Rightarrow> insert n N)" for k
    using H\<Phi> [of k]
    by (force simp: H_simps split: prod.split dest: G_increasing [where l=k])
  have H_increasing_superset: "(case H k of (n, N, j') \<Rightarrow> N) \<supseteq> (case H (n+k) of (n, N, j') \<Rightarrow> N)" for k n
  proof (induction n arbitrary:)
    case (Suc n)
    then show ?case
      using H_increasing_Suc [of "n+k"] by (auto split: prod.split_asm)
  qed auto
  then have H_increasing_less: "(case H k of (n, N, j') \<Rightarrow> N) \<supseteq> (case H l of (n, N, j') \<Rightarrow> insert n N)"
    if "k<l" for k l
    by (metis (no_types, lifting) H_increasing_Suc add.commute less_imp_Suc_add order_trans that)

  have "\<nu> k < \<nu> (Suc k)" for k
    using H\<Phi> [of k] unfolding \<nu>_def
    by (auto simp: H_simps split: prod.split dest: G_increasing [where l=k])
  then have strict_mono_\<nu>: "strict_mono \<nu>"
    by (simp add: strict_mono_Suc_iff)
  then have enum_N: "enum ?N = \<nu>"
    by (metis enum_works nat_infinite_iff range_strict_mono_ext)
  have **: "?N \<inter> {n<..} \<subseteq> N'" if H: "H k = (n, N', j)" for n N' k j
  proof clarify
    fix l
    assume "n < \<nu> l"
    then have False if "l \<le> k"
      using that strict_monoD [OF strict_mono_\<nu>, of l k ] H by (force simp: \<nu>_def)
    then have "k < l"
      using not_less by blast
    then obtain M j where Mj: "H l = (\<nu> l,M,j)"
      unfolding \<nu>_def
      by (metis (mono_tags, lifting) case_prod_conv old.prod.exhaust)
    then show "\<nu> l \<in> N'"
      using that H_increasing_less [OF \<open>k<l\<close>] Mj by auto
  qed
  show thesis
  proof
    show "infinite (?N::nat set)"
      using H_inc infinite_nat_iff_unbounded_le by auto
  next
    fix l U
    assume "0 < l" and U: "U \<in> [WW]\<^bsup>2\<^esup>"
      and interU: "[enum ?N l] < inter_scheme l U" "Form l U"
      and sub: "list.set (inter_scheme l U) \<subseteq> ?N"
    obtain k where k: "l = Suc k"
      using \<open>0 < l\<close> gr0_conv_Suc by blast
    have "U \<subseteq> WW"
      using U by (auto simp: nsets_def)
    moreover
    have "g U = v" if "H k = (m, M, j0)" and "G k m M = (n, N', v)"
      for m M j0 n N' v
    proof -
      have n: "\<nu> (Suc k) = n"
        using that by (simp add: \<nu>_def H_simps)
      have "{..enum (range \<nu>) l} \<inter> list.set (inter_scheme l U) = {}"
        using inter_scheme_strict_sorted \<open>0 < l\<close> interU singleton_less_list_iff strict_sorted_iff by blast
      then have "list.set (inter_scheme (Suc k) U) \<subseteq> N'"
        using that sub ** [of "Suc k" n N' v] Suc_le_eq not_less_eq_eq
        by (fastforce simp add:  k n enum_N H_simps)
      then show ?thesis
        using that interU \<open>U \<subseteq> WW\<close> G\<Psi> [of m M k] H\<Phi> [of k]
        by (auto simp: \<Psi>_def k enum_N H_simps n)
    qed
    ultimately show "g U = j l"
      by (auto simp: k j_def H_simps split: prod.split)
  qed
qed


subsection \<open>Larson's Lemma 3.7\<close>

subsubsection \<open>Preliminaries\<close>

text \<open>Analogous to @{thm [source] ordered_nsets_2_eq}, but without type classes\<close>
lemma total_order_nsets_2_eq:
  assumes tot: "total_on A r" and irr: "irrefl r"
  shows "nsets A 2 = {{x,y} | x y. x \<in> A \<and> y \<in> A \<and> (x,y) \<in> r}"
     (is "_ = ?rhs")
proof
  show "nsets A 2 \<subseteq> ?rhs"
    unfolding numeral_nat
    apply (clarsimp simp add: nsets_def card_Suc_eq Set.doubleton_eq_iff not_less)
    by (metis tot total_on_def)
  show "?rhs \<subseteq> nsets A 2"
    using irr unfolding numeral_nat by (force simp: nsets_def card_Suc_eq irrefl_def)
qed

lemma lenlex_nsets_2_eq: "nsets A 2 = {{x,y} | x y. x \<in> A \<and> y \<in> A \<and> (x,y) \<in> lenlex less_than}"
  using total_order_nsets_2_eq by (simp add: total_order_nsets_2_eq irrefl_def)

lemma sum_sorted_list_of_set_map: "finite I \<Longrightarrow> sum_list (map f (list_of I)) = sum f I"
proof (induction "card I" arbitrary: I)
  case 0
  then show ?case
    by auto
next
  case (Suc n I)
  then have [simp]: "I \<noteq> {}"
    by auto
  moreover have "sum_list (map f (list_of (I - {Min I}))) = sum f (I - {Min I})"
    using Suc by auto
  ultimately show ?case
    using Suc.prems sum.remove [of I "Min I" f]
    by (simp add: sorted_list_of_set_nonempty Suc)
qed


lemma sorted_list_of_set_UN_eq_concat:
  assumes I: "strict_mono_sets I f" "finite I" and fin: "\<And>i. finite (f i)"
  shows "list_of (\<Union>i \<in> I. f i) = concat (map (list_of \<circ> f) (list_of I))"
  using I
proof (induction "card I" arbitrary: I)
  case 0
  then have "I={}" by auto
  then show ?case by auto
next
  case (Suc n I)
  then have "I \<noteq> {}" and Iexp: "I = insert (Min I) (I - {Min I})"
    using Min_in Suc.hyps(2) Suc.prems(2) by fastforce+
  have IH: "list_of (\<Union> (f ` (I - {Min I}))) = concat (map (list_of \<circ> f) (list_of (I - {Min I})))"
    using Suc
    by (metis DiffE Min_in \<open>I \<noteq> {}\<close> card_Diff_singleton diff_Suc_1 finite_Diff strict_mono_sets_def)
  have "list_of (\<Union> (f ` I)) = list_of (\<Union> (f ` (insert (Min I) (I - {Min I}))))"
    using Iexp by auto
  also have "\<dots> = list_of (f (Min I) \<union> \<Union> (f ` (I - {Min I})))"
    by (metis Union_image_insert)
  also have "\<dots> = list_of (f (Min I)) @ list_of (\<Union> (f ` (I - {Min I})))"
  proof (rule sorted_list_of_set_Un)
    show "f (Min I) \<lless> \<Union> (f ` (I - {Min I}))"
      using Suc.prems \<open>I \<noteq> {}\<close> strict_mono_less_sets_Min by blast
    show "finite (\<Union> (f ` (I - {Min I})))"
      by (simp add: \<open>finite I\<close> fin)
  qed (use fin in auto)
  also have "\<dots> = list_of (f (Min I)) @ concat (map (list_of \<circ> f) (list_of (I - {Min I})))"
    using IH by metis
  also have "\<dots> = concat (map (list_of \<circ> f) (list_of I))"
    by (simp add: Suc.prems(2) \<open>I \<noteq> {}\<close> sorted_list_of_set_nonempty)
  finally show ?case .
qed

subsubsection \<open>Lemma 3.7 of Jean A. Larson, ibid.\<close>

text \<open>Possibly should be redone using grab\<close>
proposition lemma_3_7:
  assumes "infinite N" "l > 0"
  obtains M where "M \<in> [WW]\<^bsup>m\<^esup>"
                  "\<And>U. U \<in> [M]\<^bsup>2\<^esup> \<Longrightarrow> Form l U \<and> List.set (inter_scheme l U) \<subseteq> N"
proof (cases "m < 2")
  case True
  obtain w where w: "w \<in> WW"
    using WW_def strict_sorted_into_WW by auto
  define M where "M \<equiv> if m=0 then {} else {w}"
  have M: "M \<in> [WW]\<^bsup>m\<^esup>"
    using True by (auto simp: M_def nsets_def w)
  have [simp]: "[M]\<^bsup>2\<^esup> = {}"
    using True by (auto simp: M_def nsets_def w dest: subset_singletonD)
  show ?thesis
    using M that by fastforce
next
  case False
  then have "m \<ge> 2"
    by auto
  have nonz: "(enum N \<circ> Suc) i > 0" for i
    using assms(1) le_enumerate less_le_trans by fastforce
  note infinite_nxtN [OF \<open>infinite N\<close>, iff]

  have [simp]: "{n<..<Suc n} = {}" for n
    by auto

  define DF where "DF \<equiv> \<lambda>k. rec_nat ((enum N \<circ> Suc) ` {..<Suc k}) (\<lambda>r D. enum (nxt N (enum (nxt N (Max D)) (Inf D - Suc 0))) ` {..<Suc k})"
  have DF_simps: "DF k 0 = (enum N \<circ> Suc) ` {..<Suc k}"
    "DF k (Suc i) = enum (nxt N (enum (nxt N (Max (DF k i))) (Inf (DF k i) - Suc 0))) ` {..<Suc k}" for i k
    by (auto simp: DF_def)

  have card_DF: "card (DF k i) = Suc k" for i k
  proof (induction i)
    case 0
    have "inj_on (enum N \<circ> Suc) {..<Suc k}"
      by (simp add: assms(1) comp_inj_on strict_mono_enum strict_mono_imp_inj_on)
    with 0 show ?case
      using card_image DF_simps by fastforce
  next
    case (Suc i)
    then show ?case
      by (simp add: \<open>infinite N\<close> DF_simps card_image infinite_nxtN strict_mono_enum strict_mono_imp_inj_on)
  qed
  have DF_ne: "DF k i \<noteq> {}" for i k
    by (metis card_DF card_lessThan lessThan_empty_iff nat.simps(3))
  have DF_N: "DF k i \<subseteq> N \<inter> {0<..}" for i k
  proof (induction i)
    case 0
    then show ?case
      using \<open>infinite N\<close> range_enum nonz by (auto simp: DF_simps)
  next
    case (Suc i)
    then show ?case
      unfolding DF_simps image_subset_iff
      using infinite_nxtN [OF \<open>infinite N\<close>]
      by (metis Int_iff enumerate_in_set greaterThan_iff not_gr0 not_less0 nxt_def)
  qed
  then have DF_gt0: "0 < Inf (DF k i)" for i k
    using DF_ne Inf_nat_def1 by blast
  have finite_DF: "finite (DF k i)" for i k
    by (induction i) (auto simp: DF_simps)

  have sm_enum_DF: "strict_mono_on (enum (DF k i)) {..k}" for k i
    by (metis card_DF enum_works_finite finite_DF lessThan_Suc_atMost)

  have DF_Suc: "DF k i \<lless> DF k (Suc i)" for i k
    unfolding less_sets_def
    by (force simp: finite_DF DF_simps
        intro!: greaterThan_less_enum nxt_subset_greaterThan atLeast_le_enum nxt_subset_atLeast infinite_nxtN [OF \<open>infinite N\<close>])
  have DF_DF: "DF k i \<lless> DF k j" if "i<j" for i j k
    by (meson DF_Suc DF_ne UNIV_I less_sets_imp_strict_mono_sets strict_mono_setsD that)
  then have sm_DF: "strict_mono_sets UNIV (DF k)" for k
    by (simp add: strict_mono_sets_def)

  define AF where "AF \<equiv> \<lambda>k i. enum (nxt N (Max (DF k i))) ` {..<Inf (DF k i)}"
  have AF_ne: "AF k i \<noteq> {}" for i k
    by (auto simp: AF_def lessThan_empty_iff DF_gt0)
  have finite_AF [simp]: "finite (AF k i)" for i k
    by (simp add: AF_def)
  have card_AF: "card (AF k i) = \<Sqinter> (DF k i)" for k i
    by (simp add: AF_def \<open>infinite N\<close> card_image inj_enum_nxt)

  have DF_AF: "DF k i \<lless> AF k i" for i k
    unfolding less_sets_def AF_def
    by (simp add: finite_DF \<open>infinite N\<close> greaterThan_less_enum nxt_subset_greaterThan)

  have AF_DF_Suc: "AF k i \<lless> DF k (Suc i)" for i k
    apply (clarsimp simp: DF_simps less_sets_def AF_def)
    using strict_monoD [OF strict_mono_enum]
    by (metis DF_gt0 Suc_pred assms(1) dual_order.order_iff_strict greaterThan_less_enum
        infinite_nxtN linorder_neqE_nat not_less_eq nxt_subset_greaterThan)

  have AF_DF: "AF k p \<lless> DF k q" if "p<q" for k p q
    using AF_DF_Suc
    by (metis DF_ne Suc_lessI UNIV_I less_sets_trans sm_DF strict_mono_sets_def that)

  have AF_Suc: "AF k i \<lless> AF k (Suc i)" for i k
    using AF_DF_Suc DF_AF DF_ne less_sets_trans by blast
  then have sm_AF: "strict_mono_sets UNIV (AF k)" for k
    by (simp add: AF_ne less_sets_imp_strict_mono_sets)

  define del where "del \<equiv> \<lambda>k i j. enum (DF k i) j - enum (DF k i) (j - Suc 0)"

  define QF where "QF k \<equiv> wfrec pair_less (\<lambda>f (j,i).
       if j=0 then AF k i
       else let r = (if i=0 then f (j-1,m-1) else f (j,i-1)) in
                enum (nxt N (Suc (Max r))) ` {..< del k (if j=k then m - Suc i else i) j})"
    for k
  note cut_apply [simp]

  have finite_QF [simp]: "finite (QF k p)" for p k
    using wf_pair_less
  proof (induction p rule: wf_induct_rule)
    case (less p)
    then show ?case
      by (simp add: def_wfrec [OF QF_def, of k p] split: prod.split)
  qed

  have del_gt_0: "\<lbrakk>j < Suc k; 0 < j\<rbrakk> \<Longrightarrow> 0 < del k i j" for i j k
    by (simp add: card_DF del_def finite_DF)

  have QF_ne [simp]: "QF k (j,i) \<noteq> {}" if j: "j < Suc k" for j i k
    using wf_pair_less j
  proof (induction "(j,i)" rule: wf_induct_rule)
    case less
    then show ?case
      by (auto simp: def_wfrec [OF QF_def, of k "(j,i)"] AF_ne lessThan_empty_iff del_gt_0)
  qed

  have QF_0 [simp]: "QF k (0,i) = AF k i" for i k
    by (simp add: def_wfrec [OF QF_def])

  have QF_Suc: "QF k (Suc j,0) = enum (nxt N (Suc (Max (QF k (j, m - Suc 0))))) `
                       {..< del k (if Suc j = k then m - 1 else 0) (Suc j)}" for j k
    apply (simp add: def_wfrec [OF QF_def, of k "(Suc j,0)"])
    apply (simp add: pair_less_def cut_def)
    done

  have QF_Suc_Suc: "QF k (Suc j, Suc i)
                  = enum (nxt N (Suc (Max (QF k (Suc j, i))))) ` {..< del k (if Suc j = k then m - Suc(Suc i) else Suc i) (Suc j)}"
    for i j k
    by (simp add: def_wfrec [OF QF_def, of k "(Suc j,Suc i)"])

  have less_QF1: "QF k (j, m - Suc 0) \<lless> QF k (Suc j,0)" for j k
    by (auto simp: def_wfrec [OF QF_def, of k "(Suc j,0)"] pair_lessI1 \<open>infinite N\<close> enum_nxt_ge
        intro!: less_sets_weaken2 [OF less_sets_Suc_Max])

  have less_QF2: "QF k (j,i) \<lless> QF k (j, Suc i)" for j i k
    by (auto simp: def_wfrec [OF QF_def, of k "(j, Suc i)"] pair_lessI2 \<open>infinite N\<close> enum_nxt_ge
        intro: less_sets_weaken2 [OF less_sets_Suc_Max] strict_mono_setsD [OF sm_AF])

  have less_QF_same: "QF k (j,i') \<lless> QF k (j,i)"
    if "i' < i" "j \<le> k" for i' i j k
  proof (rule strict_mono_setsD [OF less_sets_imp_strict_mono_sets [of "\<lambda>i. QF k (j,i)"]])
    show "QF k (j, i) \<lless> QF k (j, Suc i)" for i
      by (simp add: less_QF2)
    show "QF k (j, i) \<noteq> {}" if "0 < i" for i
      using that by (simp add: \<open>j \<le> k\<close> le_imp_less_Suc)
  qed (use that in auto)

  have less_QF_step: "QF k (j - Suc 0, i') \<lless> QF k (j,i)"
    if "0 < j" "j \<le> k" "i' < m" for j i' i k
  proof -
    have less_QF1': "QF k (j - Suc 0, m - Suc 0) \<lless> QF k (j,0)" if "j > 0" for j
      by (metis less_QF1 that Suc_pred)
    have \<section>: "QF k (j - Suc 0, i') \<lless> QF k (j,0)"
    proof (cases "i' = m - Suc 0")
      case True
      then show ?thesis
        using less_QF1' \<open>0 < j\<close> by blast
    next
      case False
      show ?thesis
        using False that less_sets_trans [OF less_QF_same less_QF1' QF_ne] by auto
    qed
    then show ?thesis
      by (metis QF_ne less_QF_same less_Suc_eq_le less_sets_trans \<open>j \<le> k\<close> zero_less_iff_neq_zero)
  qed

  have less_QF: "QF k (j',i') \<lless> QF k (j,i)"
    if j: "j' < j" "j \<le> k" and i: "i' < m" "i < m" for j' j i' i k
    using j
  proof (induction "j-j'" arbitrary: j)
    case 0
    then show ?case
      by auto
  next
    case (Suc d)
    then have eq: "d = (j - Suc 0) - j'"
      by linarith
    show ?case
    proof (cases "j' < j - Suc 0")
      case True
      then have "QF k (j', i') \<lless> QF k (j - Suc 0, i)"
        using Suc eq by auto
      then show ?thesis
        by (rule less_sets_trans [OF _ less_QF_step QF_ne]) (use Suc i in auto)
    next
      case False
      then have "j' = j - Suc 0"
        using \<open>j' < j\<close> by linarith
      then show ?thesis
        using Suc.hyps \<open>j \<le> k\<close> less_QF_step i by auto
    qed
  qed

  have sm_QF: "strict_mono_sets ({..k} \<times> {..<m}) (QF k)" for k
    unfolding strict_mono_sets_def
  proof (intro strip)
    fix p q
    assume p: "p \<in> {..k} \<times> {..<m}" and q: "q \<in> {..k} \<times> {..<m}" and "p < q"
    then obtain j' i' j i where \<section>: "p = (j',i')" "q = (j,i)" "i' < m" "i < m" "j' \<le> k" "j \<le> k"
      using surj_pair [of p] surj_pair [of q] by blast
    with \<open>p < q\<close> have "j' < j \<or> j' = j \<and> i' < i"
      by auto
    then show "QF k p \<lless> QF k q"
    proof (elim conjE disjE)
      assume "j' < j"
      show "QF k p \<lless> QF k q"
        by (simp add: \<section> \<open>j' < j\<close> less_QF that)
    qed (use \<section> in \<open>simp add: that less_QF_same\<close>)
  qed
  then have sm_QF1: "strict_mono_sets {..<ka} (\<lambda>j. QF k (j,i))"
    if "i<m" "Suc k \<ge> ka" "ka \<ge> k" for ka k i
  proof -
    have "{..<ka} \<subseteq> {..k}"
      by (metis lessThan_Suc_atMost lessThan_subset_iff \<open>Suc k \<ge> ka\<close>)
    then show ?thesis
      by (simp add: less_QF strict_mono_sets_def subset_iff that)
  qed

  have disjoint_QF: "i'=i \<and> j'=j" if "\<not> disjnt (QF k (j', i')) (QF k (j,i))" "j' \<le> k" "j \<le> k" "i' < m" "i < m" for i' i j' j k
    using that strict_mono_sets_imp_disjoint [OF sm_QF]
    by (force simp: pairwise_def)

  have card_QF: "card (QF k (j,i)) = (if j=0 then \<Sqinter> (DF k i) else del k (if j = k then m - Suc i else i) j)"
    for i k j
  proof (cases j)
    case 0
    then show ?thesis
      by (simp add: AF_def card_image \<open>infinite N\<close> inj_enum_nxt)
  next
    case (Suc j')
    show ?thesis
      by (cases i; simp add: Suc QF_Suc QF_Suc_Suc card_image \<open>infinite N\<close> inj_enum_nxt)
  qed
  have AF_non_Nil: "list_of (AF k i) \<noteq> []" for k i
    by (simp add: AF_ne)
  have QF_non_Nil: "list_of (QF k (j,i)) \<noteq> []" if "j < Suc k" for i j k
    by (simp add: that)

  have AF_subset_N: "AF k i \<subseteq> N" for i k
    unfolding AF_def image_subset_iff
    using nxt_subset enumerate_in_set infinite_nxtN \<open>infinite N\<close> by blast

  have QF_subset_N: "QF k (j,i) \<subseteq> N" for i j k
  proof (induction j)
    case 0
    with AF_subset_N show ?case
      by auto
  next
    case (Suc j)
    show ?case
      by (cases i) (use nxt_subset enumerate_in_set in \<open>(force simp: QF_Suc QF_Suc_Suc)+\<close>)
  qed

  obtain ka k where "k>0" and kka: "k \<le> ka" "ka \<le> Suc k" "l = ((ka+k) - Suc 0)"
    by (metis One_nat_def assms(2) diff_add_inverse form_cases le0 le_refl)
  then have "ka > 0"
    using dual_order.strict_trans1 by blast
  have ka_k_or_Suc: "ka = k \<or> ka = Suc k"
    using kka by linarith
  have lessThan_k: "{..<k} = insert 0 {0<..<k}" if "k>0" for k::nat
    using that by auto
  then have sorted_list_of_set_k: "list_of {..<k} = 0 # list_of {0<..<k}" if "k>0" for k::nat
    using sorted_list_of_set_insert_cons [of concl: 0 "{0<..<k}"] that by simp

  define RF where "RF \<equiv> \<lambda>j i. if j = k then QF k (j, m - Suc i) else QF k (j,i)"
  have RF_subset_N: "RF j i \<subseteq> N" if "i<m" for i j
    using that QF_subset_N by (simp add: RF_def)
  have finite_RF [simp]: "finite (RF k p)" for p k
    by (simp add: RF_def)
  have RF_0: "RF 0 i = AF k i" for i
    using RF_def \<open>0 < k\<close> by auto
  have disjoint_RF: "i'=i \<and> j'=j" if "\<not> disjnt (RF j' i') (RF j i)" "j' \<le> k" "j \<le> k" "i' < m" "i < m" for i' i j' j
    using disjoint_QF that
    by (auto simp: RF_def split: if_split_asm dest: disjoint_QF)

  have sum_card_RF [simp]: "(\<Sum>j\<le>n. card (RF j i)) = enum (DF k i) n" if "n \<le> k" "i < m" for i n
    using that
  proof (induction n)
    case 0
    then show ?case
      using DF_ne [of k i] finite_DF [of k i] \<open>k>0\<close>
      by (simp add: RF_def AF_def card_image \<open>infinite N\<close> inj_enum_nxt enum_0_eq_Inf_finite)
  next
    case (Suc n)
    then have "enum (DF k i) 0 \<le> enum (DF k i) n \<and> enum (DF k i) n \<le> enum (DF k i) (Suc n)"
      using sm_enum_DF [of k i]
      apply (simp add: strict_mono_on_def)
      by (metis Suc_leD dual_order.order_iff_strict le0)
    with Suc show ?case
      by (auto simp: RF_def card_QF del_def)
  qed
  have DF_in_N: "enum (DF k i) j \<in> N" if "j \<le> k" for i j
    using DF_N [of k i] card_DF finite_enumerate_in_set finite_DF that
    by (metis inf.boundedE le_imp_less_Suc subsetD)
  have Inf_DF_N: "\<Sqinter>(DF k p) \<in> N" for k p
    using DF_N DF_ne Inf_nat_def1 by blast
  have RF_in_N: "(\<Sum>j\<le>n. card (RF j i)) \<in> N" if "n \<le> k" "i < m" for i n
    by (auto simp: DF_in_N that)

  have "ka - Suc 0 \<le> k"
    using kka(2) by linarith
  then have sum_card_RF' [simp]:
    "(\<Sum>j<ka. card (RF j i)) = enum (DF k i) (ka - Suc 0)" if "i < m" for i
    using sum_card_RF [of "ka - Suc 0" i]
    by (metis Suc_pred \<open>0 < ka\<close> lessThan_Suc_atMost that)

  have enum_DF_le_iff [simp]:
    "enum (DF k i) j \<le> enum (DF k i') j \<longleftrightarrow> i \<le> i'" (is "?lhs = _")
    if "j \<le> k" for i' i j k
  proof
    show "i \<le> i'" if ?lhs
    proof -
      have "enum (DF k i) j \<in> DF k i"
        by (simp add: card_DF finite_enumerate_in_set finite_DF le_imp_less_Suc \<open>j \<le> k\<close>)
      moreover have "enum (DF k i') j \<in> DF k i'"
        by (simp add: \<open>j \<le> k\<close> card_DF finite_enumerate_in_set finite_DF le_imp_less_Suc that)
      ultimately have "enum (DF k i') j < enum (DF k i) j" if "i' < i"
        using sm_DF [of k] by (meson UNIV_I less_sets_def strict_mono_setsD that)
      then show ?thesis
        using not_less that by blast
    qed
    show ?lhs if "i \<le> i'"
      using sm_DF [of k] that \<open>j \<le> k\<close> card_DF finite_enumerate_in_set finite_DF le_eq_less_or_eq
      by (force simp: strict_mono_sets_def less_sets_def finite_enumerate_in_set)
  qed
  then have enum_DF_eq_iff[simp]:
    "enum (DF k i) j = enum (DF k i') j \<longleftrightarrow> i = i'" if "j \<le> k" for i' i j k
    by (metis le_antisym order_refl that)
  have enum_DF_less_iff [simp]:
    "enum (DF k i) j < enum (DF k i') j \<longleftrightarrow> i < i'" if "j \<le> k" for i' i j k
    by (meson enum_DF_le_iff not_less that)

  have card_AF_sum: "card (AF k i) + (\<Sum>j\<in>{0<..<ka}. card (RF j i)) = enum (DF k i) (ka-1)"
    if "i < m" for i
    using that \<open>k > 0\<close>  \<open>k \<le> ka\<close> \<open>ka \<le> Suc k\<close>
    by (simp add: lessThan_k RF_0 flip: sum_card_RF')

  have sorted_list_of_set_iff [simp]: "list_of {0<..<k} = [] \<longleftrightarrow> k = Suc 0" if "k>0" for k::nat
  proof -
    have "list_of {0<..<k} = [] \<longleftrightarrow> {0<..<k} = {}"
      by simp
    also have "\<dots> \<longleftrightarrow> k = Suc 0"
      using \<open>k > 0\<close> atLeastSucLessThan_greaterThanLessThan by fastforce
    finally show ?thesis .
  qed
  show thesis \<comment>\<open>proof of main result\<close>
  proof
    have inj: "inj_on (\<lambda>i. list_of (\<Union>j<ka. RF j i)) {..<m}"
    proof (clarsimp simp: inj_on_def)
      fix x y
      assume "x < m" "y < m" "list_of (\<Union>j<ka. RF j x) = list_of (\<Union>j<ka. RF j y)"
      then have eq: "(\<Union>j<ka. RF j x) = (\<Union>j<ka. RF j y)"
        by (simp add: sorted_list_of_set_inject)
      show "x = y"
      proof -
        obtain n where n: "n \<in> RF 0 x"
          using AF_ne QF_0 \<open>0 < k\<close> Inf_nat_def1 \<open>k \<le> ka\<close> by (force simp: RF_def)
        with eq \<open>ka > 0\<close> obtain j' where "j' < ka" "n \<in> RF j' y"
          by blast
        then show ?thesis
          using disjoint_QF [of k 0 x j'] n \<open>x < m\<close> \<open>y < m\<close> \<open>ka \<le> Suc k\<close> \<open>0 < k\<close>
          by (force simp: RF_def disjnt_iff simp del: QF_0 split: if_split_asm)
      qed
    qed

    define M where "M \<equiv> (\<lambda>i. list_of (\<Union>j<ka. RF j i)) ` {..<m}"

    have "finite M"
      unfolding M_def by blast
    moreover have "card M = m"
      by (simp add: M_def \<open>k \<le> ka\<close> card_image inj)
    moreover have "M \<subseteq> WW"
      by (force simp: M_def WW_def)
    ultimately show "M \<in> [WW]\<^bsup>m\<^esup>"
      by (simp add: nsets_def)

    have sm_RF: "strict_mono_sets {..<ka} (\<lambda>j. RF j i)" if "i<m" for i
      using sm_QF1 that kka
      by (simp add: less_QF RF_def strict_mono_sets_def)

    have RF_non_Nil: "list_of (RF j i) \<noteq> []" if "j < Suc k" for i j
      using that by (simp add: RF_def)

    have less_RF_same: "RF j i' \<lless> RF j i"
      if "i' < i" "j < k" for i' i j
      using that by (simp add: less_QF_same RF_def)

    have less_RF_same_k: "RF k i' \<lless> RF k i" \<comment>\<open>reversed version for @{term k}\<close>
      if "i < i'" "i' < m" for i' i
      using that by (simp add: less_QF_same RF_def)

    show "Form l U \<and> list.set (inter_scheme l U) \<subseteq> N" if "U \<in> [M]\<^bsup>2\<^esup>" for U
    proof -
      from that obtain x y where "U = {x,y}" "x \<in> M" "y \<in> M" and xy: "(x,y) \<in> lenlex less_than"
        by (auto simp: lenlex_nsets_2_eq)
      let ?R = "\<lambda>p. list_of \<circ> (\<lambda>j. RF j p)"
      obtain p q where x: "x = list_of (\<Union>j<ka. RF j p)"
        and y: "y = list_of (\<Union>j<ka. RF j q)" and "p < m" "q < m"
        using \<open>x \<in> M\<close> \<open>y \<in> M\<close> by (auto simp: M_def)
      then have pq: "p<q" "length x < length y"
        using xy \<open>k \<le> ka\<close> \<open>ka \<le> Suc k\<close> lexl_not_refl [OF irrefl_less_than]
        by (auto simp: lenlex_def sm_RF sorted_list_of_set_UN_lessThan length_concat sum_sorted_list_of_set_map)
      moreover
      have xc: "x = concat (map (?R p) (list_of {..<ka}))"
        by (simp add: x sorted_list_of_set_UN_eq_concat \<open>k \<le> ka\<close> \<open>ka \<le> Suc k\<close> \<open>p < m\<close> sm_RF)
      have yc: "y = concat (map (?R q) (list_of {..<ka}))"
        by (simp add: y sorted_list_of_set_UN_eq_concat \<open>k \<le> ka\<close> \<open>ka \<le> Suc k\<close> \<open>q < m\<close> sm_RF)
      have enum_DF_AF: "enum (DF k p) (ka - Suc 0) < hd (list_of (AF k p))" for p
      proof (rule less_setsD [OF DF_AF])
        show "enum (DF k p) (ka - Suc 0) \<in> DF k p"
          using \<open>ka \<le> Suc k\<close> card_DF finite_DF by (auto simp: finite_enumerate_in_set)
        show "hd (list_of (AF k p)) \<in> AF k p"
          using AF_non_Nil finite_AF hd_in_set set_sorted_list_of_set by blast
      qed

      have less_RF_RF: "RF n p \<lless> RF n q" if "n < k" for n
        using that \<open>p<q\<close> by (simp add: less_RF_same)
      have less_RF_Suc: "RF n q \<lless> RF (Suc n) q" if "n < k" for n
        using \<open>q < m\<close> that by (auto simp: RF_def less_QF)
      have less_RF_k: "RF k q \<lless> RF k p"
        using \<open>q < m\<close> less_RF_same_k \<open>p<q\<close> by blast
      have less_RF_k_ka: "RF (k - Suc 0) p \<lless> RF (ka - Suc 0) q"
        using ka_k_or_Suc less_RF_RF
        by (metis One_nat_def RF_def \<open>0 < k\<close> \<open>ka - Suc 0 \<le> k\<close> \<open>p < m\<close> diff_Suc_1 diff_Suc_less less_QF_step)
      have Inf_DF_eq_enum: "\<Sqinter> (DF k i) = enum (DF k i) 0" for k i
        by (simp add: Inf_nat_def enumerate_0)

      have Inf_DF_less: "\<Sqinter> (DF k i') < \<Sqinter> (DF k i)" if "i'<i" for i' i k
        by (metis DF_ne enum_0_eq_Inf enum_0_eq_Inf_finite enum_DF_less_iff le0 that)
      have AF_Inf_DF_less: "\<And>x. x \<in> AF k i \<Longrightarrow> \<Sqinter> (DF k i') < x" if "i'\<le>i" for i' i
        using less_setsD [OF DF_AF] DF_ne that
        by (metis Inf_DF_less Inf_nat_def1 dual_order.order_iff_strict dual_order.strict_trans)

      show ?thesis
      proof (cases "k=1")
        case True
        with kka consider "ka=1" | "ka=2" by linarith
        then show ?thesis
        proof cases
          case 1
          define zs where "zs = card (AF 1 p) # list_of (AF 1 p)
                              @ card (AF 1 q) # list_of (AF 1 q)"
          have zs: "Form_Body ka k x y zs"
          proof (intro that exI conjI Form_Body.intros [OF \<open>length x < length y\<close>])
            show "x = concat ([list_of (AF k p)])" "y = concat ([list_of (AF k q)])"
              by (simp_all add: x y 1 lessThan_Suc RF_0)
            have "AF k p \<lless> insert (\<Sqinter> (DF k q)) (AF k q)"
              by (metis AF_DF DF_ne Inf_nat_def1 RF_0 \<open>0 < k\<close> insert_iff less_RF_RF less_sets_def pq(1))
            then have "strict_sorted (list_of (AF k p) @ \<Sqinter> (DF k q) # list_of (AF k q))"
              by (auto simp: strict_sorted_append_iff intro: less_sets_imp_list_less AF_Inf_DF_less)
            moreover have "\<And>x. x \<in> AF k q \<Longrightarrow> \<Sqinter> (DF k p) < x"
              by (meson AF_Inf_DF_less less_imp_le_nat \<open>p < q\<close>)
            ultimately show "strict_sorted zs"
              using \<open>p < q\<close> True Inf_DF_less DF_AF DF_ne
              apply (auto simp: zs_def less_sets_def card_AF AF_Inf_DF_less)
              by (meson Inf_nat_def1)
          qed (auto simp: \<open>k=1\<close> \<open>ka=1\<close> acc_lengths.simps zs_def AF_ne)
          have zs_N: "list.set zs \<subseteq> N"
            using AF_subset_N by (auto simp: zs_def card_AF Inf_DF_N \<open>k=1\<close>)
          show ?thesis
          proof
            have "l = 1"
              using kka \<open>k=1\<close> \<open>ka=1\<close> by auto
            have "Form (2*1-1) {x,y}"
              using "1" Form.intros(2) True zs by fastforce
            then show "Form l U"
              by (simp add: \<open>U = {x,y}\<close> \<open>l = 1\<close>)
            show "list.set (inter_scheme l U) \<subseteq> N"
              using kka zs zs_N \<open>k=1\<close> Form_Body_imp_inter_scheme by (fastforce simp add: \<open>U = {x,y}\<close>)
          qed
        next
          case 2
          note True [simp] note 2 [simp]
          have [simp]: "{0<..<2} = {Suc 0}"
            by auto
          have enum_DF1_eq: "enum (DF (Suc 0) i) (Suc 0) = card (AF (Suc 0) i) + card (RF (Suc 0) i)"
            if "i < m" for i
            using card_AF_sum that by simp
          have card_RF: "card (RF (Suc 0) i) = enum (DF (Suc 0) i) (Suc 0) - enum (DF (Suc 0) i) 0" if "i < m" for i
            using that by (auto simp: RF_def card_QF del_def)
          have list_of_AF_RF: "list_of (AF (Suc 0) q \<union> RF (Suc 0) q) = list_of (AF (Suc 0) q) @ list_of (RF (Suc 0) q)"
            using RF_def \<open>q < m\<close> less_QF_step by (fastforce intro!: sorted_list_of_set_Un)

          define zs where "zs = card (AF 1 p) # (card (AF 1 p) + card (RF 1 p))
                         # list_of (AF 1 p)
                  @ (card (AF 1 q) + card (RF 1 q)) # list_of (AF 1 q) @ list_of (RF 1 q) @ list_of (RF 1 p)"
          have zs: "Form_Body ka k x y zs"
          proof (intro that exI conjI Form_Body.intros [OF \<open>length x < length y\<close>])
            have "x = list_of (RF 0 p \<union> RF (Suc 0) p)"
              by (simp add: x eval_nat_numeral lessThan_Suc RF_0 Un_commute)
            also have "\<dots> = list_of (RF 0 p) @ list_of (RF (Suc 0) p)"
              using RF_def True \<open>p < m\<close> less_QF_step
              by (subst sorted_list_of_set_Un) (fastforce+)
            finally show "x = concat ([list_of (AF 1 p),list_of (RF 1 p)])"
              by (simp add: RF_0)
            show "y = concat [list_of (RF 1 q \<union> AF 1 q)]"
              by (simp add: y eval_nat_numeral lessThan_Suc RF_0)
            show "zs = concat [[card (AF 1 p), card (AF 1 p) + card (RF 1 p)], list_of (AF 1 p),
                              [card (AF 1 q) + card (RF 1 q)], list_of (RF 1 q \<union> AF 1 q)] @ interact [list_of (RF 1 p)] []"
              using list_of_AF_RF by (simp add: zs_def Un_commute)
            show "strict_sorted zs"
            proof (simp add: \<open>p<m\<close> \<open>q<m\<close> \<open>p<q\<close> zs_def strict_sorted_append_iff, intro conjI strip)
              show "0 < card (RF (Suc 0) p)"
                using \<open>p<m\<close> by (simp add: card_RF card_DF finite_DF)
              show "card (AF (Suc 0) p) < card (AF (Suc 0) q) + card (RF (Suc 0) q)"
                using \<open>p<q\<close> \<open>q<m\<close> by (simp add: Inf_DF_less card_AF trans_less_add1)
              show "card (AF (Suc 0) p) < x"
                if "x \<in> AF (Suc 0) p \<union> (AF (Suc 0) q \<union> (RF (Suc 0) q \<union> RF (Suc 0) p))" for x
                using that
                apply (simp add: card_AF)
                by (metis AF_ne DF_AF DF_ne less_RF_RF less_RF_Suc less_RF_k Inf_nat_def1 One_nat_def RF_0 RF_non_Nil True finite_RF lessI less_setsD less_sets_trans sorted_list_of_set_eq_Nil_iff)
              show "card (AF (Suc 0) p) + card (RF (Suc 0) p) < card (AF (Suc 0) q) + card (RF (Suc 0) q)"
                using \<open>p < q\<close> \<open>p < m\<close> \<open>q < m\<close> by (metis enum_DF1_eq enum_DF_less_iff le_refl)
              show "card (AF (Suc 0) p) + card (RF (Suc 0) p) < x"
                if "x \<in> AF (Suc 0) p \<union> (AF (Suc 0) q \<union> (RF (Suc 0) q \<union> RF (Suc 0) p))" for x
                using that \<open>p < m\<close>
                apply (simp add: flip: enum_DF1_eq)
                by (metis AF_ne DF_AF less_RF_RF less_RF_Suc less_RF_k One_nat_def RF_0 RF_non_Nil Suc_mono True \<open>0 < k\<close> card_DF finite_enumerate_in_set finite_DF less_setsD less_sets_trans sorted_list_of_set_empty)
              have "list_of (AF (Suc 0) p) < list_of {enum (DF (Suc 0) q) (Suc 0)}"
              proof (rule less_sets_imp_sorted_list_of_set)
                show "AF (Suc 0) p \<lless> {enum (DF (Suc 0) q) (Suc 0)}"
                  by (metis (no_types, lifting) AF_DF DF_ne Inf_nat_def1 \<open>q < m\<close> card_AF enum_DF1_eq less_setsD less_sets_singleton2 pq(1) trans_less_add1)
              qed auto
              then show "list_of (AF (Suc 0) p) < (card (AF (Suc 0) q) + card (RF (Suc 0) q)) # list_of (AF (Suc 0) q) @ list_of (RF (Suc 0) q) @ list_of (RF (Suc 0) p)"
                using \<open>q < m\<close> by (simp add: less_list_def enum_DF1_eq)
              show "card (AF (Suc 0) q) + card (RF (Suc 0) q) < x"
                if "x \<in> AF (Suc 0) q \<union> (RF (Suc 0) q \<union> RF (Suc 0) p)" for x
                using that \<open>q < m\<close>
                apply (simp flip: enum_DF1_eq)
                by (metis AF_ne DF_AF less_RF_Suc less_RF_k One_nat_def RF_0 RF_non_Nil True card_DF finite_enumerate_in_set finite_DF finite_RF lessI less_setsD less_sets_trans sorted_list_of_set_eq_Nil_iff)
              have "list_of (AF (Suc 0) q) < list_of (RF (Suc 0) q)"
              proof (rule less_sets_imp_sorted_list_of_set)
                show "AF (Suc 0) q \<lless> RF (Suc 0) q"
                  by (metis less_RF_Suc One_nat_def RF_0 True \<open>0 < k\<close>)
              qed auto
              then show "list_of (AF (Suc 0) q) < list_of (RF (Suc 0) q) @ list_of (RF (Suc 0) p)"
                using RF_non_Nil by (auto simp: less_list_def)
              show "list_of (RF (Suc 0) q) < list_of (RF (Suc 0) p)"
              proof (rule less_sets_imp_sorted_list_of_set)
                show "RF (Suc 0) q \<lless> RF (Suc 0) p"
                  by (metis less_RF_k One_nat_def True)
              qed auto
            qed
            show "[list_of (AF 1 p), list_of (RF 1 p)] \<in> lists (- {[]})"
              using RF_non_Nil \<open>0 < k\<close> by (auto simp: acc_lengths.simps zs_def AF_ne)
            show "[card (AF 1 q) + card (RF 1 q)] = acc_lengths 0 [list_of (RF 1 q \<union> AF 1 q)]"
              using list_of_AF_RF
              by (auto simp: acc_lengths.simps zs_def AF_ne sup_commute)
          qed (auto simp: acc_lengths.simps zs_def AF_ne)
          have zs_N: "list.set zs \<subseteq> N"
            using \<open>p < m\<close> \<open>q < m\<close> DF_in_N  enum_DF1_eq [symmetric]
            by (auto simp: zs_def card_AF AF_subset_N RF_subset_N Inf_DF_N)
          show ?thesis
          proof
            have "Form (2*1) {x,y}"
              by (metis "2" Form.simps Suc_1 True zero_less_one zs)
            with kka show "Form l U"
              by (simp add: \<open>U = {x,y}\<close>)
            show "list.set (inter_scheme l U) \<subseteq> N"
              using kka zs zs_N \<open>k=1\<close> Form_Body_imp_inter_scheme by (fastforce simp add: \<open>U = {x, y}\<close>)
          qed
        qed
      next
        case False
        then have "k \<ge> 2" "ka \<ge> 2"
          using kka \<open>k>0\<close> by auto
        then have k_minus_1 [simp]: "Suc (k - Suc (Suc 0)) = k - Suc 0"
          by auto

        define PP where "PP \<equiv> map (?R p) (list_of {0<..<ka})"
        define QQ where "QQ \<equiv> map (?R q) (list_of {0<..<k-1}) @ ([list_of (RF (k-1) q \<union> RF (ka-1) q)])"
        let ?INT = "interact PP QQ"
        \<comment>\<open>No separate sets A and B as in the text, but instead we treat both cases as once\<close>
        have [simp]: "length PP = ka - 1"
          by (simp add: PP_def)
        have [simp]: "length QQ = k - 1"
          using \<open>k \<ge> 2\<close> by (simp add: QQ_def)

        have PP_n: "PP ! n = list_of (RF (Suc n) p)"
          if "n < ka-1" for n
          using that kka by (auto simp: PP_def nth_sorted_list_of_set_greaterThanLessThan)

        have QQ_n: "QQ ! n = (if n < k - Suc (Suc 0) then list_of (RF (Suc n) q)
                              else list_of (RF (k - Suc 0) q \<union> RF (ka - Suc 0) q))"
          if "n < k-1" for n
          using that kka by (auto simp: QQ_def nth_append nth_sorted_list_of_set_greaterThanLessThan)

        have QQ_n_same: "QQ ! n = list_of (RF (Suc n) q)"
          if "n < k - Suc 0" "k=ka" for n
          using that kka Suc_diff_Suc
          by (fastforce simp add: QQ_def nth_append nth_sorted_list_of_set_greaterThanLessThan)

        have split_nat_interval: "{0<..<n} = insert (n - Suc 0) {0<..<n - Suc 0}" if "n \<ge> 2" for n
          using that by auto
        have split_list_interval: "list_of{0<..<n} = list_of{0<..<n - Suc 0} @ [n - Suc 0]" if "n \<ge> 2" for n
        proof (intro sorted_list_of_set_unique [THEN iffD1] conjI)
          have "list_of {0<..<n - Suc 0} < [n - Suc 0]"
            by (auto intro: less_sets_imp_list_less)
          then show "strict_sorted (list_of {0<..<n - Suc 0} @ [n - Suc 0])"
            by (auto simp: strict_sorted_append_iff)
        qed (use \<open>n \<ge> 2\<close> in auto)

        have list_of_RF_Un: "list_of (RF (k - Suc 0) q \<union> RF k q) = list_of (RF (k - Suc 0) q) @ list_of (RF k q)"
          by (metis less_RF_Suc Suc_pred \<open>0 < k\<close> diff_Suc_less finite_RF sorted_list_of_set_Un)

        have card_AF_sum_QQ: "card (AF k q) + sum_list (map length QQ) = (\<Sum>j<ka. card (RF j q))"
        proof (cases "ka = Suc k")
          case True
          have "RF (k - Suc 0) q \<inter> RF k q = {}"
            using less_RF_Suc [of "k - Suc 0"] \<open>k > 0\<close> by (auto simp: less_sets_def)
          then have "card (RF (k - Suc 0) q \<union> RF k q) = card (RF (k - Suc 0) q) + card (RF k q)"
            by (simp add: card_Un_disjoint)
          then show ?thesis
            using \<open>k\<ge>2\<close> \<open>q < m\<close>
            apply (simp add: QQ_def True flip: RF_0)
            apply (simp add: lessThan_k split_nat_interval sum_sorted_list_of_set_map)
            done
        next
          case False
          with kka have "ka=k" by linarith
          with \<open>k\<ge>2\<close> show ?thesis by (simp add: QQ_def lessThan_k split_nat_interval sum_sorted_list_of_set_map flip: RF_0)
        qed

        define LENS where "LENS \<equiv> \<lambda>i. acc_lengths 0 (list_of (AF k i) # map (?R i) (list_of {0<..<ka}))"
        have LENS_subset_N: "list.set (LENS i) \<subseteq> N" if "i < m" for i
        proof -
          have eq: "(list_of (AF k i) # map (?R i) (list_of {0<..<ka})) = map (?R i) (list_of {..<ka})"
            using RF_0 \<open>0 < ka\<close> sorted_list_of_set_k by auto
          let ?f = "rec_nat [card (AF k i)] (\<lambda>n r. r @ [(\<Sum>j\<le>Suc n. card (RF j i))])"
          have f: "acc_lengths 0 (map (?R i) (list_of {..v})) = ?f v" for v
            by (induction v) (auto simp: RF_0 acc_lengths.simps acc_lengths_append sum_sorted_list_of_set_map)
          have 3: "list.set (?f v) \<subseteq> N" if "v \<le> k" for v
            using that
          proof (induction v)
            case 0
            have "card (AF k i) \<in> N"
              by (metis DF_N DF_ne Inf_nat_def1 Int_subset_iff card_AF subsetD)
            with 0 show ?case by simp
          next
            case (Suc v)
            then have "enum (DF k i) (Suc v) \<in> N"
              by (metis DF_N Int_subset_iff card_DF finite_enumerate_in_set finite_DF in_mono le_imp_less_Suc)
            with Suc \<open>i < m\<close> show ?case
              by (simp del: sum.atMost_Suc)
          qed
          show ?thesis
            unfolding LENS_def
            by (metis "3" Suc_pred \<open>0 < ka\<close> \<open>ka - Suc 0 \<le> k\<close> eq f lessThan_Suc_atMost)
        qed
        define LENS_QQ where "LENS_QQ \<equiv> acc_lengths 0 (list_of (AF k q) # QQ)"
        have LENS_QQ_subset: "list.set LENS_QQ \<subseteq> list.set (LENS q)"
        proof (cases "ka = Suc k")
          case True
          with \<open>k \<ge> 2\<close> show ?thesis
            unfolding QQ_def LENS_QQ_def LENS_def
            by (auto simp: list_of_RF_Un split_list_interval acc_lengths.simps acc_lengths_append)
        next
          case False
          then have "ka=k"
            using kka by linarith
          with \<open>k \<ge> 2\<close> show ?thesis
            by (simp add: QQ_def LENS_QQ_def LENS_def split_list_interval)
        qed
        have ss_INT: "strict_sorted ?INT"
        proof (rule strict_sorted_interact_I)
          fix n
          assume "n < length QQ"
          then have n: "n < k-1"
            by simp
          have "n = k - Suc (Suc 0)" if "\<not> n < k - Suc (Suc 0)"
            using n that by linarith
          with \<open>p<q\<close> n show "PP ! n < QQ ! n"
            using \<open>0 < k\<close> \<open>k \<le> ka\<close> \<open>ka \<le> Suc k\<close> \<open>p<q\<close> n
            by (auto simp: PP_n QQ_n less_RF_same less_sets_imp_sorted_list_of_set less_sets_Un2 less_RF_RF less_RF_k_ka)
        next
          fix n
          have V: "\<lbrakk>Suc n < ka - Suc 0\<rbrakk> \<Longrightarrow> list_of (RF (Suc n) q) < list_of (RF (Suc (Suc n)) p)" for n
            by (smt One_nat_def RF_def Suc_leI \<open>ka - Suc 0 \<le> k\<close> \<open>q < m\<close> diff_Suc_1 finite_RF less_QF_step less_le_trans less_sets_imp_sorted_list_of_set nat_neq_iff zero_less_Suc)
          have "RF (k -  Suc 0) q \<lless> RF k p"
            by (metis less_RF_Suc less_RF_k RF_non_Nil Suc_pred \<open>0 < k\<close> finite_RF lessI less_sets_trans sorted_list_of_set_eq_Nil_iff)
          with kka have "RF (k - Suc 0) q \<union> RF (ka - Suc 0) q \<lless> RF k p"
            by (metis less_RF_k One_nat_def less_sets_Un1 antisym_conv2 diff_Suc_1 le_less_Suc_eq)
          then have VI: "list_of (RF (k - Suc 0) q \<union> RF (ka - Suc 0) q) < list_of (RF k p)"
            by (rule less_sets_imp_sorted_list_of_set) auto
          assume "Suc n < length PP"
          with \<open>ka \<le> Suc k\<close> VI
          show "QQ ! n < PP ! Suc n"
            apply (auto simp: PP_n QQ_n less_RF_same less_sets_imp_sorted_list_of_set less_sets_Un1 less_sets_Un2 less_RF_RF less_RF_k_ka V)
            by (metis One_nat_def Suc_less_eq Suc_pred \<open>0 < k\<close> diff_Suc_1 k_minus_1 ka_k_or_Suc less_SucE)
        next
          show "PP \<in> lists (- {[]})"
            using RF_non_Nil kka
            by (clarsimp simp: PP_def) (metis RF_non_Nil less_le_trans)
          show "QQ \<in> lists (- {[]})"
            using RF_non_Nil kka
            by (clarsimp simp: QQ_def) (metis RF_non_Nil Suc_pred \<open>0 < k\<close> less_SucI)
        qed (use kka PP_def QQ_def in auto)
        then have ss_QQ: "strict_sorted (concat QQ)"
          using strict_sorted_interact_imp_concat by blast

        obtain zs where zs: "Form_Body ka k x y zs" and zs_N: "list.set zs \<subseteq> N"
        proof (intro that exI conjI Form_Body.intros [OF \<open>length x < length y\<close>])
          show "x = concat (list_of (AF k p) # PP)"
            using \<open>ka > 0\<close> by (simp add: PP_def RF_0 xc sorted_list_of_set_k)
          let ?YR = "(map (list_of \<circ> (\<lambda>j. RF j q)) (list_of {0<..<ka}))"
          have "concat ?YR = concat QQ"
          proof (rule strict_sorted_equal [OF ss_QQ])
            show "strict_sorted (concat ?YR)"
            proof (rule strict_sorted_concat_I, simp_all)
              fix n
              assume "Suc n < ka - Suc 0"
              then show "list_of (RF (list_of {0<..<ka} ! n) q) < list_of (RF (list_of {0<..<ka} ! Suc n) q)"
                by (metis less_RF_Suc Suc_lessD \<open>ka - Suc 0 \<le> k\<close> add.left_neutral finite_RF less_le_trans less_sets_imp_sorted_list_of_set nth_sorted_list_of_set_greaterThanLessThan)
            next
              show "?YR \<in> lists (- {[]})"
                using RF_non_Nil \<open>ka \<le> Suc k\<close> by (auto simp: mem_lists_non_Nil)
            qed auto
            show "list.set (concat ?YR) = list.set (concat QQ)"
              using ka_k_or_Suc
            proof
              assume "ka = k"
              then show "list.set (concat (map (list_of \<circ> (\<lambda>j. RF j q)) (list_of {0<..<ka}))) = list.set (concat QQ)"
                using \<open>k\<ge>2\<close> by simp (simp add: split_nat_interval QQ_def)
            next
              assume "ka = Suc k"
              then show "list.set (concat (map (list_of \<circ> (\<lambda>j. RF j q)) (list_of {0<..<ka}))) = list.set (concat QQ)"
                using \<open>k\<ge>2\<close> by simp (auto simp: QQ_def split_nat_interval)
            qed
          qed
          then show "y = concat (list_of (AF k q) # QQ)"
            using \<open>ka > 0\<close> by (simp add: RF_0 yc sorted_list_of_set_k)
          show "list_of (AF k p) # PP \<in> lists (- {[]})" "list_of (AF k q) # QQ \<in> lists (- {[]})"
            using  RF_non_Nil kka by (auto simp: AF_ne PP_def QQ_def eq_commute [of "[]"])
          show "list.set ((LENS p @ list_of (AF k p) @ LENS_QQ @ list_of (AF k q) @ ?INT)) \<subseteq> N"
            using AF_subset_N RF_subset_N LENS_subset_N \<open>p < m\<close> \<open>q < m\<close> LENS_QQ_subset
            by (auto simp: subset_iff PP_def QQ_def)
          show "length (list_of (AF k p) # PP) = ka" "length (list_of (AF k q) # QQ) = k"
            using \<open>0 < ka\<close> \<open>0 < k\<close> by auto
          show "LENS p = acc_lengths 0 (list_of (AF k p) # PP)"
            by (auto simp: LENS_def PP_def)
          show "strict_sorted (LENS p @ list_of (AF k p) @ LENS_QQ @ list_of (AF k q) @ ?INT)"
            unfolding strict_sorted_append_iff
          proof (intro conjI ss_INT)
            show "LENS p < list_of (AF k p) @ LENS_QQ @ list_of (AF k q) @ ?INT"
              using AF_non_Nil [of k p] \<open>k \<le> ka\<close> \<open>ka \<le> Suc k\<close> \<open>p < m\<close> card_AF_sum enum_DF_AF
              by (simp add: enum_DF_AF less_list_def card_AF_sum LENS_def sum_sorted_list_of_set_map)
            show "strict_sorted (LENS p)"
              unfolding LENS_def
              by (rule strict_sorted_acc_lengths) (use RF_non_Nil AF_non_Nil kka in \<open>auto simp: in_lists_conv_set\<close>)
            show "strict_sorted LENS_QQ"
              unfolding LENS_QQ_def QQ_def
              by (rule strict_sorted_acc_lengths) (use RF_non_Nil AF_non_Nil kka in \<open>auto simp: in_lists_conv_set\<close>)
            have last_AF_DF: "last (list_of (AF k p)) < \<Sqinter> (DF k q)"
              using AF_DF [OF \<open>p < q\<close>, of k] AF_non_Nil [of k p] DF_ne [of k q]
              by (metis Inf_nat_def1 finite_AF last_in_set less_sets_def set_sorted_list_of_set)
            then show "list_of (AF k p) < LENS_QQ @ list_of (AF k q) @ ?INT"
              by (simp add: less_list_def card_AF LENS_QQ_def)
            show "LENS_QQ < list_of (AF k q) @ ?INT"
              using AF_non_Nil [of k q] \<open>q < m\<close> card_AF_sum enum_DF_AF card_AF_sum_QQ
              by (auto simp: less_list_def AF_ne hd_append card_AF_sum LENS_QQ_def)
            show "list_of (AF k q) < ?INT"
            proof -
              have "AF k q \<lless> RF (Suc 0) p"
                using \<open>0 < k\<close> \<open>p < m\<close> \<open>q < m\<close> by (simp add: RF_def less_QF flip: QF_0)
              then have "last (list_of (AF k q)) < hd (list_of (RF (Suc 0) p))"
              proof (rule less_setsD)
                show "last (list_of (AF k q)) \<in> AF k q"
                  using AF_non_Nil finite_AF last_in_set set_sorted_list_of_set by blast
                show "hd (list_of (RF (Suc 0) p)) \<in> RF (Suc 0) p"
                  by (metis RF_non_Nil Suc_mono \<open>0 < k\<close> finite_RF hd_in_set set_sorted_list_of_set)
              qed
              with \<open>k > 0\<close> \<open>ka \<ge> 2\<close> RF_non_Nil show ?thesis
                by (simp add: hd_interact less_list_def sorted_list_of_set_greaterThanLessThan PP_def QQ_def)
            qed
          qed auto
        qed (auto simp: LENS_QQ_def)
        show ?thesis
        proof (cases "ka = k")
          case True
          then have "l = 2*k - 1"
            by (simp add: kka(3) mult_2)
          then show ?thesis
            by (metis Form.intros(2) Form_Body_imp_inter_scheme True \<open>0 < k\<close> \<open>U = {x, y}\<close> kka zs zs_N)
        next
          case False
          then have "l = 2*k"
            using kka by linarith
          then show ?thesis
            by (metis False Form.intros(3) Form_Body_imp_inter_scheme \<open>0 < k\<close> \<open>U = {x, y}\<close> antisym kka le_SucE zs zs_N)
        qed
      qed
    qed
  qed
qed


subsection \<open>Larson's Lemma 3.8\<close>

subsubsection \<open>Primitives needed for the inductive construction of @{term b}\<close>

definition IJ where "IJ \<equiv> \<lambda>k. Sigma {..k} (\<lambda>j::nat. {..<j})"

lemma IJ_iff: "u \<in> IJ k \<longleftrightarrow> (\<exists>j i. u = (j,i) \<and> i<j \<and> j\<le>k)"
  by (auto simp: IJ_def)

lemma finite_IJ: "finite (IJ k)"
  by (auto simp: IJ_def)

fun prev where
  "prev 0 0 = None"
| "prev (Suc 0) 0 = None"
| "prev (Suc j) 0 = Some (j, j - Suc 0)"
| "prev j (Suc i) = Some (j,i)"

lemma prev_eq_None_iff: "prev j i = None \<longleftrightarrow> j \<le> Suc 0 \<and> i = 0"
  by (auto simp: le_Suc_eq elim: prev.elims)

lemma prev_pair_less:
  "prev j i = Some ji' \<Longrightarrow> (ji', (j,i)) \<in> pair_less"
  by (auto simp: pair_lessI1 elim: prev.elims)

lemma prev_Some_less: "\<lbrakk>prev j i = Some (j',i'); i \<le> j\<rbrakk> \<Longrightarrow> i' < j'"
  by (auto elim: prev.elims)

lemma prev_maximal:
  "\<lbrakk>prev j i = Some (j',i'); (ji'', (j,i)) \<in> pair_less; ji'' \<in> IJ k\<rbrakk>
   \<Longrightarrow> (ji'', (j',i')) \<in> pair_less \<or> ji'' = (j',i')"
  by (force simp: IJ_def pair_less_def elim: prev.elims)

lemma pair_less_prev:
  assumes "(u, (j,i)) \<in> pair_less" "u \<in> IJ k"
  shows "prev j i = Some u \<or> (\<exists>x. (u, x) \<in> pair_less \<and> prev j i = Some x)"
proof (cases "prev j i")
  case None
  show ?thesis
  proof (cases u)
    case (Pair j' i')
    then show ?thesis
    using assms None by (simp add: prev_eq_None_iff pair_less_def IJ_def)
  qed
next
  case (Some a)
  then show ?thesis
    by (metis assms prev_maximal prod.exhaust_sel)
qed



subsubsection \<open>Special primitives for the ordertype proof\<close>

definition USigma :: "'a set set \<Rightarrow> ('a set \<Rightarrow> 'a set) \<Rightarrow> 'a set set"
  where "USigma \<A> B \<equiv> \<Union>X\<in>\<A>. \<Union>y\<in>B X. {insert y X}"

definition usplit
  where "usplit f A \<equiv> f (A - {Max A}) (Max A)"

lemma USigma_empty [simp]: "USigma {} B = {}"
  by (auto simp: USigma_def)

lemma USigma_iff:
  assumes "\<And>I j. I \<in> \<I> \<Longrightarrow> I \<lless> J I \<and> finite I"
  shows "x \<in> USigma \<I> J \<longleftrightarrow> usplit (\<lambda>I j. I\<in>\<I> \<and> j\<in>J I \<and> x = insert j I) x"
proof -
  have [simp]: "\<And>I j. \<lbrakk>I \<in> \<I>; j \<in> J I\<rbrakk> \<Longrightarrow> Max (insert j I) = j"
    by (meson Max_insert2 assms less_imp_le less_sets_def)
  show ?thesis
  proof -
    have "I - {j} \<in> \<I>" if "I \<in> \<I>" "j \<in> J I" for I j
      using that by (metis Diff_empty Diff_insert0 assms less_irrefl less_sets_def)
    moreover have "j \<in> J (I - {j})" if "I \<in> \<I>" "j \<in> J I" for I j
      using that by (metis Diff_empty Diff_insert0 assms less_irrefl less_setsD)
    moreover have "\<exists>I\<in>\<I>. \<exists>j\<in>J I. x = insert j I"
      if "x - {Max x} \<in> \<I>" and "Max x \<in> J (x - {Max x})" "x \<noteq> {}"
      using that by (metis Max_in assms infinite_remove insert_Diff)
    ultimately show ?thesis
      by (auto simp: USigma_def usplit_def)
  qed
qed


lemma ordertype_append_image_IJ:
  assumes lenB [simp]: "\<And>i j. i \<in> \<I> \<Longrightarrow> j \<in> J i \<Longrightarrow> length (B j) = c"
    and AB: "\<And>i j. i \<in> \<I> \<Longrightarrow> j \<in> J i \<Longrightarrow> A i < B j"
    and IJ: "\<And>i. i \<in> \<I> \<Longrightarrow> i \<lless> J i \<and> finite i"
    and \<beta>: "\<And>i. i \<in> \<I> \<Longrightarrow> ordertype (B ` J i) (lenlex less_than) = \<beta>"
    and A: "inj_on A \<I>"
  shows "ordertype (usplit (\<lambda>i j. A i @ B j) ` USigma \<I> J) (lenlex less_than)
       = \<beta> * ordertype (A ` \<I>) (lenlex less_than)"
    (is "ordertype ?AB ?R = _ * ?\<alpha>")
proof (cases "\<I> = {}")
next
  case False
  have "Ord \<beta>"
    using \<beta> False wf_Ord_ordertype by fastforce
  show ?thesis
  proof (subst ordertype_eq_iff)
    define split where "split \<equiv> \<lambda>l::nat list. (take (length l - c) l, (drop (length l - c) l))"
    have oB: "ordermap (B ` J i) ?R (B j) \<sqsubset> \<beta>" if \<open>i \<in> \<I>\<close> \<open>j \<in> J i\<close> for i j
      using \<beta> less_TC_iff that by fastforce
    then show "Ord (\<beta> * ?\<alpha>)"
      by (intro \<open>Ord \<beta>\<close> wf_Ord_ordertype Ord_mult; simp)
    define f where "f \<equiv> \<lambda>u. let (x,y) = split u in let i = inv_into \<I> A x in
                        \<beta> * ordermap (A`\<I>) ?R x + ordermap (B`J i) ?R y"
    have inv_into_IA [simp]: "inv_into \<I> A (A i) = i" if "i \<in> \<I>" for i
      by (simp add: A that)
    show "\<exists>f. bij_betw f ?AB (elts (\<beta> * ?\<alpha>)) \<and> (\<forall>x\<in>?AB. \<forall>y\<in>?AB. (f x < f y) = ((x, y) \<in> ?R))"
      unfolding bij_betw_def
    proof (intro exI conjI strip)
      show "inj_on f ?AB"
      proof (clarsimp simp: f_def inj_on_def split_def USigma_iff IJ usplit_def)
        fix x y
        assume \<section>: "\<beta> * ordermap (A ` \<I>) ?R (A (x - {Max x})) + ordermap (B ` J (x - {Max x})) ?R (B (Max x))
                 = \<beta> * ordermap (A ` \<I>) ?R (A (y - {Max y})) + ordermap (B ` J (y - {Max y})) ?R (B (Max y))"
          and x: "x - {Max x} \<in> \<I>"
          and y: "y - {Max y} \<in> \<I>"
          and mx: "Max x \<in> J (x - {Max x})"
          and "x = insert (Max x) x"
          and my: "Max y \<in> J (y - {Max y})"
        have "ordermap (A`\<I>) ?R (A (x - {Max x})) = ordermap (A`\<I>) ?R (A (y - {Max y}))"
          and B_eq: "ordermap (B ` J (x - {Max x})) ?R (B (Max x)) = ordermap (B ` J (y - {Max y})) ?R (B (Max y))"
          using mult_cancellation_lemma [OF \<section>] oB mx my x y by blast+
        then have "A (x - {Max x}) = A (y - {Max y})"
          using x y by auto
        then have "x - {Max x} = y - {Max y}"
          by (metis x y inv_into_IA)
        then show "A (x - {Max x}) = A (y - {Max y}) \<and> B (Max x) = B (Max y)"
          using B_eq mx my by auto
      qed
      show "f ` ?AB = elts (\<beta> * ?\<alpha>)"
      proof
        show "f ` ?AB \<subseteq> elts (\<beta> * ?\<alpha>)"
          using \<open>Ord \<beta>\<close>
          apply (clarsimp simp add: f_def split_def USigma_iff IJ usplit_def)
          by (metis Ord_mem_iff_less_TC TC_small add_mult_less image_eqI oB ordermap_in_ordertype trans_llt wf_Ord_ordertype wf_llt)
        show "elts (\<beta> * ?\<alpha>) \<subseteq> f ` ?AB"
        proof (clarsimp simp: f_def split_def image_iff USigma_iff IJ usplit_def Bex_def elim!: elts_multE split: prod.split)
          fix \<gamma> \<delta>
          assume \<delta>: "\<delta> \<in> elts \<beta>" and \<gamma>: "\<gamma> \<in> elts ?\<alpha>"
          have "\<gamma> \<in> ordermap (A ` \<I>) (lenlex less_than) ` A ` \<I>"
            by (meson \<gamma> ordermap_surj subset_iff)
          then obtain i where "i \<in> \<I>" and yv: "\<gamma> = ordermap (A`\<I>) ?R (A i)"
            by blast
          have "\<delta> \<in> ordermap (B ` J i) (lenlex less_than) ` B ` J i"
            by (metis (no_types) \<beta> \<delta> \<open>i \<in> \<I>\<close> in_mono ordermap_surj)
          then obtain j where "j \<in> J i" and xu: "\<delta> = ordermap (B`J i) ?R (B j)"
            by blast
          then have mji: "Max (insert j i) = j"
            by (meson IJ Max_insert2 \<open>i \<in> \<I>\<close> less_imp_le less_sets_def)
          have [simp]: "i - {j} = i"
            using IJ \<open>i \<in> \<I>\<close> \<open>j \<in> J i\<close> less_setsD by fastforce
          show
            "\<exists>l. (\<exists>K. K - {Max K} \<in> \<I> \<and> Max K \<in> J (K - {Max K}) \<and>
                          K = insert (Max K) K \<and>
                          l = A (K - {Max K}) @ B (Max K)) \<and> \<beta> * \<gamma> + \<delta> =
                    \<beta> *
                    ordermap (A ` \<I>) ?R (take (length l - c) l) +
                    ordermap (B ` J (inv_into \<I> A (take (length l - c) l)))
                     ?R (drop (length l - c) l)"
          proof (intro conjI exI)
          let ?ji = "insert j i"
            show "A i @ B j = A (?ji - {Max ?ji}) @ B (Max ?ji)"
              by (auto simp: mji)
          qed (use \<open>i \<in> \<I>\<close> \<open>j \<in> J i\<close> mji xu yv in auto)
        qed
      qed
    next
      fix p q
      assume "p \<in> ?AB" and "q \<in> ?AB"
      then obtain x y where peq: "p = A (x - {Max x}) @ B (Max x)"
                      and qeq: "q = A (y - {Max y}) @ B (Max y)"
                      and x: "x - {Max x} \<in> \<I>"
                      and y: "y - {Max y} \<in> \<I>"
                      and mx: "Max x \<in> J (x - {Max x})"
                      and my: "Max y \<in> J (y - {Max y})"
        by (auto simp: USigma_iff IJ usplit_def)
      let ?mx = "x - {Max x}"
      let ?my = "y - {Max y}"
      show "(f p < f q) \<longleftrightarrow> ((p, q) \<in> ?R)"
      proof
        assume "f p < f q"
        then
        consider "ordermap (A`\<I>) ?R (A (x - {Max x})) < ordermap (A`\<I>) ?R (A (y - {Max y}))"
          | "ordermap (A`\<I>) ?R (A (x - {Max x})) = ordermap (A`\<I>) ?R (A (y - {Max y}))"
            "ordermap (B`J (x - {Max x})) ?R (B (Max x)) < ordermap (B`J (y - {Max y})) ?R (B (Max y))"
          using x y mx my
          by (auto dest: mult_cancellation_less simp: f_def split_def peq qeq oB)
        then have "(A ?mx @ B (Max x), A ?my @ B (Max y)) \<in> ?R"
        proof cases
          case 1
          then have "(A ?mx, A ?my) \<in> ?R"
            using x y
            by (force simp: Ord_mem_iff_lt intro: converse_ordermap_mono)
          then show ?thesis
            using x y mx my lenB lenlex_append1 by blast
        next
          case 2
          then have "A ?mx = A ?my"
            using \<open>?my \<in> \<I>\<close> \<open>?mx \<in> \<I>\<close> by auto
          then have eq: "?mx = ?my"
            by (metis \<open>?my \<in> \<I>\<close> \<open>?mx \<in> \<I>\<close> inv_into_IA)
          then have "(B (Max x), B (Max y)) \<in> ?R"
            using mx my  2
            by (force simp: Ord_mem_iff_lt intro: converse_ordermap_mono)
          with 2 show ?thesis
            by (simp add: eq irrefl_less_than)
        qed
        then show "(p,q) \<in> ?R"
          by (simp add: peq qeq f_def split_def sorted_list_of_set_Un AB)
      next
        assume pqR: "(p,q) \<in> ?R"
        then have \<section>: "(A ?mx @ B (Max x), A ?my @ B (Max y)) \<in> ?R"
          using peq qeq by blast
        then consider "(A ?mx, A ?my) \<in> ?R" | "A ?mx = A ?my \<and> (B (Max x), B (Max y)) \<in> ?R"
        proof (cases "(A ?mx, A ?my) \<in> ?R")
          case False
          have False if "(A ?my, A ?mx) \<in> ?R"
            by (metis \<open>?my \<in> \<I>\<close> \<open>?mx \<in> \<I>\<close> "\<section>" \<open>(Max y) \<in> J ?my\<close> \<open>(Max x) \<in> J ?mx\<close> lenB lenlex_append1 omega_sum_1_less order.asym that)
          then have "A ?mx = A ?my"
            by (meson False UNIV_I total_llt total_on_def)
          then show ?thesis
            using "\<section>" irrefl_less_than that(2) by auto
        qed (use that in blast)
        then have "\<beta> * ordermap (A`\<I>) ?R (A ?mx) + ordermap (B`J ?mx) ?R (B (Max x))
               < \<beta> * ordermap (A`\<I>) ?R (A ?my) + ordermap (B`J ?my) ?R (B (Max y))"
        proof cases
          case 1
          show ?thesis
          proof (rule add_mult_less_add_mult)
            show "ordermap (A`\<I>) (lenlex less_than) (A ?mx) < ordermap (A`\<I>) (lenlex less_than) (A ?my)"
              by (simp add: "1" \<open>?my \<in> \<I>\<close> \<open>?mx \<in> \<I>\<close> ordermap_mono_less)
            show "Ord (ordertype (A`\<I>) ?R)"
              using wf_Ord_ordertype by blast+
            show "ordermap (B ` J ?mx) ?R (B (Max x)) \<in> elts \<beta>"
              using Ord_less_TC_mem \<open>Ord \<beta>\<close> \<open>?mx \<in> \<I>\<close> \<open>(Max x) \<in> J ?mx\<close> oB by blast
            show "ordermap (B ` J ?my) ?R (B (Max y)) \<in> elts \<beta>"
              using Ord_less_TC_mem \<open>Ord \<beta>\<close> \<open>?my \<in> \<I>\<close> \<open>(Max y) \<in> J ?my\<close> oB by blast
          qed (use \<open>?my \<in> \<I>\<close> \<open>?mx \<in> \<I>\<close> \<open>Ord \<beta>\<close> in auto)
        next
          case 2
          with \<open>?mx \<in> \<I>\<close> show ?thesis
            using \<open>(Max y) \<in> J ?my\<close> \<open>(Max x) \<in> J ?mx\<close> ordermap_mono_less
            by (metis (no_types, hide_lams) Kirby.add_less_cancel_left TC_small image_iff inv_into_IA trans_llt wf_llt y)
        qed
        then show "f p < f q"
          using \<open>?my \<in> \<I>\<close> \<open>?mx \<in> \<I>\<close> \<open>(Max y) \<in> J ?my\<close> \<open>(Max x) \<in> J ?mx\<close>
          by (auto simp: peq qeq f_def split_def AB)
      qed
    qed
  qed auto
qed auto


subsubsection \<open>The final part of 3.8, where two sequences are merged\<close>

inductive merge :: "[nat list list,nat list list,nat list list,nat list list] \<Rightarrow> bool"
  where NullNull: "merge [] [] [] []"
      | Null: "as \<noteq> [] \<Longrightarrow> merge as [] [concat as] []"
      | App: "\<lbrakk>as1 \<noteq> []; bs1 \<noteq> [];
               concat as1 < concat bs1; concat bs1 < concat as2; merge as2 bs2 as bs\<rbrakk>
              \<Longrightarrow> merge (as1@as2) (bs1@bs2) (concat as1 # as) (concat bs1 # bs)"

inductive_simps Null1 [simp]: "merge [] bs us vs"
inductive_simps Null2 [simp]: "merge as [] us vs"

lemma merge_single:
  "\<lbrakk>concat as < concat bs; concat as \<noteq> []; concat bs \<noteq> []\<rbrakk> \<Longrightarrow> merge as bs [concat as] [concat bs]"
  using merge.App [of as bs "[]" "[]"]
  by (fastforce simp add: less_list_def)

lemma merge_length1_nonempty:
  assumes "merge as bs us vs" "as \<in> lists (- {[]})"
  shows "us \<in> lists (- {[]})"
  using assms by induction (auto simp: mem_lists_non_Nil)

lemma merge_length2_nonempty:
  assumes "merge as bs us vs" "bs \<in> lists (- {[]})"
  shows "vs \<in> lists (- {[]})"
  using assms by induction (auto simp: mem_lists_non_Nil)

lemma merge_length1_gt_0:
  assumes "merge as bs us vs" "as \<noteq> []"
  shows "length us > 0"
  using assms by induction auto

lemma merge_length_le:
  assumes "merge as bs us vs"
  shows "length vs \<le> length us"
  using assms by induction auto

lemma merge_length_le_Suc:
  assumes "merge as bs us vs"
  shows "length us \<le> Suc (length vs)"
  using assms by induction auto

lemma merge_length_less2:
  assumes "merge as bs us vs"
  shows "length vs \<le> length as"
  using assms
proof induction
case (App as1 bs1 as2 bs2 as bs)
  then show ?case
    by simp (metis One_nat_def Suc_eq_plus1 Suc_leI add.commute add_mono length_greater_0_conv)
qed auto

lemma merge_preserves:
  assumes "merge as bs us vs"
  shows "concat as = concat us \<and> concat bs = concat vs"
  using assms by induction auto

lemma merge_interact:
  assumes "merge as bs us vs" "strict_sorted (concat as)" "strict_sorted (concat bs)"
           "bs \<in> lists (- {[]})"
  shows "strict_sorted (interact us vs)"
  using assms
proof induction
  case (App as1 bs1 as2 bs2 as bs)
  then have "concat bs1 < concat bs" "concat bs1 < concat as" and xx: "concat bs1 \<noteq> []"
    using merge_preserves strict_sorted_append_iff by fastforce+
  then have "concat bs1 < interact as bs"
    using App
    apply (simp add: less_list_def del: concat_eq_Nil_conv)
    by (metis (full_types) Un_iff \<open>concat bs1 < concat as\<close> \<open>concat bs1 < concat bs\<close> last_in_set list.set_sel(1) set_interact sorted_wrt_append strict_sorted_append_iff strict_sorted_interact_imp_concat strict_sorted_sorted_wrt xx)
  with App show ?case
    apply (simp add: strict_sorted_append_iff del: concat_eq_Nil_conv)
    by (metis hd_append2 less_list_def xx)
qed auto


lemma acc_lengths_merge1:
  assumes "merge as bs us vs"
  shows "list.set (acc_lengths k us) \<subseteq> list.set (acc_lengths k as)"
  using assms
proof (induction arbitrary: k)
  case (App as1 bs1 as2 bs2 as bs)
  then show ?case
    apply (simp add: acc_lengths_append acc_lengths.simps strict_sorted_append_iff length_concat_acc_lengths)
    by (simp add: le_supI2 length_concat)
qed (auto simp: acc_lengths.simps length_concat_acc_lengths)

lemma acc_lengths_merge2:
  assumes "merge as bs us vs"
  shows "list.set (acc_lengths k vs) \<subseteq> list.set (acc_lengths k bs)"
  using assms
proof (induction arbitrary: k)
  case (App as1 bs1 as2 bs2 as bs)
  then show ?case
    apply (simp add: acc_lengths_append acc_lengths.simps strict_sorted_append_iff length_concat_acc_lengths)
    by (simp add: le_supI2 length_concat)
qed (auto simp: acc_lengths.simps length_concat_acc_lengths)

lemma length_hd_le_concat:
  assumes "as \<noteq> []" shows "length (hd as) \<le> length (concat as)"
  by (metis (no_types) add.commute assms concat.simps(2) le_add2 length_append list.exhaust_sel)

lemma length_hd_merge2:
  assumes "merge as bs us vs"
  shows "length (hd bs) \<le> length (hd vs)"
  using assms by induction (auto simp: length_hd_le_concat)

lemma merge_less_sets_hd:
  assumes "merge as bs us vs" "strict_sorted (concat as)" "strict_sorted (concat bs)" "bs \<in> lists (- {[]})"
  shows "list.set (hd us) \<lless> list.set (concat vs)"
  using assms
proof induction
  case (App as1 bs1 as2 bs2 as bs)
  then have \<section>: "list.set (concat bs1) \<lless> list.set (concat bs2)"
    by (force simp: dest: strict_sorted_imp_less_sets)+
  have *: "list.set (concat as1) \<lless> list.set (concat bs1)"
    using App by (metis concat_append strict_sorted_append_iff strict_sorted_imp_less_sets)
  then have "list.set (concat as1) \<lless> list.set (concat bs)"
    using App \<section> less_sets_trans merge_preserves
    by (metis List.set_empty append_in_lists_conv le_zero_eq length_concat_ge length_greater_0_conv list.size(3))
  with * App.hyps show ?case
    by (fastforce simp add: less_sets_UN1 less_sets_UN2 less_sets_Un2)
qed auto

lemma set_takeWhile:
  assumes "strict_sorted (concat as)" "as \<in> lists (- {[]})"
  shows "list.set (takeWhile (\<lambda>x. x < y) as) = {x \<in> list.set as. x < y}"
  using assms
proof (induction as)
  case (Cons a as)
  have *: "a < y"
    if a: "a < concat as" "strict_sorted a" "strict_sorted (concat as)" "x < y" "x \<noteq> []" "x \<in> list.set as"
    for x
  proof -
    have "last x \<in> list.set (concat as)"
      using set_concat that(5) that(6) by fastforce
    then have "last a < hd (concat as)"
      using Cons.prems that by (auto simp: less_list_def)
    also have "\<dots> \<le> hd y" if "y \<noteq> []"
      using that a
      by (meson \<open>last x \<in> list.set (concat as)\<close> dual_order.strict_trans less_list_def not_le sorted_hd_le strict_sorted_imp_sorted)
    finally show ?thesis
      by (simp add: less_list_def)
  qed
  then show ?case
    using Cons by (auto simp: strict_sorted_append_iff)
qed auto

proposition merge_exists:
  assumes "strict_sorted (concat as)" "strict_sorted (concat bs)"
          "as \<in> lists (- {[]})" "bs \<in> lists (- {[]})"
          "hd as < hd bs" "as \<noteq> []" "bs \<noteq> []"
  and disj: "\<And>a b. \<lbrakk>a \<in> list.set as; b \<in> list.set bs\<rbrakk> \<Longrightarrow> a<b \<or> b<a"
shows "\<exists>us vs. merge as bs us vs"
  using assms
proof (induction "length as + length bs" arbitrary: as bs rule: less_induct)
  case (less as bs)
  obtain as1 as2 bs1 bs2
    where A: "as1 \<noteq> []" "bs1 \<noteq> []" "concat as1 < concat bs1" "concat bs1 < concat as2"
      and B: "as = as1@as2" "bs = bs1@bs2" and C: "bs2 = [] \<or> (as2 \<noteq> [] \<and> hd as2 < hd bs2)"
  proof
    define as1 where "as1 \<equiv> takeWhile (\<lambda>x. x < hd bs) as"
    define as2 where "as2 \<equiv> dropWhile (\<lambda>x. x < hd bs) as"
    define bs1 where "bs1 \<equiv> if as2=[] then bs else takeWhile (\<lambda>x. x < hd as2) bs"
    define bs2 where "bs2 \<equiv> if as2=[] then [] else dropWhile (\<lambda>x. x < hd as2) bs"

    have as1: "as1 = takeWhile (\<lambda>x. last x < hd (hd bs)) as"
      using less.prems by (auto simp: as1_def less_list_def cong: takeWhile_cong)
    have as2: "as2 = dropWhile (\<lambda>x. last x < hd (hd bs)) as"
      using less.prems by (auto simp: as2_def less_list_def cong: dropWhile_cong)

    have hd_as2: "as2 \<noteq> [] \<Longrightarrow> \<not> hd as2 < hd bs"
      using as2_def hd_dropWhile by metis
    have hd_bs2: "bs2 \<noteq> [] \<Longrightarrow> \<not> hd bs2 < hd as2"
      using bs2_def hd_dropWhile by metis
    show "as1 \<noteq> []"
      by (simp add: as1_def less.prems takeWhile_eq_Nil_iff)
    show "bs1 \<noteq> []"
      by (metis as2 bs1_def hd_as2 hd_in_set less.prems(7) less.prems(8) set_dropWhileD takeWhile_eq_Nil_iff)
    show "bs2 = [] \<or> (as2 \<noteq> [] \<and> hd as2 < hd bs2)"
      by (metis as2_def bs2_def hd_bs2 less.prems(8) list.set_sel(1) set_dropWhileD)
    have AB: "list.set A \<lless> list.set B"
      if "A \<in> list.set as1" "B \<in> list.set bs" for A B
    proof -
      have "A \<in> list.set as"
        using that by (metis as1 set_takeWhileD)
      then have "sorted A"
        by (metis concat.simps(2) concat_append less.prems(1) sorted_append split_list_last strict_sorted_imp_sorted)
      moreover have "sorted (hd bs)"
        by (metis concat.simps(2) hd_Cons_tl less.prems(2) less.prems(7) strict_sorted_append_iff strict_sorted_imp_sorted)
      ultimately show ?thesis
        using that
       apply (clarsimp simp add: as1_def less.prems set_takeWhile less_list_iff_less_sets less_sets_def)
        by (smt UN_I dual_order.strict_trans2 hd_concat less.prems(2) less.prems(4) less.prems(7) list.set_sel(1) mem_lists_non_Nil not_le set_concat sorted_hd_le strict_sorted_imp_sorted)
    qed
    show "as = as1@as2"
      by (simp add: as1_def as2_def)
    show "bs = bs1@bs2"
      by (simp add: bs1_def bs2_def)
    have "list.set (concat as1) \<lless> list.set (concat bs1)"
      using AB set_takeWhileD by (fastforce simp add: as1_def bs1_def less_sets_UN1 less_sets_UN2)
    then show "concat as1 < concat bs1"
      by (rule less_sets_imp_list_less)
    have "list.set (concat bs1) \<lless> list.set (concat as2)" if "as2 \<noteq> []"
    proof (clarsimp simp add: bs1_def less_sets_UN1 less_sets_UN2 set_takeWhile less.prems)
      fix A B
      assume "A \<in> list.set as2" "B \<in> list.set bs" "B < hd as2"
      with that show "list.set B \<lless> list.set A"
        using hd_as2 less.prems(1,2)
        apply (clarsimp simp add: less_sets_def less_list_def)
        apply (auto simp: as2_def)
        apply (simp flip: as2_def)
        by (metis UN_I \<open>as = as1 @ as2\<close> concat.simps(2) concat_append dual_order.strict_trans2 hd_concat in_set_conv_decomp_last not_le set_concat sorted_hd_le sorted_le_last sorted_sorted_wrt sorted_wrt_append strict_sorted_imp_sorted that)
    qed
    then show "concat bs1 < concat as2"
      by (simp add: bs1_def less_sets_imp_list_less)
  qed
  obtain cs ds where "merge as2 bs2 cs ds"
  proof (cases "as2 = [] \<or> bs2 = []")
    case True
    then show thesis
      using that C NullNull Null by metis
  next
    have \<dagger>: "length as2 + length bs2 < length as + length bs"
      by (simp add: A B)
    case False
    moreover have "strict_sorted (concat as2)" "strict_sorted (concat bs2)"
      "as2 \<in> lists (- {[]})" "bs2 \<in> lists (- {[]})"
      "\<And>a b. \<lbrakk>a \<in> list.set as2; b \<in> list.set bs2\<rbrakk> \<Longrightarrow> a < b \<or> b < a"
      using B less.prems strict_sorted_append_iff by auto
    ultimately show ?thesis
      using C less.hyps [OF \<dagger>] False that by force
  qed
  then obtain cs where "merge (as1 @ as2) (bs1 @ bs2) (concat as1 # cs) (concat bs1 # ds)"
    using A merge.App by blast
  then show ?case
    using B by blast
qed

subsubsection \<open>Actual proof of lemma 3.8\<close>

text \<open>Lemma 3.8 of Jean A. Larson, ibid.\<close>
proposition lemma_3_8:
  assumes "infinite N"
  obtains X where "X \<subseteq> WW" "ordertype X (lenlex less_than) = \<omega>\<up>\<omega>"
            "\<And>u. u \<in> [X]\<^bsup>2\<^esup> \<Longrightarrow>
                   \<exists>l. Form l u \<and> (l > 0 \<longrightarrow> [enum N l] < inter_scheme l u \<and> List.set (inter_scheme l u) \<subseteq> N)"
proof -
  let ?LL = "lenlex less_than"
  define bf where "bf \<equiv> \<lambda>M q. wfrec pair_less (\<lambda>f (j,i).
                                  let R = (case prev j i of None \<Rightarrow> M | Some u \<Rightarrow> snd (f u))
                                  in grab R (q j i))"

  have bf_rec: "bf M q (j,i) =
                 (let R = (case prev j i of None \<Rightarrow> M | Some u \<Rightarrow> snd (bf M q u))
                  in  grab R (q j i))" for M q j i
    by (subst (1) bf_def) (simp add: Let_def wfrec bf_def cut_apply prev_pair_less cong: conj_cong split: option.split)

  have infinite_bf [simp]: "infinite (snd (bf M q u)) = infinite M" for M q u
    using wf_pair_less
  proof (induction u rule: wf_induct_rule)
    case (less u)
    then show ?case
    proof (cases u)
      case (Pair j i)
      with less.IH prev_pair_less show ?thesis
        by (auto simp: bf_rec [of M q j i] split: option.split)
    qed
  qed

  have bf_less_sets: "fst (bf M q ij) \<lless> snd (bf M q ij)" if "infinite M" for M q ij
    using wf_pair_less
  proof (induction ij rule: wf_induct_rule)
    case (less u)
    then show ?case
    proof (cases u)
      case (Pair j i)
      with less_sets_grab show ?thesis
        by (simp add: bf_rec [of M q j i] less.IH prev_pair_less that split: option.split)
    qed
  qed

  have bf_subset: "fst (bf M q u) \<subseteq> M \<and> snd (bf M q u) \<subseteq> M" for M q u
    using wf_pair_less
  proof (induction u rule: wf_induct_rule)
    case (less u)
    show ?case
    proof (cases u)
      case (Pair j i)
      then show ?thesis
      apply (simp add: bf_rec [of M q j i] that split: option.split)
        using fst_grab_subset less.IH prev_pair_less snd_grab_subset by blast
    qed
  qed

  have card_fst_bf: "finite (fst (bf M q (j,i))) \<and> card (fst (bf M q (j,i))) = q j i" if "infinite M" for M q j i
    by (simp add: that bf_rec [of M q j i] split: option.split)

  have bf_cong: "bf M q u = bf M q' u"
    if "snd u \<le> fst u" and eq: "\<And>y x. \<lbrakk>x\<le>y; y\<le>fst u\<rbrakk> \<Longrightarrow> q' y x = q y x" for M q q' u
    using wf_pair_less that
  proof (induction u rule: wf_induct_rule)
    case (less u)
    show ?case
    proof (cases u)
      case (Pair j i)
      with less.prems show ?thesis
      proof (clarsimp simp add: bf_rec [of M _ j i]  split: option.split)
        fix j' i'
        assume *: "prev j i = Some (j',i')"
        then have **: "((j', i'), u) \<in> pair_less"
          by (simp add: Pair prev_pair_less)
        moreover have "i' < j'"
          using Pair less.prems by (simp add: prev_Some_less [OF *])
        moreover have "\<And>x y. \<lbrakk>x \<le> y; y \<le> j'\<rbrakk> \<Longrightarrow> q' y x = q y x"
          using ** less.prems by (auto simp: pair_less_def Pair)
        ultimately show "grab (snd (bf M q (j',i'))) (q j i) = grab (snd (bf M q' (j',i'))) (q j i)"
          using less.IH by auto
      qed
    qed
  qed

  define ediff where "ediff \<equiv> \<lambda>D:: nat \<Rightarrow> nat set. \<lambda>j i. enum (D j) (Suc i) - enum (D j) i"
  define F where "F \<equiv> \<lambda>l (dl,a0::nat set,b0::nat \<times> nat \<Rightarrow> nat set,M).
          let (d,Md) = grab (nxt M (enum N (Suc (2 * Suc l)))) (Suc l) in
          let (a,Ma) = grab Md (Min d) in
          let Gb = bf Ma (ediff (dl(l := d))) in
          let dl' = dl(l := d) in
          (dl', a, fst \<circ> Gb, snd (Gb(l, l-1)))"
  define DF where "DF \<equiv> rec_nat (\<lambda>i\<in>{..<0}. {}, {}, \<lambda>p. {}, N) F"
  have DF_simps: "DF 0 = (\<lambda>i\<in>{..<0}. {}, {}, \<lambda>p. {}, N)"
                 "DF (Suc l) = F l (DF l)" for l
    by (auto simp: DF_def)
  note cut_apply [simp]

  have inf [rule_format]: "\<forall>dl al bl L. DF l = (dl,al,bl,L) \<longrightarrow> infinite L" for l
    by (induction l) (auto simp: DF_simps F_def Let_def grab_eqD infinite_nxtN assms split: prod.split)

  define \<Psi> where
    "\<Psi> \<equiv> \<lambda>(dl, a, b :: nat \<times> nat \<Rightarrow> nat set, M::nat set). \<lambda>l::nat.
           dl l \<lless> a \<and> finite a \<and> dl l \<noteq> {} \<and> a \<noteq> {} \<and>
           (\<forall>j\<le>l. card (dl j) = Suc j) \<and> a \<lless> \<Union>(range b) \<and> range b \<subseteq> Collect finite \<and>
           a \<subseteq> N \<and> \<Union>(range b) \<subseteq> N \<and> infinite M \<and> b(l,l-1) \<lless> M \<and>
           M \<subseteq> N"
  have \<Psi>_DF: "\<Psi> (DF (Suc l)) l" for l
  proof (induction l)
    case 0
    show ?case
      using assms
      apply (clarsimp simp add: bf_rec F_def DF_simps \<Psi>_def split: prod.split)
      apply (drule grab_eqD, blast dest: grab_eqD infinite_nxtN)+
      apply (auto simp: less_sets_UN2 less_sets_grab card_fst_bf elim!: less_sets_weaken2)
      apply (metis Min_in card_eq_0_iff greaterThan_iff le_inf_iff less_nat_zero_code n_not_Suc_n nxt_def subsetD)
      using nxt_subset snd_grab_subset bf_subset by blast+
  next
    case (Suc l)
    then show ?case
      using assms
      unfolding Let_def DF_simps(2)[of "Suc l"] F_def \<Psi>_def
      apply (clarsimp simp add: bf_rec DF_simps split: prod.split)
      apply (drule grab_eqD, metis grab_eqD infinite_nxtN)+
      apply (safe, simp_all add: less_sets_UN2 less_sets_grab card_fst_bf)
             apply (meson less_sets_weaken2)
            apply (metis (no_types, hide_lams) IntE Min_in card.empty greaterThan_iff leD not_less_eq_eq nxt_def subsetD zero_less_Suc)
           apply (meson bf_subset less_sets_weaken2)
          apply (meson nxt_subset subset_eq)
         apply (meson bf_subset nxt_subset subset_eq)
        using bf_rec infinite_bf apply force
       using bf_less_sets bf_rec apply force
      by (metis bf_rec bf_subset nxt_subset subsetD)
  qed

  define d where "d \<equiv> \<lambda>k. let (dk,ak,bk,M) = DF(Suc k) in dk k"
  define a where "a \<equiv> \<lambda>k. let (dk,ak,bk,M) = DF(Suc k) in ak"
  define b where "b \<equiv> \<lambda>k. let (dk,ak,bk,M) = DF(Suc k) in bk"
  define M where "M \<equiv> \<lambda>k. let (dk,ak,bk,M) = DF k in M"

  have infinite_M [simp]: "infinite (M k)" for k
    by (auto simp: M_def inf split: prod.split)

  have M_Suc_subset: "M (Suc k) \<subseteq> M k" for k
    apply (clarsimp simp add: Let_def M_def F_def DF_simps split: prod.split)
    apply (drule grab_eqD, blast dest: infinite_nxtN local.inf)+
    using bf_subset nxt_subset by blast

  have Inf_M_Suc_ge: "Inf (M k) \<le> Inf (M (Suc k))" for k
    by (simp add: M_Suc_subset cInf_superset_mono infinite_imp_nonempty)

  have Inf_M_telescoping: "{Inf (M k)..} \<subseteq> {Inf (M k')..}" if "k'\<le>k" for k k'
    using that
    by (induction "k-k'")(auto simp: Inf_M_Suc_ge M_Suc_subset cInf_superset_mono infinite_imp_nonempty lift_Suc_antimono_le)

  have d_eq: "d k = fst (grab (nxt (M k) (enum N (Suc (2 * Suc k)))) (Suc k))" for k
    by (simp add: d_def M_def Let_def DF_simps F_def split: prod.split)
  then have finite_d [simp]: "finite (d k)" for k
    by simp
  then have d_ne [simp]: "d k \<noteq> {}" for k
    by (metis card.empty card_grab d_eq infinite_M infinite_nxtN nat.distinct(1))
  have a_eq: "\<exists>M. a k = fst (grab M (Min (d k))) \<and> infinite M" for k
    apply (simp add: a_def d_def M_def Let_def DF_simps F_def split: prod.split)
    by (metis fst_conv grab_eqD infinite_nxtN local.inf)
  then have card_a: "card (a k) = Inf (d k)" for k
    by (metis cInf_eq_Min card_grab d_ne finite_d)

  have d_eq_dl: "d k = dl k" if "(dl,a,b,P) = DF l" "k < l" for k l dl a b P
    using that
    by (induction l arbitrary: dl a b P) (simp_all add: d_def DF_simps F_def Let_def split: prod.split_asm prod.split)

  have card_d [simp]: "card (d k) = Suc k" for k
    by (auto simp: d_eq infinite_nxtN)

  have d_ne [simp]: "d j \<noteq> {}" and a_ne [simp]: "a j \<noteq> {}"
    and finite_d [simp]: "finite (d j)" and finite_a [simp]: "finite (a j)" for j
    using \<Psi>_DF [of "j"] by (auto simp: \<Psi>_def a_def d_def split: prod.split_asm)

  have da: "d k \<lless> a k" for k
    using \<Psi>_DF [of "k"] by (simp add: \<Psi>_def a_def d_def split: prod.split_asm)

  have ab_same: "a k \<lless> \<Union>(range(b k))" for k
    using \<Psi>_DF [of "k"]
    by (simp add: \<Psi>_def a_def b_def M_def split: prod.split_asm)

  have snd_bf_subset: "snd (bf M r (j,i)) \<subseteq> snd (bf M r (j',i'))"
    if ji: "((j',i'), (j,i)) \<in> pair_less" "(j',i') \<in> IJ k"
    for M r k j i j' i'
    using wf_pair_less ji
  proof (induction rule: wf_induct_rule [where a= "(j,i)"])
    case (less u)
    show ?case
    proof (cases u)
      case (Pair j i)
      then consider "prev j i = Some (j', i')" | x where "((j', i'), x) \<in> pair_less" "prev j i = Some x"
        using less.prems pair_less_prev by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis
          by (simp add: Pair bf_rec snd_grab_subset)
      next
        case 2
        then have "snd (bf M r x) \<subseteq> snd (bf M r (j', i'))"
          by (simp add: Pair less.IH prev_pair_less that(2))
        moreover have "snd (bf M r u) \<subseteq> snd (bf M r x)"
          by (simp add: 2 Pair bf_rec snd_grab_subset)
        ultimately show ?thesis
          by auto
      qed
    qed
  qed

  have less_bf: "fst (bf M r (j',i')) \<lless> fst (bf M r (j,i))"
    if ji: "((j',i'), (j,i)) \<in> pair_less" "(j',i') \<in> IJ k" and "infinite M"
    for M r k j i j' i'
  proof -
    consider "prev j i = Some (j', i')" | j'' i'' where "((j', i'), (j'',i'')) \<in> pair_less" "prev j i = Some (j'',i'')"
      by (metis pair_less_prev ji prod.exhaust_sel)
    then show ?thesis
    proof cases
      case 1
      then show ?thesis
        using bf_less_sets bf_rec infinite_bf less_sets_fst_grab \<open>infinite M\<close> by auto
    next
      case 2
      then have "fst (bf M r (j',i')) \<lless> snd (bf M r (j'',i''))"
        by (meson bf_less_sets snd_bf_subset less_sets_weaken2 that)
      with 2 show ?thesis
        using bf_rec infinite_bf less_sets_fst_grab \<open>infinite M\<close> by auto
    qed
  qed

  have aM: "a k \<lless> M (Suc k)" for k
    apply (clarsimp simp add: a_def M_def DF_simps F_def Let_def split: prod.split)
    by (meson bf_subset grab_eqD infinite_nxtN less_sets_weaken2 local.inf)
  then have "a k \<lless> a (Suc k)" for k
    by (metis IntE card_d card.empty d_eq da fst_grab_subset less_sets_trans less_sets_weaken2 nat.distinct(1) nxt_def subsetI)
  then have aa: "a j \<lless> a k" if "j<k" for k j
    by (meson UNIV_I a_ne less_sets_imp_strict_mono_sets strict_mono_sets_def that)
  then have ab: "a k' \<lless> b k (j,i)" if "k'\<le>k" for k k' j i
    by (metis a_ne ab_same le_less less_sets_UN2 less_sets_trans rangeI that)
  have db: "d j \<lless> b k (j,i)" if "j\<le>k" for k j i
    by (meson a_ne ab da less_sets_trans that)

  have bMkk: "b k (k,k-1) \<lless> M (Suc k)" for k
    using \<Psi>_DF [of k]
    by (simp add: \<Psi>_def b_def d_def M_def split: prod.split_asm)

  have b: "\<exists>P \<subseteq> M k. infinite P \<and> (\<forall>j i. i\<le>j \<longrightarrow> j\<le>k \<longrightarrow> b k (j,i) = fst (bf P (ediff d) (j,i)))" for k
  proof (clarsimp simp: b_def DF_simps F_def Let_def split: prod.split)
    fix a a' d' dl bb P M' M''
    assume gr: "grab M'' (Min d') = (a', M')" "grab (nxt P (enum N (Suc (Suc (Suc (2 * k)))))) (Suc k) = (d', M'')"
      and DF: "DF k = (dl, a, bb, P)"
    have deq: "d j = (if j = k then d' else dl j)" if "j\<le>k" for j
    proof (cases "j < k")
      case True
      then show ?thesis
        by (metis DF d_eq_dl less_not_refl)
    next
      case False
      then show ?thesis
        using that DF gr
        by (auto simp: d_def DF_simps F_def Let_def split: prod.split)
    qed
    have "M' \<subseteq> P"
      by (metis gr in_mono nxt_subset snd_conv snd_grab_subset subsetI)
    also have "P \<subseteq> M k"
      using DF by (simp add: M_def)
    finally have "M' \<subseteq> M k" .
    moreover have "infinite M'"
      using DF by (metis (mono_tags) finite_grab_iff gr infinite_nxtN local.inf snd_conv)
    moreover
    have "ediff (dl(k := d')) j i = ediff d j i" if "j\<le>k" for j i
      by (simp add: deq that ediff_def)
    then have "bf M' (ediff (dl(k := d'))) (j,i)
             = bf M' (ediff d) (j,i)" if "i \<le> j" "j\<le>k" for j i
      using bf_cong that by fastforce
    ultimately show "\<exists>P\<subseteq>M k. infinite P \<and>
                           (\<forall>j i. i \<le> j \<longrightarrow> j \<le> k
                                        \<longrightarrow> fst (bf M' (ediff (dl(k := d'))) (j,i))
                         = fst (bf P (ediff d) (j,i)))"
      by auto
  qed

  have card_b: "card (b k (j,i)) = enum (d j) (Suc i) - enum (d j) i" if "j\<le>k" for k j i
    \<comment>\<open>there's a short proof of this from the previous result but it would need @{term"i\<le>j"}\<close>
  proof (clarsimp simp: b_def DF_simps F_def Let_def split: prod.split)
    fix dl
      and a a' d':: "nat set"
      and bb M M' M''
    assume gr: "grab M'' (Min d') = (a', M')" "grab (nxt M (enum N (Suc (Suc (Suc (2 * k)))))) (Suc k) = (d',M'')"
      and DF: "DF k = (dl, a, bb, M)"
    have "d j = (if j = k then d' else dl j)"
    proof (cases "j < k")
      case True
      then show ?thesis
        by (metis DF d_eq_dl less_not_refl)
    next
      case False
      then show ?thesis
        using that DF gr by (auto simp: d_def DF_simps F_def Let_def split: prod.split)
    qed
    then show "card (fst (bf M' (ediff (dl(k := d'))) (j,i)))
             = enum (d j) (Suc i) - enum (d j) i"
      using DF gr card_fst_bf grab_eqD infinite_nxtN local.inf ediff_def by auto
  qed

  have card_b_pos: "card (b k (j,i)) > 0" if "i < j" "j\<le>k" for k j i
    by (simp add: card_b that finite_enumerate_step)
  have b_ne [simp]: "b k (j,i) \<noteq> {}" if "i < j" "j\<le>k" for k j i
    using card_b_pos [OF that] less_imp_neq by fastforce+

  have card_b_finite [simp]: "finite (b k u)" for k u
    using \<Psi>_DF [of k] by (fastforce simp add: \<Psi>_def b_def)

  have bM: "b k (j,i) \<lless> M (Suc k)" if "i<j" "j\<le>k" for i j k
  proof -
    obtain M' where "M' \<subseteq> M k" "infinite M'"
      and bk: "\<And>j i. i\<le>j \<Longrightarrow> j\<le>k \<Longrightarrow> b k (j,i) = fst (bf M' (ediff d) (j,i))"
      using b by (metis (no_types, lifting))
    show ?thesis
    proof (cases "j=k \<and> i = k-1")
      case False
      show ?thesis
      proof (rule less_sets_trans [OF _ bMkk])
        show "b k (j,i) \<lless> b k (k, k - 1)"
          using that \<open>infinite M'\<close> False
            by (force simp: bk pair_less_def IJ_def intro: less_bf)
        show "b k (k, k - 1) \<noteq> {}"
          using b_ne that by auto
      qed
    qed (use bMkk in auto)
  qed

  have b_InfM: "\<Union> (range (b k)) \<subseteq> {\<Sqinter>(M k)..}" for k
  proof (clarsimp simp add: \<Psi>_def b_def M_def DF_simps F_def Let_def split: prod.split)
    fix r dl :: "nat \<Rightarrow> nat set"
      and a b and d' a' M'' M' P :: "nat set"
      and x j' i' :: nat
    assume gr: "grab M'' (Min d') = (a', M')"
               "grab (nxt P (enum N (Suc (Suc (Suc (2 * k)))))) (Suc k) = (d', M'')"
      and DF: "DF k = (dl, a, b, P)"
      and x: "x \<in> fst (bf M' (ediff (dl(k := d'))) (j', i'))"
    have "infinite P"
      using DF local.inf by blast
    then have "M' \<subseteq> P"
      by (meson gr grab_eqD infinite_nxtN nxt_subset order.trans)
    with bf_subset show "\<Sqinter> P \<le> (x::nat)"
      using Inf_nat_def x le_less_linear not_less_Least by fastforce
  qed

  have b_Inf_M_Suc: "b k (j,i) \<lless> {Inf(M (Suc k))}" if "i<j" "j\<le>k" for k j i
    using bMkk [of k] that
    by (metis Inf_nat_def1 bM finite.emptyI infinite_M less_setsD less_sets_singleton2)

  have bb_same: "b k (j',i') \<lless> b k (j,i)"
    if "((j',i'), (j,i)) \<in> pair_less" "(j',i') \<in> IJ k" for k j i j' i'
    using that
    unfolding b_def DF_simps F_def Let_def
    by (auto simp: less_bf grab_eqD infinite_nxtN local.inf split: prod.split)

  have bb: "b k' (j',i') \<lless> b k (j,i)"
    if j: "i' < j'" "j'\<le>k'" and k: "k'<k" for i i' j j' k' k
  proof (rule atLeast_less_sets)
    show "b k' (j', i') \<lless> {Inf(M (Suc k'))}"
      using Suc_lessD b_Inf_M_Suc nat_less_le j by blast
    have "b k (j,i) \<subseteq> {\<Sqinter>(M k)..}"
      by (rule order_trans [OF _ b_InfM]) auto
    also have "\<dots>  \<subseteq> {Inf(M (Suc k'))..}"
      using Inf_M_telescoping k by auto
    finally show "b k (j,i) \<subseteq> {Inf(M (Suc k'))..}" .
  qed

  have M_subset_N: "M k \<subseteq> N" for k
  proof (cases k)
    case (Suc k')
    with \<Psi>_DF [of k'] show ?thesis
      by (auto simp: M_def Let_def \<Psi>_def split: prod.split)
  qed (auto simp: M_def DF_simps)
  have a_subset_N: "a k \<subseteq> N" for k
    using \<Psi>_DF [of k] by (simp add: a_def \<Psi>_def split: prod.split prod.split_asm)
  have d_subset_N: "d k \<subseteq> N" for k
    using M_subset_N [of k] d_eq fst_grab_subset nxt_subset by blast
  have b_subset_N: "b k (j,i) \<subseteq> N" for k j i
    using \<Psi>_DF [of k] by (force simp: b_def \<Psi>_def)

  define \<K>:: "[nat,nat] \<Rightarrow> nat set set"
    where "\<K> \<equiv> \<lambda>j0 j. nsets {j0<..} j"

  have \<K>_finite: "K \<in> \<K> j0 j \<Longrightarrow> finite K" for K j0 j
    by (simp add: \<K>_def nsets_def)
  have \<K>_card: "K \<in> \<K> j0 j \<Longrightarrow> card K = j" for K j0 j
    by (simp add: \<K>_def nsets_def)
  have \<K>_enum: "j0 < enum K i" if "K \<in> \<K> j0 j" "i < card K" for K j0 j i
    using that by (auto simp: \<K>_def nsets_def finite_enumerate_in_set subset_eq)
  have \<K>_0 [simp]: "\<K> k 0 = {{}}" for k
    by (auto simp: \<K>_def)

  have \<K>_Suc: "\<K> j0 (Suc j) = USigma (\<K> j0 j) (\<lambda>K. {Max (insert j0 K)<..})" (is "?lhs = ?rhs")
    for j j0
  proof
    show "\<K> j0 (Suc j) \<subseteq> USigma (\<K> j0 j) (\<lambda>K. {Max (insert j0 K)<..})"
      unfolding \<K>_def nsets_def USigma_def
    proof clarsimp
      fix K
      assume K: "K \<subseteq> {j0<..}" "finite K" "card K = Suc j"
      then obtain i where "Max (insert j0 (K - {Max K})) < i" "K = insert i (K - {Max K})"
        apply (simp add: subset_iff)
        by (metis Diff_iff Max.coboundedI Max_in card_0_eq insert_Diff insert_iff le_neq_implies_less nat.distinct(1))
      then  show "\<exists>L\<subseteq>{j0<..}. finite L \<and> card L = j \<and>
                 (\<exists>i\<in>{Max (insert j0 L)<..}. K = insert i L)"
        using K
        by (metis Max_in card_Diff_singleton_if card_gt_0_iff diff_Suc_1 finite_Diff greaterThan_iff insert_subset zero_less_Suc)
    qed
    show "?rhs \<subseteq> \<K> j0 (Suc j)"
      by (force simp:  \<K>_def nsets_def USigma_def)
  qed

  define BB where "BB \<equiv> \<lambda>j0 j K. list_of (a j0 \<union> (\<Union>i<j. b (enum K i) (j0,i)))"
  define XX where "XX \<equiv> \<lambda>j. BB j j ` \<K> j j"

  have less_list_of:  "BB j i K < list_of (b l (j,i))"
    if K: "K \<in> \<K> j i" "\<forall>j\<in>K. j < l" and "i \<le> j" "j \<le> l" for j i K l
    unfolding BB_def
  proof (rule less_sets_imp_sorted_list_of_set)
    have "\<And>i. i < card K \<Longrightarrow> b (enum K i) (j,i) \<lless> b l (j, card K)"
      using that by (metis \<K>_card \<K>_enum \<K>_finite bb finite_enumerate_in_set nat_less_le less_le_trans)
    then show "a j \<union> (\<Union>i<i. b (enum K i) (j,i)) \<lless> b l (j,i)"
      using that unfolding \<K>_def nsets_def
      by (auto simp: less_sets_Un1 less_sets_UN1 ab finite_enumerate_in_set subset_eq)
  qed auto
  have BB_Suc: "BB j0 (Suc j) K = usplit (\<lambda>L k. BB j0 j L @ list_of (b k (j0, j))) K"
    if j: "j \<le> j0" and K: "K \<in> \<K> j0 (Suc j)" for j0 j K
    \<comment>\<open>towards the ordertype proof\<close>
  proof -
    have Kj: "K \<subseteq> {j0<..}" and [simp]: "finite K" and cardK: "card K = Suc j"
      using K by (auto simp: \<K>_def nsets_def)
    have KMK: "K - {Max K} \<in> \<K> j0 j"
      using that by (simp add: \<K>_Suc USigma_iff \<K>_finite less_sets_def usplit_def)
    have "j0 < Max K"
      by (metis Kj Max_in cardK card_gt_0_iff greaterThan_iff subsetD zero_less_Suc)
    have MaxK: "Max K = enum K j"
    proof (rule Max_eqI)
      show "enum K j \<in> K"
        by (simp add: cardK finite_enumerate_in_set)
      show "k \<le> enum K j" if "k \<in> K" for k
        using that K
        by (metis \<open>finite K\<close> cardK enum_obtain_index_finite finite_enumerate_mono leI less_Suc_eq less_asym)
    qed auto
    have ene: "i<j \<Longrightarrow> enum (K - {enum K j}) i = enum K i" for i
      using finite_enumerate_Diff_singleton [OF \<open>finite K\<close>] by (simp add: cardK)
    have "BB j0 (Suc j) K = list_of ((a j0 \<union> (\<Union>x<j. b (enum K x) (j0, x))) \<union> b (enum K j) (j0, j))"
      by (simp add: BB_def lessThan_Suc Un_ac)
    also have "\<dots> = list_of ((a j0 \<union> (\<Union>i<j. b (enum K i) (j0, i)))) @ list_of (b (enum K j) (j0, j))"
    proof (rule sorted_list_of_set_Un)
      have "b (enum K i) (j0, i) \<lless> b (enum K j) (j0, j)" if "i<j" for i
      proof (rule bb)
        show "i < j0"
          using j that by linarith
        show "j0 \<le> enum K i"
          using that K by (metis \<K>_enum cardK less_SucI less_imp_le_nat)
        show "enum K i < enum K j"
          by (simp add: cardK finite_enumerate_mono that)
      qed
      moreover have "a j0 \<lless> b (enum K j) (j0, j)"
        using MaxK \<open>j0 < Max K\<close> ab by auto
      ultimately show "a j0 \<union> (\<Union>x<j. b (enum K x) (j0, x)) \<lless> b (enum K j) (j0, j)"
        by (simp add: less_sets_Un1 less_sets_UN1)
    qed (auto simp: finite_UnI)
    also have "\<dots> = BB j0 j (K - {Max K}) @ list_of (b (Max K) (j0, j))"
      by (simp add: BB_def MaxK ene)
    also have "\<dots> = usplit (\<lambda>L k. BB j0 j L @ list_of (b k (j0, j))) K"
      by (simp add: usplit_def)
    finally show ?thesis .
  qed

  have enum_d_0: "enum (d j) 0 = Inf (d j)" for j
    using enum_0_eq_Inf_finite by auto

  have Inf_b_less: "\<Sqinter>(b k' (j',i')) < \<Sqinter>(b k (j,i))"
    if j: "i' < j'" "i < j" "j'\<le>k'" "j\<le>k" and k: "k'<k" for i i' j j' k' k
    using bb [of i' j' k' k j i] that b_ne [of i' j' k'] b_ne [of i j k]
    by (simp add: less_sets_def Inf_nat_def1)

  have b_ge_k: "\<Sqinter> (b k (k, k-1)) \<ge> k-1" if "k>0" for k
    using that
  proof (induction k)
    case (Suc k)
    show ?case
    proof (cases "k=0")
      case False
      have "\<Sqinter> (b k (k, k - Suc 0)) < \<Sqinter> (b (Suc k) (Suc k, k))"
        using False Inf_b_less by auto
      with False Suc show ?thesis
        by simp
    qed auto
  qed auto

  have b_ge: "\<Sqinter> (b k (j,i)) \<ge> k-1" if k: "k>0" "k \<ge> j" and "j > i" for k j i
    using k
  proof (induction k)
    case (Suc k)
    show ?case
    proof (cases "j \<le> k")
      case True
      have "\<Sqinter> (b k (j,i)) < \<Sqinter> (b (Suc k) (j,i))"
        using \<open>j > i\<close> Suc True by (force intro: Inf_b_less)
      then show ?thesis
        using Suc.IH True by linarith
    next
      case False
      then have "j = Suc k"
        using Suc.prems(2) by linarith
      with \<open>i < j\<close> have "i < Suc k"
        by fastforce
      moreover have "\<not> \<Sqinter> (b (Suc k) (j,i)) < \<Sqinter> (b (Suc k) (j,i))"
        by fastforce
      ultimately have "\<not> Suc (\<Sqinter> (b (Suc k) (j,i))) < Suc k"
        by (metis Inf_b_less \<open>j = Suc k\<close> b_ge_k diff_Suc_1 leD le_refl lessI zero_less_Suc)
      then show ?thesis
        by simp
    qed
  qed auto

  have hd_b: "hd (list_of (b k (j,i))) = \<Sqinter> (b k (j,i))"
    if "i < j" "j \<le> k" for k j i
    using that by (simp add: hd_list_of cInf_eq_Min)

  have b_disjoint_less: "b (enum K i) (j0, i) \<inter> b (enum K i') (j0, i') = {}"
    if K: "K \<subseteq> {j0<..}" "finite K" "card K \<ge> j0" "i' < j" "i < i'" "j \<le> j0" for i i' j j0 K
  proof (intro bb less_sets_imp_disjnt [unfolded disjnt_def])
    show "i < j0"
      using that by linarith
    then show "j0 \<le> enum K i"
      by (meson K finite_enumerate_in_set greaterThan_iff less_imp_le_nat less_le_trans subsetD)
    show "enum K i < enum K i'"
      using K \<open>j \<le> j0\<close> that by auto
  qed

  have b_disjoint: "b (enum K i) (j0, i) \<inter> b (enum K i') (j0, i') = {}"
    if K: "K \<subseteq> {j0<..}" "finite K" "card K \<ge> j0" "i < j" "i' < j" "i \<noteq> i'" "j \<le> j0" for i i' j j0 K
    using that b_disjoint_less inf_commute neq_iff by metis

  have ot\<omega>: "ordertype ((\<lambda>k. list_of (b k (j,i))) ` {Max (insert j K)<..}) ?LL = \<omega>"
             (is "?lhs = _")
    if K: "K \<in> \<K> j i" "j > i" for j i K
  proof -
    have Sucj: "Suc (Max (insert j K)) \<ge> j"
      using \<K>_finite that(1) le_Suc_eq by auto
    let ?N = "{Inf(b k (j,i))| k. Max (insert j K) < k}"
    have infN: "infinite ?N"
    proof (clarsimp simp add: infinite_nat_iff_unbounded_le)
      fix m
      show "\<exists>n\<ge>m. \<exists>k. n = \<Sqinter> (b k (j,i)) \<and> Max (insert j K) < k"
        using b_ge [of _ j i] \<open>j > i\<close> Sucj
        by (metis (no_types, lifting) diff_Suc_1 le_SucI le_trans less_Suc_eq_le nat_le_linear zero_less_Suc)
    qed
    have [simp]: "Max (insert j K) < k \<longleftrightarrow> j < k \<and> (\<forall>a\<in>K. a < k)" for k
      using that by (auto simp: \<K>_finite)
    have "?lhs = ordertype ?N less_than"
    proof (intro ordertype_eqI strip)
      have "list_of (b k (j,i)) = list_of (b k' (j,i))"
        if "j \<le> k" "j \<le> k'"  "hd (list_of (b k (j,i))) = hd (list_of (b k' (j,i)))"
        for k k'
        by (metis Inf_b_less \<open>i < j\<close> hd_b nat_less_le not_le that)
      moreover have "\<exists>k' j' i'. hd (list_of (b k (j,i))) = \<Sqinter> (b k' (j', i')) \<and> i' < j' \<and> j' \<le> k'"
        if "j \<le> k" for k
        using that \<open>i < j\<close> hd_b less_imp_le_nat by blast
      moreover have "\<exists>k'. hd (list_of (b k (j,i))) = \<Sqinter> (b k' (j,i)) \<and> j < k' \<and> (\<forall>a\<in>K. a < k')"
         if "j < k" "\<forall>a\<in>K. a < k" for k
        using that K hd_b less_imp_le_nat by blast
      moreover have "\<Sqinter> (b k (j,i)) \<in> hd ` (\<lambda>k. list_of (b k (j,i))) ` {Max (insert j K)<..}"
        if "j < k" "\<forall>a\<in>K. a < k" for k
        using that K by (auto simp: hd_b image_iff)
      ultimately
      show "bij_betw hd ((\<lambda>k. list_of (b k (j,i))) ` {Max (insert j K)<..}) {\<Sqinter> (b k (j,i)) |k. Max (insert j K) < k}"
        by (auto simp: bij_betw_def inj_on_def)
    next
      fix ms ns
      assume "ms \<in> (\<lambda>k. list_of (b k (j,i))) ` {Max (insert j K)<..}"
        and "ns \<in> (\<lambda>k. list_of (b k (j,i))) ` {Max (insert j K)<..}"
      with that obtain k k' where
        ms: "ms = list_of (b k (j,i))" and ns: "ns = list_of (b k' (j,i))"
        and "j < k" "j < k'" and lt_k: "\<forall>a\<in>K. a < k" and lt_k': "\<forall>a\<in>K. a < k'"
        by (auto simp: \<K>_finite)
      then have len_eq [simp]: "length ns = length ms"
        by (simp add: card_b)
      have nz: "length ns \<noteq> 0"
        using b_ne \<open>i < j\<close> \<open>j < k'\<close> ns by auto
      show "(hd ms, hd ns) \<in> less_than \<longleftrightarrow> (ms, ns) \<in> ?LL"
      proof
        assume "(hd ms, hd ns) \<in> less_than"
        then show "(ms, ns) \<in> ?LL"
          using that nz
          by (fastforce simp add: lenlex_def \<K>_finite card_b intro: hd_lex)
      next
        assume \<section>: "(ms, ns) \<in> ?LL"
        then have "(list_of (b k' (j,i)), list_of (b k (j,i))) \<notin> ?LL"
          using less_asym ms ns omega_sum_1_less by blast
        then show "(hd ms, hd ns) \<in> less_than"
          using \<open>j < k\<close> \<open>j < k'\<close> Inf_b_less [of i j i j] ms ns
          by (metis Cons_lenlex_iff \<section> len_eq b_ne card_b_finite diff_Suc_1 hd_Cons_tl hd_b length_Cons less_or_eq_imp_le less_than_iff linorder_neqE_nat sorted_list_of_set_eq_Nil_iff that(2))
      qed
    qed auto
    also have "\<dots> = \<omega>"
      using infN ordertype_nat_\<omega> by blast
    finally show ?thesis .
  qed

  have ot\<omega>j: "ordertype (BB j0 j ` \<K> j0 j) ?LL = \<omega>\<up>j" if "j \<le> j0" for j j0
    using that
  proof (induction j)
    case 0
    then show ?case
      by (auto simp: XX_def)
  next
    case (Suc j)
    then have ih: "ordertype (BB j0 j ` \<K> j0 j) ?LL = \<omega> \<up> j"
      by simp
    have "j \<le> j0"
      by (simp add: Suc.prems Suc_leD)
    have inj_BB: "inj_on (BB j0 j) ([{j0<..}]\<^bsup>j\<^esup>)"
    proof (clarsimp simp: inj_on_def BB_def nsets_def subset_iff sorted_list_of_set_Un less_sets_UN2)
      fix X Y
      assume X [rule_format]: "\<forall>t. t \<in> X \<longrightarrow> j0 < t"
        and Y [rule_format]: "\<forall>t. t \<in> Y \<longrightarrow> j0 < t"
        and "finite X"
        and jeq: "j = card X"
        and "finite Y"
        and "card Y = card X"
        and eq: "list_of (a j0 \<union> (\<Union>i<card X. b (enum X i) (j0,i)))
               = list_of (a j0 \<union> (\<Union>i<card X. b (enum Y i) (j0,i)))"
      have enumX: "\<And>n. \<lbrakk>n < card X\<rbrakk> \<Longrightarrow> j0 \<le> enum X n"
        using X \<open>finite X\<close> finite_enumerate_in_set less_imp_le_nat by blast
      have enumY: "\<And>n. \<lbrakk>n < card X\<rbrakk> \<Longrightarrow> j0 \<le> enum Y n"
        by (simp add: Y \<open>card Y = card X\<close> \<open>finite Y\<close> finite_enumerate_in_set less_imp_le_nat)
      have smX: "strict_mono_sets {..<card X} (\<lambda>i. b (enum X i) (j0, i))"
        and smY: "strict_mono_sets {..<card X} (\<lambda>i. b (enum Y i) (j0, i))"
        using Suc.prems \<open>card Y = card X\<close> \<open>finite X\<close> \<open>finite Y\<close> bb enumX enumY jeq
        by (auto simp: strict_mono_sets_def)

      have len_eq: "length ms = length ns"
        if "(ms, ns) \<in> list.set (zip (map (list_of \<circ> (\<lambda>i. b (enum X i) (j0,i))) (list_of {..<n}))
                                     (map (list_of \<circ> (\<lambda>i. b (enum Y i) (j0,i))) (list_of {..<n})))"
          "n \<le> card X"
        for ms ns n
        using that
      by (induction n rule: nat.induct) (auto simp: card_b enumX enumY)
      have "concat (map (list_of \<circ> (\<lambda>i. b (enum X i) (j0, i))) (list_of {..<card X}))
          = concat (map (list_of \<circ> (\<lambda>i. b (enum Y i) (j0, i))) (list_of {..<card X}))"
        using eq
        by (simp add: sorted_list_of_set_Un less_sets_UN2 sorted_list_of_set_UN_lessThan ab enumX enumY smX smY)
      then have map_eq: "map (list_of \<circ> (\<lambda>i. b (enum X i) (j0, i))) (list_of {..<card X})
                       = map (list_of \<circ> (\<lambda>i. b (enum Y i) (j0, i))) (list_of {..<card X})"
        by (rule concat_injective) (auto simp: len_eq split: prod.split)
      have "enum X i = enum Y i" if "i < card X" for i
      proof -
        have "Inf (b (enum X i) (j0,i)) = Inf (b (enum Y i) (j0,i))"
          using iffD1 [OF map_eq_conv, OF map_eq] Suc.prems that
          by (metis (mono_tags, lifting) card_b_finite comp_apply finite_lessThan lessThan_iff set_sorted_list_of_set)
        moreover have "Inf (b (enum X i) (j0,i)) \<in> (b (enum X i) (j0,i))"
          "Inf (b (enum Y i) (j0,i)) \<in> (b (enum Y i) (j0,i))" "i < j0"
          using Inf_nat_def1 Suc.prems b_ne enumX enumY jeq that by auto
        ultimately show ?thesis
          by (metis Inf_b_less enumX enumY leI nat_less_le that)
      qed
      then show "X = Y"
        by (simp add: \<open>card Y = card X\<close> \<open>finite X\<close> \<open>finite Y\<close> finite_enum_ext)
    qed
    have BB_Suc': "BB j0 (Suc j) X = usplit (\<lambda>L k. BB j0 j L @ list_of (b k (j0, j))) X"
      if "X \<in> USigma (\<K> j0 j) (\<lambda>K. {Max (insert j0 K)<..})" for X
      using that
      by (simp add: USigma_iff \<K>_finite less_sets_def usplit_def \<K>_Suc BB_Suc \<open>j \<le> j0\<close>)
    have "ordertype (BB j0 (Suc j) ` \<K> j0 (Suc j)) ?LL
        = ordertype
           (usplit (\<lambda>L k. BB j0 j L @ list_of (b k (j0, j))) ` USigma (\<K> j0 j) (\<lambda>K. {Max (insert j0 K)<..})) ?LL"
      by (simp add: BB_Suc' \<K>_Suc)
    also have "\<dots> = \<omega> * ordertype (BB j0 j ` \<K> j0 j) ?LL"
    proof (rule ordertype_append_image_IJ)
      fix L k
      assume "L \<in> \<K> j0 j" and "k \<in> {Max (insert j0 L)<..}"
      then have "j0 < k" and L: "\<And>a. a \<in> L \<Longrightarrow> a < k"
        by (simp_all add: \<K>_finite)
      then show "BB j0 j L < list_of (b k (j0, j))"
        by (simp add: \<open>L \<in> \<K> j0 j\<close> \<open>j \<le> j0\<close> \<K>_finite less_list_of)
    next
      show "inj_on (BB j0 j) (\<K> j0 j)"
        by (simp add: \<K>_def inj_BB)
    next
      fix L
      assume L: "L \<in> \<K> j0 j"
      then show "L \<lless> {Max (insert j0 L)<..} \<and> finite L"
        by (metis \<K>_finite atLeast_Suc_greaterThan finite_insert less_sets_Suc_Max less_sets_weaken1 subset_insertI)
      show "ordertype ((\<lambda>i. list_of (b i (j0, j))) ` {Max (insert j0 L)<..}) ?LL = \<omega>"
        using L Suc.prems Suc_le_lessD ot\<omega> by blast
    qed (auto simp: \<K>_finite card_b)
    also have "\<dots> = \<omega> \<up> ord_of_nat (Suc j)"
      by (metis ih One_nat_def Ord_\<omega> Ord_ord_of_nat oexp_1_right oexp_add one_V_def ord_of_nat.simps(1) ord_of_nat.simps(2) ord_of_nat_add plus_1_eq_Suc)
    finally show ?case .
  qed

  define seqs where "seqs \<equiv> \<lambda>j0 j K. list_of (a j0) # (map (list_of \<circ> (\<lambda>i. b (enum K i) (j0,i))) (list_of {..<j}))"

  have length_seqs [simp]: "length (seqs j0 j K) = Suc j" for j0 j K
    by (simp add: seqs_def)

  have BB_eq_concat_seqs: "BB j0 j K = concat (seqs j0 j K)"
          and seqs_ne: "seqs j0 j K \<in> lists (- {[]})"
      if K: "K \<in> \<K> j0 j" and "j \<le> j0" for K j j0
  proof -
    have j0: "\<And>i. i < card K \<Longrightarrow> j0 \<le> enum K i" and le_j0: "card K \<le> j0"
      using finite_enumerate_in_set that unfolding \<K>_def nsets_def by fastforce+
    show "BB j0 j K = concat (seqs j0 j K)"
      using that unfolding BB_def \<K>_def nsets_def seqs_def
      by (fastforce simp: j0 ab bb less_sets_UN2 sorted_list_of_set_Un
          strict_mono_sets_def sorted_list_of_set_UN_lessThan)
    have "b (enum K i) (j0, i) \<noteq> {}" if "i < card K" for i
      using j0 le_j0 less_le_trans that by simp
    moreover have "card K = j"
      using K \<K>_card by blast
    ultimately show "seqs j0 j K \<in> lists (- {[]})"
      by (clarsimp simp: seqs_def) (metis card_b_finite sorted_list_of_set_eq_Nil_iff)
  qed

  have BB_decomp: "\<exists>cs. BB j0 j K = concat cs \<and> cs \<in> lists (- {[]})"
    if K: "K \<in> \<K> j0 j" and "j \<le> j0" for K j j0
    using BB_eq_concat_seqs seqs_ne K that(2) by blast

  have a_subset_M: "a k \<subseteq> M k" for k
    apply (clarsimp simp: a_def M_def DF_simps F_def Let_def split: prod.split_asm)
    by (metis (no_types) fst_conv fst_grab_subset nxt_subset snd_conv snd_grab_subset subsetD)
  have ba_Suc: "b k (j,i) \<lless> a (Suc k)" if "i < j" "j \<le> k" for i j k
    by (meson a_subset_M bM less_sets_weaken2 nat_less_le that(1) that(2))
  have ba: "b k (j,i) \<lless> a r" if "i < j" "j \<le> k" "k < r" for i j k r
    by (metis Suc_lessI a_ne aa ba_Suc less_sets_trans that)

  have disjnt_ba: "disjnt (b k (j,i)) (a r)" if "i < j" "j \<le> k" for i j k r
  proof (cases "k < r")
    case True
    then show ?thesis
      by (simp add: ba less_sets_imp_disjnt that)
  next
    case False
    then show ?thesis
    proof -
      have "a r \<lless> b k (j,i)"
        by (metis False a_ne aa ab_same less_linear less_sets_UN2 less_sets_trans rangeI)
      then show ?thesis
        using disjnt_sym less_sets_imp_disjnt by blast
    qed
  qed

  have bb_disjnt: "disjnt (b k (j,i)) (b l (r,q))"
    if "q < r" "i < j" "j \<le> k" "r \<le> l" "j < r" for i j q r k l
  proof (cases "k=l")
    case True
    with that show ?thesis
      by (force simp: pair_less_def IJ_def intro: bb_same less_sets_imp_disjnt)
  next
    case False
    with that show ?thesis
      by (metis bb less_sets_imp_disjnt disjnt_sym nat_neq_iff)
  qed

  have sum_card_b: "(\<Sum>i<j. card (b (enum K i) (j0, i))) = enum (d j0) j - enum (d j0) 0"
    if K: "K \<subseteq> {j0<..}" "finite K" "card K \<ge> j0" and "j \<le> j0" for j0 j K
    using \<open>j \<le> j0\<close>
  proof (induction j)
    case 0
    then show ?case
      by auto
  next
    case (Suc j)
    have dis: "disjnt (b (enum K j) (j0, j)) (\<Union>i<j. b (enum K i) (j0, i))"
    proof (clarsimp simp add: b_disjoint)
      fix i
      assume "i < j"
      show "disjnt (b (enum K j) (j0, j)) (b (enum K i) (j0,i))"
        by (meson Suc.prems \<open>i < j\<close> b_disjoint_less disjnt_def disjnt_sym less_Suc_eq that)
    qed
    have j0_less: "j0 < enum K j"
      by (meson Suc.prems Suc_le_lessD finite_enumerate_in_set greaterThan_iff less_le_trans subsetD K)
    have "(\<Sum>i<Suc j. card (b (enum K i) (j0, i)))
          = card (b (enum K j) (j0, j)) + (\<Sum>i<j. card (b (enum K i) (j0, i)))"
      by (simp add: lessThan_Suc card_Un_disjnt [OF _ _ dis])
    also have "\<dots> = card (b (enum K j) (j0, j)) + enum (d j0) j - enum (d j0) 0"
      using \<open>Suc j \<le> j0\<close> by (simp add: Suc.IH split: nat_diff_split)
    also have "\<dots> = enum (d j0) (Suc j) - enum (d j0) 0"
      using j0_less
      apply (simp add: card_b split: nat_diff_split)
      by (metis Suc.prems card_d finite_d finite_enumerate_step le_imp_less_Suc less_asym)
    finally show ?case .
  qed

  have card_UN_b: "card (\<Union>i<j. b (enum K i) (j0, i)) = enum (d j0) j - enum (d j0) 0"
    if K: "K \<subseteq> {j0<..}" "finite K" "card K \<ge> j0" and "j \<le> j0" for j0 j K
    using that by (simp add: card_UN_disjoint sum_card_b b_disjoint)

  have len_BB: "length (BB j j K) = enum (d j) j"
    if K: "K \<in> \<K> j j" and "j \<le> j" for j K
  proof -
    have dis_ab: "\<And>i. i < j \<Longrightarrow> disjnt (a j) (b (enum K i) (j,i))"
      using K \<K>_card \<K>_enum ab less_sets_imp_disjnt nat_less_le by blast
    show ?thesis
      using K unfolding BB_def \<K>_def nsets_def
      by (simp add: card_UN_b card_Un_disjnt dis_ab card_a cInf_le_finite finite_enumerate_in_set enum_0_eq_Inf_finite)
  qed

  have "d k \<lless> d (Suc k)" for k
    by (metis aM a_ne d_eq da less_sets_fst_grab less_sets_trans less_sets_weaken2 nxt_subset)
  then have dd: "d k' \<lless> d k" if "k' < k" for k' k
    by (meson UNIV_I d_ne less_sets_imp_strict_mono_sets strict_mono_sets_def that)

  show thesis
  proof
    show "(\<Union> (range XX)) \<subseteq> WW"
      by (auto simp: XX_def BB_def WW_def)
    show "ordertype (\<Union> (range XX)) (?LL) = \<omega> \<up> \<omega>"
      using ot\<omega>j by (simp add: XX_def ordertype_\<omega>\<omega>)
  next
    fix U
    assume U: "U \<in> [\<Union> (range XX)]\<^bsup>2\<^esup>"
    then obtain x y where Ueq: "U = {x,y}" and len_xy: "length x \<le> length y"
      by (auto simp: lenlex_nsets_2_eq lenlex_length)

    show "\<exists>l. Form l U \<and> (0 < l \<longrightarrow> [enum N l] < inter_scheme l U \<and> list.set (inter_scheme l U) \<subseteq> N)"
    proof (cases "length x = length y")
      case True
      then show ?thesis
        using Form.intros(1) U Ueq by fastforce
    next
      case False
      then have xy: "length x < length y"
        using len_xy by auto
      obtain j r K L where K: "K \<in> \<K> j j" and xeq: "x = BB j j K"
        and ne: "BB j j K \<noteq> BB r r L"
        and L: "L \<in> \<K> r r" and yeq: "y = BB r r L"
        using U by (auto simp: Ueq XX_def)
      then have "length x = enum (d j) j" "length y = enum (d r) r"
        by (auto simp: len_BB)
      then have "j < r"
        using xy dd
        by (metis card_d finite_enumerate_in_set finite_d lessI less_asym less_setsD linorder_neqE_nat)
      then have aj_ar: "a j \<lless> a r"
        using aa by auto
      have Ksub: "K \<subseteq> {j<..}" and "finite K" "card K \<ge> j"
        using K by (auto simp: \<K>_def nsets_def)
      have Lsub: "L \<subseteq> {r<..}" and "finite L" "card L \<ge> r"
        using L by (auto simp: \<K>_def nsets_def)
      have enumK: "enum K i > j" if "i < j" for i
        using K \<K>_card \<K>_enum that by blast
      have enumL: "enum L i > r" if "i < r" for i
        using L \<K>_card \<K>_enum that by blast
      have "list.set (acc_lengths w (seqs j0 j K)) \<subseteq> (+) w ` d j0"
        if K: "K \<subseteq> {j0<..}" "finite K" "card K \<ge> j0" and "j \<le> j0" for j0 j K w
        using \<open>j \<le> j0\<close>
      proof (induction j arbitrary: w)
        case 0
        then show ?case
          by (simp add: seqs_def acc_lengths.simps Inf_nat_def1 card_a)
      next
        case (Suc j)
        let ?db = "\<Sqinter> (d j0) + ((\<Sum>i<j. card (b (enum K i) (j0,i))) + card (b (enum K j) (j0,j)))"
        have "j0 < enum K j"
          by (meson Suc.prems Suc_le_lessD finite_enumerate_in_set greaterThan_iff le_trans subsetD K)
        then have "?db = enum (d j0) (Suc j)"
          using Suc.prems
          apply (simp add: sum_card_b card_b that enum_d_0 split: nat_diff_split)
          by (simp add: cInf_le_finite finite_enumerate_in_set leD)
        then have "?db \<in> d j0"
          using Suc.prems finite_enumerate_in_set by (auto simp: finite_enumerate_in_set)
        moreover have "list.set (acc_lengths w (seqs j0 j K)) \<subseteq> (+) w ` d j0"
          by (simp add: Suc Suc_leD)
        then have "list.set (acc_lengths (w + \<Sqinter> (d j0))
                             (map (list_of \<circ> (\<lambda>i. b (enum K i) (j0,i))) (list_of {..<j})))
                   \<subseteq> (+) w ` d j0"
          by (simp add: seqs_def acc_lengths.simps card_a subset_insertI)
        ultimately show ?case
          by (simp add: seqs_def acc_lengths.simps acc_lengths_append image_iff Inf_nat_def1
                        sum_sorted_list_of_set_map card_a)
      qed
      then have acc_lengths_subset_d: "list.set (acc_lengths 0 (seqs j0 j K)) \<subseteq> d j0"
        if K: "K \<subseteq> {j0<..}" "finite K" "card K \<ge> j0" and "j \<le> j0" for j0 j K
        by (metis image_add_0 that)

      have "strict_sorted x" "strict_sorted y"
        by (auto simp: xeq yeq BB_def)
      have disjnt_xy: "disjnt (list.set x) (list.set y)"
      proof -
        have "disjnt (a j) (a r)"
          using \<open>j < r\<close> aa less_sets_imp_disjnt by blast
        moreover have "disjnt (b (enum K i) (j,i)) (a r)" if "i < j" for i
          by (simp add: disjnt_ba enumK less_imp_le_nat that)
        moreover have "disjnt (a j) (b (enum L q) (r,q))" if "q < r" for q
          by (meson disjnt_ba disjnt_sym enumL less_imp_le_nat that)
        moreover have "disjnt (b (enum K i) (j,i)) (b (enum L q) (r,q))" if "i < j" "q < r" for i q
        by (meson \<open>j < r\<close> bb_disjnt enumK enumL less_imp_le that)
      ultimately show ?thesis
          by (simp add: xeq yeq BB_def)
      qed
      have "\<exists>us vs. merge (seqs j j K) (seqs r r L) us vs"
      proof (rule merge_exists)
        show "strict_sorted (concat (seqs j j K))"
          using BB_eq_concat_seqs K \<open>strict_sorted x\<close> xeq by auto
        show "strict_sorted (concat (seqs r r L))"
          using BB_eq_concat_seqs L \<open>strict_sorted y\<close> yeq by auto
        show "seqs j j K \<in> lists (- {[]})" "seqs r r L \<in> lists (- {[]})"
          by (auto simp: K L seqs_ne)
        show "hd (seqs j j K) < hd (seqs r r L)"
          by (simp add: aj_ar less_sets_imp_list_less seqs_def)
        show "seqs j j K \<noteq> []" "seqs r r L \<noteq> []"
          using seqs_def by blast+
        have less_bb: "b (enum K i) (j,i) \<lless> b (enum L p) (r, p)"
          if neg: "\<not> b (enum L p) (r, p) \<lless> b (enum K i) (j,i)" and "i < j" "p < r"
          for i p
        proof (cases "enum K i" "enum L p" rule: linorder_cases)
          case less
          then show ?thesis
            by (simp add: bb enumK less_imp_le_nat \<open>i < j\<close>)
        next
          case equal
          then show ?thesis
            using \<open>j < r\<close> enumK \<open>i < j\<close> by (force simp: IJ_iff pair_less_def intro: bb_same)
        next
          case greater
          then show ?thesis
            using bb enumL less_imp_le_nat neg \<open>p < r\<close> by blast
        qed
        show "u < v \<or> v < u"
          if "u \<in> list.set (seqs j j K)" and "v \<in> list.set (seqs r r L)" for u v
          using that enumK enumL
          apply (auto simp: seqs_def aj_ar intro!: less_bb less_sets_imp_list_less)
          apply (meson ab ba less_imp_le_nat not_le)+
          done
      qed
      then obtain uus vvs where merge: "merge (seqs j j K) (seqs r r L) uus vvs"
        by metis
      then have "uus \<noteq> []"
        using merge_length1_gt_0 by (auto simp: seqs_def)
      then obtain u1 us where us: "u1#us = uus"
        by (metis neq_Nil_conv)
      define ku where "ku \<equiv> length (u1#us)"
      define ps where "ps \<equiv> acc_lengths 0 (u1#us)"
      have us_ne: "u1#us \<in> lists (- {[]})"
        using merge_length1_nonempty seqs_ne us merge us K by auto
      have xu_eq: "x = concat (u1#us)"
        using BB_eq_concat_seqs K merge merge_preserves us xeq by auto
      then have "strict_sorted u1"
        using \<open>strict_sorted x\<close> strict_sorted_append_iff by auto
      have u_sub: "list.set ps \<subseteq> list.set (acc_lengths 0 (seqs j j K))"
        using acc_lengths_merge1 merge ps_def us by blast
      have "vvs \<noteq> []"
        using merge BB_eq_concat_seqs L merge_preserves xy yeq by auto
      then obtain v1 vs where vs: "v1#vs = vvs"
        by (metis neq_Nil_conv)
      define kv where "kv \<equiv> length (v1#vs)"
      define qs where "qs \<equiv> acc_lengths 0 (v1#vs)"
      have vs_ne: "v1#vs \<in> lists (- {[]})"
        using L merge merge_length2_nonempty seqs_ne vs by auto
      have yv_eq: "y = concat (v1#vs)"
        using BB_eq_concat_seqs L merge merge_preserves vs yeq by auto
      then have "strict_sorted v1"
        using \<open>strict_sorted y\<close> strict_sorted_append_iff by auto
      have v_sub: "list.set qs \<subseteq> list.set (acc_lengths 0 (seqs r r L))"
        using acc_lengths_merge2 merge qs_def vs by blast

      have ss_concat_jj: "strict_sorted (concat (seqs j j K))"
        using BB_eq_concat_seqs K \<open>strict_sorted x\<close> xeq by auto
      then obtain k: "0 < kv" "kv \<le> ku" "ku \<le> Suc kv" "kv \<le> Suc j"
        using us vs merge_length_le merge_length_le_Suc merge_length_less2 merge
        unfolding ku_def kv_def by fastforce

      define zs where "zs \<equiv> concat [ps,u1,qs,v1] @ interact us vs"
      have ss: "strict_sorted zs"
      proof -
        have ssp: "strict_sorted ps"
          unfolding ps_def by (meson strict_sorted_acc_lengths us_ne)
        have ssq: "strict_sorted qs"
          unfolding qs_def by (meson strict_sorted_acc_lengths vs_ne)

        have "d j \<lless> list.set x"
          using da [of j] db [of j]  K \<K>_card \<K>_enum nat_less_le
          by (auto simp: xeq BB_def less_sets_Un2 less_sets_UN2)
        then have ac_x: "acc_lengths 0 (seqs j j K) < x"
          by (meson Ksub \<open>finite K\<close> \<open>j \<le> card K\<close> acc_lengths_subset_d dual_order.refl less_sets_imp_list_less less_sets_weaken1)
        then have "ps < u1"
          by (metis K Ksub UnI1 \<K>_card \<open>finite K\<close> \<open>j \<le> card K\<close> \<open>d j \<lless> list.set x\<close> acc_lengths_subset_d concat.simps(2) empty_iff empty_set hd_append2 less_list_def less_sets_imp_list_less less_sets_weaken1 list.set_sel(1) set_append u_sub xu_eq)

        have "d r \<lless> list.set y"
          using da [of r] db [of r]  L \<K>_card \<K>_enum nat_less_le
          by (auto simp: yeq BB_def less_sets_Un2 less_sets_UN2)
        then have "acc_lengths 0 (seqs r r L) < y"
          by (meson Lsub \<open>finite L\<close> \<open>r \<le> card L\<close> acc_lengths_subset_d dual_order.refl less_sets_imp_list_less less_sets_weaken1)
        then have "qs < v1"
          by (metis L Lsub UnI1 \<K>_card \<open>finite L\<close> \<open>r \<le> card L\<close> \<open>d r \<lless> list.set y\<close> acc_lengths_subset_d concat.simps(2) empty_iff empty_set hd_append2 less_list_def less_sets_imp_list_less less_sets_weaken1 list.set_sel(1) set_append v_sub yv_eq)

        have carda_v1: "card (a r) \<le> length v1"
          using length_hd_merge2 [OF merge] unfolding vs [symmetric] by (simp add: seqs_def)
        have ab_enumK: "\<And>i. i < j \<Longrightarrow> a j \<lless> b (enum K i) (j,i)"
          by (meson ab enumK le_trans less_imp_le_nat)

        have ab_enumL: "\<And>q. q < r \<Longrightarrow> a j \<lless> b (enum L q) (r,q)"
          by (meson \<open>j < r\<close> ab enumL le_trans less_imp_le_nat)
        then have ay: "a j \<lless> list.set y"
          by (auto simp: yeq BB_def less_sets_Un2 less_sets_UN2 aj_ar)

        have disjnt_hd_last_K_y: "disjnt {hd l..last l} (list.set y)"
          if l: "l \<in> list.set (seqs j j K)" for l
        proof (clarsimp simp add: yeq BB_def disjnt_iff Ball_def, intro conjI strip)
          fix u
          assume u: "u \<le> last l" and "hd l \<le> u"
          with l consider "u \<le> last (list_of (a j))" "hd (list_of (a j)) \<le> u"
            | i where "i<j" "u \<le> last (list_of (b (enum K i) (j,i)))" "hd (list_of (b (enum K i) (j,i))) \<le> u"
            by (force simp: seqs_def)
          note l_cases = this
          then show "u \<notin> a r"
          proof cases
            case 1
            then show ?thesis
              by (metis a_ne aj_ar finite_a last_in_set leD less_setsD set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)
          next
            case 2
            then show ?thesis
              by (metis enumK ab ba Inf_nat_def1 b_ne card_b_finite hd_b last_in_set less_asym less_setsD not_le set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)
          qed
          fix q
          assume "q < r"
          show "u \<notin> b (enum L q) (r,q)" using l_cases
          proof cases
            case 1
            then show ?thesis
              by (metis \<open>q < r\<close> a_ne ab_enumL finite_a last_in_set leD less_setsD set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)
          next
            case 2
            show ?thesis
            proof (cases "enum K i = enum L q")
              case True
              then show ?thesis
                using 2 bb_same [of concl: "enum L q" j i r q] \<open>j < r\<close>
                apply (simp add: IJ_def pair_less_def less_sets_def)
                by (metis enumK b_ne card_b_finite last_in_set leD less_imp_le_nat set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)
            next
              case False
              with 2 bb enumK enumL show ?thesis
                unfolding less_sets_def
                by (metis \<open>q < r\<close> b_ne card_b_finite last_in_set leD less_imp_le_nat list.set_sel(1) nat_neq_iff set_sorted_list_of_set sorted_list_of_set_eq_Nil_iff)
            qed
          qed
        qed

        have u1_y: "list.set u1 \<lless> list.set y"
          using vs yv_eq L \<open>strict_sorted y\<close> merge merge_less_sets_hd merge_preserves seqs_ne ss_concat_jj us by fastforce
        have u1_subset_seqs: "list.set u1 \<subseteq> list.set (concat (seqs j j K))"
          using merge_preserves [OF merge] us by auto

        have "b k (j,i) \<lless> d (Suc k)" if "j\<le>k" "i<j" for k j i
          by (metis bM d_eq less_sets_fst_grab less_sets_weaken2 nxt_subset that)
        then have bd: "b k (j,i) \<lless> d k'" if "j\<le>k" "i<j" "k < k'" for k k' j i
          by (metis Suc_lessI d_ne dd less_sets_trans that)

        have "a k \<lless> d (Suc k)" for k
          by (metis aM d_eq less_sets_fst_grab less_sets_weaken2 nxt_subset)
        then have ad: "a k \<lless> d k'" if "k<k'" for k k'
          by (metis Suc_lessI d_ne dd less_sets_trans that)

        have "u1 < y"
          by (simp add: u1_y less_sets_imp_list_less)
        have "n < Inf (d r)" if n: "n \<in> list.set u1" for n
        proof -
          obtain l where l: "l \<in> list.set (seqs j j K)" and n: "n \<in> list.set l"
            using n u1_subset_seqs by auto
          then consider "l = list_of (a j)" | i where "l = list_of (b (enum K i) (j,i))" "i < j"
            by (force simp: seqs_def)
          then show ?thesis
          proof cases
            case 1
            then show ?thesis
              by (metis Inf_nat_def1 \<open>j < r\<close> ad d_ne finite_a less_setsD n set_sorted_list_of_set)
          next
            case 2
            then have "Min (b (enum K i) (j,i)) \<le> n"
              using n by (simp add: less_list_def disjnt_iff less_sets_def)
            also have f8: "n < hd y"
              using less_setsD that u1_y
              by (metis gr_implies_not0 list.set_sel(1) list.size(3) xy)
            finally have "l < y"
              using 2 disjnt_hd_last_K_y [OF l] u1_y
              apply (simp add: less_list_def disjnt_iff)
              by (metis card_b_finite hd_list_of leI less_imp_le_nat list.set_sel(1))
            moreover have "last (list_of (b (enum K i) (j,i))) < hd (list_of (a r))"
              using \<open>l < y\<close> L n by (auto simp:  2yeq BB_eq_concat_seqs seqs_def less_list_def)
            then have "enum K i < r"
              by (metis "2"(1) a_ne ab card_b_finite empty_iff finite.emptyI finite_a last_in_set leI less_asym less_setsD list.set_sel(1) n set_sorted_list_of_set)
            moreover have "j \<le> enum K i"
              by (simp add: "2"(2) enumK less_imp_le_nat)
            ultimately show ?thesis
              using 2 n bd [of j "enum K i" i r] Inf_nat_def1 less_setsD by force
          qed
        qed
        then have "last u1 < Inf (d r)"
          using \<open>uus \<noteq> []\<close> us_ne by auto
        also have "\<dots> \<le> length v1"
          using card_a carda_v1 by auto
        finally have "last u1 < length v1" .
        then have "u1 < qs"
          by (simp add: qs_def acc_lengths.simps less_list_def)

        have "strict_sorted (interact (u1#us) (v1#vs))"
          using L \<open>strict_sorted x\<close> \<open>strict_sorted y\<close> merge merge_interact merge_preserves seqs_ne us vs xu_eq yv_eq by auto
        then have "strict_sorted (interact us vs)" "v1 < interact us vs"
          by (auto simp: strict_sorted_append_iff)
        moreover have "ps < u1 @ qs @ v1 @ interact us vs"
          using \<open>ps < u1\<close> us_ne unfolding less_list_def by auto
        moreover have "u1 < qs @ v1 @ interact us vs"
          by (metis \<open>u1 < qs\<close> \<open>vvs \<noteq> []\<close> acc_lengths_eq_Nil_iff hd_append less_list_def qs_def vs)
        moreover have "qs < v1 @ interact us vs"
          using \<open>qs < v1\<close> us_ne \<open>last u1 < length v1\<close> vs_ne by (auto simp: less_list_def)
        ultimately show ?thesis
          by (simp add: zs_def strict_sorted_append_iff ssp ssq \<open>strict_sorted u1\<close> \<open>strict_sorted v1\<close>)
      qed
      have ps_subset_d: "list.set ps \<subseteq> d j"
          using K Ksub \<K>_card \<open>finite K\<close> acc_lengths_subset_d u_sub by blast
      have ps_less_u1: "ps < u1"
      proof -
        have "hd u1 = hd x"
          using us_ne by (auto simp: xu_eq)
        then have "hd u1 \<in> a j"
          by (simp add: xeq BB_eq_concat_seqs K seqs_def hd_append hd_list_of)
        then have "list.set ps \<lless> {hd u1}"
          by (metis da ps_subset_d less_sets_def singletonD subset_iff)
        then show ?thesis
          by (metis less_hd_imp_less list.set(2) empty_set less_sets_imp_list_less)
      qed
      have qs_subset_d: "list.set qs \<subseteq> d r"
        using L Lsub \<K>_card \<open>finite L\<close> acc_lengths_subset_d v_sub by blast
      have qs_less_v1: "qs < v1"
      proof -
        have "hd v1 = hd y"
          using vs_ne by (auto simp: yv_eq)
        then have "hd v1 \<in> a r"
          by (simp add: yeq BB_eq_concat_seqs L seqs_def hd_append hd_list_of)
        then have "list.set qs \<lless> {hd v1}"
          by (metis da qs_subset_d less_sets_def singletonD subset_iff)
        then show ?thesis
          by (metis less_hd_imp_less list.set(2) empty_set less_sets_imp_list_less)
      qed
      have FB: "Form_Body ku kv x y zs"
        unfolding Form_Body.simps
        using ku_def kv_def ps_def qs_def ss us_ne vs_ne xu_eq xy yv_eq zs_def by blast
      then have "zs = (inter_scheme ((ku+kv) - Suc 0) {x,y})"
        by (simp add: Form_Body_imp_inter_scheme k)
      obtain l where "l \<le> 2 * (Suc j)" and l: "Form l U" and zs_eq_interact: "zs = inter_scheme l {x,y}"
      proof
        show "ku+kv-1 \<le> 2 * (Suc j)"
          using k by auto
        show "Form (ku+kv-1) U"
        proof (cases "ku=kv")
          case True
          then show ?thesis
            using FB Form.simps Ueq \<open>0 < kv\<close> by (auto simp: mult_2)
        next
          case False
          then have "ku = Suc kv"
            using k by auto
          then show ?thesis
            using FB Form.simps Ueq \<open>0 < kv\<close> by auto
        qed
        show "zs = inter_scheme (ku + kv - 1) {x, y}"
          using Form_Body_imp_inter_scheme by (simp add: FB k)
      qed
      then have "enum N l \<le> enum N (Suc (2 * Suc j))"
        by (simp add: assms less_imp_le_nat)
      also have "\<dots> < Min (d j)"
        by (metis Min_in card_0_eq card_d d_eq finite_d fst_grab_subset greaterThan_iff in_mono le_inf_iff nxt_def old.nat.distinct(2))
      finally have ls: "{enum N l} \<lless> d j"
        by simp
      have "l > 0"
        by (metis l False Form_0_cases_raw Set.doubleton_eq_iff Ueq gr0I)
      show ?thesis
        unfolding Ueq
      proof (intro exI conjI impI)
        have zs_subset: "list.set zs \<subseteq> list.set (acc_lengths 0 (seqs j j K)) \<union> list.set (acc_lengths 0 (seqs r r L)) \<union> list.set x \<union> list.set y"
          using u_sub v_sub by (auto simp: zs_def xu_eq yv_eq)
        also have "\<dots> \<subseteq> N"
        proof (simp, intro conjI)
          show "list.set (acc_lengths 0 (seqs j j K)) \<subseteq> N"
            using d_subset_N Ksub \<open>finite K\<close> \<open>j \<le> card K\<close> acc_lengths_subset_d by blast
          show "list.set (acc_lengths 0 (seqs r r L)) \<subseteq> N"
            using d_subset_N Lsub \<open>finite L\<close> \<open>r \<le> card L\<close> acc_lengths_subset_d by blast
          show "list.set x \<subseteq> N" "list.set y \<subseteq> N"
            by (simp_all add: xeq yeq BB_def a_subset_N UN_least b_subset_N)
        qed
        finally show "list.set (inter_scheme l {x, y}) \<subseteq> N"
          using zs_eq_interact by blast
        have "[enum N l] < ps"
          using ps_subset_d ls
          by (metis empty_set less_sets_imp_list_less less_sets_weaken2 list.simps(15))
        then show "[enum N l] < inter_scheme l {x, y}"
          by (simp add: zs_def less_list_def ps_def flip: zs_eq_interact)
      qed (use Ueq l in blast)
    qed
  qed
qed




subsection \<open>The main partition theorem for @{term "\<omega>\<up>\<omega>"}\<close>

definition iso_ll where "iso_ll A B \<equiv> iso (lenlex less_than \<inter> (A\<times>A)) (lenlex less_than \<inter> (B\<times>B))"

corollary ordertype_eq_ordertype_iso_ll:
  assumes "Field (Restr (lenlex less_than) A) = A" "Field (Restr (lenlex less_than) B) = B"
  shows "(ordertype A (lenlex less_than) = ordertype B (lenlex less_than))
         \<longleftrightarrow> (\<exists>f. iso_ll A B f)"
proof -
  have "total_on A (lenlex less_than) \<and> total_on B (lenlex less_than)"
    by (meson UNIV_I total_lenlex total_on_def total_on_less_than)
  then show ?thesis
    by (simp add: assms wf_lenlex lenlex_transI iso_ll_def ordertype_eq_ordertype_iso_Restr)
qed

theorem partition_\<omega>\<omega>_aux:
  assumes "\<alpha> \<in> elts \<omega>"
  shows "partn_lst (lenlex less_than) WW [\<omega>\<up>\<omega>,\<alpha>] 2" (is "partn_lst ?R WW [\<omega>\<up>\<omega>,\<alpha>] 2")
proof (cases "\<alpha> \<le> 1")
  case True
  then show ?thesis
    using strict_sorted_into_WW unfolding WW_def by (auto intro!: partn_lst_triv1[where i=1])
next
  case False
  obtain m where m: "\<alpha> = ord_of_nat m"
    using assms elts_\<omega> by auto
  then have "m>1"
    using False by auto
  show ?thesis
    unfolding partn_lst_def
  proof clarsimp
    fix f
    assume f: "f \<in> [WW]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
    let ?P0 = "\<exists>X \<subseteq> WW. ordertype X ?R = \<omega>\<up>\<omega> \<and> f ` [X]\<^bsup>2\<^esup> \<subseteq> {0}"
    let ?P1 = "\<exists>M \<subseteq> WW. ordertype M ?R = \<alpha> \<and> f ` [M]\<^bsup>2\<^esup> \<subseteq> {1}"
    have \<dagger>: "?P0 \<or> ?P1"
    proof (rule disjCI)
      assume not1: "\<not> ?P1"
      have "\<exists>W'. ordertype W' ?R = \<omega>\<up>n \<and> f ` [W']\<^bsup>2\<^esup> \<subseteq> {0} \<and> W' \<subseteq> WW_seg (n*m)" for n::nat
      proof -
        have fnm: "f \<in> [WW_seg (n*m)]\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
          using f WW_seg_subset_WW [of "n*m"] by (meson in_mono nsets_Pi_contra)
        have *: "partn_lst ?R (WW_seg (n*m)) [\<omega>\<up>n, ord_of_nat m] 2"
          using ordertype_WW_seg [of "n*m"]
          by (simp add: partn_lst_VWF_imp_partn_lst [OF Theorem_3_2])
        show ?thesis
          using partn_lst_E [OF * fnm, simplified]
          by (metis (no_types, hide_lams) One_nat_def Suc_1 WW_seg_subset_WW order.trans less_2_cases m not1 nth_Cons' nth_Cons_Suc)
      qed
      then obtain W':: "nat \<Rightarrow> nat list set"
          where otW': "\<And>n. ordertype (W' n) ?R = \<omega>\<up>n"
          and f_W': "\<And>n. f ` [W' n]\<^bsup>2\<^esup> \<subseteq> {0}"
          and seg_W': "\<And>n. W' n \<subseteq> WW_seg (n*m)"
        by metis
      define WW' where "WW' \<equiv> (\<Union>n. W' n)"
      have "WW' \<subseteq> WW"
        using seg_W' WW_seg_subset_WW by (force simp: WW'_def)
      with f have f': "f \<in> [WW']\<^bsup>2\<^esup> \<rightarrow> {..<Suc (Suc 0)}"
        using nsets_mono by fastforce
      have ot': "ordertype WW' ?R = \<omega>\<up>\<omega>"
      proof (rule antisym)
        have "ordertype WW' ?R \<le> ordertype WW ?R"
          by (simp add: \<open>WW' \<subseteq> WW\<close> lenlex_transI ordertype_mono wf_lenlex)
        with ordertype_WW
        show "ordertype WW' ?R \<le> \<omega> \<up> \<omega>"
          by simp
        have "\<omega> \<up> n \<le> ordertype (\<Union> (range W')) ?R" for n::nat
          by (metis TC_small UNIV_I UN_I otW' lenlex_transI ordertype_mono subsetI trans_less_than wf_lenlex wf_less_than)
        then show "\<omega> \<up> \<omega> \<le> ordertype WW' ?R"
          by (auto simp: elts_\<omega> oexp_Limit ZFC_in_HOL.SUP_le_iff WW'_def)
      qed
      have FR_WW: "Field (Restr (lenlex less_than) WW) = WW"
        by (simp add: Limit_omega_oexp Limit_ordertype_imp_Field_Restr ordertype_WW)
      have FR_WW': "Field (Restr (lenlex less_than) WW') = WW'"
        by (simp add: Limit_omega_oexp Limit_ordertype_imp_Field_Restr ot')
      have FR_W: "Field (Restr (lenlex less_than) (WW_seg n)) = WW_seg n" if "n>0" for n
        by (simp add: Limit_omega_oexp ordertype_WW_seg that Limit_ordertype_imp_Field_Restr)
      have FR_W': "Field (Restr (lenlex less_than) (W' n)) = W' n" if "n>0" for n
        by (simp add: Limit_omega_oexp otW' that Limit_ordertype_imp_Field_Restr)
      have "\<exists>h. iso_ll (WW_seg n) (W' n) h" if "n>0" for n
      proof (subst ordertype_eq_ordertype_iso_ll [symmetric])
        show "ordertype (WW_seg n) (lenlex less_than) = ordertype (W' n) (lenlex less_than)"
          by (simp add: ordertype_WW_seg otW')
      qed (auto simp: FR_W FR_W' that)
      then obtain h_seg where h_seg: "\<And>n. n > 0 \<Longrightarrow> iso_ll (WW_seg n) (W' n) (h_seg n)"
        by metis
      define h where "h \<equiv> \<lambda>l. if l=[] then [] else h_seg (length l) l"

      have bij_h_seg: "\<And>n. n > 0 \<Longrightarrow> bij_betw (h_seg n) (WW_seg n) (W' n)"
        using h_seg by (simp add: iso_ll_def iso_iff2 FR_W FR_W')
      have len_h_seg: "length (h_seg (length l) l) = length l * m"
        if "length l > 0" "l \<in> WW" for l
        using bij_betwE [OF bij_h_seg] seg_W' that by (simp add: WW_seg_def subset_iff)
      have hlen: "length (h x) = length (h y) \<longleftrightarrow> length x = length y" if "x \<in> WW" "y \<in> WW" for x y
        using that \<open>1 < m\<close> h_def len_h_seg by force

      have h: "iso_ll WW WW' h"
        unfolding iso_ll_def iso_iff2 FR_WW FR_WW'
      proof (intro conjI strip)
        have W'_ne: "W' n \<noteq> {}" for n
          using otW' [of n] by auto
        then have "[] \<in> WW'"
          using seg_W' [of 0] by (auto simp: WW'_def WW_seg_def)
        let ?g = "\<lambda>l. if l=[] then l else inv_into (WW_seg (length l div m)) (h_seg (length l div m)) l"
        have h_seg_iff: "\<And>n a b. \<lbrakk>a \<in> WW_seg n; b \<in> WW_seg n; n>0\<rbrakk> \<Longrightarrow>
                          (a, b) \<in> lenlex less_than \<longleftrightarrow>
                          (h_seg n a, h_seg n b) \<in> lenlex less_than \<and> h_seg n a \<in> W' n \<and> h_seg n b \<in> W' n"
          using h_seg by (auto simp: iso_ll_def iso_iff2 FR_W FR_W')

        show "bij_betw h WW WW'"
          unfolding bij_betw_iff_bijections
        proof (intro exI conjI ballI)
          fix l
          assume "l \<in> WW"
          then have l: "l \<in> WW_seg (length l)"
            by (simp add: WW_seg_def)
          have "h l \<in> W' (length l)"
          proof (cases "l=[]")
            case True
            with seg_W' [of 0] W'_ne show ?thesis
              by (auto simp: WW_seg_def h_def)
          next
            case False
            then show ?thesis
              using bij_betwE bij_h_seg h_def l by fastforce
          qed
          show "h l \<in> WW'"
            using WW'_def \<open>h l \<in> W' (length l)\<close> by blast
          show "?g (h l) = l"
          proof (cases "l=[]")
            case False
            then have "length l > 0"
              by auto
            then have "h_seg (length l) l \<noteq> []"
              using \<open>1 < m\<close> \<open>l \<in> WW\<close> len_h_seg by fastforce
            with \<open>1 < m\<close> show ?thesis
              apply (simp add: h_def len_h_seg \<open>l \<in> WW\<close>)
              by (meson \<open>0 < length l\<close> bij_betw_inv_into_left bij_h_seg l)
          qed (auto simp: h_def)
        next
          fix l
          assume "l \<in> WW'"
          then have l: "l \<in> W' (length l div m)"
            using WW_seg_def \<open>1 < m\<close> seg_W' by (fastforce simp: WW'_def)
          show "?g l \<in> WW"
          proof (cases "l=[]")
            case False
            then have "l \<notin> W' 0"
              using WW_seg_def seg_W' by fastforce
            with l have "inv_into (WW_seg (length l div m)) (h_seg (length l div m)) l \<in> WW_seg (length l div m)"
              by (metis Nat.neq0_conv bij_betwE bij_betw_inv_into bij_h_seg)
            then show ?thesis
              using False WW_seg_subset_WW by auto
          qed (auto simp: WW_def)

          show "h (?g l) = l"
          proof (cases "l=[]")
            case False
            then have "0 < length l div m"
              using WW_seg_def l seg_W' by fastforce
            then have "inv_into (WW_seg (length l div m)) (h_seg (length l div m)) l \<in> WW_seg (length l div m)"
              by (metis bij_betw_imp_surj_on bij_h_seg inv_into_into l)
            then show ?thesis
              using bij_h_seg [of "length l div m"] WW_seg_def \<open>0 < length l div m\<close> bij_betw_inv_into_right l
              by (fastforce simp add: h_def)
          qed (auto simp: h_def)
        qed
        fix a b
        assume "a \<in> WW" "b \<in> WW"
        show "(a, b) \<in> Restr (lenlex less_than) WW \<longleftrightarrow> (h a, h b) \<in> Restr (lenlex less_than) WW'"
          (is "?lhs = ?rhs")
        proof
          assume L: ?lhs
          then consider "length a < length b" | "length a = length b" "(a, b) \<in> lex less_than"
            by (auto simp: lenlex_conv)
          then show ?rhs
          proof cases
            case 1
            then have "length (h a) < length (h b)"
              using \<open>1 < m\<close> \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> h_def len_h_seg by auto
            then have "(h a, h b) \<in> lenlex less_than"
              by (auto simp: lenlex_conv)
            then show ?thesis
              using \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> \<open>bij_betw h WW WW'\<close> bij_betwE by fastforce
          next
            case 2
            then have ab: "a \<in> WW_seg (length a)" "b \<in> WW_seg (length a)"
              using \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> by (auto simp: WW_seg_def)
            have "length (h a) = length (h b)"
              using 2 \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> h_def len_h_seg by force
            moreover have "(a, b) \<in> lenlex less_than"
              using L by blast
            then have "(h_seg (length a) a, h_seg (length a) b) \<in> lenlex less_than"
              using 2 ab h_seg_iff by blast
            ultimately show ?thesis
              using 2 \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> \<open>bij_betw h WW WW'\<close> bij_betwE h_def by fastforce
          qed
        next
          assume R: ?rhs
          then have R': "(h a, h b) \<in> lenlex less_than"
            by blast
          then consider "length a < length b"
            | "length a = length b" "(h a, h b) \<in> lex less_than"
            using  \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> \<open>m > 1\<close>
            by (auto simp: lenlex_conv h_def len_h_seg split: if_split_asm)
          then show ?lhs
          proof cases
            case 1
            then have "(a, b) \<in> lenlex less_than"
              using omega_sum_less_iff by auto
            then show ?thesis
              by (simp add: \<open>a \<in> WW\<close> \<open>b \<in> WW\<close>)
          next
            case 2
            then have ab: "a \<in> WW_seg (length a)" "b \<in> WW_seg (length a)"
              using \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> by (auto simp: WW_seg_def)
            then have "(a, b) \<in> lenlex less_than"
              using bij_betwE [OF bij_h_seg] \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> R' 2
              by (simp add: h_def h_seg_iff split: if_split_asm)
            then show ?thesis
              using \<open>a \<in> WW\<close> \<open>b \<in> WW\<close> by blast
          qed
        qed
      qed

      let ?fh = "f \<circ> image h"
      have "bij_betw h WW WW'"
        using h unfolding iso_ll_def iso_iff2 by (fastforce simp: FR_WW FR_WW')
      moreover have "{..<Suc (Suc 0)} = {0,1}"
        by auto
      ultimately have fh: "?fh \<in> [WW]\<^bsup>2\<^esup> \<rightarrow> {0,1}"
        unfolding Pi_iff using bij_betwE f' bij_betw_nsets by (metis PiE comp_apply)

      have "f{x,y} = 0" if "x \<in> WW'" "y \<in> WW'" "length x = length y" "x \<noteq> y" for x y
      proof -
        obtain p q where "x \<in> W' p" and "y \<in> W' q"
          using WW'_def \<open>x \<in> WW'\<close> \<open>y \<in> WW'\<close> by blast
        then obtain n where "{x,y} \<in> [W' n]\<^bsup>2\<^esup>"
          using seg_W' \<open>1 < m\<close> \<open>length x = length y\<close> \<open>x \<noteq> y\<close>
          by (auto simp: WW'_def WW_seg_def subset_iff)
        then show "f{x,y} = 0"
          using f_W' by blast
      qed
      then have fh_eq_0_eqlen: "?fh{x,y} = 0" if "x \<in> WW" "y \<in> WW" "length x = length y" "x \<noteq> y" for x y
        using  \<open>bij_betw h WW WW'\<close>  that hlen
        by (simp add: bij_betw_iff_bijections) metis
      have m_f_0: "\<exists>x\<in>[M]\<^bsup>2\<^esup>. f x = 0" if "M \<subseteq> WW" "card M = m" for M
      proof -
        have "finite M"
          using False m that by auto
        with not1 [simplified, rule_format, of M] f
        show ?thesis
          using that \<open>1 < m\<close>
          apply (simp add: Pi_iff image_subset_iff finite_ordertype_eq_card m)
          by (metis less_2_cases nsets_mono numeral_2_eq_2 subset_iff)
      qed
      have m_fh_0: "\<exists>x\<in>[M]\<^bsup>2\<^esup>. ?fh x = 0" if "M \<subseteq> WW" "card M = m" for M
      proof -
        have "h ` M \<subseteq> WW"
          using \<open>WW' \<subseteq> WW\<close> \<open>bij_betw h WW WW'\<close> bij_betwE that(1) by fastforce
        moreover have "card (h ` M) = m"
          by (metis \<open>bij_betw h WW WW'\<close> bij_betw_def bij_betw_subset card_image that)
        ultimately have "\<exists>x \<in> [h ` M]\<^bsup>2\<^esup>. f x = 0"
          by (metis m_f_0)
        then obtain Y where "f (h ` Y) = 0" "finite Y" "card Y = 2" "Y \<subseteq> M"
          apply (simp add: nsets_def subset_image_iff)
          by (metis \<open>M \<subseteq> WW\<close> \<open>bij_betw h WW WW'\<close> bij_betw_def card_image card.infinite inj_on_subset zero_neq_numeral)
        then show ?thesis
          by (auto simp: nsets_def)
      qed

      obtain N j where "infinite N"
        and N: "\<And>k u. \<lbrakk>k > 0; u \<in> [WW]\<^bsup>2\<^esup>; Form k u; [enum N k] < inter_scheme k u; List.set (inter_scheme k u) \<subseteq> N\<rbrakk> \<Longrightarrow> ?fh u = j k"
        using lemma_3_6 [OF fh] by blast

      have infN': "infinite (enum N ` {k<..})" for k
        by (simp add: \<open>infinite N\<close> enum_works finite_image_iff infinite_Ioi strict_mono_imp_inj_on)
      have j_0: "j k = 0" if "k>0" for k
      proof -
        obtain M where M: "M \<in> [WW]\<^bsup>m\<^esup>"
                 and MF: "\<And>u. u \<in> [M]\<^bsup>2\<^esup> \<Longrightarrow> Form k u"
                 and Mi: "\<And>u. u \<in> [M]\<^bsup>2\<^esup> \<Longrightarrow> List.set (inter_scheme k u) \<subseteq> enum N ` {k<..}"
          using lemma_3_7 [OF infN' \<open>k > 0\<close>] by metis
        obtain u where u: "u \<in> [M]\<^bsup>2\<^esup>" "?fh u = 0"
          using m_fh_0 [of M] M [unfolded nsets_def] by force
        moreover
        have \<section>: "Form k u" "List.set (inter_scheme k u) \<subseteq> enum N ` {k<..}"
          by (simp_all add: MF Mi \<open>u \<in> [M]\<^bsup>2\<^esup>\<close>)
        moreover have "u \<in> [WW]\<^bsup>2\<^esup>"
          using M u by (auto simp: nsets_def)
        moreover have "enum N ` {k<..} \<subseteq> N"
          using \<open>infinite N\<close> range_enum by auto
        moreover
        have "[enum N k] < inter_scheme k u"
          using inter_scheme [of k u]  strict_mono_enum [OF \<open>infinite N\<close>] \<section>
          apply (auto simp: less_list_def subset_image_iff subset_eq Bex_def image_iff)
          by (metis hd_in_set strict_mono_def)
        ultimately show ?thesis
          using N that by auto
      qed
      obtain X where "X \<subseteq> WW" and otX: "ordertype X (lenlex less_than) = \<omega>\<up>\<omega>"
            and X: "\<And>u. u \<in> [X]\<^bsup>2\<^esup> \<Longrightarrow>
                   \<exists>l. Form l u \<and> (l > 0 \<longrightarrow> [enum N l] < inter_scheme l u \<and> List.set (inter_scheme l u) \<subseteq> N)"
        using lemma_3_8 [OF \<open>infinite N\<close>] ot' by blast
      have 0: "?fh ` [X]\<^bsup>2\<^esup> \<subseteq> {0}"
      proof clarsimp
        fix u
        assume u: "u \<in> [X]\<^bsup>2\<^esup>"
        obtain l where "Form l u" and l: "l > 0 \<longrightarrow> [enum N l] < inter_scheme l u \<and> List.set (inter_scheme l u) \<subseteq> N"
          using u X by blast
        have "?fh u = 0"
        proof (cases "l > 0")
          case False
          then have "l = 0"
            by blast
          then show ?thesis
            by (metis Form_0_cases_raw \<open>Form l u\<close> \<open>X \<subseteq> WW\<close> doubleton_in_nsets_2 fh_eq_0_eqlen subset_iff u)
        next
          case True
          then obtain "[enum N l] < inter_scheme l u" "List.set (inter_scheme l u) \<subseteq> N" "j l = 0"
            using Nat.neq0_conv j_0 l by blast
          with True show ?thesis
            using \<open>X \<subseteq> WW\<close> N inter_scheme \<open>Form l u\<close> doubleton_in_nsets_2 u by (auto simp: nsets_def)
        qed
        then show "f (h ` u) = 0"
          by auto
      qed
      show ?P0
      proof (intro exI conjI)
        show "h ` X \<subseteq> WW"
          using \<open>WW' \<subseteq> WW\<close> \<open>X \<subseteq> WW\<close> \<open>bij_betw h WW WW'\<close> bij_betw_imp_surj_on by fastforce
        show "ordertype (h ` X) (lenlex less_than) = \<omega> \<up> \<omega>"
        proof (subst ordertype_inc_eq)
          show "(h x, h y) \<in> lenlex less_than"
            if "x \<in> X" "y \<in> X" "(x, y) \<in> lenlex less_than" for x y
            using that h \<open>X \<subseteq> WW\<close> by (auto simp: FR_WW FR_WW' iso_iff2 iso_ll_def)
        qed (use otX in auto)
        show "f ` [h ` X]\<^bsup>2\<^esup> \<subseteq> {0}"
        proof (clarsimp simp: image_subset_iff nsets_def)
          fix Y
          assume "Y \<subseteq> h ` X" and "finite Y" and "card Y = 2"
          have "inv_into WW h ` Y \<subseteq> X"
            using \<open>X \<subseteq> WW\<close> \<open>Y \<subseteq> h ` X\<close> \<open>bij_betw h WW WW'\<close> bij_betw_inv_into_LEFT by blast
          moreover have "finite (inv_into WW h ` Y)"
            using \<open>finite Y\<close> by blast
          moreover have "card (inv_into WW h ` Y) = 2"
            by (metis \<open>X \<subseteq> WW\<close> \<open>Y \<subseteq> h ` X\<close> \<open>card Y = 2\<close> card_image inj_on_inv_into subset_image_iff subset_trans)
          ultimately have "f (h ` inv_into WW h ` Y) = 0"
            using 0 by (auto simp: image_subset_iff nsets_def)
          then show "f Y = 0"
            by (metis \<open>X \<subseteq> WW\<close> \<open>Y \<subseteq> h ` X\<close> image_inv_into_cancel image_mono order_trans)
        qed
      qed
    qed
    then show "\<exists>i<Suc (Suc 0). \<exists>H\<subseteq>WW. ordertype H ?R = [\<omega>\<up>\<omega>, \<alpha>] ! i \<and> f ` [H]\<^bsup>2\<^esup> \<subseteq> {i}"
      by (metis One_nat_def lessI nth_Cons_0 nth_Cons_Suc zero_less_Suc)
  qed
qed

text \<open>Theorem 3.1 of Jean A. Larson, ibid.\<close>
theorem partition_\<omega>\<omega>: "\<alpha> \<in> elts \<omega> \<Longrightarrow> partn_lst_VWF (\<omega>\<up>\<omega>) [\<omega>\<up>\<omega>,\<alpha>] 2"
  using partn_lst_imp_partn_lst_VWF_eq [OF partition_\<omega>\<omega>_aux] ordertype_WW by auto

end
