section \<open>Multiset extension of order pairs in the other direction\<close>

text \<open>Many term orders are formulated in the other direction, i.e., they use 
  strong normalization of $>$ instead of well-foundedness of $<$. Here, we
  flip the direction of the multiset extension of two orders, connect it to existing interfaces,
  and prove some further properties of the multiset extension.\<close>

theory Multiset_Extension2
  imports
    List_Order
    Multiset_Extension_Pair
begin

subsection \<open>List based characterization of @{const multpw}\<close>

lemma multpw_listI:
  assumes "length xs = length ys" "X = mset xs" "Y = mset ys"
    "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns"
  shows "(X, Y) \<in> multpw ns"
  using assms
proof (induct xs arbitrary: ys X Y)
  case (Nil ys) then show ?case by (cases ys) (auto intro: multpw.intros)
next
  case Cons1: (Cons x xs ys' X Y) then show ?case
  proof (cases ys')
    case (Cons y ys)
    then have "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns" using Cons1(5) by fastforce
    then show ?thesis using Cons1(2,5) by (auto intro!: multpw.intros simp: Cons(1) Cons1)
  qed auto
qed

lemma multpw_listE:
  assumes "(X, Y) \<in> multpw ns"
  obtains xs ys where "length xs = length ys" "X = mset xs" "Y = mset ys"
    "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns"
  using assms
proof (induct X Y arbitrary: thesis rule: multpw.induct)
  case (add x y X Y)
  then obtain xs ys where "length xs = length ys" "X = mset xs"
    "Y = mset ys" "(\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> ns)" by blast
  then show ?case using add(1) by (intro add(4)[of "x # xs" "y # ys"]) (auto, case_tac i, auto)
qed auto

subsection\<open>Definition of the multiset extension of $>$-orders\<close>

text\<open>We define here the non-strict extension of the order pair $(\geqslant, >)$ -- 
  usually written as (ns, s) in the sources --
  by just flipping the directions twice.\<close>

definition ns_mul_ext :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel"
  where "ns_mul_ext ns s \<equiv> (mult2_alt_ns (ns\<inverse>) (s\<inverse>))\<inverse>"

lemma ns_mul_extI:
  assumes "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  shows "(A, B) \<in> ns_mul_ext ns s"
  using assms by (auto simp: ns_mul_ext_def multpw_converse intro!: mult2_alt_nsI)

lemma ns_mul_extE:
  assumes "(A, B) \<in> ns_mul_ext ns s"
  obtains A1 A2 B1 B2 where "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  using assms by (auto simp: ns_mul_ext_def multpw_converse elim!: mult2_alt_nsE)

lemmas ns_mul_extI_old = ns_mul_extI[OF _ _ multpw_listI[OF _ refl refl], rule_format]

text\<open>Same for the "greater than" order on multisets.\<close>

definition s_mul_ext :: "'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a multiset rel"
  where "s_mul_ext ns s \<equiv> (mult2_alt_s (ns\<inverse>) (s\<inverse>))\<inverse>"

lemma s_mul_extI:
  assumes "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "A2 \<noteq> {#}" and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  shows "(A, B) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def multpw_converse intro!: mult2_alt_sI)

lemma s_mul_extE:
  assumes "(A, B) \<in> s_mul_ext ns s"
  obtains A1 A2 B1 B2 where "A = A1 + A2" and "B = B1 + B2"
    and "(A1, B1) \<in> multpw ns"
    and "A2 \<noteq> {#}" and "\<And>b. b \<in># B2 \<Longrightarrow> \<exists>a. a \<in># A2 \<and> (a, b) \<in> s"
  using assms by (auto simp: s_mul_ext_def multpw_converse elim!: mult2_alt_sE)

lemmas s_mul_extI_old = s_mul_extI[OF _ _ multpw_listI[OF _ refl refl], rule_format]


subsection\<open>Basic properties\<close>

lemma s_mul_ext_mono:
  assumes "ns \<subseteq> ns'" "s \<subseteq> s'" shows "s_mul_ext ns s \<subseteq> s_mul_ext ns' s'"
  unfolding s_mul_ext_def using assms mono_mult2_alt[of "ns\<inverse>" "ns'\<inverse>" "s\<inverse>" "s'\<inverse>"] by simp

lemma ns_mul_ext_mono:
  assumes "ns \<subseteq> ns'" "s \<subseteq> s'" shows "ns_mul_ext ns s \<subseteq> ns_mul_ext ns' s'"
  unfolding ns_mul_ext_def using assms mono_mult2_alt[of "ns\<inverse>" "ns'\<inverse>" "s\<inverse>" "s'\<inverse>"] by simp

lemma s_mul_ext_local_mono:
  assumes sub: "(set_mset xs \<times> set_mset ys) \<inter> ns \<subseteq> ns'" "(set_mset xs \<times> set_mset ys) \<inter> s \<subseteq> s'"
    and rel: "(xs,ys) \<in> s_mul_ext ns s"
  shows "(xs,ys) \<in> s_mul_ext ns' s'"
  using rel s_mul_ext_mono[OF sub] mult2_alt_local[of ys xs False "ns\<inverse>" "s\<inverse>"]
  by (auto simp: s_mul_ext_def converse_Int ac_simps converse_Times)

lemma ns_mul_ext_local_mono:
  assumes sub: "(set_mset xs \<times> set_mset ys) \<inter> ns \<subseteq> ns'" "(set_mset xs \<times> set_mset ys) \<inter> s \<subseteq> s'"
    and rel: "(xs,ys) \<in> ns_mul_ext ns s"
  shows "(xs,ys) \<in> ns_mul_ext ns' s'"
  using rel ns_mul_ext_mono[OF sub] mult2_alt_local[of ys xs True "ns\<inverse>" "s\<inverse>"]
  by (auto simp: ns_mul_ext_def converse_Int ac_simps converse_Times)


text\<open>The empty multiset is the minimal element for these orders\<close>

lemma ns_mul_ext_bottom: "(A,{#}) \<in> ns_mul_ext ns s"
  by (auto intro!: ns_mul_extI)

lemma ns_mul_ext_bottom_uniqueness:
  assumes "({#},A) \<in> ns_mul_ext ns s"
  shows "A = {#}"
  using assms by (auto simp: ns_mul_ext_def mult2_alt_ns_def)

lemma ns_mul_ext_bottom2:
  assumes "(A,B) \<in> ns_mul_ext ns s"
    and "B \<noteq> {#}"
  shows "A \<noteq> {#}"
  using assms by (auto simp: ns_mul_ext_def mult2_alt_ns_def)

lemma s_mul_ext_bottom:
  assumes "A \<noteq> {#}"
  shows "(A,{#}) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def mult2_alt_s_def)

lemma s_mul_ext_bottom_strict:
  "({#},A) \<notin> s_mul_ext ns s"
  by (auto simp: s_mul_ext_def mult2_alt_s_def)

text\<open>Obvious introduction rules.\<close>

lemma all_ns_ns_mul_ext:
  assumes "length as = length bs"
    and "\<forall>i. i < length bs \<longrightarrow> (as ! i, bs ! i) \<in> ns"
  shows "(mset as, mset bs) \<in> ns_mul_ext ns s"
  using assms by (auto intro!: ns_mul_extI[of _ _ "{#}" _ _ "{#}"] multpw_listI)

lemma all_s_s_mul_ext:
  assumes "A \<noteq> {#}"
    and "\<forall>b. b \<in># B \<longrightarrow> (\<exists>a. a \<in># A \<and> (a,b) \<in> s)"
  shows "(A, B) \<in> s_mul_ext ns s"
  using assms by (auto intro!: s_mul_extI[of _ "{#}" _ _ "{#}"] multpw_listI)

text\<open>Being stricly lesser than implies being lesser than\<close>

lemma s_ns_mul_ext:
  assumes "(A, B) \<in> s_mul_ext ns s"
  shows "(A, B) \<in> ns_mul_ext ns s"
  using assms by (simp add: s_mul_ext_def ns_mul_ext_def mult2_alt_s_implies_mult2_alt_ns)

text\<open>The non-strict order is reflexive.\<close>

lemma multpw_refl':
  assumes "locally_refl ns A"
  shows "(A, A) \<in> multpw ns"
proof -
  have "Restr Id (set_mset A) \<subseteq> ns" using assms by (auto simp: locally_refl_def)
  from refl_multpw[of Id] multpw_local[of A A Id] mono_multpw[OF this]
  show ?thesis by (auto simp: refl_on_def)
qed

lemma ns_mul_ext_refl_local:
  assumes "locally_refl ns A"
  shows "(A, A) \<in> ns_mul_ext ns s"
  using assms by (auto intro!:  ns_mul_extI[of A A "{#}" A A "{#}" ns s] multpw_refl')

lemma ns_mul_ext_refl:
  assumes "refl ns"
  shows "(A, A) \<in> ns_mul_ext ns s"
  using assms ns_mul_ext_refl_local[of ns A s] unfolding refl_on_def locally_refl_def by auto

text\<open>The orders are union-compatible\<close>

lemma ns_s_mul_ext_union_multiset_l:
  assumes "(A, B) \<in> ns_mul_ext ns s"
    and "C \<noteq> {#}"
    and "\<forall>d. d \<in># D \<longrightarrow> (\<exists>c. c \<in># C \<and> (c,d) \<in> s)"
  shows "(A + C, B + D) \<in> s_mul_ext ns s"
  using assms unfolding ns_mul_ext_def s_mul_ext_def
  by (auto intro!: converseI mult2_alt_ns_s_add mult2_alt_sI[of _ "{#}" _ _ "{#}"])

lemma s_mul_ext_union_compat:
  assumes "(A, B) \<in> s_mul_ext ns s"
    and "locally_refl ns C"
  shows "(A + C, B + C) \<in> s_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(2)] unfolding ns_mul_ext_def s_mul_ext_def
  by (auto intro!: converseI mult2_alt_s_ns_add)

lemma ns_mul_ext_union_compat:
  assumes "(A, B) \<in> ns_mul_ext ns s"
    and "locally_refl ns C"
  shows "(A + C, B + C) \<in> ns_mul_ext ns s"
  using assms ns_mul_ext_refl_local[OF assms(2)] unfolding ns_mul_ext_def s_mul_ext_def
  by (auto intro!: converseI mult2_alt_ns_ns_add)

context
  fixes NS :: "'a rel"
  assumes NS: "refl NS"
begin

lemma refl_imp_locally_refl: "locally_refl NS A" using NS unfolding refl_on_def locally_refl_def by auto

lemma supseteq_imp_ns_mul_ext:
  assumes "A \<supseteq># B"
  shows "(A, B) \<in> ns_mul_ext NS S"
  using assms
  by (auto intro!: ns_mul_extI[of A B "A - B" B B "{#}"] multpw_refl' refl_imp_locally_refl
      simp: subset_mset.add_diff_inverse)

lemma supset_imp_s_mul_ext:
  assumes "A \<supset># B"
  shows "(A, B) \<in> s_mul_ext NS S"
  using assms subset_mset.add_diff_inverse[of B A]
  by (auto intro!: s_mul_extI[of A B "A - B" B B "{#}"] multpw_refl' refl_imp_locally_refl
      simp: Diff_eq_empty_iff_mset subset_mset.order.strict_iff_order)

end

definition mul_ext :: "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
  where "mul_ext f xs ys \<equiv> let s = {(x,y). fst (f x y)}; ns = {(x,y). snd (f x y)}
    in ((mset xs,mset ys) \<in> s_mul_ext ns s, (mset xs, mset ys) \<in> ns_mul_ext ns s)"

definition "smulextp f m n \<longleftrightarrow> (m, n) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
definition "nsmulextp f m n \<longleftrightarrow> (m, n) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"


lemma smulextp_cong[fundef_cong]:
  assumes "xs1 = ys1"
    and "xs2 = ys2"
    and "\<And> x x'. x \<in># ys1 \<Longrightarrow> x' \<in># ys2 \<Longrightarrow> f x x' = g x x'"
  shows "smulextp f xs1 xs2 = smulextp g ys1 ys2"
  unfolding smulextp_def
proof
  assume "(xs1, xs2) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
  from s_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (g x y)}" "{(x, y). fst (g x y)}"]
  show "(ys1, ys2) \<in> s_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
    using assms by force 
next 
  assume "(ys1, ys2) \<in> s_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
  from s_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (f x y)}" "{(x, y). fst (f x y)}"]
  show "(xs1, xs2) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
    using assms by force
qed

lemma nsmulextp_cong[fundef_cong]:
  assumes "xs1 = ys1"
    and "xs2 = ys2"
    and "\<And> x x'. x \<in># ys1 \<Longrightarrow> x' \<in># ys2 \<Longrightarrow> f x x' = g x x'"
  shows "nsmulextp f xs1 xs2 = nsmulextp g ys1 ys2"
  unfolding nsmulextp_def
proof
  assume "(xs1, xs2) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
  from ns_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (g x y)}" "{(x, y). fst (g x y)}"]
  show "(ys1, ys2) \<in> ns_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
    using assms by force 
next 
  assume "(ys1, ys2) \<in> ns_mul_ext {(x, y). snd (g x y)} {(x, y). fst (g x y)}"
  from ns_mul_ext_local_mono[OF _ _ this, of "{(x, y). snd (f x y)}" "{(x, y). fst (f x y)}"]
  show "(xs1, xs2) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y). fst (f x y)}"
    using assms by force
qed


definition "mulextp f m n = (smulextp f m n, nsmulextp f m n)"

lemma mulextp_cong[fundef_cong]:
  assumes "xs1 = ys1"
    and "xs2 = ys2"
    and "\<And> x x'. x \<in># ys1 \<Longrightarrow> x' \<in># ys2 \<Longrightarrow> f x x' = g x x'"
  shows "mulextp f xs1 xs2 = mulextp g ys1 ys2"
  unfolding mulextp_def using assms by (auto cong: nsmulextp_cong smulextp_cong) 

lemma mset_s_mul_ext:
  "(mset xs, mset ys) \<in> s_mul_ext {(x, y). snd (f x y)} {(x, y).fst (f x y)} \<longleftrightarrow>
    fst (mul_ext f xs ys)"
  by (auto simp: mul_ext_def Let_def)

lemma mset_ns_mul_ext:
  "(mset xs, mset ys) \<in> ns_mul_ext {(x, y). snd (f x y)} {(x, y).fst (f x y)} \<longleftrightarrow>
    snd (mul_ext f xs ys)"
  by (auto simp: mul_ext_def Let_def)

lemma smulextp_mset_code:
  "smulextp f (mset xs) (mset ys) \<longleftrightarrow> fst (mul_ext f xs ys)"
  unfolding smulextp_def mset_s_mul_ext ..

lemma nsmulextp_mset_code:
  "nsmulextp f (mset xs) (mset ys) \<longleftrightarrow> snd (mul_ext f xs ys)"
  unfolding nsmulextp_def mset_ns_mul_ext ..

lemma nstri_mul_ext_map:
  assumes "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> fst (order s t) \<Longrightarrow> fst (order' (f s) (f t))"
    and "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> snd (order s t) \<Longrightarrow> snd (order' (f s) (f t))"
    and "snd (mul_ext order ss ts)"
  shows "snd (mul_ext order' (map f ss) (map f ts))"
  using assms mult2_alt_map[of "mset ts" "mset ss" "{(t, s). snd (order s t)}" f f
      "{(t, s). snd (order' s t)}" "{(t, s). fst (order s t)}" "{(t, s). fst (order' s t)}" True]
  by (auto simp: mul_ext_def ns_mul_ext_def converse_unfold)

lemma stri_mul_ext_map:
  assumes "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> fst (order s t) \<Longrightarrow> fst (order' (f s) (f t))"
    and "\<And>s t. s \<in> set ss \<Longrightarrow> t \<in> set ts \<Longrightarrow> snd (order s t) \<Longrightarrow> snd (order' (f s) (f t))"
    and "fst (mul_ext order ss ts)"
  shows "fst (mul_ext order' (map f ss) (map f ts))"
  using assms mult2_alt_map[of "mset ts" "mset ss" "{(t,s). snd (order s t)}" f f
      "{(t, s). snd (order' s t)}" "{(t, s). fst (order s t)}" "{(t, s). fst (order' s t)}" False]
  by (auto simp: mul_ext_def s_mul_ext_def converse_unfold)

text \<open>The non-strict order is transitive.\<close>

lemma ns_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> ns_mul_ext ns s"
    and "(B, C) \<in> ns_mul_ext ns s"
  shows "(A, C) \<in> ns_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def ns_mul_ext_def
  using trans_mult2_ns[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_ns_eq_mult2_ns_alt converse_relcomp[symmetric]) (metis trans_def)

text\<open>The strict order is trans.\<close>

lemma s_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> s_mul_ext ns s"
    and "(B, C) \<in> s_mul_ext ns s"
  shows "(A, C) \<in> s_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def s_mul_ext_def
  using trans_mult2_s[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_s_eq_mult2_s_alt converse_relcomp[symmetric]) (metis trans_def)

text\<open>The strict order is compatible on the left with the non strict one\<close>

lemma s_ns_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> s_mul_ext ns s"
    and "(B, C) \<in> ns_mul_ext ns s"
  shows "(A, C) \<in> s_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def s_mul_ext_def ns_mul_ext_def
  using compat_mult2(1)[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_s_eq_mult2_s_alt mult2_ns_eq_mult2_ns_alt converse_relcomp[symmetric])


text\<open>The strict order is compatible on the right with the non-strict one.\<close>

lemma ns_s_mul_ext_trans:
  assumes "trans s" "trans ns" "compatible_l ns s" "compatible_r ns s" "refl ns"
    and "(A, B) \<in> ns_mul_ext ns s"
    and "(B, C) \<in> s_mul_ext ns s"
  shows "(A, C) \<in> s_mul_ext ns s"
  using assms unfolding compatible_l_def compatible_r_def s_mul_ext_def ns_mul_ext_def
  using compat_mult2(2)[of "s\<inverse>" "ns\<inverse>"]
  by (auto simp: mult2_s_eq_mult2_s_alt mult2_ns_eq_mult2_ns_alt converse_relcomp[symmetric])

text\<open>@{const s_mul_ext} is strongly normalizing\<close>

lemma SN_s_mul_ext_strong:
  assumes "order_pair s ns"
    and "\<forall>y. y \<in># M \<longrightarrow> SN_on s {y}"
  shows "SN_on (s_mul_ext ns s) {M}"
  using mult2_s_eq_mult2_s_alt[of "ns\<inverse>" "s\<inverse>"] assms wf_below_pointwise[of "s\<inverse>" "set_mset M"]
  unfolding SN_on_iff_wf_below s_mul_ext_def order_pair_def compat_pair_def pre_order_pair_def
  by (auto intro!: wf_below_mult2_s_local simp: converse_relcomp[symmetric])

lemma SN_s_mul_ext:
  assumes "order_pair s ns" "SN s"
  shows "SN (s_mul_ext ns s)"
  using SN_s_mul_ext_strong[OF assms(1)] assms(2)
  by (auto simp: SN_on_def)

lemma (in order_pair) mul_ext_order_pair:
  "order_pair (s_mul_ext NS S) (ns_mul_ext NS S)" (is "order_pair ?S ?NS")
proof
  from s_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "trans ?S" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from ns_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "trans ?NS" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from ns_s_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "?NS O ?S \<subseteq> ?S" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from s_ns_mul_ext_trans trans_S trans_NS compat_NS_S compat_S_NS refl_NS
  show "?S O ?NS \<subseteq> ?S" unfolding trans_def compatible_l_def compatible_r_def by blast
next
  from ns_mul_ext_refl[OF refl_NS, of _ S]
  show "refl ?NS" unfolding refl_on_def by fast
qed

lemma (in SN_order_pair) mul_ext_SN_order_pair: "SN_order_pair (s_mul_ext NS S) (ns_mul_ext NS S)"
  (is "SN_order_pair ?S ?NS")
proof -
  from mul_ext_order_pair
  interpret order_pair ?S ?NS .
  have "order_pair S NS" by unfold_locales
  then interpret SN_ars ?S using SN_s_mul_ext[of S NS] SN by unfold_locales
  show ?thesis by unfold_locales
qed

lemma mul_ext_compat:
  assumes compat: "\<And> s t u. \<lbrakk>s \<in> set ss; t \<in> set ts; u \<in> set us\<rbrakk> \<Longrightarrow>
    (snd (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u)) \<and>
    (fst (f s t) \<and> snd (f t u) \<longrightarrow> fst (f s u)) \<and>
    (snd (f s t) \<and> snd (f t u) \<longrightarrow> snd (f s u)) \<and>
    (fst (f s t) \<and> fst (f t u) \<longrightarrow> fst (f s u))"
  shows "
    (snd (mul_ext f ss ts) \<and> fst (mul_ext f ts us) \<longrightarrow> fst (mul_ext f ss us)) \<and>
    (fst (mul_ext f ss ts) \<and> snd (mul_ext f ts us) \<longrightarrow> fst (mul_ext f ss us)) \<and>
    (snd (mul_ext f ss ts) \<and> snd (mul_ext f ts us) \<longrightarrow> snd (mul_ext f ss us)) \<and>
    (fst (mul_ext f ss ts) \<and> fst (mul_ext f ts us) \<longrightarrow> fst (mul_ext f ss us)) "
proof -
  let ?s = "{(x, y). fst (f x y)}\<inverse>" and ?ns = "{(x, y). snd (f x y)}\<inverse>"
  have [dest]: "(mset ts, mset ss) \<in> mult2_alt b2 ?ns ?s \<Longrightarrow> (mset us, mset ts) \<in> mult2_alt b1 ?ns ?s \<Longrightarrow>
    (mset us, mset ss) \<in> mult2_alt (b1 \<and> b2) ?ns ?s" for b1 b2
    using assms by (auto intro!: trans_mult2_alt_local[of _ "mset ts"] simp: in_multiset_in_set)
  show ?thesis by (auto simp: mul_ext_def s_mul_ext_def ns_mul_ext_def Let_def)
qed

lemma mul_ext_cong[fundef_cong]:
  assumes "mset xs1 = mset ys1"
    and "mset xs2 = mset ys2"
    and "\<And> x x'. x \<in> set ys1 \<Longrightarrow> x' \<in> set ys2 \<Longrightarrow> f x x' = g x x'"
  shows "mul_ext f xs1 xs2 = mul_ext g ys1 ys2"
  using assms
    mult2_alt_map[of "mset xs2" "mset xs1" "{(x, y). snd (f x y)}\<inverse>" id id "{(x, y). snd (g x y)}\<inverse>"
      "{(x, y). fst (f x y)}\<inverse>" "{(x, y). fst (g x y)}\<inverse>"]
    mult2_alt_map[of "mset ys2" "mset ys1" "{(x, y). snd (g x y)}\<inverse>" id id "{(x, y). snd (f x y)}\<inverse>"
      "{(x, y). fst (g x y)}\<inverse>" "{(x, y). fst (f x y)}\<inverse>"]
  by (auto simp: mul_ext_def s_mul_ext_def ns_mul_ext_def Let_def in_multiset_in_set)

lemma all_nstri_imp_mul_nstri:
  assumes "\<forall>i<length ys. snd (f (xs ! i) (ys ! i))"
    and "length xs = length ys"
  shows "snd (mul_ext f xs ys)"
proof-
  from assms(1) have "\<forall>i. i < length ys \<longrightarrow> (xs ! i, ys ! i) \<in> {(x,y). snd (f x y)}" by simp
  from all_ns_ns_mul_ext[OF assms(2) this] show ?thesis by (simp add: mul_ext_def)
qed

lemma relation_inter:
  shows "{(x,y). P x y} \<inter> {(x,y). Q x y} = {(x,y). P x y \<and> Q x y}"
  by blast

lemma mul_ext_unfold:
  "(x,y) \<in> {(a,b). fst (mul_ext g a b)} \<longleftrightarrow> (mset x, mset y) \<in> (s_mul_ext {(a,b). snd (g a b)} {(a,b). fst (g a b)})"
  unfolding mul_ext_def by (simp add: Let_def)

text \<open>The next lemma is a local version of strong-normalization of 
  the multiset extension, where the base-order only has to be strongly normalizing
  on elements of the multisets. This will be crucial for orders that are defined recursively
  on terms, such as RPO or WPO.\<close>
lemma mul_ext_SN:
  assumes "\<forall>x. snd (g x x)"
    and "\<forall>x y z. fst (g x y) \<longrightarrow> snd (g y z) \<longrightarrow> fst (g x z)"
    and "\<forall>x y z. snd (g x y) \<longrightarrow> fst (g y z) \<longrightarrow> fst (g x z)"
    and "\<forall>x y z. snd (g x y) \<longrightarrow> snd (g y z) \<longrightarrow> snd (g x z)"
    and "\<forall>x y z. fst (g x y) \<longrightarrow> fst (g y z) \<longrightarrow> fst (g x z)"
  shows "SN {(ys, xs).
  (\<forall>y\<in>set ys. SN_on {(s ,t). fst (g s t)} {y}) \<and>
  fst (mul_ext g ys xs)}"
proof -
  let ?R1 = "\<lambda>xs ys. \<forall>y\<in> set ys. SN_on {(s ,t). fst (g s t)} {y}"
  let ?R2 = "\<lambda>xs ys. fst (mul_ext g ys xs)"
  let ?s = "{(x,y). fst (g x y)}" and ?ns = "{(x,y). snd (g x y)}"
  have OP: "order_pair ?s ?ns" using assms(1-5)
    by unfold_locales ((unfold refl_on_def trans_def)?, blast)+
  let ?R = "{(ys, xs). ?R1 xs ys \<and> ?R2 xs ys}"
  let ?Sn = "SN_on ?R"
  {
    fix ys xs
    assume R_ys_xs: "(ys, xs) \<in> ?R"
    let ?mys = "mset ys"
    let ?mxs = "mset xs"
    from R_ys_xs have  HSN_ys: "\<forall>y. y \<in> set ys \<longrightarrow> SN_on ?s {y}" by simp
    with in_multiset_in_set[of ys] have "\<forall>y. y \<in># ?mys \<longrightarrow> SN_on ?s {y}" by simp
    from SN_s_mul_ext_strong[OF OP this] and mul_ext_unfold
    have "SN_on {(ys,xs). fst (mul_ext g ys xs)} {ys}" by fast
    from relation_inter[of ?R2 ?R1] and SN_on_weakening[OF this]
    have "SN_on ?R {ys}" by blast
  }
  then have Hyp: "\<forall>ys xs. (ys,xs) \<in> ?R \<longrightarrow> SN_on ?R {ys}" by auto
  {
    fix ys
    have "SN_on ?R {ys}"
    proof (cases "\<exists> xs. (ys, xs) \<in> ?R")
      case True with Hyp show ?thesis by simp
    next
      case False then show ?thesis by auto
    qed
  }
  then show ?thesis unfolding SN_on_def by simp
qed

lemma mul_ext_stri_imp_nstri:
  assumes "fst (mul_ext f as bs)"
  shows "snd (mul_ext f as bs)"
  using assms and s_ns_mul_ext unfolding mul_ext_def by (auto simp: Let_def)

lemma ns_ns_mul_ext_union_compat:
  assumes "(A,B) \<in> ns_mul_ext ns s"
    and "(C,D) \<in> ns_mul_ext ns s"
  shows "(A + C, B + D) \<in> ns_mul_ext ns s"
  using assms by (auto simp: ns_mul_ext_def intro: mult2_alt_ns_ns_add)

lemma s_ns_mul_ext_union_compat:
  assumes "(A,B) \<in> s_mul_ext ns s"
    and "(C,D) \<in> ns_mul_ext ns s"
  shows "(A + C, B + D) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def ns_mul_ext_def intro: mult2_alt_s_ns_add)

lemma ns_ns_mul_ext_union_compat_rtrancl: assumes refl: "refl ns"
  and AB: "(A, B) \<in> (ns_mul_ext ns s)\<^sup>*"
  and CD: "(C, D) \<in> (ns_mul_ext ns s)\<^sup>*"
shows "(A + C, B + D) \<in> (ns_mul_ext ns s)\<^sup>*"
proof -
  {
    fix A B C
    assume "(A, B) \<in> (ns_mul_ext ns s)\<^sup>*"
    then have "(A + C, B + C) \<in> (ns_mul_ext ns s)\<^sup>*"
    proof (induct rule: rtrancl_induct)
      case (step B D)
      have "(C, C) \<in> ns_mul_ext ns s"
        by (rule ns_mul_ext_refl, insert refl, auto simp: locally_refl_def refl_on_def)
      from ns_ns_mul_ext_union_compat[OF step(2) this] step(3)
      show ?case by auto
    qed auto
  }
  from this[OF AB, of C] this[OF CD, of B]
  show ?thesis by (auto simp: ac_simps)
qed

subsection \<open>Multisets as order on lists\<close>

interpretation mul_ext_list: list_order_extension
  "\<lambda>s ns. {(as, bs). (mset as, mset bs) \<in> s_mul_ext ns s}"
  "\<lambda>s ns. {(as, bs). (mset as, mset bs) \<in> ns_mul_ext ns s}"
proof -
  let ?m = "mset :: ('a list \<Rightarrow> 'a multiset)"
  let ?S = "\<lambda>s ns. {(as, bs). (?m as, ?m bs) \<in> s_mul_ext ns s}"
  let ?NS = "\<lambda>s ns. {(as, bs). (?m as, ?m bs) \<in> ns_mul_ext ns s}"
  show "list_order_extension ?S ?NS"
  proof (rule list_order_extension.intro)
    fix s ns
    let ?s = "?S s ns"
    let ?ns = "?NS s ns"
    assume "SN_order_pair s ns"
    then interpret SN_order_pair s ns .
    interpret SN_order_pair "(s_mul_ext ns s)" "(ns_mul_ext ns s)"
      by (rule mul_ext_SN_order_pair)
    show "SN_order_pair ?s ?ns"
    proof
      show "refl ?ns" using refl_NS unfolding refl_on_def by blast
      show "?ns O ?s \<subseteq> ?s" using compat_NS_S by blast
      show "?s O ?ns \<subseteq> ?s" using compat_S_NS by blast
      show "trans ?ns" using trans_NS unfolding trans_def by blast
      show "trans ?s" using trans_S unfolding trans_def by blast
      show "SN ?s" using SN_inv_image[OF SN, of ?m, unfolded inv_image_def] .
    qed
  next
    fix S f NS as bs
    assume "\<And>a b. (a, b) \<in> S \<Longrightarrow> (f a, f b) \<in> S"
      "\<And>a b. (a, b) \<in> NS \<Longrightarrow> (f a, f b) \<in> NS"
      "(as, bs) \<in> ?S S NS"
    then show "(map f as, map f bs) \<in> ?S S NS"
      using mult2_alt_map[of _ _ "NS\<inverse>" f f "NS\<inverse>" "S\<inverse>" "S\<inverse>"] by (auto simp: mset_map s_mul_ext_def)
  next
    fix S f NS as bs
    assume "\<And>a b. (a, b) \<in> S \<Longrightarrow> (f a, f b) \<in> S"
      "\<And>a b. (a, b) \<in> NS \<Longrightarrow> (f a, f b) \<in> NS"
      "(as, bs) \<in> ?NS S NS"
    then show "(map f as, map f bs) \<in> ?NS S NS"
      using mult2_alt_map[of _ _ "NS\<inverse>" f f "NS\<inverse>" "S\<inverse>" "S\<inverse>"] by (auto simp: mset_map ns_mul_ext_def)
  next
    fix as bs :: "'a list" and NS S :: "'a rel"
    assume ass: "length as = length bs"
      "\<And>i. i < length bs \<Longrightarrow> (as ! i, bs ! i) \<in> NS"
    show "(as, bs) \<in> ?NS S NS"
      by (rule, unfold split, rule all_ns_ns_mul_ext, insert ass, auto)
  qed
qed

lemma s_mul_ext_singleton [simp, intro]:
  assumes "(a, b) \<in> s"
  shows "({#a#}, {#b#}) \<in> s_mul_ext ns s"
  using assms by (auto simp: s_mul_ext_def mult2_alt_s_single)

lemma ns_mul_ext_singleton [simp, intro]:
  "(a, b) \<in> ns \<Longrightarrow> ({#a#}, {#b#}) \<in> ns_mul_ext ns s"
  by (auto simp: ns_mul_ext_def multpw_converse intro: multpw_implies_mult2_alt_ns multpw_single)

lemma ns_mul_ext_singleton2:
  "(a, b) \<in> s \<Longrightarrow> ({#a#}, {#b#}) \<in> ns_mul_ext ns s"
  by (intro s_ns_mul_ext s_mul_ext_singleton)

lemma s_mul_ext_self_extend_left:
  assumes "A \<noteq> {#}" and "locally_refl W B"
  shows "(A + B, B) \<in> s_mul_ext W S"
proof -
  have "(A + B, {#} + B) \<in> s_mul_ext W S"
    using assms by (intro s_mul_ext_union_compat) (auto dest: s_mul_ext_bottom)
  then show ?thesis by simp
qed

lemma s_mul_ext_ne_extend_left:
  assumes "A \<noteq> {#}" and "(B, C) \<in> ns_mul_ext W S"
  shows "(A + B, C) \<in> s_mul_ext W S"
  using assms
proof -
  have "(A + B, {#} + C) \<in> s_mul_ext W S"
    using assms by (intro s_ns_mul_ext_union_compat)
      (auto simp: s_mul_ext_bottom dest: s_ns_mul_ext)
  then show ?thesis by (simp add: ac_simps)
qed

lemma s_mul_ext_extend_left:
  assumes "(B, C) \<in> s_mul_ext W S"
  shows "(A + B, C) \<in> s_mul_ext W S"
  using assms
proof -
  have "(B + A, C + {#}) \<in> s_mul_ext W S"
    using assms by (intro s_ns_mul_ext_union_compat)
      (auto simp: ns_mul_ext_bottom dest: s_ns_mul_ext)
  then show ?thesis by (simp add: ac_simps)
qed

lemma mul_ext_mono:
  assumes "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set ys; fst (P x y)\<rbrakk> \<Longrightarrow> fst (P' x y)"
    and   "\<And>x y. \<lbrakk>x \<in> set xs; y \<in> set ys; snd (P x y)\<rbrakk> \<Longrightarrow> snd (P' x y)"
  shows
    "fst (mul_ext P xs ys) \<Longrightarrow> fst (mul_ext P' xs ys)" 
    "snd (mul_ext P xs ys) \<Longrightarrow> snd (mul_ext P' xs ys)"
  unfolding mul_ext_def Let_def fst_conv snd_conv
proof - 
  assume mem: "(mset xs, mset ys) \<in> s_mul_ext {(x, y). snd (P x y)} {(x, y). fst (P x y)}" 
  show "(mset xs, mset ys) \<in> s_mul_ext {(x, y). snd (P' x y)} {(x, y). fst (P' x y)}" 
    by (rule s_mul_ext_local_mono[OF _ _ mem], insert assms, auto)
next
  assume mem: "(mset xs, mset ys) \<in> ns_mul_ext {(x, y). snd (P x y)} {(x, y). fst (P x y)}" 
  show "(mset xs, mset ys) \<in> ns_mul_ext {(x, y). snd (P' x y)} {(x, y). fst (P' x y)}" 
    by (rule ns_mul_ext_local_mono[OF _ _ mem], insert assms, auto)
qed



subsection \<open>Special case: non-strict order is equality\<close>

lemma ns_mul_ext_IdE:
  assumes "(M, N) \<in> ns_mul_ext Id R"
  obtains X and Y and Z where "M = X + Z" and "N = Y + Z"
    and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  using assms
  by (auto simp: ns_mul_ext_def elim!: mult2_alt_nsE) (insert union_commute, blast)

lemma ns_mul_ext_IdI:
  assumes "M = X + Z" and "N = Y + Z" and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  shows "(M, N) \<in> ns_mul_ext Id R"
  using assms mult2_alt_nsI[of N Z Y M Z X Id "R\<inverse>"]
  by (auto simp: ns_mul_ext_def)

lemma s_mul_ext_IdE:
  assumes "(M, N) \<in> s_mul_ext Id R"
  obtains X and Y and Z where "X \<noteq> {#}" and "M = X + Z" and "N = Y + Z"
    and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  using assms
  by (auto simp: s_mul_ext_def elim!: mult2_alt_sE) (metis union_commute)

lemma s_mul_ext_IdI:
  assumes "X \<noteq> {#}" and "M = X + Z" and "N = Y + Z"
    and "\<forall>y \<in> set_mset Y. \<exists>x \<in> set_mset X. (x, y) \<in> R"
  shows "(M, N) \<in> s_mul_ext Id R"
  using assms mult2_alt_sI[of N Z Y M Z X Id "R\<inverse>"]
  by (auto simp: s_mul_ext_def ac_simps)

lemma mult_s_mul_ext_conv:
  assumes "trans R"
  shows "(mult (R\<inverse>))\<inverse> = s_mul_ext Id R"
  using mult2_s_eq_mult2_s_alt[of Id "R\<inverse>"] assms
  by (auto simp: s_mul_ext_def refl_Id mult2_s_def)

lemma ns_mul_ext_Id_eq:
  "ns_mul_ext Id R = (s_mul_ext Id R)\<^sup>="
  by (auto simp add: ns_mul_ext_def s_mul_ext_def mult2_alt_ns_conv)

lemma subseteq_mset_imp_ns_mul_ext_Id:
  assumes "A \<subseteq># B"
  shows "(B, A) \<in> ns_mul_ext Id R"
proof -
  obtain C where [simp]: "B = C + A" using assms by (auto simp: mset_subset_eq_exists_conv ac_simps)
  have "(C + A, {#} + A) \<in> ns_mul_ext Id R"
    by (intro ns_mul_ext_IdI [of _ C A _ "{#}"]) auto
  then show ?thesis by simp
qed

lemma subset_mset_imp_s_mul_ext_Id:
  assumes "A \<subset># B"
  shows "(B, A) \<in> s_mul_ext Id R"
  using assms by (intro supset_imp_s_mul_ext) (auto simp: refl_Id)


end
