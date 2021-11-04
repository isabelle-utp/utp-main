(*<*)
theory Trace
  imports "HOL-Library.Stream"
begin
(*>*)

section \<open>Traces and trace prefixes\<close>

subsection \<open>Infinite traces\<close>

coinductive ssorted :: "'a :: linorder stream \<Rightarrow> bool" where
  "shd s \<le> shd (stl s) \<Longrightarrow> ssorted (stl s) \<Longrightarrow> ssorted s"

lemma ssorted_siterate[simp]: "(\<And>n. n \<le> f n) \<Longrightarrow> ssorted (siterate f n)"
  by (coinduction arbitrary: n) auto

lemma ssortedD: "ssorted s \<Longrightarrow> s !! i \<le> stl s !! i"
  by (induct i arbitrary: s) (auto elim: ssorted.cases)

lemma ssorted_sdrop: "ssorted s \<Longrightarrow> ssorted (sdrop i s)"
  by (coinduction arbitrary: i s) (auto elim: ssorted.cases ssortedD)

lemma ssorted_monoD: "ssorted s \<Longrightarrow> i \<le> j \<Longrightarrow> s !! i \<le> s !! j"
proof (induct "j - i" arbitrary: j)
  case (Suc x)
  from Suc(1)[of "j - 1"] Suc(2-4) ssortedD[of s "j - 1"]
    show ?case by (cases j) (auto simp: le_Suc_eq Suc_diff_le)
qed simp

lemma sorted_stake: "ssorted s \<Longrightarrow> sorted (stake i s)"
  by (induct i arbitrary: s)
    (auto elim: ssorted.cases simp: in_set_conv_nth
      intro!: ssorted_monoD[of _ 0, simplified, THEN order_trans, OF _ ssortedD])

lemma ssorted_monoI: "\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j \<Longrightarrow> ssorted s"
  by (coinduction arbitrary: s)
    (auto dest: spec2[of _ "Suc _" "Suc _"] spec2[of _ 0 "Suc 0"])

lemma ssorted_iff_mono: "ssorted s \<longleftrightarrow> (\<forall>i j. i \<le> j \<longrightarrow> s !! i \<le> s !! j)"
  using ssorted_monoI ssorted_monoD by metis

lemma ssorted_iff_le_Suc: "ssorted s \<longleftrightarrow> (\<forall>i. s !! i \<le> s !! Suc i)"
  using mono_iff_le_Suc[of "snth s"] by (simp add: mono_def ssorted_iff_mono)

definition "sincreasing s = (\<forall>x. \<exists>i. x < s !! i)"

lemma sincreasingI: "(\<And>x. \<exists>i. x < s !! i) \<Longrightarrow> sincreasing s"
  by (simp add: sincreasing_def)

lemma sincreasing_grD:
  fixes x :: "'a :: semilattice_sup"
  assumes "sincreasing s"
  shows "\<exists>j>i. x < s !! j"
proof -
  let ?A = "insert x {s !! n | n. n \<le> i}"
  from assms obtain j where *: "Sup_fin ?A < s !! j"
    by (auto simp: sincreasing_def)
  then have "x < s !! j"
    by (rule order.strict_trans1[rotated]) (auto intro: Sup_fin.coboundedI)
  moreover have "i < j"
  proof (rule ccontr)
    assume "\<not> i < j"
    then have "s !! j \<in> ?A" by (auto simp: not_less)
    then have "s !! j \<le> Sup_fin ?A"
      by (auto intro: Sup_fin.coboundedI)
    with * show False by simp
  qed
  ultimately show ?thesis by blast
qed

lemma sincreasing_siterate_nat[simp]:
  fixes n :: nat
  assumes "(\<And>n. n < f n)"
  shows "sincreasing (siterate f n)"
unfolding sincreasing_def proof
  fix x
  show "\<exists>i. x < siterate f n !! i"
  proof (induction x)
    case 0
    have "0 < siterate f n !! 1"
      using order.strict_trans1[OF le0 assms] by simp
    then show ?case ..
  next
    case (Suc x)
    then obtain i where "x < siterate f n !! i" ..
    then have "Suc x < siterate f n !! Suc i"
      using order.strict_trans1[OF _ assms] by (simp del: snth.simps)
    then show ?case ..
  qed
qed

lemma sincreasing_stl: "sincreasing s \<Longrightarrow> sincreasing (stl s)" for s :: "'a :: semilattice_sup stream"
  by (auto 0 4 simp: gr0_conv_Suc intro!: sincreasingI dest: sincreasing_grD[of s 0])

typedef 'a trace = "{s :: ('a set \<times> nat) stream. ssorted (smap snd s) \<and> sincreasing (smap snd s)}"
  by (intro exI[of _ "smap (\<lambda>i. ({}, i)) nats"])
    (auto simp: stream.map_comp stream.map_ident cong: stream.map_cong)

setup_lifting type_definition_trace

lift_definition \<Gamma> :: "'a trace \<Rightarrow> nat \<Rightarrow> 'a set" is
  "\<lambda>s i. fst (s !! i)" .
lift_definition \<tau> :: "'a trace \<Rightarrow> nat \<Rightarrow> nat" is
  "\<lambda>s i. snd (s !! i)" .

lemma stream_eq_iff: "s = s' \<longleftrightarrow> (\<forall>n. s !! n = s' !! n)"
  by (metis stream.map_cong0 stream_smap_nats)

lemma trace_eqI: "(\<And>i. \<Gamma> \<sigma> i = \<Gamma> \<sigma>' i) \<Longrightarrow> (\<And>i. \<tau> \<sigma> i = \<tau> \<sigma>' i) \<Longrightarrow> \<sigma> = \<sigma>'"
  by transfer (auto simp: stream_eq_iff intro!: prod_eqI)

lemma \<tau>_mono[simp]: "i \<le> j \<Longrightarrow> \<tau> s i \<le> \<tau> s j"
  by transfer (auto simp: ssorted_iff_mono)

lemma ex_le_\<tau>: "\<exists>j\<ge>i. x \<le> \<tau> s j"
  by (transfer fixing: i x) (auto dest!: sincreasing_grD[of _ i x] less_imp_le)

lemma le_\<tau>_less: "\<tau> \<sigma> i \<le> \<tau> \<sigma> j \<Longrightarrow> j < i \<Longrightarrow> \<tau> \<sigma> i = \<tau> \<sigma> j"
  by (simp add: antisym)

lemma less_\<tau>D: "\<tau> \<sigma> i < \<tau> \<sigma> j \<Longrightarrow> i < j"
  by (meson \<tau>_mono less_le_not_le not_le_imp_less)

abbreviation "\<Delta> s i \<equiv> \<tau> s i - \<tau> s (i - 1)"

lift_definition map_\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a trace \<Rightarrow> 'b trace" is
  "\<lambda>f s. smap (\<lambda>(x, i). (f x, i)) s"
  by (auto simp: stream.map_comp prod.case_eq_if cong: stream.map_cong)

lemma \<Gamma>_map_\<Gamma>[simp]: "\<Gamma> (map_\<Gamma> f s) i = f (\<Gamma> s i)"
  by transfer (simp add: prod.case_eq_if)

lemma \<tau>_map_\<Gamma>[simp]: "\<tau> (map_\<Gamma> f s) i = \<tau> s i"
  by transfer (simp add: prod.case_eq_if)

lemma map_\<Gamma>_id[simp]: "map_\<Gamma> id s = s"
  by transfer (simp add: stream.map_id)

lemma map_\<Gamma>_comp: "map_\<Gamma> g (map_\<Gamma> f s) = map_\<Gamma> (g \<circ> f) s"
  by transfer (simp add: stream.map_comp comp_def prod.case_eq_if case_prod_beta')

lemma map_\<Gamma>_cong: "\<sigma>\<^sub>1 = \<sigma>\<^sub>2 \<Longrightarrow> (\<And>x. f\<^sub>1 x = f\<^sub>2 x) \<Longrightarrow> map_\<Gamma> f\<^sub>1 \<sigma>\<^sub>1 = map_\<Gamma> f\<^sub>2 \<sigma>\<^sub>2"
  by transfer (auto intro!: stream.map_cong)


subsection \<open>Finite trace prefixes\<close>

typedef 'a prefix = "{p :: ('a set \<times> nat) list. sorted (map snd p)}"
  by (auto intro!: exI[of _ "[]"])

setup_lifting type_definition_prefix

lift_definition pmap_\<Gamma> :: "('a set \<Rightarrow> 'b set) \<Rightarrow> 'a prefix \<Rightarrow> 'b prefix" is
  "\<lambda>f. map (\<lambda>(x, i). (f x, i))"
  by (simp add: split_beta comp_def)

lift_definition last_ts :: "'a prefix \<Rightarrow> nat" is
  "\<lambda>p. (case p of [] \<Rightarrow> 0 | _ \<Rightarrow> snd (last p))" .

lift_definition first_ts :: "nat \<Rightarrow> 'a prefix \<Rightarrow> nat" is
  "\<lambda>n p. (case p of [] \<Rightarrow> n | _ \<Rightarrow> snd (hd p))" .

lift_definition pnil :: "'a prefix" is "[]" by simp

lift_definition plen :: "'a prefix \<Rightarrow> nat" is "length" .

lift_definition psnoc :: "'a prefix \<Rightarrow> 'a set \<times> nat \<Rightarrow> 'a prefix" is
  "\<lambda>p x. if (case p of [] \<Rightarrow> 0 | _ \<Rightarrow> snd (last p)) \<le> snd x then p @ [x] else []"
proof (goal_cases sorted_psnoc)
  case (sorted_psnoc p x)
  then show ?case
    by (induction p) (auto split: if_splits list.splits)
qed

instantiation prefix :: (type) order begin

lift_definition less_eq_prefix :: "'a prefix \<Rightarrow> 'a prefix \<Rightarrow> bool" is
  "\<lambda>p q. \<exists>r. q = p @ r" .

definition less_prefix :: "'a prefix \<Rightarrow> 'a prefix \<Rightarrow> bool" where
  "less_prefix x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof (standard, goal_cases less refl trans antisym)
  case (less x y)
  then show ?case unfolding less_prefix_def ..
next
  case (refl x)
  then show ?case by transfer auto
next
  case (trans x y z)
  then show ?case by transfer auto
next
  case (antisym x y)
  then show ?case by transfer auto
qed

end

lemma psnoc_inject[simp]:
  "last_ts p \<le> snd x \<Longrightarrow> last_ts q \<le> snd y \<Longrightarrow> psnoc p x = psnoc q y \<longleftrightarrow> (p = q \<and> x = y)"
  by transfer auto

lift_definition prefix_of :: "'a prefix \<Rightarrow> 'a trace \<Rightarrow> bool" is "\<lambda>p s. stake (length p) s = p" .

lemma prefix_of_pnil[simp]: "prefix_of pnil \<sigma>"
  by transfer auto

lemma plen_pnil[simp]: "plen pnil = 0"
  by transfer auto

lemma prefix_of_pmap_\<Gamma>[simp]: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of (pmap_\<Gamma> f \<pi>) (map_\<Gamma> f \<sigma>)"
  by transfer auto

lemma plen_mono: "\<pi> \<le> \<pi>' \<Longrightarrow> plen \<pi> \<le> plen \<pi>'"
  by transfer auto

lemma prefix_of_psnocE: "prefix_of (psnoc p x) s \<Longrightarrow> last_ts p \<le> snd x \<Longrightarrow>
  (prefix_of p s \<Longrightarrow> \<Gamma> s (plen p) = fst x \<Longrightarrow> \<tau> s (plen p) = snd x \<Longrightarrow> P) \<Longrightarrow> P"
  by transfer (simp del: stake.simps add: stake_Suc)

lemma le_pnil[simp]: "pnil \<le> \<pi>"
  by transfer auto

lift_definition take_prefix :: "nat \<Rightarrow> 'a trace \<Rightarrow> 'a prefix" is stake
  by (auto dest: sorted_stake)

lemma plen_take_prefix[simp]: "plen (take_prefix i \<sigma>) = i"
  by transfer auto

lemma plen_psnoc[simp]: "last_ts \<pi> \<le> snd x \<Longrightarrow> plen (psnoc \<pi> x) = plen \<pi> + 1"
  by transfer auto

lemma prefix_of_take_prefix[simp]: "prefix_of (take_prefix i \<sigma>) \<sigma>"
  by transfer auto

lift_definition pdrop :: "nat \<Rightarrow> 'a prefix \<Rightarrow> 'a prefix" is drop
  by (auto simp: drop_map[symmetric] sorted_drop)

lemma pdrop_0[simp]: "pdrop 0 \<pi> = \<pi>"
  by transfer auto

lemma prefix_of_antimono: "\<pi> \<le> \<pi>' \<Longrightarrow> prefix_of \<pi>' s \<Longrightarrow> prefix_of \<pi> s"
  by transfer (auto simp del: stake_add simp add: stake_add[symmetric])

lemma prefix_of_imp_linear: "prefix_of \<pi> \<sigma> \<Longrightarrow> prefix_of \<pi>' \<sigma> \<Longrightarrow> \<pi> \<le> \<pi>' \<or> \<pi>' \<le> \<pi>"
proof transfer
  fix \<pi> \<pi>' and \<sigma> :: "('a set \<times> nat) stream"
  assume assms: "stake (length \<pi>) \<sigma> = \<pi>" "stake (length \<pi>') \<sigma> = \<pi>'"
  show "(\<exists>r. \<pi>' = \<pi> @ r) \<or> (\<exists>r. \<pi> = \<pi>' @ r)"
  proof (cases "length \<pi>" "length \<pi>'" rule: le_cases)
    case le
    then have "\<pi>' = take (length \<pi>) \<pi>' @ drop (length \<pi>) \<pi>'"
      by simp
    moreover have "take (length \<pi>) \<pi>' = \<pi>"
      using assms le by (metis min.absorb1 take_stake)
    ultimately show ?thesis by auto
  next
    case ge
    then have "\<pi> = take (length \<pi>') \<pi> @ drop (length \<pi>') \<pi>"
      by simp
    moreover have "take (length \<pi>') \<pi> = \<pi>'"
      using assms ge by (metis min.absorb1 take_stake)
    ultimately show ?thesis by auto
  qed
qed

lemma ex_prefix_of: "\<exists>s. prefix_of p s"
proof (transfer, intro bexI CollectI conjI)
  fix p :: "('a set \<times> nat) list"
  assume *: "sorted (map snd p)"
  let ?\<sigma> = "p @- smap (Pair undefined) (fromN (snd (last p)))"
  show "stake (length p) ?\<sigma> = p" by (simp add: stake_shift)
  have le_last: "snd (p ! i) \<le> snd (last p)" if "i < length p" for i
    using sorted_nth_mono[OF *, of i "length p - 1"] that
    by (cases p) (auto simp: last_conv_nth nth_Cons')
  with * show "ssorted (smap snd ?\<sigma>)"
    by (force simp: ssorted_iff_mono sorted_iff_nth_mono shift_snth)
  show "sincreasing (smap snd ?\<sigma>)"
  proof (rule sincreasingI)
    fix x
    have "x < smap snd ?\<sigma> !! Suc (length p + x)"
      by simp (metis Suc_pred add.commute diff_Suc_Suc length_greater_0_conv less_add_Suc1 less_diff_conv)
    then show "\<exists>i. x < smap snd ?\<sigma> !! i" ..
  qed
qed

lemma \<tau>_prefix_conv: "prefix_of p s \<Longrightarrow> prefix_of p s' \<Longrightarrow> i < plen p \<Longrightarrow> \<tau> s i = \<tau> s' i"
  by transfer (simp add: stake_nth[symmetric])

lemma \<Gamma>_prefix_conv: "prefix_of p s \<Longrightarrow> prefix_of p s' \<Longrightarrow> i < plen p \<Longrightarrow> \<Gamma> s i = \<Gamma> s' i"
  by transfer (simp add: stake_nth[symmetric])

lemma sincreasing_sdrop:
  fixes s :: "('a :: semilattice_sup) stream"
  assumes "sincreasing s"
  shows "sincreasing (sdrop n s)"
proof (rule sincreasingI)
  fix x
  obtain i where "n < i" and "x < s !! i"
    using sincreasing_grD[OF assms] by blast
  then have "x < sdrop n s !! (i - n)"
    by (simp add: sdrop_snth)
  then show "\<exists>i. x < sdrop n s !! i" ..
qed

lemma ssorted_shift:
  "ssorted (xs @- s) = (sorted xs \<and> ssorted s \<and> (\<forall>x\<in>set xs. \<forall>y\<in>sset s. x \<le> y))"
proof safe
  assume *: "ssorted (xs @- s)"
  then show "sorted xs"
    by (auto simp: ssorted_iff_mono shift_snth sorted_iff_nth_mono split: if_splits)
  from ssorted_sdrop[OF *, of "length xs"] show "ssorted s"
    by (auto simp: sdrop_shift)
  fix x y assume "x \<in> set xs" "y \<in> sset s"
  then obtain i j where "i < length xs" "xs ! i = x" "s !! j = y"
    by (auto simp: set_conv_nth sset_range)
  with ssorted_monoD[OF *, of i "j + length xs"] show "x \<le> y" by auto
next
  assume "sorted xs" "ssorted s" "\<forall>x\<in>set xs. \<forall>y\<in>sset s. x \<le> y"
  then show "ssorted (xs @- s)"
  proof (coinduction arbitrary: xs s)
    case (ssorted xs s)
    with \<open>ssorted s\<close> show ?case
      by (subst (asm) ssorted.simps) (auto 0 4 simp: neq_Nil_conv shd_sset intro: exI[of _ "_ # _"])
  qed
qed

lemma sincreasing_shift:
  assumes "sincreasing s"
  shows "sincreasing (xs @- s)"
proof (rule sincreasingI)
  fix x
  from assms obtain i where "x < s !! i"
    unfolding sincreasing_def by blast
  then have "x < (xs @- s) !! (length xs + i)"
    by simp
  then show "\<exists>i. x < (xs @- s) !! i" ..
qed

lift_definition replace_prefix :: "'a prefix \<Rightarrow> 'a trace \<Rightarrow> 'a trace" is
   "\<lambda>\<pi> \<sigma>. if ssorted (smap snd (\<pi> @- sdrop (length \<pi>) \<sigma>)) then
     \<pi> @- sdrop (length \<pi>) \<sigma> else smap (\<lambda>i. ({}, i)) nats"
  by (auto split: if_splits simp: stream.map_comp stream.map_ident sdrop_smap[symmetric]
    simp del: sdrop_smap intro!: sincreasing_shift sincreasing_sdrop cong: stream.map_cong)

lemma prefix_of_replace_prefix:
  "prefix_of (pmap_\<Gamma> f \<pi>) \<sigma> \<Longrightarrow> prefix_of \<pi> (replace_prefix \<pi> \<sigma>)"
proof (transfer; safe; goal_cases)
  case (1 f \<pi> \<sigma>)
  then show ?case
    by (subst (asm) (2) stake_sdrop[symmetric, of _ "length \<pi>"])
      (auto 0 3 simp: ssorted_shift split_beta o_def stake_shift sdrop_smap[symmetric]
        ssorted_sdrop not_le simp del: sdrop_smap)
qed

lemma map_\<Gamma>_replace_prefix:
  "\<forall>x. f (f x) = f x \<Longrightarrow> prefix_of (pmap_\<Gamma> f \<pi>) \<sigma> \<Longrightarrow> map_\<Gamma> f (replace_prefix \<pi> \<sigma>) = map_\<Gamma> f \<sigma>"
proof (transfer; safe; goal_cases)
  case (1 f \<pi> \<sigma>)
  then show ?case
    by (subst (asm) (2) stake_sdrop[symmetric, of \<sigma> "length \<pi>"],
        subst (3) stake_sdrop[symmetric, of \<sigma> "length \<pi>"])
      (auto simp: ssorted_shift split_beta o_def stake_shift sdrop_smap[symmetric] ssorted_sdrop
        not_le simp del: sdrop_smap cong: map_cong)
qed

lemma prefix_of_pmap_\<Gamma>_D:
  assumes "prefix_of (pmap_\<Gamma> f \<pi>) \<sigma>"
  shows "\<exists>\<sigma>'. prefix_of \<pi> \<sigma>' \<and> prefix_of (pmap_\<Gamma> f \<pi>) (map_\<Gamma> f \<sigma>')"
proof -
  from assms(1) obtain \<sigma>' where 1: "prefix_of \<pi> \<sigma>'"
    using ex_prefix_of by blast
  then have "prefix_of (pmap_\<Gamma> f \<pi>) (map_\<Gamma> f \<sigma>')"
    by transfer simp
  with 1 show ?thesis by blast
qed

lemma prefix_of_map_\<Gamma>_D:
  assumes "prefix_of \<pi>' (map_\<Gamma> f \<sigma>)"
  shows "\<exists>\<pi>''. \<pi>' = pmap_\<Gamma> f \<pi>'' \<and> prefix_of \<pi>'' \<sigma>"
  using assms
  by transfer (auto intro!: exI[of _ "stake (length _) _"] elim: sym dest: sorted_stake)

lift_definition pts :: "'a prefix \<Rightarrow> nat list" is "map snd" .

lemma pts_pmap_\<Gamma>[simp]: "pts (pmap_\<Gamma> f \<pi>) = pts \<pi>"
  by (transfer fixing: f) (simp add: split_beta)

(*<*)
end
(*>*)
