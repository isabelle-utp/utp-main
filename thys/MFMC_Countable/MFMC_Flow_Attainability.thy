theory MFMC_Flow_Attainability imports
  MFMC_Network
begin

section \<open>Attainability of flows in networks\<close>

subsection \<open>Cleaning up flows\<close>

text \<open>If there is a flow along antiparallel edges, it suffices to consider the difference.\<close>

definition cleanup :: "'a flow \<Rightarrow> 'a flow"
where "cleanup f = (\<lambda>(a, b). if f (a, b) > f (b, a) then f (a, b) - f (b, a) else 0)"

lemma cleanup_simps [simp]:
  "cleanup f (a, b) = (if f (a, b) > f (b, a) then f (a, b) - f (b, a) else 0)"
by(simp add: cleanup_def)

lemma value_flow_cleanup:
  assumes [simp]: "\<And>x. f (x, source \<Delta>) = 0"
  shows "value_flow \<Delta> (cleanup f) = value_flow \<Delta> f"
unfolding d_OUT_def
by (auto simp add: not_less intro!: nn_integral_cong intro: antisym)

lemma KIR_cleanup:
  assumes KIR: "KIR f x"
  and finite_IN: "d_IN f x \<noteq> \<top>"
  shows "KIR (cleanup f) x"
proof -
  from finite_IN KIR have finite_OUT: "d_OUT f x \<noteq> \<top>" by simp

  have finite_IN: "(\<Sum>\<^sup>+ y\<in>A. f (y, x)) \<noteq> \<top>" for A
    using finite_IN by(rule neq_top_trans)(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
  have finite_OUT: "(\<Sum>\<^sup>+ y\<in>A. f (x, y)) \<noteq> \<top>" for A
    using finite_OUT by(rule neq_top_trans)(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
  have finite_in: "f (x, y) \<noteq> \<top>" for y using \<open>d_OUT f x \<noteq> \<top>\<close>
    by(rule neq_top_trans) (rule d_OUT_ge_point)

  let ?M = "{y. f (x, y) > f (y, x)}"

  have "d_OUT (cleanup f) x = (\<Sum>\<^sup>+ y\<in>?M. f (x, y) - f (y, x))"
    by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?M. f (x, y)) - (\<Sum>\<^sup>+ y\<in>?M. f (y, x))" using finite_IN
    by(subst nn_integral_diff)(auto simp add: AE_count_space)
  also have "\<dots> = (d_OUT f x - (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (x, y))) - (\<Sum>\<^sup>+ y\<in>?M. f (y, x))"
    unfolding d_OUT_def d_IN_def using finite_IN finite_OUT
    apply(simp add: nn_integral_count_space_indicator)
    apply(subst (2) nn_integral_diff[symmetric])
    apply(auto simp add: AE_count_space finite_in split: split_indicator intro!: arg_cong2[where f="(-)"] intro!: nn_integral_cong)
    done
  also have "\<dots> = (d_IN f x - (\<Sum>\<^sup>+ y\<in>?M. f (y, x))) - (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (x, y))"
    using KIR by(simp add: diff_diff_commute_ennreal)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (y, x)) - (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (x, y))"
    using finite_IN finite_IN[of "{ _ }"]
    apply(simp add: d_IN_def nn_integral_count_space_indicator)
    apply(subst nn_integral_diff[symmetric])
    apply(auto simp add: d_IN_def AE_count_space split: split_indicator intro!: arg_cong2[where f="(-)"] intro!: nn_integral_cong)
    done
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (y, x) - f (x, y))" using finite_OUT
    by(subst nn_integral_diff)(auto simp add: AE_count_space)
  also have "\<dots> = d_IN (cleanup f) x" using finite_in
    by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: ennreal_diff_self nn_integral_cong split: split_indicator)
  finally show "KIR (cleanup f) x" .
qed

locale flow_attainability = countable_network \<Delta>
  for \<Delta> :: "('v, 'more) network_scheme" (structure)
  +
  assumes finite_capacity: "\<And>x. x \<noteq> sink \<Delta> \<Longrightarrow> d_IN (capacity \<Delta>) x \<noteq> \<top> \<or> d_OUT (capacity \<Delta>) x \<noteq> \<top>"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
begin

lemma source_in_not_cycle:
  assumes "cycle \<Delta> p"
  shows "(x, source \<Delta>) \<notin> set (cycle_edges p)"
using cycle_edges_edges[OF assms] source_in[of x] by(auto)

lemma source_out_not_cycle:
  "cycle \<Delta> p \<Longrightarrow> (source \<Delta>, x) \<notin> set (cycle_edges p)"
by(auto dest: cycle_leave_ex_enter source_in_not_cycle)

lemma flowD_source_IN:
  assumes "flow \<Delta> f"
  shows "d_IN f (source \<Delta>) = 0"
proof -
  have "d_IN f (source \<Delta>) = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N (source \<Delta>). f (y, source \<Delta>))"
    by(rule d_IN_alt_def)(simp add: flowD_outside[OF assms])
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N (source \<Delta>). 0)"
    by(rule nn_integral_cong)(simp add: source_in incoming_def)
  finally show ?thesis by simp
qed

lemma flowD_finite_IN:
  assumes f: "flow \<Delta> f" and x: "x \<noteq> sink \<Delta>"
  shows "d_IN f x \<noteq> top"
proof(cases "x = source \<Delta>")
  case True thus ?thesis by(simp add: flowD_source_IN[OF f])
next
  case False
  from finite_capacity[OF x] show ?thesis
  proof
    assume *: "d_IN (capacity \<Delta>) x \<noteq> \<top>"
    from flowD_capacity[OF f] have "d_IN f x \<le> d_IN (capacity \<Delta>) x" by(rule d_IN_mono)
    also have "\<dots> < \<top>" using * by (simp add: less_top)
    finally show ?thesis by simp
  next
    assume *: "d_OUT (capacity \<Delta>) x \<noteq> \<top>"
    have "d_IN f x = d_OUT f x" using flowD_KIR[OF f False x] by simp
    also have "\<dots> \<le> d_OUT (capacity \<Delta>) x" using flowD_capacity[OF f] by(rule d_OUT_mono)
    also have "\<dots> < \<top>" using * by (simp add: less_top)
    finally show ?thesis by simp
  qed
qed

lemma flowD_finite_OUT:
  assumes "flow \<Delta> f" "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  shows "d_OUT f x \<noteq> \<top>"
using flowD_KIR[OF assms] assms by(simp add: flowD_finite_IN)

end

locale flow_network = flow_attainability
  +
  fixes g :: "'v flow"
  assumes g: "flow \<Delta> g"
  and g_finite: "value_flow \<Delta> g \<noteq> \<top>"
  and nontrivial: "\<^bold>V - {source \<Delta>, sink \<Delta>} \<noteq> {}"
begin

lemma g_outside: "e \<notin> \<^bold>E \<Longrightarrow> g e = 0"
by(rule flowD_outside)(rule g)

lemma g_loop [simp]: "g (x, x) = 0"
by(rule g_outside)(simp add: no_loop)

lemma finite_IN_g: "x \<noteq> sink \<Delta> \<Longrightarrow> d_IN g x \<noteq> top"
by(rule flowD_finite_IN[OF g])

lemma finite_OUT_g:
  assumes "x \<noteq> sink \<Delta>"
  shows "d_OUT g x \<noteq> top"
proof(cases "x = source \<Delta>")
  case True
  with g_finite show ?thesis by simp
next
  case False
  with g have "KIR g x" using assms by(auto dest: flowD_KIR)
  with finite_IN_g[of x] False assms show ?thesis by(simp)
qed

lemma g_source_in [simp]: "g (x, source \<Delta>) = 0"
by(rule g_outside)(simp add: source_in)

lemma finite_g [simp]: "g e \<noteq> top"
  by(rule flowD_finite[OF g])


definition enum_v :: "nat \<Rightarrow> 'v"
where "enum_v n = from_nat_into (\<^bold>V - {source \<Delta>, sink \<Delta>}) (fst (prod_decode n))"

lemma range_enum_v: "range enum_v \<subseteq> \<^bold>V - {source \<Delta>, sink \<Delta>}"
using from_nat_into[OF nontrivial] by(auto simp add: enum_v_def)

lemma enum_v_repeat:
  assumes x: "x \<in> \<^bold>V" "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  shows "\<exists>i'>i. enum_v i' = x"
proof -
  let ?V = "\<^bold>V - {source \<Delta>, sink \<Delta>}"
  let ?n = "to_nat_on ?V x"
  let ?A = "{?n} \<times> (UNIV :: nat set)"
  from x have x': "x \<in> \<^bold>V - {source \<Delta>, sink \<Delta>}" by simp
  have "infinite ?A" by(auto dest: finite_cartesian_productD2)
  hence "infinite (prod_encode ` ?A)" by(auto dest: finite_imageD simp add: inj_prod_encode)
  then obtain i' where "i' > i" "i' \<in> prod_encode ` ?A"
    unfolding infinite_nat_iff_unbounded by blast
  from this(2) have "enum_v i' = x" using x by(clarsimp simp add: enum_v_def)
  with \<open>i' > i\<close> show ?thesis by blast
qed

fun h_plus :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where
  "h_plus 0 (x, y) = (if x = source \<Delta> then g (x, y) else 0)"
| "h_plus (Suc i) (x, y) =
  (if enum_v (Suc i) = x \<and> d_OUT (h_plus i) x < d_IN (h_plus i) x then
   let total = d_IN (h_plus i) x - d_OUT (h_plus i) x;
       share = g (x, y) - h_plus i (x, y);
       shares = d_OUT g x - d_OUT (h_plus i) x
   in h_plus i (x, y) + share * total / shares
   else h_plus i (x, y))"


lemma h_plus_le_g: "h_plus i e \<le> g e"
proof(induction i arbitrary: e and e)
  case 0 thus ?case by(cases e) simp
next
  case (Suc i)
  { fix x y
    assume enum: "x = enum_v (Suc i)"
    assume less: "d_OUT (h_plus i) x < d_IN (h_plus i) x"
    from enum have x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using range_enum_v
      by(auto dest: sym intro: rev_image_eqI)

    define share where "share = g (x, y) - h_plus i (x, y)"
    define shares where "shares = d_OUT g x - d_OUT (h_plus i) x"
    define total where "total = d_IN (h_plus i) x - d_OUT (h_plus i) x"
    let ?h = "h_plus i (x, y) + share * total / shares"

    have "d_OUT (h_plus i) x \<le> d_OUT g x" by(rule d_OUT_mono)(rule Suc.IH)
    also have "\<dots> < top" using finite_OUT_g[of x] x by (simp add: less_top)
    finally have "d_OUT (h_plus i) x \<noteq> \<top>" by simp
    then have shares_eq: "shares = (\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y))" unfolding shares_def d_OUT_def
      by(subst nn_integral_diff)(simp_all add: AE_count_space Suc.IH)

    have *: "share / shares \<le> 1"
    proof (cases "share = 0")
      case True thus ?thesis by(simp)
    next
      case False
      hence "share > 0" using \<open>h_plus i (x, y) \<le> g _\<close>
        by(simp add: share_def dual_order.strict_iff_order)
      moreover have "share \<le> shares" unfolding share_def shares_eq by(rule nn_integral_ge_point)simp
      ultimately show ?thesis by(simp add: divide_le_posI_ennreal)
    qed

    note shares_def
    also have "d_OUT g x = d_IN g x" by(rule flowD_KIR[OF g x])
    also have "d_IN (h_plus i) x \<le> d_IN g x" by(rule d_IN_mono)(rule Suc.IH)
    ultimately have *: "total \<le> shares" unfolding total_def by(simp add: ennreal_minus_mono)
    moreover have "total > 0" unfolding total_def using less by (clarsimp simp add: diff_gr0_ennreal)
    ultimately have "total / shares \<le> 1" by(intro divide_le_posI_ennreal)(simp_all)
    hence "share * (total / shares) \<le> share * 1"
      by(rule mult_left_mono) simp
    hence "?h \<le> h_plus i (x, y) + share" by(simp add: ennreal_times_divide add_mono)
    also have "\<dots> = g (x, y)" unfolding share_def using \<open>h_plus i (x, y) \<le> g _\<close> finite_g[of "(x, y)"]
      by simp
    moreover
    note calculation }
  note * = this
  show ?case using Suc.IH * by(cases e) clarsimp
qed

lemma h_plus_outside: "e \<notin> \<^bold>E \<Longrightarrow> h_plus i e = 0"
by (metis g_outside h_plus_le_g le_zero_eq)

lemma h_plus_not_infty [simp]: "h_plus i e \<noteq> top"
using h_plus_le_g[of i e] by (auto simp: top_unique)

lemma h_plus_mono: "h_plus i e \<le> h_plus (Suc i) e"
proof(cases e)
  case [simp]: (Pair x y)
  { assume "d_OUT (h_plus i) x < d_IN (h_plus i) x"
    hence "h_plus i (x, y) + 0 \<le> h_plus i (x, y) + (g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)"
      by(intro add_left_mono d_OUT_mono le_funI) (simp_all add: h_plus_le_g) }
  then show ?thesis by clarsimp
qed

lemma h_plus_mono': "i \<le> j \<Longrightarrow> h_plus i e \<le> h_plus j e"
by(induction rule: dec_induct)(auto intro: h_plus_mono order_trans)

lemma d_OUT_h_plus_not_infty': "x \<noteq> sink \<Delta> \<Longrightarrow> d_OUT (h_plus i) x \<noteq> top"
using d_OUT_mono[of "h_plus i" x g, OF h_plus_le_g] finite_OUT_g[of x] by (auto simp: top_unique)

lemma h_plus_OUT_le_IN:
  assumes "x \<noteq> source \<Delta>"
  shows "d_OUT (h_plus i) x \<le> d_IN (h_plus i) x"
proof(induction i)
  case 0
  thus ?case using assms by(simp add: d_OUT_def)
next
  case (Suc i)
  have "d_OUT (h_plus (Suc i)) x \<le> d_IN (h_plus i) x"
  proof(cases "enum_v (Suc i) = x \<and> d_OUT (h_plus i) x < d_IN (h_plus i) x")
    case False
    thus ?thesis using Suc.IH by(simp add: d_OUT_def cong: conj_cong)
  next
    case True
    hence x: "x \<noteq> sink \<Delta>" and le: "d_OUT (h_plus i) x < d_IN (h_plus i) x" using range_enum_v by auto
    let ?r = "\<lambda>y. (g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)"
    have "d_OUT (h_plus (Suc i)) x = d_OUT (h_plus i) x + (\<Sum>\<^sup>+ y. ?r y)"
      using True unfolding d_OUT_def h_plus.simps by(simp add: AE_count_space nn_integral_add)
    also from True have "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using range_enum_v by auto
    from flowD_KIR[OF g this] le d_IN_mono[of "h_plus i" x g, OF h_plus_le_g]
    have le': "d_OUT (h_plus i) x < d_OUT g x" by(simp)
    then have "(\<Sum>\<^sup>+ y. ?r y) =
      (d_IN (h_plus i) x - d_OUT (h_plus i) x) * ((\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) / (d_OUT g x - d_OUT (h_plus i) x))"
      by(subst mult.commute, subst ennreal_times_divide[symmetric])
        (simp add: nn_integral_cmult nn_integral_divide Suc.IH diff_gr0_ennreal)
    also have "(\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) = d_OUT g x - d_OUT (h_plus i) x" using x
      by(subst nn_integral_diff)(simp_all add: d_OUT_def[symmetric] h_plus_le_g d_OUT_h_plus_not_infty')
    also have "\<dots> / \<dots> = 1" using le' finite_OUT_g[of x] x
      by(auto intro!: ennreal_divide_self dest: diff_gr0_ennreal simp: less_top[symmetric])
    also have "d_OUT (h_plus i) x + (d_IN (h_plus i) x - d_OUT (h_plus i) x) * 1 = d_IN (h_plus i) x" using x
      by (simp add: Suc)
    finally show ?thesis by simp
  qed
  also have "\<dots> \<le> d_IN (h_plus (Suc i)) x" by(rule d_IN_mono)(rule h_plus_mono)
  finally show ?case .
qed

lemma h_plus_OUT_eq_IN:
  assumes enum: "enum_v (Suc i) = x"
  shows "d_OUT (h_plus (Suc i)) x = d_IN (h_plus i) x"
proof(cases "d_OUT (h_plus i) x < d_IN (h_plus i) x")
  case False
  from enum have "x \<noteq> source \<Delta>" using range_enum_v by auto
  from h_plus_OUT_le_IN[OF this, of i] False have "d_OUT (h_plus i) x = d_IN (h_plus i) x" by auto
  with False enum show ?thesis by(simp add: d_OUT_def)
next
  case True
  from enum have x: "x \<noteq> source \<Delta>" and sink: "x \<noteq> sink \<Delta>" using range_enum_v by auto
  let ?r = "\<lambda>y. (g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)"
  have "d_OUT (h_plus (Suc i)) x = d_OUT (h_plus i) x + (\<Sum>\<^sup>+ y. ?r y)"
    using True enum unfolding d_OUT_def h_plus.simps by(simp add: AE_count_space nn_integral_add)
  also from True enum have "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using range_enum_v by auto
  from flowD_KIR[OF g this] True d_IN_mono[of "h_plus i" x g, OF h_plus_le_g]
  have le': "d_OUT (h_plus i) x < d_OUT g x" by(simp)
  then have "(\<Sum>\<^sup>+ y. ?r y ) =
    (d_IN (h_plus i) x - d_OUT (h_plus i) x) * ((\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) / (d_OUT g x - d_OUT (h_plus i) x))"
    by(subst mult.commute, subst ennreal_times_divide[symmetric])
      (simp add: nn_integral_cmult nn_integral_divide h_plus_OUT_le_IN[OF x] diff_gr0_ennreal)
  also have "(\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) = d_OUT g x - d_OUT (h_plus i) x" using sink
    by(subst nn_integral_diff)(simp_all add: d_OUT_def[symmetric] h_plus_le_g d_OUT_h_plus_not_infty')
  also have "\<dots> / \<dots> = 1" using le' finite_OUT_g[of x] sink
    by(auto intro!: ennreal_divide_self dest: diff_gr0_ennreal simp: less_top[symmetric])
  also have "d_OUT (h_plus i) x + (d_IN (h_plus i) x - d_OUT (h_plus i) x) * 1 = d_IN (h_plus i) x" using sink
    by (simp add: h_plus_OUT_le_IN x)
  finally show ?thesis .
qed

lemma h_plus_source_in [simp]: "h_plus i (x, source \<Delta>) = 0"
by(induction i)simp_all

lemma h_plus_sum_finite: "(\<Sum>\<^sup>+ e. h_plus i e) \<noteq> top"
proof(induction i)
  case 0
  have "(\<Sum>\<^sup>+ e\<in>UNIV. h_plus 0 e) = (\<Sum>\<^sup>+ (x, y). h_plus 0 (x, y))"
    by(simp del: h_plus.simps)
  also have "\<dots> = (\<Sum>\<^sup>+ (x, y)\<in>range (Pair (source \<Delta>)). h_plus 0 (x, y))"
    by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong)
  also have "\<dots> = value_flow \<Delta> g" by(simp add: d_OUT_def nn_integral_count_space_reindex)
  also have "\<dots> < \<top>" using g_finite by (simp add: less_top)
  finally show ?case by simp
next
  case (Suc i)
  define xi where "xi = enum_v (Suc i)"
  then have xi: "xi \<noteq> source \<Delta>" "xi \<noteq> sink \<Delta>" using range_enum_v by auto
  show ?case
  proof(cases "d_OUT (h_plus i) xi < d_IN (h_plus i) xi")
    case False
    hence "(\<Sum>\<^sup>+ e\<in>UNIV. h_plus (Suc i) e) = (\<Sum>\<^sup>+ e. h_plus i e)"
      by(auto intro!: nn_integral_cong simp add: xi_def)
    with Suc.IH show ?thesis by simp
  next
    case True
    have less: "d_OUT (h_plus i) xi < d_OUT g xi"
      using True flowD_KIR[OF g xi] d_IN_mono[of "h_plus i" xi, OF h_plus_le_g]
      by simp

    have "(\<Sum>\<^sup>+ e. h_plus (Suc i) e) =
      (\<Sum>\<^sup>+ e\<in>UNIV. h_plus i e) + (\<Sum>\<^sup>+ (x, y). ((g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)) * indicator (range (Pair xi)) (x, y))"
      (is "_ = ?IH + ?rest" is "_ = _ + \<integral>\<^sup>+ (x, y). ?f x y * _ \<partial>_") using xi True
      by(subst nn_integral_add[symmetric])(auto simp add: xi_def split_beta AE_count_space intro!: nn_integral_cong split: split_indicator intro!: h_plus_le_g h_plus_OUT_le_IN d_OUT_mono le_funI)
    also have "?rest = (\<Sum>\<^sup>+ (x, y)\<in>range (Pair xi). ?f x y)"
      by(simp add: nn_integral_count_space_indicator split_def)
    also have "\<dots> = (\<Sum>\<^sup>+ y. ?f xi y)" by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = (\<Sum>\<^sup>+ y. g (xi, y) - h_plus i (xi, y)) * ((d_IN (h_plus i) xi - d_OUT (h_plus i) xi) / (d_OUT g xi - d_OUT (h_plus i) xi))"
      (is "_ = ?integral * ?factor")  using True less
      by(simp add: nn_integral_multc nn_integral_divide diff_gr0_ennreal ennreal_times_divide)
    also have "?integral = d_OUT g xi - d_OUT (h_plus i) xi" unfolding d_OUT_def using xi
      by(subst nn_integral_diff)(simp_all add: h_plus_le_g d_OUT_def[symmetric] d_OUT_h_plus_not_infty')
    also have "\<dots> * ?factor = (d_IN (h_plus i) xi - d_OUT (h_plus i) xi)" using xi
      apply (subst ennreal_times_divide)
      apply (subst mult.commute)
      apply (subst ennreal_mult_divide_eq)
      apply (simp_all add: diff_gr0_ennreal finite_OUT_g less zero_less_iff_neq_zero[symmetric])
      done
    also have "\<dots> \<noteq> \<top>" using h_plus_OUT_eq_IN[OF refl, of i, folded xi_def, symmetric] xi
      by(simp add: d_OUT_h_plus_not_infty')
    ultimately show ?thesis using Suc.IH by simp
  qed
qed

lemma d_OUT_h_plus_not_infty [simp]: "d_OUT (h_plus i) x \<noteq> top"
proof -
  have "d_OUT (h_plus i) x \<le> (\<Sum>\<^sup>+ y\<in>UNIV. \<Sum>\<^sup>+ x. h_plus i (x, y))"
    unfolding d_OUT_def by(rule nn_integral_mono nn_integral_ge_point)+ simp
  also have "\<dots> < \<top>" using h_plus_sum_finite by(simp add: nn_integral_snd_count_space less_top)
  finally show ?thesis by simp
qed

definition enum_cycle :: "nat \<Rightarrow> 'v path"
where "enum_cycle = from_nat_into (cycles \<Delta>)"

lemma cycle_enum_cycle [simp]: "cycles \<Delta> \<noteq> {} \<Longrightarrow> cycle \<Delta> (enum_cycle n)"
unfolding enum_cycle_def using from_nat_into[of "cycles \<Delta>" n] by simp

context
  fixes h' :: "'v flow"
  assumes finite_h': "h' e \<noteq> top"
begin

fun h_minus_aux :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where
  "h_minus_aux 0 e = 0"
| "h_minus_aux (Suc j) e =
  (if e \<in> set (cycle_edges (enum_cycle j)) then
     h_minus_aux j e + Min {h' e' - h_minus_aux j e'|e'. e'\<in>set (cycle_edges (enum_cycle j))}
   else h_minus_aux j e)"

lemma h_minus_aux_le_h': "h_minus_aux j e \<le> h' e"
proof(induction j e rule: h_minus_aux.induct)
  case 0: (1 e) show ?case by simp
next
  case Suc: (2 j e)
  { assume e: "e \<in> set (cycle_edges (enum_cycle j))"
    then have "h_minus_aux j e + Min {h' e' - h_minus_aux j e' |e'. e' \<in> set (cycle_edges (enum_cycle j))} \<le>
      h_minus_aux j e + (h' e - h_minus_aux j e)"
      using [[simproc add: finite_Collect]] by(cases e rule: prod.exhaust)(auto intro!: add_mono Min_le)
    also have "\<dots> = h' e" using e finite_h'[of e] Suc.IH(2)[of e]
      by(cases e rule: prod.exhaust)
        (auto simp add: add_diff_eq_ennreal top_unique intro!: ennreal_add_diff_cancel_left)
    also note calculation }
  then show ?case using Suc by clarsimp
qed

lemma h_minus_aux_finite [simp]: "h_minus_aux j e \<noteq> top"
using h_minus_aux_le_h'[of j e] finite_h'[of e] by (auto simp: top_unique)

lemma h_minus_aux_mono: "h_minus_aux j e \<le> h_minus_aux (Suc j) e"
proof(cases "e \<in> set (cycle_edges (enum_cycle j)) = True")
  case True
  have "h_minus_aux j e + 0 \<le> h_minus_aux (Suc j) e" unfolding h_minus_aux.simps True if_True
    using True [[simproc add: finite_Collect]]
    by(cases e)(rule add_mono, auto intro!: Min.boundedI simp add: h_minus_aux_le_h')
  thus ?thesis by simp
qed simp

lemma d_OUT_h_minus_aux:
  assumes "cycles \<Delta> \<noteq> {}"
  shows "d_OUT (h_minus_aux j) x = d_IN (h_minus_aux j) x"
proof(induction j)
  case 0 show ?case by simp
next
  case (Suc j)
  define C where "C = enum_cycle j"
  define \<delta> where "\<delta> = Min {h' e' - h_minus_aux j e' |e'. e' \<in> set (cycle_edges C)}"

  have "d_OUT (h_minus_aux (Suc j)) x =
    (\<Sum>\<^sup>+ y. h_minus_aux j (x, y) + (if (x, y) \<in> set (cycle_edges C) then \<delta> else 0))"
    unfolding d_OUT_def by(simp add: if_distrib C_def \<delta>_def cong del: if_weak_cong)
  also have "\<dots> = d_OUT (h_minus_aux j) x + (\<Sum>\<^sup>+ y. \<delta> * indicator (set (cycle_edges C)) (x, y))"
    (is "_ = _ + ?add")
    by(subst nn_integral_add)(auto simp add: AE_count_space d_OUT_def intro!: arg_cong2[where f="(+)"] nn_integral_cong)
  also have "?add = (\<Sum>\<^sup>+ e\<in>range (Pair x). \<delta> * indicator {(x', y). (x', y) \<in> set (cycle_edges C) \<and> x' = x} e)"
    by(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = \<delta> * card (set (filter (\<lambda>(x', y). x' = x) (cycle_edges C)))"
    using [[simproc add: finite_Collect]]
    apply(subst nn_integral_cmult_indicator; auto)
    apply(subst emeasure_count_space; auto simp add: split_def)
    done
  also have "card (set (filter (\<lambda>(x', y). x' = x) (cycle_edges C))) = card (set (filter (\<lambda>(x', y). y = x) (cycle_edges C)))"
    unfolding C_def by(rule cycle_enter_leave_same)(rule cycle_enum_cycle[OF assms])
  also have "\<delta> * \<dots> =  (\<Sum>\<^sup>+ e\<in>range (\<lambda>x'. (x', x)). \<delta> * indicator {(x', y). (x', y) \<in> set (cycle_edges C) \<and> y = x} e)"
    using [[simproc add: finite_Collect]]
    apply(subst nn_integral_cmult_indicator; auto)
    apply(subst emeasure_count_space; auto simp add: split_def)
    done
  also have "\<dots> = (\<Sum>\<^sup>+ x'. \<delta> * indicator (set (cycle_edges C)) (x', x))"
    by(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
  also have "d_OUT (h_minus_aux j) x + \<dots> = (\<Sum>\<^sup>+ x'. h_minus_aux j (x', x) + \<delta> * indicator (set (cycle_edges C)) (x', x))"
    unfolding Suc.IH d_IN_def by(simp add: nn_integral_add[symmetric])
  also have "\<dots> = d_IN (h_minus_aux (Suc j)) x" unfolding d_IN_def
    by(auto intro!: nn_integral_cong simp add: \<delta>_def C_def split: split_indicator)
  finally show ?case .
qed

lemma h_minus_aux_source:
  assumes "cycles \<Delta> \<noteq> {}"
  shows "h_minus_aux j (source \<Delta>, y) = 0"
proof(induction j)
  case 0 thus ?case by simp
next
  case (Suc j)
  have "(source \<Delta>, y) \<notin> set (cycle_edges (enum_cycle j))"
  proof
    assume *: "(source \<Delta>, y) \<in> set (cycle_edges (enum_cycle j))"
    have cycle: "cycle \<Delta> (enum_cycle j)" using assms by(rule cycle_enum_cycle)
    from cycle_leave_ex_enter[OF this *]
    obtain z where "(z, source \<Delta>) \<in> set (cycle_edges (enum_cycle j))" ..
    with cycle_edges_edges[OF cycle] have "(z, source \<Delta>) \<in> \<^bold>E" ..
    thus False using source_in[of z] by simp
  qed
  then show ?case using Suc.IH by simp
qed

lemma h_minus_aux_cycle:
  fixes j defines "C \<equiv> enum_cycle j"
  assumes "cycles \<Delta> \<noteq> {}"
  shows "\<exists>e\<in>set (cycle_edges C). h_minus_aux (Suc j) e = h' e"
proof -
  let ?A = "{h' e' - h_minus_aux j e'|e'. e' \<in> set (cycle_edges C)}"
  from assms have "cycle \<Delta> C" by auto
  from cycle_edges_not_Nil[OF this] have "Min ?A \<in> ?A" using [[simproc add: finite_Collect]]
    by(intro Min_in)(fastforce simp add: neq_Nil_conv)+
  then obtain e' where e: "e' \<in> set (cycle_edges C)"
    and "Min ?A = h' e' - h_minus_aux j e'" by auto
  hence "h_minus_aux (Suc j) e' = h' e'"
    by(simp add: C_def h_minus_aux_le_h')
  with e show ?thesis by blast
qed

end

fun h_minus :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where
  "h_minus 0 e = 0"
| "h_minus (Suc i) e = h_minus i e + (SUP j. h_minus_aux (\<lambda>e'. h_plus (Suc i) e' - h_minus i e') j e)"

lemma h_minus_le_h_plus: "h_minus i e \<le> h_plus i e"
proof(induction i e rule: h_minus.induct)
  case 0: (1 e) show ?case by simp
next
  case Suc: (2 i e)
  note IH = Suc.IH(2)[OF UNIV_I]
  let ?h' = "\<lambda>e'. h_plus (Suc i) e' - h_minus i e'"
  have h': "?h' e' \<noteq> top" for e' using IH(1)[of e'] by(simp add: )

  have "(\<Squnion>j. h_minus_aux ?h' j e) \<le> ?h' e" by(rule SUP_least)(rule h_minus_aux_le_h'[OF h'])
  hence "h_minus (Suc i) e \<le> h_minus i e + \<dots>" by(simp add: add_mono)
  also have "\<dots> = h_plus (Suc i) e" using IH[of e] h_plus_mono[of i e]
    by auto
  finally show ?case .
qed

lemma finite_h': "h_plus (Suc i) e - h_minus i e \<noteq> top"
  by simp

lemma h_minus_mono: "h_minus i e \<le> h_minus (Suc i) e"
proof -
  have "h_minus i e + 0 \<le> h_minus (Suc i) e" unfolding h_minus.simps
    by(rule add_mono; simp add: SUP_upper2)
  thus ?thesis by simp
qed

lemma h_minus_finite [simp]: "h_minus i e \<noteq> \<top>"
proof -
  have "h_minus i e \<le> h_plus i e" by(rule h_minus_le_h_plus)
  also have "\<dots> < \<top>" by (simp add: less_top[symmetric])
  finally show ?thesis by simp
qed

lemma d_OUT_h_minus:
  assumes cycles: "cycles \<Delta> \<noteq> {}"
  shows "d_OUT (h_minus i) x = d_IN (h_minus i) x"
proof(induction i)
  case (Suc i)
  let ?h' = "\<lambda>e. h_plus (Suc i) e - h_minus i e"
  have "d_OUT (\<lambda>e. h_minus (Suc i) e) x = d_OUT (h_minus i) x + d_OUT (\<lambda>e. SUP j. h_minus_aux ?h' j e) x"
    by(simp add: d_OUT_add SUP_upper2)
  also have "d_OUT (\<lambda>e. SUP j. h_minus_aux ?h' j e) x = (SUP j. d_OUT (h_minus_aux ?h' j) x)"
    by(rule d_OUT_monotone_convergence_SUP incseq_SucI le_funI h_minus_aux_mono finite_h')+
  also have "\<dots> = (SUP j. d_IN (h_minus_aux ?h' j) x)"
    by(rule SUP_cong[OF refl])(rule d_OUT_h_minus_aux[OF finite_h' cycles])
  also have "\<dots> = d_IN (\<lambda>e. SUP j. h_minus_aux ?h' j e) x"
    by(rule d_IN_monotone_convergence_SUP[symmetric] incseq_SucI le_funI h_minus_aux_mono finite_h')+
  also have "d_OUT (h_minus i) x + \<dots> = d_IN (\<lambda>e. h_minus (Suc i) e) x" using Suc.IH
    by(simp add: d_IN_add SUP_upper2)
  finally show ?case .
qed simp

lemma h_minus_source:
  assumes "cycles \<Delta> \<noteq> {}"
  shows "h_minus n (source \<Delta>, y) = 0"
by(induction n)(simp_all add: h_minus_aux_source[OF finite_h' assms])

lemma h_minus_source_in [simp]: "h_minus i (x, source \<Delta>) = 0"
using h_minus_le_h_plus[of i "(x, source \<Delta>)"] by simp

lemma h_minus_OUT_finite [simp]: "d_OUT (h_minus i) x \<noteq> top"
proof -
  have "d_OUT (h_minus i) x \<le> d_OUT (h_plus i) x" by(rule d_OUT_mono)(rule h_minus_le_h_plus)
  also have "\<dots> < \<top>" by (simp add: less_top[symmetric])
  finally show ?thesis by simp
qed

lemma h_minus_cycle:
  assumes "cycle \<Delta> C"
  shows "\<exists>e\<in>set (cycle_edges C). h_minus i e = h_plus i e"
proof(cases i)
  case (Suc i)
  let ?h' = "\<lambda>e. h_plus (Suc i) e - h_minus i e"
  from assms have cycles: "cycles \<Delta> \<noteq> {}" by auto
  with assms from_nat_into_surj[of "cycles \<Delta>" C] obtain j where j: "C = enum_cycle j"
    by(auto simp add: enum_cycle_def)
  from h_minus_aux_cycle[of "?h'" j, OF finite_h' cycles] j
  obtain e where e: "e \<in> set (cycle_edges C)" and "h_minus_aux ?h' (Suc j) e = ?h' e" by(auto)
  then have "h_plus (Suc i) e = h_minus i e + h_minus_aux ?h' (Suc j) e"
    using order_trans[OF h_minus_le_h_plus h_plus_mono]
    by (subst eq_commute) simp
  also have "\<dots> \<le> h_minus (Suc i) e" unfolding h_minus.simps
    by(intro add_mono SUP_upper; simp)
  finally show ?thesis using e h_minus_le_h_plus[of "Suc i" e] Suc by auto
next
  case 0
  from cycle_edges_not_Nil[OF assms] obtain x y where e: "(x, y) \<in> set (cycle_edges C)"
    by(fastforce simp add: neq_Nil_conv)
  then have "x \<noteq> source \<Delta>" using assms by(auto dest: source_out_not_cycle)
  hence "h_plus 0 (x, y) = 0" by simp
  with e 0 show ?thesis by(auto simp del: h_plus.simps)
qed

abbreviation lim_h_plus :: "'v edge \<Rightarrow> ennreal"
where "lim_h_plus e \<equiv> SUP n. h_plus n e"

abbreviation lim_h_minus :: "'v edge \<Rightarrow> ennreal"
where "lim_h_minus e \<equiv> SUP n. h_minus n e"

lemma lim_h_plus_le_g: "lim_h_plus e \<le> g e"
by(rule SUP_least)(rule h_plus_le_g)

lemma lim_h_plus_finite [simp]: "lim_h_plus e \<noteq> top"
proof -
  have "lim_h_plus e \<le> g e" by(rule lim_h_plus_le_g)
  also have "\<dots> < top" by (simp add: less_top[symmetric])
  finally show ?thesis unfolding less_top .
qed

lemma lim_h_minus_le_lim_h_plus: "lim_h_minus e \<le> lim_h_plus e"
by(rule SUP_mono)(blast intro: h_minus_le_h_plus)

lemma lim_h_minus_finite [simp]: "lim_h_minus e \<noteq> top"
proof -
  have "lim_h_minus e \<le> lim_h_plus e" by(rule lim_h_minus_le_lim_h_plus)
  also have "\<dots> < top" unfolding less_top[symmetric] by (rule lim_h_plus_finite)
  finally show ?thesis unfolding less_top[symmetric] by simp
qed

lemma lim_h_minus_IN_finite [simp]:
  assumes "x \<noteq> sink \<Delta>"
  shows "d_IN lim_h_minus x \<noteq> top"
proof -
  have "d_IN lim_h_minus x \<le> d_IN lim_h_plus x"
    by(intro d_IN_mono le_funI lim_h_minus_le_lim_h_plus)
  also have "\<dots> \<le> d_IN g x" by(intro d_IN_mono le_funI lim_h_plus_le_g)
  also have "\<dots> < \<top>" using assms by(simp add: finite_IN_g less_top[symmetric])
  finally show ?thesis by simp
qed

lemma lim_h_plus_OUT_IN:
  assumes "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  shows "d_OUT lim_h_plus x = d_IN lim_h_plus x"
proof(cases "x \<in> \<^bold>V")
  case True
  have "d_OUT lim_h_plus x = (SUP n. d_OUT (h_plus n) x)"
    by(rule d_OUT_monotone_convergence_SUP incseq_SucI le_funI h_plus_mono)+
  also have "\<dots> = (SUP n. d_IN (h_plus n) x)" (is "?lhs = ?rhs")
  proof(rule antisym)
    show "?lhs \<le> ?rhs" by(rule SUP_mono)(auto intro: h_plus_OUT_le_IN[OF assms(1)])
    show "?rhs \<le> ?lhs"
    proof(rule SUP_mono)
      fix i
      from enum_v_repeat[OF True assms, of i]
      obtain i' where "i' > i" "enum_v i' = x" by auto
      moreover then obtain i'' where i': "i' = Suc i''" by(cases i') auto
      ultimately have "d_OUT (h_plus i') x = d_IN (h_plus i'') x" using  \<open>x \<noteq> source \<Delta>\<close>
        by(simp add: h_plus_OUT_eq_IN)
      moreover have "i \<le> i''" using \<open>i < i'\<close> i' by simp
      then have "d_IN (h_plus i) x \<le> d_IN (h_plus i'') x" by(intro d_IN_mono h_plus_mono')
      ultimately have "d_IN (h_plus i) x \<le> d_OUT (h_plus i') x" by simp
      thus "\<exists>i'\<in>UNIV. d_IN (h_plus i) x \<le> d_OUT (h_plus i') x" by blast
    qed
  qed
  also have "\<dots> = d_IN lim_h_plus x"
    by(rule d_IN_monotone_convergence_SUP[symmetric] incseq_SucI le_funI h_plus_mono)+
  finally show ?thesis .
next
  case False
  have "(x, y) \<notin> support_flow lim_h_plus" for y using False h_plus_outside[of "(x, y)"]
    by(fastforce elim!: support_flow.cases simp add: less_SUP_iff vertex_def)
  moreover have "(y, x) \<notin> support_flow lim_h_plus" for y using False h_plus_outside[of "(y, x)"]
    by(fastforce elim!: support_flow.cases simp add: less_SUP_iff vertex_def)
  ultimately show ?thesis
    by(auto simp add: d_OUT_alt_def2 d_IN_alt_def2 AE_count_space intro!: nn_integral_cong_AE)
qed

lemma lim_h_minus_OUT_IN:
  assumes cycles: "cycles \<Delta> \<noteq> {}"
  shows "d_OUT lim_h_minus x = d_IN lim_h_minus x"
proof -
  have "d_OUT lim_h_minus x = (SUP n. d_OUT (h_minus n) x)"
    by(rule d_OUT_monotone_convergence_SUP incseq_SucI le_funI h_minus_mono)+
  also have "\<dots> = (SUP n. d_IN (h_minus n) x)" using cycles by(simp add: d_OUT_h_minus)
  also have "\<dots> = d_IN lim_h_minus x"
    by(rule d_IN_monotone_convergence_SUP[symmetric] incseq_SucI le_funI h_minus_mono)+
  finally show ?thesis .
qed

definition h :: "'v edge \<Rightarrow> ennreal"
where "h e = lim_h_plus e - (if cycles \<Delta> \<noteq> {} then lim_h_minus e else 0)"

lemma h_le_lim_h_plus: "h e \<le> lim_h_plus e"
by (simp add: h_def)

lemma h_le_g: "h e \<le> g e"
using h_le_lim_h_plus[of e] lim_h_plus_le_g[of e] by simp

lemma flow_h: "flow \<Delta> h"
proof
  fix e
  have "h e \<le> lim_h_plus e" by(rule h_le_lim_h_plus)
  also have "\<dots> \<le> g e" by(rule lim_h_plus_le_g)
  also have "\<dots> \<le> capacity \<Delta> e" using g by(rule flowD_capacity)
  finally show "h e \<le> \<dots>" .
next
  fix x
  assume "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  then show "KIR h x"
    by (cases "cycles \<Delta> = {}")
       (auto simp add: h_def[abs_def] lim_h_plus_OUT_IN d_OUT_diff d_IN_diff lim_h_minus_le_lim_h_plus lim_h_minus_OUT_IN)
qed

lemma value_h_plus: "value_flow \<Delta> (h_plus i) = value_flow \<Delta> g" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" by(rule d_OUT_mono)(rule h_plus_le_g)

  have "?rhs \<le> value_flow \<Delta> (h_plus 0)"
    by(auto simp add: d_OUT_def cong: if_cong intro!: nn_integral_mono)
  also have "\<dots> \<le> value_flow \<Delta> (h_plus i)"
    by(rule d_OUT_mono)(rule h_plus_mono'; simp)
  finally show "?rhs \<le> ?lhs" .
qed

lemma value_h: "value_flow \<Delta> h = value_flow \<Delta> g" (is "?lhs = ?rhs")
proof(rule antisym)
  have "?lhs \<le> value_flow \<Delta> lim_h_plus" using ennreal_minus_mono
    by(fastforce simp add: h_def intro!: d_OUT_mono)
  also have "\<dots> \<le> ?rhs" by(rule d_OUT_mono)(rule lim_h_plus_le_g)
  finally show "?lhs \<le> ?rhs" .

  show "?rhs \<le> ?lhs"
    by(auto simp add: d_OUT_def h_def h_minus_source cong: if_cong intro!: nn_integral_mono SUP_upper2[where i=0])
qed


definition h_diff :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where "h_diff i e = h_plus i e - (if cycles \<Delta> \<noteq> {} then h_minus i e else 0)"

lemma d_IN_h_source [simp]: "d_IN (h_diff i) (source \<Delta>) = 0"
by(simp add: d_IN_def h_diff_def cong del: if_weak_cong)

lemma h_diff_le_h_plus: "h_diff i e \<le> h_plus i e"
by(simp add: h_diff_def)

lemma h_diff_le_g: "h_diff i e \<le> g e"
using h_diff_le_h_plus[of i e] h_plus_le_g[of i e] by simp

lemma h_diff_loop [simp]: "h_diff i (x, x) = 0"
using h_diff_le_g[of i "(x, x)"] by simp

lemma supp_h_diff_edges: "support_flow (h_diff i) \<subseteq> \<^bold>E"
proof
  fix e
  assume "e \<in> support_flow (h_diff i)"
  then have "0 < h_diff i e" by(auto elim: support_flow.cases)
  also have "h_diff i e \<le> h_plus i e" by(rule h_diff_le_h_plus)
  finally show "e \<in> \<^bold>E" using h_plus_outside[of e i] by(cases "e \<in> \<^bold>E") auto
qed

lemma h_diff_OUT_le_IN:
  assumes "x \<noteq> source \<Delta>"
  shows "d_OUT (h_diff i) x \<le> d_IN (h_diff i) x"
proof(cases "cycles \<Delta> \<noteq> {}")
  case False
  thus ?thesis using assms by(simp add: h_diff_def[abs_def] h_plus_OUT_le_IN)
next
  case cycles: True
  then have "d_OUT (h_diff i) x = d_OUT (h_plus i) x - d_OUT (h_minus i) x"
    unfolding h_diff_def[abs_def] using assms
    by (simp add: h_minus_le_h_plus d_OUT_diff)
  also have "\<dots> \<le> d_IN (h_plus i) x - d_IN (h_minus i) x" using cycles assms
    by(intro ennreal_minus_mono h_plus_OUT_le_IN)(simp_all add: d_OUT_h_minus)
  also have "\<dots> = d_IN (h_diff i) x" using cycles
    unfolding h_diff_def[abs_def] by(subst d_IN_diff)(simp_all add: h_minus_le_h_plus d_OUT_h_minus[symmetric])
  finally show ?thesis .
qed

lemma h_diff_cycle:
  assumes "cycle \<Delta> p"
  shows "\<exists>e\<in>set (cycle_edges p). h_diff i e = 0"
proof -
  from h_minus_cycle[OF assms, of i] obtain e
    where e: "e \<in> set (cycle_edges p)" and "h_minus i e = h_plus i e" by auto
  hence "h_diff i e = 0" using assms by(auto simp add: h_diff_def)
  with e show ?thesis by blast
qed

lemma d_IN_h_le_value': "d_IN (h_diff i) x \<le> value_flow \<Delta> (h_plus i)"
proof -
  let ?supp = "support_flow (h_diff i)"
  define X where "X = {y. (y, x) \<in> ?supp^*} - {x}"

  { fix x y
    assume x: "x \<notin> X" and y: "y \<in> X"
    { assume yx: "(y, x) \<in> ?supp\<^sup>*" and neq: "y \<noteq> x" and xy: "(x, y) \<in> ?supp"
      from yx obtain p' where "rtrancl_path (\<lambda>x y. (x, y) \<in> ?supp) y p' x"
        unfolding rtrancl_def rtranclp_eq_rtrancl_path by auto
      then obtain p where p: "rtrancl_path (\<lambda>x y. (x, y) \<in> ?supp) y p x"
        and distinct: "distinct (y # p)" by(rule rtrancl_path_distinct)
      with neq have "p \<noteq> []" by(auto elim: rtrancl_path.cases)

      from xy have "(x, y) \<in> \<^bold>E" using supp_h_diff_edges[of i] by(auto)
      moreover from p have "path \<Delta> y p x"
        by(rule rtrancl_path_mono)(auto dest: supp_h_diff_edges[THEN subsetD])
      ultimately have "path \<Delta> x (y # p) x" by(auto intro: rtrancl_path.intros)
      hence cycle: "cycle \<Delta> (y # p)" using _ distinct by(rule cycle) simp
      from h_diff_cycle[OF this, of i] obtain e
        where e: "e \<in> set (cycle_edges (y # p))" and 0: "h_diff i e = 0" by blast
      from e obtain n where e': "e = ((y # p) ! n, (p @ [y]) ! n)" and n: "n < Suc (length p)"
        by(auto simp add: cycle_edges_def set_zip)
      have "e \<in> ?supp"
      proof(cases "n = length p")
        case True
        with rtrancl_path_last[OF p] \<open>p \<noteq> []\<close> have "(y # p) ! n = x"
          by(cases p)(simp_all add: last_conv_nth del: last.simps)
        with e' True have "e = (x, y)" by simp
        with xy show ?thesis by simp
      next
        case False
        with n have "n < length p" by simp
        with rtrancl_path_nth[OF p this] e' show ?thesis by(simp add: nth_append)
      qed
      with 0 have False by(simp add: support_flow.simps) }
    hence "(x, y) \<notin> ?supp" using x y
      by(auto simp add: X_def intro: converse_rtrancl_into_rtrancl)
    then have "h_diff i (x, y) = 0"
      by(simp add: support_flow.simps) }
  note acyclic = this

  { fix y
    assume "y \<notin> X"
    hence "(y, x) \<notin> ?supp" by(auto simp add: X_def support_flow.simps intro: not_in_support_flowD)
    hence "h_diff i (y, x) = 0"  by(simp add: support_flow.simps) }
  note in_X = this

  let ?diff = "\<lambda>x. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator X y)"
  have finite2: "(\<Sum>\<^sup>+ x. ?diff x) \<noteq> top" (is "?lhs \<noteq> _")
  proof -
    have "?lhs \<le> (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_plus i (x, y))"
      by(intro nn_integral_mono)(auto simp add: h_diff_def split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ e. h_plus i e)" by(rule nn_integral_fst_count_space)
    also have "\<dots> < \<top>" by(simp add: h_plus_sum_finite less_top[symmetric])
    finally show ?thesis by simp
  qed
  have finite1: "?diff x \<noteq> top" for x
    using finite2 by(rule neq_top_trans)(rule nn_integral_ge_point, simp)
  have finite3: "(\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x) \<noteq> \<top>" (is "?lhs \<noteq> _")
  proof -
    have "?lhs \<le> (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_plus i (x, y))" unfolding d_OUT_def
      apply(simp add: nn_integral_multc[symmetric])
      apply(intro nn_integral_mono)
      apply(auto simp add: h_diff_def split: split_indicator)
      done
    also have "\<dots> = (\<Sum>\<^sup>+ e. h_plus i e)" by(rule nn_integral_fst_count_space)
    also have "\<dots> < \<top>" by(simp add: h_plus_sum_finite less_top[symmetric])
    finally show ?thesis by simp
  qed

  have "d_IN (h_diff i) x = (\<Sum>\<^sup>+ y. h_diff i (y, x) * indicator X y)" unfolding d_IN_def
    by(rule nn_integral_cong)(simp add: in_X split: split_indicator)
  also have "\<dots> \<le> (\<Sum>\<^sup>+ x\<in>- X. \<Sum>\<^sup>+ y. h_diff i (y, x) * indicator X y)"
    by(rule nn_integral_ge_point)(simp add: X_def)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (y, x) * indicator X y * indicator (- X) x)"
    by(simp add: nn_integral_multc nn_integral_count_space_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator (- X) y)"
    by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])(simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator (- X) y) + (?diff x - ?diff x))"
    by(simp add: finite1)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator (- X) y + h_diff i (x, y) * indicator X x * indicator X y) - ?diff x)"
    apply (subst add_diff_eq_ennreal)
    apply simp
    by(subst nn_integral_add[symmetric])(simp_all add:)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x) - ?diff x)"
    by(auto intro!: nn_integral_cong arg_cong2[where f="(-)"] split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y\<in>UNIV. h_diff i (x, y) * indicator X x) - (\<Sum>\<^sup>+ x. ?diff x)"
    by(subst nn_integral_diff)(auto simp add: AE_count_space finite2 intro!: nn_integral_mono split: split_indicator)
  also have "(\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y\<in>UNIV. h_diff i (x, y) * indicator X x) = (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator X x)"
    unfolding d_OUT_def by(simp add: nn_integral_multc)
  also have "\<dots> = (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x + value_flow \<Delta> (h_diff i) * indicator X (source \<Delta>) * indicator {source \<Delta>} x)"
    by(rule nn_integral_cong)(simp split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x) + value_flow \<Delta> (h_diff i) * indicator X (source \<Delta>)"
    (is "_ = ?out" is "_ = _ + ?value")
    by(subst nn_integral_add) simp_all
  also have "(\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator X y) =
             (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X y)"
    using acyclic by(intro nn_integral_cong)(simp split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. \<Sum>\<^sup>+ x. h_diff i (x, y) * indicator X y)"
    by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])(simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
  also have "\<dots> = (\<Sum>\<^sup>+ y. d_IN (h_diff i) y * indicator X y)" unfolding d_IN_def
    by(simp add: nn_integral_multc)
  also have "\<dots> = (\<Sum>\<^sup>+ y. d_IN (h_diff i) y * indicator (X - {source \<Delta>}) y)"
    by(rule nn_integral_cong)(simp split: split_indicator)
  also have "?out - \<dots> \<le> (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x) - \<dots> + ?value"
    by (auto simp add: add_ac intro!: add_diff_le_ennreal)
  also have "\<dots> \<le> 0 + ?value" using h_diff_OUT_le_IN finite3
    by(intro nn_integral_mono add_right_mono)(auto split: split_indicator intro!: diff_eq_0_ennreal nn_integral_mono simp add: less_top)
  also have "\<dots> \<le> value_flow \<Delta> (h_diff i)" by(simp split: split_indicator)
  also have "\<dots> \<le> value_flow \<Delta> (h_plus i)" by(rule d_OUT_mono le_funI h_diff_le_h_plus)+
  finally show ?thesis .
qed

lemma d_IN_h_le_value: "d_IN h x \<le> value_flow \<Delta> h" (is "?lhs \<le> ?rhs")
proof -
  have [tendsto_intros]: "(\<lambda>i. h_plus i e) \<longlonglongrightarrow> lim_h_plus e" for e
    by(rule LIMSEQ_SUP incseq_SucI h_plus_mono)+
  have [tendsto_intros]: "(\<lambda>i. h_minus i e) \<longlonglongrightarrow> lim_h_minus e" for e
    by(rule LIMSEQ_SUP incseq_SucI h_minus_mono)+
  have "(\<lambda>i. h_diff i e) \<longlonglongrightarrow> lim_h_plus e - (if cycles \<Delta> \<noteq> {} then lim_h_minus e else 0)" for e
    by(auto intro!: tendsto_intros tendsto_diff_ennreal simp add: h_diff_def simp del: Sup_eq_top_iff SUP_eq_top_iff)
  then have "d_IN h x = (\<Sum>\<^sup>+ y. liminf (\<lambda>i. h_diff i (y, x)))"
    by(simp add: d_IN_def h_def tendsto_iff_Liminf_eq_Limsup)
  also have "\<dots> \<le> liminf (\<lambda>i. d_IN (h_diff i) x)" unfolding d_IN_def
    by(rule nn_integral_liminf) simp_all
  also have "\<dots> \<le> liminf (\<lambda>i. value_flow \<Delta> h)" using d_IN_h_le_value'[of _ x]
    by(intro Liminf_mono eventually_sequentiallyI)(auto simp add: value_h_plus value_h)
  also have "\<dots> = value_flow \<Delta> h" by(simp add: Liminf_const)
  finally show ?thesis .
qed

lemma flow_cleanup: \<comment> \<open>Lemma 5.4\<close>
  "\<exists>h \<le> g. flow \<Delta> h \<and> value_flow \<Delta> h = value_flow \<Delta> g \<and> (\<forall>x. d_IN h x \<le> value_flow \<Delta> h)"
by(intro exI[where x=h] conjI strip le_funI d_IN_h_le_value flow_h value_h h_le_g)

end

subsection \<open>Residual network\<close>

context countable_network begin

definition residual_network :: "'v flow \<Rightarrow> ('v, 'more) network_scheme"
where "residual_network f =
  \<lparr>edge = \<lambda>x y. edge \<Delta> x y \<or> edge \<Delta> y x \<and> y \<noteq> source \<Delta>,
   capacity = \<lambda>(x, y). if edge \<Delta> x y then capacity \<Delta> (x, y) - f (x, y) else if y = source \<Delta> then 0 else f (y, x),
   source = source \<Delta>, sink = sink \<Delta>, \<dots> = network.more \<Delta> \<rparr>"

lemma residual_network_sel [simp]:
  "edge (residual_network f) x y \<longleftrightarrow> edge \<Delta> x y \<or> edge \<Delta> y x \<and> y \<noteq> source \<Delta>"
  "capacity (residual_network f) (x, y) = (if edge \<Delta> x y then capacity \<Delta> (x, y) - f (x, y) else if y = source \<Delta> then 0 else f (y, x))"
  "source (residual_network f) = source \<Delta>"
  "sink (residual_network f) = sink \<Delta>"
  "network.more (residual_network f) = network.more \<Delta>"
by(simp_all add: residual_network_def)

lemma "\<^bold>E_residual_network": "\<^bold>E\<^bsub>residual_network f\<^esub> = \<^bold>E \<union> {(x, y). (y, x) \<in> \<^bold>E \<and> y \<noteq> source \<Delta>}"
by auto

lemma vertices_residual_network [simp]: "vertex (residual_network f) = vertex \<Delta>"
by(auto simp add: vertex_def fun_eq_iff)

inductive wf_residual_network :: "bool"
where "\<lbrakk> \<And>x y. (x, y) \<in> \<^bold>E \<Longrightarrow> (y, x) \<notin> \<^bold>E; (source \<Delta>, sink \<Delta>) \<notin> \<^bold>E \<rbrakk> \<Longrightarrow> wf_residual_network"

lemma wf_residual_networkD:
  "\<lbrakk> wf_residual_network; edge \<Delta> x y \<rbrakk> \<Longrightarrow> \<not> edge \<Delta> y x"
  "\<lbrakk> wf_residual_network; e \<in> \<^bold>E \<rbrakk> \<Longrightarrow> prod.swap e \<notin> \<^bold>E"
  "\<lbrakk> wf_residual_network; edge \<Delta> (source \<Delta>) (sink \<Delta>) \<rbrakk> \<Longrightarrow> False"
by(auto simp add: wf_residual_network.simps)

lemma residual_countable_network:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  shows "countable_network (residual_network f)" (is "countable_network ?\<Delta>")
proof
  have "countable (converse \<^bold>E)" by simp
  then have "countable {(x, y). (y, x) \<in> \<^bold>E \<and> y \<noteq> source \<Delta>}"
    by(rule countable_subset[rotated]) auto
  then show "countable \<^bold>E\<^bsub>?\<Delta>\<^esub>" unfolding "\<^bold>E_residual_network" by simp

  show "source ?\<Delta> \<noteq> sink ?\<Delta>" by simp
  show "capacity ?\<Delta> e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Delta>\<^esub>" for e using that by(cases e)(auto intro: flowD_outside[OF f])
  show "capacity ?\<Delta> e \<noteq> top" for e
    using flowD_finite[OF f] by(cases e) auto
qed

end

context antiparallel_edges begin

interpretation \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)

lemma \<Delta>''_flow_attainability:
  assumes "flow_attainability_axioms \<Delta>"
  shows "flow_attainability \<Delta>''"
proof -
  interpret flow_attainability \<Delta> using _ assms by(rule flow_attainability.intro) unfold_locales
  show ?thesis
  proof
    show "d_IN (capacity \<Delta>'') v \<noteq> \<top> \<or> d_OUT (capacity \<Delta>'') v \<noteq> \<top>" if "v \<noteq> sink \<Delta>''" for v
      using that finite_capacity by(cases v)(simp_all add: max_def)
    show "\<not> edge \<Delta>'' v v" for v by(auto elim: edg.cases)
    show "\<not> edge \<Delta>'' v (source \<Delta>'')" for v by(simp add: source_in)
  qed
qed

lemma \<Delta>''_wf_residual_network:
  assumes no_loop: "\<And>x. \<not> edge \<Delta> x x"
  shows "\<Delta>''.wf_residual_network"
by(auto simp add: \<Delta>''.wf_residual_network.simps assms elim!: edg.cases)

end

subsection \<open>The attainability theorem\<close>

context flow_attainability begin

lemma residual_flow_attainability:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  shows "flow_attainability (residual_network f)" (is "flow_attainability ?\<Delta>")
proof -
  interpret res: countable_network "residual_network f" by(rule residual_countable_network[OF assms])
  show ?thesis
  proof
    fix x
    assume sink: "x \<noteq> sink ?\<Delta>"
    then consider (source) "x = source \<Delta>" | (IN) "d_IN (capacity \<Delta>) x \<noteq> \<top>" | (OUT) "x \<noteq> source \<Delta>" "d_OUT (capacity \<Delta>) x \<noteq> \<top>"
      using finite_capacity[of x] by auto
    then show "d_IN (capacity ?\<Delta>) x \<noteq> \<top> \<or> d_OUT (capacity ?\<Delta>) x \<noteq> \<top>"
    proof(cases)
      case source
      hence "d_IN (capacity ?\<Delta>) x = 0" by(simp add: d_IN_def source_in)
      thus ?thesis by simp
    next
      case IN
      have "d_IN (capacity ?\<Delta>) x =
        (\<Sum>\<^sup>+ y. (capacity \<Delta> (y, x) - f (y, x)) * indicator \<^bold>E (y, x) +
              (if x = source \<Delta> then 0 else f (x, y) * indicator \<^bold>E (x, y)))"
        using flowD_outside[OF f] unfolding d_IN_def
        by(auto intro!: nn_integral_cong split: split_indicator dest: wf_residual_networkD[OF wf])
      also have "\<dots> = (\<Sum>\<^sup>+ y. (capacity \<Delta> (y, x) - f (y, x)) * indicator \<^bold>E (y, x)) +
        (\<Sum>\<^sup>+ y. (if x = source \<Delta> then 0 else f (x, y) * indicator \<^bold>E (x, y)))"
        (is "_ = ?in + ?out")
        by(subst nn_integral_add)(auto simp add: AE_count_space split: split_indicator intro!: flowD_capacity[OF f])
      also have "\<dots> \<le> d_IN (capacity \<Delta>) x + (if x = source \<Delta> then 0 else d_OUT f x)" (is "_ \<le> ?in + ?rest")
        unfolding d_IN_def d_OUT_def
        by(rule add_mono)(auto intro!: nn_integral_mono split: split_indicator simp add: nn_integral_0_iff_AE AE_count_space intro!: diff_le_self_ennreal)
      also consider (source) "x = source \<Delta>" | (inner) "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using sink by auto
      then have "?rest < \<top>"
      proof cases
        case inner
        show ?thesis using inner flowD_finite_OUT[OF f inner] by (simp add: less_top)
      qed simp
      ultimately show ?thesis using IN sink by (auto simp: less_top[symmetric] top_unique)
    next
      case OUT
      have "d_OUT (capacity ?\<Delta>) x =
        (\<Sum>\<^sup>+ y. (capacity \<Delta> (x, y) - f (x, y)) * indicator \<^bold>E (x, y) +
              (if y = source \<Delta> then 0 else f (y, x) * indicator \<^bold>E (y, x)))"
        using flowD_outside[OF f] unfolding d_OUT_def
        by(auto intro!: nn_integral_cong split: split_indicator dest: wf_residual_networkD[OF wf] simp add: source_in)
      also have "\<dots> = (\<Sum>\<^sup>+ y. (capacity \<Delta> (x, y) - f (x, y)) * indicator \<^bold>E (x, y)) +
        (\<Sum>\<^sup>+ y. (if y = source \<Delta> then 0 else f (y, x) * indicator \<^bold>E (y, x)))"
        (is "_ = ?in + ?out")
        by(subst nn_integral_add)(auto simp add: AE_count_space split: split_indicator intro!: flowD_capacity[OF f])
      also have "\<dots> \<le> d_OUT (capacity \<Delta>) x + d_IN f x" (is "_ \<le> ?out + ?rest")
        unfolding d_IN_def d_OUT_def
        by(rule add_mono)(auto intro!: nn_integral_mono split: split_indicator simp add: nn_integral_0_iff_AE AE_count_space intro!: diff_le_self_ennreal)
      also have "?rest = d_OUT f x" using flowD_KIR[OF f OUT(1)] sink by simp
      also have "?out + \<dots> \<le> ?out + ?out" by(intro add_left_mono d_OUT_mono flowD_capacity[OF f])
      finally show ?thesis using OUT by (auto simp: top_unique)
    qed
  next
    show "\<not> edge ?\<Delta> x x" for x by(simp add: no_loop)
    show "\<not> edge ?\<Delta> x (source ?\<Delta>)" for x by(simp add: source_in)
  qed
qed

end

definition plus_flow :: "('v, 'more) graph_scheme \<Rightarrow> 'v flow \<Rightarrow> 'v flow \<Rightarrow> 'v flow" (infixr "\<oplus>\<index>" 65)
where "plus_flow G f g = (\<lambda>(x, y). if edge G x y then f (x, y) + g (x, y) - g (y, x) else 0)"

lemma plus_flow_simps [simp]: fixes G (structure) shows
  "(f \<oplus> g) (x, y) = (if edge G x y then f (x, y) + g (x, y) - g (y, x) else 0)"
by(simp add: plus_flow_def)

lemma plus_flow_outside: fixes G (structure) shows "e \<notin> \<^bold>E \<Longrightarrow> (f \<oplus> g) e = 0"
by(cases e) simp

lemma
  fixes \<Delta> (structure)
  assumes f_outside: "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
  and g_le_f: "\<And>x y. edge \<Delta> x y \<Longrightarrow> g (y, x) \<le> f (x, y)"
  shows OUT_plus_flow: "d_IN g x \<noteq> top \<Longrightarrow> d_OUT (f \<oplus> g) x = d_OUT f x + (\<Sum>\<^sup>+ y\<in>UNIV. g (x, y) * indicator \<^bold>E (x, y)) - (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (x, y))"
    (is "_ \<Longrightarrow> ?OUT" is "_ \<Longrightarrow> _ = _ + ?g_out - ?g_out'")
  and IN_plus_flow: "d_OUT g x \<noteq> top \<Longrightarrow> d_IN (f \<oplus> g) x = d_IN f x + (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * indicator \<^bold>E (y, x)) - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))"
    (is "_ \<Longrightarrow> ?IN" is "_ \<Longrightarrow> _ = _ + ?g_in - ?g_in'")
proof -
  assume "d_IN g x \<noteq> top"
  then have finite1: "(\<Sum>\<^sup>+ y. g (y, x) * indicator A (f y)) \<noteq> top" for A f
    by(rule neq_top_trans)(auto split: split_indicator simp add: d_IN_def intro!: nn_integral_mono)

  have "d_OUT (f \<oplus> g) x = (\<Sum>\<^sup>+ y. (g (x, y) + (f (x, y) - g (y, x))) * indicator \<^bold>E (x, y))"
    unfolding d_OUT_def by(rule nn_integral_cong)(simp split: split_indicator add: add_diff_eq_ennreal add.commute ennreal_diff_add_assoc g_le_f)
  also have "\<dots> = ?g_out + (\<Sum>\<^sup>+ y. (f (x, y) - g (y, x)) * indicator \<^bold>E (x, y))"
    (is "_ = _ + ?rest")
    by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space g_le_f split: split_indicator intro!: nn_integral_cong)
  also have "?rest = (\<Sum>\<^sup>+ y. f (x, y) * indicator \<^bold>E (x, y)) - ?g_out'" (is "_ = ?f - _")
    apply(subst nn_integral_diff[symmetric])
    apply(auto intro!: nn_integral_cong split: split_indicator simp add: AE_count_space g_le_f finite1)
    done
  also have "?f = d_OUT f x" unfolding d_OUT_def using f_outside
    by(auto intro!: nn_integral_cong split: split_indicator)
  also have "(\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (x, y)) + (d_OUT f x - (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (x, y))) =
     d_OUT f x + ?g_out - ?g_out'"
     by (subst ennreal_diff_add_assoc[symmetric])
        (auto simp: ac_simps d_OUT_def intro!: nn_integral_mono g_le_f split: split_indicator)
  finally show ?OUT .
next
  assume "d_OUT g x \<noteq> top"
  then have finite2: "(\<Sum>\<^sup>+ y. g (x, y) * indicator A (f y)) \<noteq> top" for A f
    by(rule neq_top_trans)(auto split: split_indicator simp add: d_OUT_def intro!: nn_integral_mono)

  have "d_IN (f \<oplus> g) x = (\<Sum>\<^sup>+ y. (g (y, x) + (f (y, x) - g (x, y))) * indicator \<^bold>E (y, x))"
    unfolding d_IN_def by(rule nn_integral_cong)(simp split: split_indicator add: add_diff_eq_ennreal add.commute ennreal_diff_add_assoc g_le_f)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * indicator \<^bold>E (y, x)) + (\<Sum>\<^sup>+ y. (f (y, x) - g (x, y)) * indicator \<^bold>E (y, x))"
    (is "_ = _ + ?rest")
    by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space g_le_f split: split_indicator intro!: nn_integral_cong)
  also have "?rest = (\<Sum>\<^sup>+ y. f (y, x) * indicator \<^bold>E (y, x))- ?g_in'"
    by(subst nn_integral_diff[symmetric])(auto intro!: nn_integral_cong split: split_indicator simp add: add_ac add_diff_eq_ennreal AE_count_space g_le_f finite2)
  also have "(\<Sum>\<^sup>+ y. f (y, x) * indicator \<^bold>E (y, x)) = d_IN f x"
    unfolding d_IN_def using f_outside by(auto intro!: nn_integral_cong split: split_indicator)
  also have "(\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (y, x)) + (d_IN f x - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))) =
     d_IN f x + ?g_in - ?g_in'"
     by (subst ennreal_diff_add_assoc[symmetric])
        (auto simp: ac_simps d_IN_def intro!: nn_integral_mono g_le_f split: split_indicator)
  finally show ?IN .
qed

context countable_network begin

lemma d_IN_plus_flow:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow (residual_network f) g"
  shows "d_IN (f \<oplus> g) x \<le> d_IN f x + d_IN g x"
proof -
  have "d_IN (f \<oplus> g) x \<le> (\<Sum>\<^sup>+ y. f (y, x) + g (y, x))" unfolding d_IN_def
    by(rule nn_integral_mono)(auto intro: diff_le_self_ennreal)
  also have "\<dots> = d_IN f x + d_IN g x"
    by(subst nn_integral_add)(simp_all add: d_IN_def)
  finally show ?thesis .
qed

lemma scale_flow:
  assumes f: "flow \<Delta> f"
  and c: "c \<le> 1"
  shows "flow \<Delta> (\<lambda>e. c * f e)"
proof(intro flow.intros)
  fix e
  from c have "c * f e \<le> 1 * f e" by(rule mult_right_mono) simp
  also have "\<dots> \<le> capacity \<Delta> e" using flowD_capacity[OF f, of e] by simp
  finally show "c * f e \<le> \<dots>" .
next
  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT (\<lambda>e. c * f e) x = c * d_OUT f x" by(simp add: d_OUT_cmult)
  also have "d_OUT f x = d_IN f x" using f x by(rule flowD_KIR)
  also have "c * \<dots> = d_IN (\<lambda>e. c * f e) x" by(simp add: d_IN_cmult)
  finally show "KIR (\<lambda>e. c * f e) x" .
qed

lemma value_scale_flow:
  "value_flow \<Delta> (\<lambda>e. c * f e) = c * value_flow \<Delta> f"
by(rule d_OUT_cmult)

lemma value_flow:
  assumes f: "flow \<Delta> f"
  and source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  shows "value_flow \<Delta> f = f (source \<Delta>, x)"
proof -
  have "value_flow \<Delta> f = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T (source \<Delta>). f (source \<Delta>, y))"
    by(rule d_OUT_alt_def)(simp add: flowD_outside[OF f])
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (source \<Delta>, y) * indicator {x} y)"
    by(subst nn_integral_count_space_indicator)(auto intro!: nn_integral_cong split: split_indicator simp add: outgoing_def source_out)
  also have "\<dots> = f (source \<Delta>, x)" by(simp add: one_ennreal_def[symmetric] max_def)
  finally show ?thesis .
qed

end

context flow_attainability begin

lemma value_plus_flow:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow (residual_network f) g"
  shows "value_flow \<Delta> (f \<oplus> g) = value_flow \<Delta> f + value_flow \<Delta> g"
proof -
  interpret RES: countable_network "residual_network f" using wf f by(rule residual_countable_network)
  have "value_flow \<Delta> (f \<oplus> g) = (\<Sum>\<^sup>+ y. f (source \<Delta>, y) + g (source \<Delta>, y))"
    unfolding d_OUT_def by(rule nn_integral_cong)(simp add: flowD_outside[OF f] RES.flowD_outside[OF g] source_in)
  also have "\<dots> = value_flow \<Delta> f + value_flow \<Delta> g" unfolding d_OUT_def
    by(rule nn_integral_add) simp_all
  finally show ?thesis .
qed

lemma flow_residual_add: \<comment> \<open>Lemma 5.3\<close>
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow (residual_network f) g"
  shows "flow \<Delta> (f \<oplus> g)"
proof
  fix e
  { assume e: "e \<in> \<^bold>E"
    hence "(f \<oplus> g) e = f e + g e - g (prod.swap e)" by(cases e) simp
    also have "\<dots> \<le> f e + g e - 0" by(rule ennreal_minus_mono) simp_all
    also have "\<dots> \<le> f e + (capacity \<Delta> e - f e)"
      using e flowD_capacity[OF g, of e] by(simp split: prod.split_asm add: add_mono)
    also have "\<dots> = capacity \<Delta> e" using flowD_capacity[OF f, of e]
      by simp
    also note calculation }
  thus "(f \<oplus> g) e \<le> capacity \<Delta> e" by(cases e) auto
next
  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have g_le_f: "g (y, x) \<le> f (x, y)" if "edge \<Delta> x y" for x y
    using that flowD_capacity[OF g, of "(y, x)"]
    by(auto split: if_split_asm dest: wf_residual_networkD[OF wf] elim: order_trans)

  interpret RES: flow_attainability "residual_network f" using wf f by(rule residual_flow_attainability)

  have finite1: "(\<Sum>\<^sup>+ y. g (y, x) * indicator A (f y)) \<noteq> \<top>" for A f
    using RES.flowD_finite_IN[OF g, of x]
    by(rule neq_top_trans)(auto simp add: x d_IN_def split: split_indicator intro: nn_integral_mono)
  have finite2: "(\<Sum>\<^sup>+ y. g (x, y) * indicator A (f y)) \<noteq> \<top>" for A f
    using RES.flowD_finite_OUT[OF g, of x]
    by(rule neq_top_trans)(auto simp add: x d_OUT_def split: split_indicator intro: nn_integral_mono)

  have "d_OUT (f \<oplus> g) x = d_OUT f x + (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (x, y)) - (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (x, y))"
    (is "_ = ?f + ?g_out - ?g_in")
    using flowD_outside[OF f] g_le_f RES.flowD_finite_IN[OF g, of x]
    by(rule OUT_plus_flow)(simp_all add: x)
  also have "?f = d_IN f x" using f x by(auto dest: flowD_KIR)
  also have "?g_out = (\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (y, x))"
  proof -
    have "(\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (y, x)) =
          (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (x, y)) + (\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x))"
      by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space dest: wf_residual_networkD[OF wf] split: split_indicator intro!: nn_integral_cong)
    also have "(\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x)) = 0"
      using RES.flowD_outside[OF g]
      by(auto simp add: nn_integral_0_iff_AE AE_count_space split: split_indicator)
    finally show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>\<^sup>+ y. g (x, y) - g (x, y) * indicator \<^bold>E (y, x))"
    by(rule nn_integral_cong)(simp split: split_indicator add: RES.flowD_finite[OF g])
  also have "\<dots> = d_OUT g x - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))"
    (is "_ = _ - ?g_in_E") unfolding d_OUT_def
    by(subst nn_integral_diff)(simp_all add: AE_count_space finite2 split: split_indicator)
  also have "d_IN f x + (d_OUT g x - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))) - ?g_in =
    ((d_IN f x + d_OUT g x) - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))) - ?g_in"
    by (subst add_diff_eq_ennreal) (auto simp: d_OUT_def intro!: nn_integral_mono split: split_indicator)
  also have "d_OUT g x = d_IN g x" using x g by(auto dest: flowD_KIR)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * indicator (- \<^bold>E) (y, x)) + (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (y, x))"
    (is "_ = ?x + ?g_in_E'")
    by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong simp add: d_IN_def AE_count_space split: split_indicator)
  also have "?x = ?g_in"
  proof -
    have "?x = (\<Sum>\<^sup>+ y. g (y, x) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x)) + ?g_in"
      by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space  dest: wf_residual_networkD[OF wf] split: split_indicator intro!: nn_integral_cong)
    also have "(\<Sum>\<^sup>+ y. g (y, x) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x)) = 0"
      using RES.flowD_outside[OF g]
      by(auto simp add: nn_integral_0_iff_AE AE_count_space split: split_indicator)
    finally show ?thesis by simp
  qed
  also have "(d_IN f x + (?g_in + ?g_in_E') - ?g_in_E) - ?g_in =
    d_IN f x + ?g_in_E' + ?g_in - ?g_in - ?g_in_E"
    by (subst diff_diff_commute_ennreal) (simp add: ac_simps)
  also have "\<dots> = d_IN f x + ?g_in_E' - ?g_in_E"
    by (subst ennreal_add_diff_cancel_right) (simp_all add: finite1)
  also have "\<dots> = d_IN (f \<oplus> g) x"
    using flowD_outside[OF f]  g_le_f RES.flowD_finite_OUT[OF g, of x]
    by(rule IN_plus_flow[symmetric])(simp_all add: x)
  finally show "KIR (f \<oplus> g) x" by simp
qed

definition minus_flow :: "'v flow \<Rightarrow> 'v flow \<Rightarrow> 'v flow" (infixl "\<ominus>" 65)
where
  "f \<ominus> g = (\<lambda>(x, y). if edge \<Delta> x y then f (x, y) - g (x, y) else if edge \<Delta> y x then g (y, x) - f (y, x) else 0)"

lemma minus_flow_simps [simp]:
  "(f \<ominus> g) (x, y) = (if edge \<Delta> x y then f (x, y) - g (x, y) else if edge \<Delta> y x then g (y, x) - f (y, x) else 0)"
by(simp add: minus_flow_def)

lemma minus_flow:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow \<Delta> g"
  and value_le: "value_flow \<Delta> g \<le> value_flow \<Delta> f"
  and f_finite: "f (source \<Delta>, x) \<noteq> \<top>"
  and source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  shows "flow (residual_network g) (f \<ominus> g)" (is "flow ?\<Delta> ?f")
proof
  show "?f e \<le> capacity ?\<Delta> e" for e
    using value_le f_finite flowD_capacity[OF g] flowD_capacity[OF f]
    by(cases e)(auto simp add: source_in source_out value_flow[OF f source_out] value_flow[OF g source_out] less_top
                     intro!: diff_le_self_ennreal diff_eq_0_ennreal ennreal_minus_mono)

  fix x
  assume "x \<noteq> source ?\<Delta>" "x \<noteq> sink ?\<Delta>"
  hence x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" by simp_all

  have finite_f_in: "(\<Sum>\<^sup>+ y. f (y, x) * indicator A y) \<noteq> top" for A
    using flowD_finite_IN[OF f, of x]
    by(rule neq_top_trans)(auto simp add: x d_IN_def split: split_indicator intro!: nn_integral_mono)
  have finite_f_out: "(\<Sum>\<^sup>+ y. f (x, y) * indicator A y) \<noteq> top" for A
    using flowD_finite_OUT[OF f, of x]
    by(rule neq_top_trans)(auto simp add: x d_OUT_def split: split_indicator intro!: nn_integral_mono)
  have finite_f[simp]: "f (x, y) \<noteq> top" "f (y, x) \<noteq> top" for y
    using finite_f_in[of "{y}"] finite_f_out[of "{y}"] by auto

  have finite_g_in: "(\<Sum>\<^sup>+ y. g (y, x) * indicator A y) \<noteq> top" for A
    using flowD_finite_IN[OF g, of x]
    by(rule neq_top_trans)(auto simp add: x d_IN_def split: split_indicator intro!: nn_integral_mono)
  have finite_g_out: "(\<Sum>\<^sup>+ y. g (x, y) * indicator A y) \<noteq> top" for A
    using flowD_finite_OUT[OF g x]
    by(rule neq_top_trans)(auto simp add: x d_OUT_def split: split_indicator intro!: nn_integral_mono)
  have finite_g[simp]: "g (x, y) \<noteq> top" "g (y, x) \<noteq> top" for y
    using finite_g_in[of "{y}"] finite_g_out[of "{y}"] by auto

  have "d_OUT (f \<ominus> g) x = (\<Sum>\<^sup>+ y. (f (x, y) - g (x, y)) * indicator \<^bold>E (x, y) * indicator {y. g (x, y) \<le> f (x, y)} y) +
    (\<Sum>\<^sup>+ y. (g (y, x) - f (y, x)) * indicator \<^bold>E (y, x) * indicator {y. f (y, x) < g (y, x)} y)"
    (is "_ = ?out + ?in" is "_ = (\<Sum>\<^sup>+ y\<in>_. _ * ?f_ge_g y) + (\<Sum>\<^sup>+ y\<in>_. _ * ?g_gt_f y)")
    using flowD_finite[OF g]
    apply(subst nn_integral_add[symmetric])
    apply(auto 4 4 simp add: d_OUT_def not_le less_top[symmetric] intro!: nn_integral_cong
           dest!: wf_residual_networkD[OF wf] split: split_indicator intro!: diff_eq_0_ennreal)
    done
  also have "?in = (\<Sum>\<^sup>+ y. (g (y, x) - f (y, x)) * ?g_gt_f y)"
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * ?g_gt_f y) - (\<Sum>\<^sup>+ y. f (y, x) * ?g_gt_f y)" (is "_ = ?g_in - ?f_in")
    using finite_f_in
    by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "?out = (\<Sum>\<^sup>+ y. (f (x, y) - g (x, y)) * ?f_ge_g y)"
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (x, y) * ?f_ge_g y) - (\<Sum>\<^sup>+ y. g (x, y) * ?f_ge_g y)" (is "_ = ?f_out - ?g_out")
    using finite_g_out
    by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "?f_out = d_OUT f x - (\<Sum>\<^sup>+ y. f (x, y) * indicator {y. f (x, y) < g (x, y)} y)" (is "_ = _ - ?f_out_less")
    unfolding d_OUT_def using flowD_finite[OF f] using finite_f_out
    by(subst nn_integral_diff[symmetric])(auto split: split_indicator intro!: nn_integral_cong)
  also have "?g_out = d_OUT g x - (\<Sum>\<^sup>+ y. g (x, y) * indicator {y. f (x, y) < g (x, y)} y)" (is "_ = _ - ?g_less_f")
    unfolding d_OUT_def using flowD_finite[OF g] finite_g_out
    by(subst nn_integral_diff[symmetric])(auto split: split_indicator intro!: nn_integral_cong)
  also have "d_OUT f x - ?f_out_less - (d_OUT g x - ?g_less_f) + (?g_in - ?f_in) =
    (?g_less_f + (d_OUT f x - ?f_out_less)) - d_OUT g x + (?g_in - ?f_in)"
    by (subst diff_diff_ennreal')
       (auto simp: ac_simps d_OUT_def nn_integral_diff[symmetric] finite_g_out finite_f_out intro!: nn_integral_mono split: split_indicator )
  also have "\<dots> = ?g_less_f + d_OUT f x - ?f_out_less - d_OUT g x + (?g_in - ?f_in)"
    by (subst add_diff_eq_ennreal)
       (auto simp: d_OUT_def intro!: nn_integral_mono split: split_indicator)
  also have "\<dots> = d_OUT f x + ?g_less_f - ?f_out_less - d_OUT g x + (?g_in - ?f_in)"
    by (simp add: ac_simps)
  also have "\<dots> = d_OUT f x + (?g_less_f - ?f_out_less) - d_OUT g x + (?g_in - ?f_in)"
    by (subst add_diff_eq_ennreal[symmetric])
       (auto intro!: nn_integral_mono split: split_indicator)
  also have "\<dots> = (?g_in - ?f_in) + ((?g_less_f - ?f_out_less) + d_OUT f x - d_OUT g x)"
    by (simp add: ac_simps)
  also have "\<dots> = ((?g_in - ?f_in) + ((?g_less_f - ?f_out_less) + d_OUT f x)) - d_OUT g x"
    apply (subst add_diff_eq_ennreal)
    apply (simp_all add: d_OUT_def)
    apply (subst nn_integral_diff[symmetric])
    apply (auto simp: AE_count_space finite_f_out nn_integral_add[symmetric] not_less diff_add_cancel_ennreal intro!: nn_integral_mono split: split_indicator)
    done
  also have "\<dots> = ((?g_less_f - ?f_out_less) + (d_OUT f x + (?g_in - ?f_in))) - d_OUT g x"
    by (simp add: ac_simps)
  also have "\<dots> = ((?g_less_f - ?f_out_less) + (d_IN f x + (?g_in - ?f_in))) - d_IN g x"
    unfolding flowD_KIR[OF f x] flowD_KIR[OF g x] ..
  also have "\<dots> = (?g_less_f - ?f_out_less) + ((d_IN f x + (?g_in - ?f_in)) - d_IN g x)"
    apply (subst (2) add_diff_eq_ennreal)
    apply (simp_all add: d_IN_def)
    apply (subst nn_integral_diff[symmetric])
    apply (auto simp: AE_count_space finite_f_in finite_f_out nn_integral_add[symmetric] not_less  ennreal_ineq_diff_add[symmetric]
                intro!: nn_integral_mono split: split_indicator)
    done
  also have "\<dots> = (?g_less_f - ?f_out_less) + (d_IN f x + ?g_in - d_IN g x - ?f_in)"
    by (subst (2) add_diff_eq_ennreal) (auto intro!: nn_integral_mono split: split_indicator simp: diff_diff_commute_ennreal)
  also have "\<dots> = (?g_less_f - ?f_out_less) + (d_IN f x - (d_IN g x - ?g_in) - ?f_in)"
    apply (subst diff_diff_ennreal')
    apply (auto simp: d_IN_def intro!: nn_integral_mono split: split_indicator)
    apply (subst nn_integral_diff[symmetric])
    apply (auto simp: AE_count_space finite_g_in intro!: nn_integral_mono split: split_indicator)
    done
  also have "\<dots> =(d_IN f x - ?f_in) - (d_IN g x - ?g_in) + (?g_less_f - ?f_out_less)"
    by (simp add: ac_simps diff_diff_commute_ennreal)
  also have "?g_less_f - ?f_out_less = (\<Sum>\<^sup>+ y. (g (x, y) - f (x, y)) * indicator {y. f (x, y) < g (x, y)} y)" using finite_f_out
    by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y. (g (x, y) - f (x, y)) * indicator \<^bold>E (x, y) * indicator {y. f (x, y) < g (x, y)} y)" (is "_ = ?diff_out")
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "d_IN f x - ?f_in = (\<Sum>\<^sup>+ y. f (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    unfolding d_IN_def using finite_f_in
    apply(subst nn_integral_diff[symmetric])
    apply(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
    done
  also have "d_IN g x - ?g_in = (\<Sum>\<^sup>+ y. g (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    unfolding d_IN_def using finite_g_in
    by(subst nn_integral_diff[symmetric])(auto simp add: flowD_finite[OF g] AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "(\<Sum>\<^sup>+ y\<in>UNIV. f (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y) - \<dots> = (\<Sum>\<^sup>+ y. (f (y, x) - g (y, x)) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    using finite_g_in
    by(subst nn_integral_diff[symmetric])(auto simp add: flowD_finite[OF g] AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y. (f (y, x) - g (y, x)) * indicator \<^bold>E (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> + ?diff_out = d_IN ?f x"
    using flowD_finite[OF g]
    apply(subst nn_integral_add[symmetric])
    apply(auto 4 4 simp add: d_IN_def not_le less_top[symmetric] intro!: nn_integral_cong
               dest!: wf_residual_networkD[OF wf] split: split_indicator intro: diff_eq_0_ennreal)
    done
  finally show "KIR ?f x" .
qed

lemma value_minus_flow:
  assumes f: "flow \<Delta> f"
  and g: "flow \<Delta> g"
  and value_le: "value_flow \<Delta> g \<le> value_flow \<Delta> f"
  and source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  shows "value_flow \<Delta> (f \<ominus> g) = value_flow \<Delta> f - value_flow \<Delta> g" (is "?value")
proof -
  have "value_flow \<Delta> (f \<ominus> g) = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T (source \<Delta>). (f \<ominus> g) (source \<Delta>, y))"
    by(subst d_OUT_alt_def)(auto simp add: flowD_outside[OF f] flowD_outside[OF g] source_in)
  also have "\<dots> = (\<Sum>\<^sup>+ y. (f (source \<Delta>, y) - g (source \<Delta>, y)) * indicator {x} y)"
    by(subst nn_integral_count_space_indicator)(auto intro!: nn_integral_cong split: split_indicator simp add: outgoing_def source_out)
  also have "\<dots> = f (source \<Delta>, x) - g (source \<Delta>, x)"
    using value_le value_flow[OF f source_out] value_flow[OF g source_out]
    by(auto simp add: one_ennreal_def[symmetric] max_def not_le intro: antisym)
  also have "\<dots> = value_flow \<Delta> f - value_flow \<Delta> g" using f g source_out by(simp add: value_flow)
  finally show ?value .
qed

context
  fixes \<alpha>
  defines "\<alpha> \<equiv> (SUP g\<in>{g. flow \<Delta> g}. value_flow \<Delta> g)"
begin

lemma flow_by_value:
  assumes "v < \<alpha>"
  and real[rule_format]: "\<forall>f. \<alpha> = \<top> \<longrightarrow> flow \<Delta> f \<longrightarrow> value_flow \<Delta> f < \<alpha>"
  obtains f where "flow \<Delta> f" "value_flow \<Delta> f = v"
proof -
  have \<alpha>_pos: "\<alpha> > 0" using assms by (auto simp add: zero_less_iff_neq_zero)
  from \<open>v < \<alpha>\<close> obtain f where f: "flow \<Delta> f" and v: "v < value_flow \<Delta> f"
    unfolding \<alpha>_def less_SUP_iff by blast
  have [simp]: "value_flow \<Delta> f \<noteq> \<top>"
  proof
    assume val: "value_flow \<Delta> f = \<top>"
    from f have "value_flow \<Delta> f \<le> \<alpha>" unfolding \<alpha>_def by(blast intro: SUP_upper2)
    with val have "\<alpha> = \<top>" by (simp add: top_unique)
    from real[OF this f] val show False by simp
  qed
  let ?f = "\<lambda>e. (v / value_flow \<Delta> f) * f e"
  note f
  moreover
  have *: "0 < value_flow \<Delta> f"
    using \<open>v < value_flow \<Delta> f\<close> by (auto simp add: zero_less_iff_neq_zero)
  then have "v / value_flow \<Delta> f \<le> 1" using v
    by (auto intro!: divide_le_posI_ennreal)
  ultimately have "flow \<Delta> ?f" by (rule scale_flow)
  moreover {
    have "value_flow \<Delta> ?f = v * (value_flow \<Delta> f / value_flow \<Delta> f)"
      by(subst value_scale_flow)(simp add: divide_ennreal_def ac_simps)
    also have "\<dots> = v" using * by(subst ennreal_divide_self) (auto simp: less_top[symmetric])
    also note calculation }
  ultimately show ?thesis by(rule that)
qed

theorem ex_max_flow':
  assumes wf: "wf_residual_network"
  assumes source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  and nontrivial: "\<^bold>V - {source \<Delta>, sink \<Delta>} \<noteq> {}"
  and real: "\<alpha> = ennreal \<alpha>'" and \<alpha>'_nonneg[simp]: "0 \<le> \<alpha>'"
  shows "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<alpha> \<and> (\<forall>x. d_IN f x \<le> value_flow \<Delta> f)"
proof -
  have \<alpha>'_not_neg[simp]: "\<not> \<alpha>' < 0"
    using \<alpha>'_nonneg by linarith

  let ?v = "\<lambda>i. (1 - (1 / 2) ^ i) * \<alpha>"
  let ?v_r = "\<lambda>i. ennreal ((1 - (1 / 2) ^ i) * \<alpha>')"
  have v_eq: "?v i = ?v_r i" for i
    by (auto simp: real ennreal_mult power_le_one ennreal_lessI ennreal_minus[symmetric]
                   ennreal_power[symmetric] divide_ennreal_def)
  have "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = ?v i" for i :: nat
  proof(cases "\<alpha> = 0")
    case True thus ?thesis by(auto intro!: exI[where x="\<lambda>_. 0"])
  next
    case False
    then have "?v i < \<alpha>"
      unfolding v_eq by (auto simp: real field_simps intro!: ennreal_lessI) (simp_all add: less_le)
    then obtain f where "flow \<Delta> f" and "value_flow \<Delta> f = ?v i"
      by(rule flow_by_value)(simp add: real)
    thus ?thesis by blast
  qed
  then obtain f_aux where f_aux: "\<And>i. flow \<Delta> (f_aux i)"
    and value_aux: "\<And>i. value_flow \<Delta> (f_aux i) = ?v_r i"
    unfolding v_eq by moura

  define f_i where "f_i = rec_nat (\<lambda>_. 0) (\<lambda>i f_i.
    let g = f_aux (Suc i) \<ominus> f_i;
      k_i = SOME k. k \<le> g \<and> flow (residual_network f_i) k \<and> value_flow (residual_network f_i) k = value_flow (residual_network f_i) g \<and> (\<forall>x. d_IN k x \<le> value_flow (residual_network f_i) k)
    in f_i \<oplus> k_i)"
  let ?P = "\<lambda>i k. k \<le> f_aux (Suc i) \<ominus> f_i i \<and> flow (residual_network (f_i i)) k \<and> value_flow (residual_network (f_i i)) k = value_flow (residual_network (f_i i)) (f_aux (Suc i) \<ominus> f_i i) \<and> (\<forall>x. d_IN k x \<le> value_flow (residual_network (f_i i)) k)"
  define k_i where "k_i i = Eps (?P i)" for i

  have f_i_simps [simp]: "f_i 0 = (\<lambda>_. 0)" "f_i (Suc i) = f_i i \<oplus> k_i i" for i
    by(simp_all add: f_i_def Let_def k_i_def)

  have k_i: "flow (residual_network (f_i i)) (k_i i)" (is ?k_i)
    and value_k_i: "value_flow (residual_network (f_i i)) (k_i i) = value_flow (residual_network (f_i i)) (f_aux (Suc i) \<ominus> f_i i)" (is "?value_k_i")
    and IN_k_i: "d_IN (k_i i) x \<le> value_flow (residual_network (f_i i)) (k_i i)" (is "?IN_k_i")
    and value_diff: "value_flow (residual_network (f_i i)) (f_aux (Suc i) \<ominus> f_i i) = value_flow \<Delta> (f_aux (Suc i)) - value_flow \<Delta> (f_i i)" (is "?value_diff")
    if "flow_network \<Delta> (f_i i)" and value_f_i: "value_flow \<Delta> (f_i i) = value_flow \<Delta> (f_aux i)" for i x
  proof -
    let ?RES = "residual_network (f_i i)"
    interpret fn: flow_network \<Delta> "f_i i" by(rule that)
    interpret RES: flow_attainability "?RES" using wf fn.g by(rule residual_flow_attainability)
    have le: "value_flow \<Delta> (f_i i) \<le> value_flow \<Delta> (f_aux (Suc i))"
      unfolding value_aux value_f_i
      unfolding v_eq by (rule ennreal_leI) (auto simp: field_simps)
    with wf f_aux fn.g have res_flow: "flow ?RES (f_aux (Suc i) \<ominus> f_i i)"
      using flowD_finite[OF f_aux] source_out
      by(rule minus_flow)
    show value': ?value_diff by(simp add: value_minus_flow[OF f_aux fn.g le source_out])
    also have "\<dots> < \<top>"
      unfolding value_aux v_eq by (auto simp: less_top[symmetric])
    finally have "value_flow ?RES (f_aux (Suc i) \<ominus> f_i i) \<noteq> \<top>" by simp
    then have fn': "flow_network ?RES (f_aux (Suc i) \<ominus> f_i i)"
      using nontrivial res_flow by(unfold_locales) simp_all
    then interpret fn': flow_network "?RES" "f_aux (Suc i) \<ominus> f_i i" .
    from fn'.flow_cleanup show ?k_i ?value_k_i ?IN_k_i unfolding k_i_def by(rule someI2_ex; blast)+
  qed

  have fn_i: "flow_network \<Delta> (f_i i)"
    and value_f_i: "value_flow \<Delta> (f_i i) = value_flow \<Delta> (f_aux i)"
    and d_IN_i: "d_IN (f_i i) x \<le> value_flow \<Delta> (f_i i)"  for i x
  proof(induction i)
    case 0
    { case 1 show ?case using nontrivial by(unfold_locales)(simp_all add: f_aux value_aux) }
    { case 2 show ?case by(simp add: value_aux) }
    { case 3 show ?case by(simp) }
  next
    case (Suc i)
    interpret fn: flow_network \<Delta> "f_i i" using Suc.IH(1) .
    let ?RES = "residual_network (f_i i)"

    have k_i: "flow ?RES (k_i i)"
      and value_k_i: "value_flow ?RES (k_i i) = value_flow ?RES (f_aux (Suc i) \<ominus> f_i i)"
      and d_IN_k_i: "d_IN (k_i i) x \<le> value_flow ?RES (k_i i)" for x
      using Suc.IH(1-2) by(rule k_i value_k_i IN_k_i)+

    interpret RES: flow_attainability "?RES" using wf fn.g by(rule residual_flow_attainability)
    have le: "value_flow \<Delta> (f_i i) \<le> value_flow \<Delta> (f_aux (Suc i))"
      unfolding value_aux Suc.IH(2) v_eq using \<alpha>'_nonneg by(intro ennreal_leI)(simp add: real field_simps)
    { case 1 show ?case unfolding f_i_simps
      proof
        show "flow \<Delta> (f_i i \<oplus> k_i i)" using wf fn.g k_i by(rule flow_residual_add)
        with RES.flowD_finite[OF k_i] show "value_flow \<Delta> (f_i i \<oplus> k_i i) \<noteq> \<top>"
          by(simp add: value_flow[OF _ source_out])
      qed(rule nontrivial) }
    from value_k_i have value_k: "value_flow ?RES (k_i i) = value_flow \<Delta> (f_aux (Suc i)) - value_flow \<Delta> (f_aux i)"
      by(simp add: value_minus_flow[OF f_aux fn.g le source_out] Suc.IH)
    { case 2 show ?case using value_k
        by(auto simp add: source_out value_plus_flow[OF wf fn.g k_i] Suc.IH value_aux field_simps intro!: ennreal_leI) }
    note value_f = this
    { case 3
      have "d_IN (f_i i \<oplus> k_i i) x \<le> d_IN (f_i i) x + d_IN (k_i i) x"
        using fn.g k_i by(rule d_IN_plus_flow[OF wf])
      also have "\<dots> \<le> value_flow \<Delta> (f_i i) + d_IN (k_i i) x" using Suc.IH(3) by(rule add_right_mono)
      also have "\<dots> \<le> value_flow \<Delta> (f_i i) + value_flow ?RES (k_i i)" using d_IN_k_i by(rule add_left_mono)
      also have "\<dots> = value_flow \<Delta> (f_i (Suc i))" unfolding value_f Suc.IH(2) value_k
        by(auto simp add: value_aux field_simps intro!: ennreal_leI)
      finally show ?case by simp }
  qed
  interpret fn: flow_network \<Delta> "f_i i" for i by(rule fn_i)
  note k_i = k_i[OF fn_i value_f_i] and value_k_i = value_k_i[OF fn_i value_f_i]
    and IN_k_i = IN_k_i[OF fn_i value_f_i] and value_diff = value_diff[OF fn_i value_f_i]

  have "\<exists>x\<ge>0. f_i i e = ennreal x" for i e
    using fn.finite_g[of i e] by (cases "f_i i e") auto
  then obtain f_i' where f_i': "\<And>i e. f_i i e = ennreal (f_i' i e)" and [simp]: "\<And>i e. 0 \<le> f_i' i e"
    by metis

  { fix i e
    obtain x y :: 'v where e: "e = (x, y)" by(cases e)
    have "k_i i (x, y) \<le> d_IN (k_i i) y" by (rule d_IN_ge_point)
    also have "\<dots> \<le> value_flow (residual_network (f_i i)) (k_i i)" by(rule IN_k_i)
    also have "\<dots> < \<top>" using value_k_i[of i] value_diff[of i]
      by(simp add: value_k_i value_f_i value_aux real less_top[symmetric])
    finally have "\<exists>x\<ge>0. k_i i e = ennreal x"
      by(cases "k_i i e")(auto simp add: e) }
  then obtain k_i' where k_i': "\<And>i e. k_i i e = ennreal (k_i' i e)" and k_i'_nonneg[simp]: "\<And>i e. 0 \<le> k_i' i e"
    by metis

  have wf_k: "(x, y) \<in> \<^bold>E \<Longrightarrow> k_i i (y, x) \<le> f_i i (x, y) + k_i i (x, y)" for i x y
    using flowD_capacity[OF k_i, of i "(y, x)"]
    by (auto split: if_split_asm dest: wf_residual_networkD[OF wf] elim: order_trans)

  have f_i'_0[simp]: "f_i' 0 = (\<lambda>_. 0)" using f_i_simps(1) by (simp del: f_i_simps add: fun_eq_iff f_i')

  have f_i'_Suc[simp]: "f_i' (Suc i) e =  (if e \<in> \<^bold>E then f_i' i e + (k_i' i e - k_i' i (prod.swap e)) else 0)" for i e
    using f_i_simps(2)[of i, unfolded fun_eq_iff, THEN spec, of e] wf_k[of "fst e" "snd e" i]
    by (auto simp del: f_i_simps ennreal_plus
             simp add: fun_eq_iff f_i' k_i' ennreal_plus[symmetric] ennreal_minus split: if_split_asm)

  have k_i'_le: "k_i' i e \<le> \<alpha>' / 2 ^ (Suc i)" for i e
  proof -
    obtain x y where e: "e = (x, y)" by(cases e)
    have "k_i' i (x, y) \<le> d_IN (k_i' i) y" by (rule d_IN_ge_point)
    also have "\<dots> \<le> value_flow (residual_network (f_i i)) (k_i' i)"
      using IN_k_i[of i y] by(simp add: k_i'[abs_def])
    also have "\<dots> = \<alpha>' / 2 ^ (Suc i)" using value_k_i[of i] value_diff[of i]
      by(simp add: value_f_i value_aux real k_i'[abs_def] field_simps ennreal_minus mult_le_cancel_left1)
    finally show ?thesis using e by simp
  qed

  have convergent: "convergent (\<lambda>i. f_i' i e)" for e
  proof(cases "\<alpha>' > 0")
    case False
    obtain x y where [simp]: "e = (x, y)" by(cases e)

    { fix i
      from False \<alpha>'_nonneg have "\<alpha>' = 0" by simp
      moreover have "f_i i (x, y) \<le> d_IN (f_i i) y" by (rule d_IN_ge_point)
      ultimately have "f_i i (x, y) = 0" using d_IN_i[of i y]
        by(simp add: value_f_i value_aux real) }
    thus ?thesis by(simp add: f_i' convergent_const)
  next
    case \<alpha>'_pos: True
    show ?thesis
    proof(rule real_Cauchy_convergent Cauchy_real_Suc_diff)+
      fix n
      have "\<bar>k_i' n e - k_i' n (prod.swap e)\<bar> \<le> \<bar>k_i' n e\<bar> + \<bar>k_i' n (prod.swap e)\<bar>"
        by (rule abs_triangle_ineq4)
      then have "\<bar>k_i' n e - k_i' n (prod.swap e)\<bar> \<le> \<alpha>' / 2 ^ n"
        using k_i'_le[of n e] k_i'_le[of n "prod.swap e"] by simp
      then have "\<bar>f_i' (Suc n) e - f_i' n e\<bar> \<le> \<alpha>' / 2 ^ n"
        using flowD_outside[OF fn.g] by (cases e) (auto simp: f_i')
      thus "\<bar>f_i' (Suc n) e - f_i' n e\<bar> \<le> \<alpha>' / 2 ^ n" by simp
    qed simp
  qed
  then obtain f' where f': "\<And>e. (\<lambda>i. f_i' i e) \<longlonglongrightarrow> f' e" unfolding convergent_def by metis
  hence f: "\<And>e. (\<lambda>i. f_i i e) \<longlonglongrightarrow> ennreal (f' e)" unfolding f_i' by simp

  have f'_nonneg: "0 \<le> f' e" for e
    by (rule LIMSEQ_le_const[OF f']) auto

  let ?k = "\<lambda>i x y. (k_i' i (x, y) - k_i' i (y, x)) * indicator \<^bold>E (x, y)"
  have sum_i': "f_i' i (x, y) = (\<Sum>j<i. ?k j x y)" for x y i
    by (induction i) auto

  have summable_nk: "summable (\<lambda>i. \<bar>?k i x y\<bar>)" for x y
  proof(rule summable_rabs_comparison_test)
    show "\<exists>N. \<forall>i\<ge>N. \<bar>?k i x y\<bar> \<le> \<alpha>' * (1 / 2) ^ i"
    proof (intro exI allI impI)
      fix i have "\<bar>?k i x y\<bar> \<le> k_i' i (x, y) + k_i' i (y, x)"
        by (auto intro!: abs_triangle_ineq4[THEN order_trans] split: split_indicator)
      also have "\<dots> \<le> \<alpha>' * (1 / 2) ^ i"
        using k_i'_le[of i "(x, y)"] k_i'_le[of i "(y, x)"] \<alpha>'_nonneg k_i'_nonneg[of i "(x, y)"] k_i'_nonneg[of i "(y, x)"]
        by(auto simp add: abs_real_def power_divide split: split_indicator)
      finally show "\<bar>?k i x y\<bar> \<le> \<alpha>' * (1 / 2) ^ i"
        by simp
    qed
    show "summable (\<lambda>i. \<alpha>' * (1 / 2) ^ i)"
      by(rule summable_mult complete_algebra_summable_geometric)+ simp
  qed
  hence summable_k: "summable (\<lambda>i. ?k i x y)" for x y by(auto intro: summable_norm_cancel)

  have suminf: "(\<Sum>i. (k_i' i (x, y) - k_i' i (y, x)) * indicator \<^bold>E (x, y)) = f' (x, y)" for x y
    by(rule LIMSEQ_unique[OF summable_LIMSEQ])(simp_all add: sum_i'[symmetric] f' summable_k)

  have flow: "flow \<Delta> f'"
  proof
    fix e
    have "f' e \<le> Sup {..capacity \<Delta> e}" using _ f
      by(rule Sup_lim)(simp add: flowD_capacity[OF fn.g])
    then show "f' e \<le> capacity \<Delta> e" by simp
  next
    fix x
    assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"

    have integrable_f_i: "integrable (count_space UNIV) (\<lambda>y. f_i' i (x, y))" for i
      using flowD_finite_OUT[OF fn.g x, of i] by(auto intro!: integrableI_bounded simp add: f_i' d_OUT_def less_top)
    have integrable_f_i': "integrable (count_space UNIV) (\<lambda>y. f_i' i (y, x))" for i
      using flowD_finite_IN[OF fn.g, of x i] x by(auto intro!: integrableI_bounded simp add: f_i' d_IN_def less_top)

    have integral_k_bounded: "(\<Sum>\<^sup>+ y. norm (?k i x y)) \<le> \<alpha>' / 2 ^ i" (is ?thesis1)
      and integral_k'_bounded: "(\<Sum>\<^sup>+ y. norm (?k i y x)) \<le> \<alpha>' / 2 ^ i" (is ?thesis2) for i
    proof -
      define b where "b = (\<Sum>\<^sup>+ y. k_i i (x, y) + k_i i (y, x))"
      have "b = d_OUT (k_i i) x + d_IN (k_i i) x" unfolding b_def
        by(subst nn_integral_add)(simp_all add: d_OUT_def d_IN_def)
      also have "d_OUT (k_i i) x = d_IN (k_i i) x" using k_i by(rule flowD_KIR)(simp_all add: x)
      also have "\<dots> + \<dots> \<le> value_flow \<Delta> (k_i i) + value_flow \<Delta> (k_i i)"
        using IN_k_i[of i x, simplified] by-(rule add_mono)
      also have "\<dots> \<le> \<alpha>' / 2 ^ i" using value_k_i[of i] value_diff[of i]
        by(simp add: value_aux value_f_i  field_simps ennreal_minus_if ennreal_plus_if mult_le_cancel_left1
                del: ennreal_plus)
      also have "(\<Sum>\<^sup>+ y\<in>UNIV. norm (?k i x y)) \<le> b" and "(\<Sum>\<^sup>+ y. norm (?k i y x)) \<le> b" unfolding b_def
        by(rule nn_integral_mono; simp add: abs_real_def k_i' ennreal_plus_if del:  ennreal_plus split: split_indicator)+
      ultimately show ?thesis1 ?thesis2 by(auto)
    qed

    have integrable_k: "integrable (count_space UNIV) (\<lambda>y. ?k i x y)"
      and integrable_k': "integrable (count_space UNIV) (\<lambda>y. ?k i y x)" for i
      using integral_k_bounded[of i] integral_k'_bounded[of i] real
      by(auto intro!: integrableI_bounded simp: less_top[symmetric] top_unique ennreal_divide_eq_top_iff)

    have summable'_k: "summable (\<lambda>i. \<integral> y. \<bar>?k i x y\<bar> \<partial>count_space UNIV)"
    proof(rule summable_comparison_test)
      have "\<bar>\<integral> y. \<bar>?k i x y\<bar> \<partial>count_space UNIV\<bar> \<le> \<alpha>' * (1 / 2) ^ i" for i
        using integral_norm_bound_ennreal[OF integrable_norm, OF integrable_k, of i] integral_k_bounded[of i]
        by(bestsimp simp add: real power_divide dest: order_trans)
      thus "\<exists>N. \<forall>i\<ge>N. norm (\<integral> y. \<bar>?k i x y\<bar> \<partial>count_space UNIV) \<le> \<alpha>' * (1 / 2) ^ i"
        by auto
      show "summable (\<lambda>i. \<alpha>' * (1 / 2) ^ i)"
        by(rule summable_mult complete_algebra_summable_geometric)+ simp
    qed
    have summable'_k': "summable (\<lambda>i. \<integral> y. \<bar>?k i y x\<bar> \<partial>count_space UNIV)"
    proof(rule summable_comparison_test)
      have "\<bar>\<integral> y. \<bar>?k i y x\<bar> \<partial>count_space UNIV\<bar> \<le> \<alpha>' * (1 / 2) ^ i" for i
        using integral_norm_bound_ennreal[OF integrable_norm, OF integrable_k', of i] integral_k'_bounded[of i]
        by(bestsimp simp add: real power_divide dest: order_trans)
      thus "\<exists>N. \<forall>i\<ge>N. norm (\<integral> y. \<bar>?k i y x\<bar> \<partial>count_space UNIV) \<le> \<alpha>' * (1 / 2) ^ i" by auto
      show "summable (\<lambda>i. \<alpha>' * (1 / 2) ^ i)"
        by(rule summable_mult complete_algebra_summable_geometric)+ simp
    qed

    have "(\<lambda>i. \<integral> y. ?k i x y \<partial>count_space UNIV) sums \<integral> y. (\<Sum>i. ?k i x y) \<partial>count_space UNIV"
      using integrable_k by(rule sums_integral)(simp_all add: summable_nk summable'_k)
    also have "\<dots> = \<integral> y. f' (x, y) \<partial>count_space UNIV" by(rule Bochner_Integration.integral_cong[OF refl])(rule suminf)
    finally have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j x y \<partial>count_space UNIV) \<longlonglongrightarrow> \<dots>" unfolding sums_def .
    also have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j x y \<partial>count_space UNIV) = (\<lambda>i. \<integral> y. f_i' i (x, y) \<partial>count_space UNIV)"
      unfolding sum_i' by(rule ext Bochner_Integration.integral_sum[symmetric] integrable_k)+
    finally have "(\<lambda>i. ennreal (\<integral> y. f_i' i (x, y) \<partial>count_space UNIV)) \<longlonglongrightarrow> ennreal (\<integral> y. f' (x, y) \<partial>count_space UNIV)" by simp
    also have "(\<lambda>i. ennreal (\<integral> y. f_i' i (x, y) \<partial>count_space UNIV)) = (\<lambda>i. d_OUT (f_i i) x)"
      unfolding d_OUT_def f_i' by(rule ext nn_integral_eq_integral[symmetric] integrable_f_i)+ simp
    also have "ennreal (\<integral> y. f' (x, y) \<partial>count_space UNIV) = d_OUT f' x"
      unfolding d_OUT_def by(rule nn_integral_eq_integral[symmetric])(simp_all add: f'_nonneg, simp add: suminf[symmetric] integrable_suminf integrable_k summable_nk summable'_k)
    also have "(\<lambda>i. d_OUT (f_i i) x) = (\<lambda>i. d_IN (f_i i) x)"
      using flowD_KIR[OF fn.g x] by(simp)
    finally have *: "(\<lambda>i. d_IN (f_i i) x) \<longlonglongrightarrow> d_OUT (\<lambda>x. ennreal (f' x)) x" .

    have "(\<lambda>i. \<integral> y. ?k i y x \<partial>count_space UNIV) sums \<integral> y. (\<Sum>i. ?k i y x) \<partial>count_space UNIV"
      using integrable_k' by(rule sums_integral)(simp_all add: summable_nk summable'_k')
    also have "\<dots> = \<integral> y. f' (y, x) \<partial>count_space UNIV" by(rule Bochner_Integration.integral_cong[OF refl])(rule suminf)
    finally have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j y x \<partial>count_space UNIV) \<longlonglongrightarrow> \<dots>" unfolding sums_def .
    also have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j y x \<partial>count_space UNIV) = (\<lambda>i. \<integral> y. f_i' i (y, x) \<partial>count_space UNIV)"
      unfolding sum_i' by(rule ext Bochner_Integration.integral_sum[symmetric] integrable_k')+
    finally have "(\<lambda>i. ennreal (\<integral> y. f_i' i (y, x) \<partial>count_space UNIV)) \<longlonglongrightarrow> ennreal (\<integral> y. f' (y, x) \<partial>count_space UNIV)" by simp
    also have "(\<lambda>i. ennreal (\<integral> y. f_i' i (y, x) \<partial>count_space UNIV)) = (\<lambda>i. d_IN (f_i i) x)"
      unfolding d_IN_def f_i' by(rule ext nn_integral_eq_integral[symmetric] integrable_f_i')+ simp
    also have "ennreal (\<integral> y. f' (y, x) \<partial>count_space UNIV) = d_IN f' x"
      unfolding d_IN_def by(rule nn_integral_eq_integral[symmetric])(simp_all add: f'_nonneg, simp add: suminf[symmetric] integrable_suminf integrable_k' summable_nk summable'_k')
    finally show "d_OUT f' x = d_IN f' x" using * by(blast intro: LIMSEQ_unique)
  qed
  moreover
  { have "incseq (\<lambda>i. value_flow \<Delta> (f_i i))"
      by(rule incseq_SucI)(simp add: value_aux value_f_i real field_simps \<alpha>'_nonneg ennreal_leI del: f_i_simps)
    then have "(\<lambda>i. value_flow \<Delta> (f_i i)) \<longlonglongrightarrow> (SUP i. value_flow \<Delta> (f_i i))" by(rule LIMSEQ_SUP)
    also have "(SUP i. value_flow \<Delta> (f_i i)) = \<alpha>"
    proof -
      have "\<alpha> - (SUP i. value_flow \<Delta> (f_i i)) = (INF i. \<alpha> - value_flow \<Delta> (f_i i))"
        by(simp add: ennreal_SUP_const_minus real)
      also have "\<alpha> - value_flow \<Delta> (f_i i) = \<alpha>' / 2 ^ i" for i
        by(simp add: value_f_i value_aux real ennreal_minus_if field_simps mult_le_cancel_left1)
      hence "(INF i. \<alpha> - value_flow \<Delta> (f_i i)) = (INF i. ennreal (\<alpha>' / 2  ^ i))"
        by(auto intro: INF_cong)
      also have "\<dots> = 0"
      proof(rule LIMSEQ_unique)
        show "(\<lambda>i. \<alpha>' / 2 ^ i) \<longlonglongrightarrow> (INF i. ennreal (\<alpha>' / 2  ^ i))"
          by(rule LIMSEQ_INF)(simp add: field_simps real decseq_SucI)
      qed(simp add: LIMSEQ_divide_realpow_zero real ennreal_0[symmetric] del: ennreal_0)
      finally show "(SUP i. value_flow \<Delta> (f_i i)) = \<alpha>"
        apply (intro antisym)
        apply (auto simp: \<alpha>_def intro!: SUP_mono fn.g) []
        apply (rule ennreal_minus_eq_0)
        apply assumption
        done
    qed
    also have "(\<lambda>i. value_flow \<Delta> (f_i i)) \<longlonglongrightarrow> value_flow \<Delta> f'"
      by(simp add: value_flow[OF flow source_out] value_flow[OF fn.g source_out] f)
    ultimately have "value_flow \<Delta> f' = \<alpha>" by(blast intro: LIMSEQ_unique) }
  note value_f = this
  moreover {
    fix x
    have "d_IN f' x = \<integral>\<^sup>+ y. liminf (\<lambda>i. f_i i (y, x)) \<partial>count_space UNIV" unfolding d_IN_def using f
      by(simp add: tendsto_iff_Liminf_eq_Limsup)
    also have "\<dots> \<le> liminf (\<lambda>i. d_IN (f_i i) x)" unfolding d_IN_def
      by(rule nn_integral_liminf)(simp_all add:)
    also have "\<dots> \<le> liminf (\<lambda>i. \<alpha>)" using d_IN_i[of _ x] fn.g
      by(auto intro!: Liminf_mono SUP_upper2 eventually_sequentiallyI simp add: \<alpha>_def)
    also have "\<dots> = value_flow \<Delta> f'" using value_f by(simp add: Liminf_const)
    also note calculation
  } ultimately show ?thesis by blast
qed

theorem ex_max_flow'': \<comment> \<open>eliminate assumption of no antiparallel edges using locale @{const wf_residual_network}\<close>
  assumes source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  and nontrivial: "\<^bold>E \<noteq> {}"
  and real: "\<alpha> = ennreal \<alpha>'" and nn[simp]: "0 \<le> \<alpha>'"
  shows "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<alpha> \<and> (\<forall>x. d_IN f x \<le> value_flow \<Delta> f)"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': flow_attainability \<Delta>''
    by(rule \<Delta>''_flow_attainability flow_attainability.axioms(2))+unfold_locales
  have wf_\<Delta>'': "\<Delta>''.wf_residual_network"
    by(rule \<Delta>''_wf_residual_network; simp add: no_loop)

  have source_out': "edge \<Delta>'' (source \<Delta>'') y \<longleftrightarrow> y = Edge (source \<Delta>) x" for y
    by(auto simp add: source_out)
  have nontrivial': "\<^bold>V\<^bsub>\<Delta>''\<^esub> - {source \<Delta>'', sink \<Delta>''} \<noteq> {}" using nontrivial by(auto simp add: "\<^bold>V_\<Delta>''")

  have "(SUP g \<in> {g. flow \<Delta>'' g}. value_flow \<Delta>'' g) = (SUP g \<in> {g. flow \<Delta> g}. value_flow \<Delta> g)" (is "?lhs = ?rhs")
  proof(intro antisym SUP_least; unfold mem_Collect_eq)
    fix g
    assume g: "flow \<Delta>'' g"
    hence "value_flow \<Delta>'' g = value_flow \<Delta> (collect g)" by(simp add: value_collect)
    also { from g have "flow \<Delta> (collect g)" by simp }
    then have "\<dots> \<le> ?rhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta>'' g \<le> \<dots>" .
  next
    fix g
    assume g: "flow \<Delta> g"
    hence "value_flow \<Delta> g = value_flow \<Delta>'' (split g)" by simp
    also { from g have "flow \<Delta>'' (split g)" by simp }
    then have "\<dots> \<le> ?lhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta> g \<le> ?lhs" .
  qed
  with real have eq: "(SUP g \<in> {g. flow \<Delta>'' g}. value_flow \<Delta>'' g) = ennreal \<alpha>'" by(simp add: \<alpha>_def)
  from \<Delta>''.ex_max_flow'[OF wf_\<Delta>'' source_out' nontrivial' eq]
  obtain f where f: "flow \<Delta>'' f"
    and "value_flow \<Delta>'' f = \<alpha>"
    and IN: "\<And>x. d_IN f x \<le> value_flow \<Delta>'' f" unfolding eq real using nn by blast
  hence "flow \<Delta> (collect f)" and "value_flow \<Delta> (collect f) = \<alpha>" by(simp_all add: value_collect)
  moreover {
    fix x
    have "d_IN (collect f) x = (\<Sum>\<^sup>+ y\<in>range (\<lambda>y. Edge y x). f (y, Vertex x))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> \<le> d_IN f (Vertex x)" unfolding d_IN_def
      by (auto intro!: nn_integral_mono simp add: nn_integral_count_space_indicator split: split_indicator)
    also have "\<dots> \<le> value_flow \<Delta> (collect f)" using IN[of "Vertex x"] f by(simp add: value_collect)
    also note calculation }
  ultimately show ?thesis by blast
qed

context begin \<comment> \<open>We eliminate the assumption of only one edge leaving the source by introducing a new source vertex.\<close>
private datatype (plugins del: transfer size) 'v' node = SOURCE | Inner (inner: 'v')

private lemma not_Inner_conv: "x \<notin> range Inner \<longleftrightarrow> x = SOURCE"
by(cases x) auto

private lemma inj_on_Inner [simp]: "inj_on Inner A"
by(simp add: inj_on_def)

private inductive edge' :: "'v node \<Rightarrow> 'v node \<Rightarrow> bool"
where
  SOURCE: "edge' SOURCE (Inner (source \<Delta>))"
| Inner: "edge \<Delta> x y \<Longrightarrow> edge' (Inner x) (Inner y)"

private inductive_simps edge'_simps [simp]:
  "edge' SOURCE x"
  "edge' (Inner y) x"
  "edge' y SOURCE"
  "edge' y (Inner x)"

private fun capacity' :: "'v node flow"
where
  "capacity' (SOURCE, Inner x) = (if x = source \<Delta> then \<alpha> else 0)"
| "capacity' (Inner x, Inner y) = capacity \<Delta> (x, y)"
| "capacity' _ = 0"

private lemma capacity'_source_in [simp]: "capacity' (y, Inner (source \<Delta>)) = (if y = SOURCE then \<alpha> else 0)"
by(cases y)(simp_all add: capacity_outside source_in)

private definition \<Delta>' :: "'v node network"
where "\<Delta>' = \<lparr>edge = edge', capacity = capacity', source = SOURCE, sink = Inner (sink \<Delta>)\<rparr>"

private lemma \<Delta>'_sel [simp]:
  "edge \<Delta>' = edge'"
  "capacity \<Delta>' = capacity'"
  "source \<Delta>' = SOURCE"
  "sink \<Delta>' = Inner (sink \<Delta>)"
by(simp_all add: \<Delta>'_def)

private lemma "\<^bold>E_\<Delta>'": "\<^bold>E\<^bsub>\<Delta>'\<^esub> = {(SOURCE, Inner (source \<Delta>))} \<union> (\<lambda>(x, y). (Inner x, Inner y)) ` \<^bold>E"
by(auto elim: edge'.cases)

private lemma \<Delta>'_countable_network:
  assumes "\<alpha> \<noteq> \<top>"
  shows "countable_network \<Delta>'"
proof
  show "countable \<^bold>E\<^bsub>\<Delta>'\<^esub>" unfolding "\<^bold>E_\<Delta>'" by simp
  show "source \<Delta>' \<noteq> sink \<Delta>'" by simp
  show "capacity \<Delta>' e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Delta>'\<^esub>" for e using that unfolding "\<^bold>E_\<Delta>'"
    by(cases e rule: capacity'.cases)(auto intro: capacity_outside)
  show "capacity \<Delta>' e \<noteq> \<top>" for e by(cases e rule: capacity'.cases)(simp_all add: assms)
qed

private lemma \<Delta>'_flow_attainability:
  assumes "\<alpha> \<noteq> \<top>"
  shows "flow_attainability \<Delta>'"
proof -
  interpret \<Delta>': countable_network \<Delta>' using assms by(rule \<Delta>'_countable_network)
  show ?thesis
  proof
    show "d_IN (capacity \<Delta>') x \<noteq> \<top> \<or> d_OUT (capacity \<Delta>') x \<noteq> \<top>" if sink: "x \<noteq> sink \<Delta>'" for x
    proof(cases x)
      case (Inner x')
      consider (source) "x' = source \<Delta>" | (IN) "x' \<noteq> source \<Delta>" "d_IN (capacity \<Delta>) x' \<noteq> \<top>" | (OUT) "d_OUT (capacity \<Delta>) x' \<noteq> \<top>"
        using finite_capacity[of x'] sink Inner by(auto)
      thus ?thesis
      proof(cases)
        case source
        with Inner have "d_IN (capacity \<Delta>') x = (\<Sum>\<^sup>+ y. \<alpha> * indicator {SOURCE :: 'v node} y)"
          unfolding d_IN_def by(intro nn_integral_cong)(simp split: split_indicator)
        also have "\<dots> = \<alpha>" by(simp add: max_def)
        finally show ?thesis using assms by simp
      next
        case IN
        with Inner have "d_IN (capacity \<Delta>') x = (\<Sum>\<^sup>+ y\<in>range Inner. capacity \<Delta> (node.inner y, x'))"
          by(auto simp add: d_IN_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
        also have "\<dots> = d_IN (capacity \<Delta>) x'" unfolding d_IN_def
          by(simp add: nn_integral_count_space_reindex)
        finally show ?thesis using Inner sink IN by(simp)
      next
        case OUT
        from Inner have "d_OUT (capacity \<Delta>') x = (\<Sum>\<^sup>+ y\<in>range Inner. capacity \<Delta> (x', node.inner y))"
          by(auto simp add: d_OUT_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
        also have "\<dots> = d_OUT (capacity \<Delta>) x'" by(simp add: d_OUT_def nn_integral_count_space_reindex)
        finally show ?thesis using OUT by auto
      qed
    qed(simp add: d_IN_def)
    show "\<not> edge \<Delta>' x x" for x by(cases x)(simp_all add: no_loop)
    show "\<not> edge \<Delta>' x (source \<Delta>')" for x by simp
  qed
qed

private fun lift :: "'v flow \<Rightarrow> 'v node flow"
where
  "lift f (SOURCE, Inner y) = (if y = source \<Delta> then value_flow \<Delta> f else 0)"
| "lift f (Inner x, Inner y) = f (x, y)"
| "lift f _ = 0"

private lemma d_OUT_lift_Inner [simp]: "d_OUT (lift f) (Inner x) = d_OUT f x" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y\<in>range Inner. lift f (Inner x, y))"
    by(auto simp add: d_OUT_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_OUT_def)
  finally show ?thesis .
qed

private lemma d_OUT_lift_SOURCE [simp]: "d_OUT (lift f) SOURCE = value_flow \<Delta> f" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y. lift f (SOURCE, y) * indicator {Inner (source \<Delta>)} y)"
    unfolding d_OUT_def by(rule nn_integral_cong)(case_tac x; simp)
  also have "\<dots> = ?rhs" by(simp add: nn_integral_count_space_indicator max_def)
  finally show ?thesis .
qed

private lemma d_IN_lift_Inner [simp]:
  assumes "x \<noteq> source \<Delta>"
  shows "d_IN (lift f) (Inner x) = d_IN f x" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y\<in>range Inner. lift f (y, Inner x))" using assms
    by(auto simp add: d_IN_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_IN_def)
  finally show ?thesis .
qed

private lemma d_IN_lift_source [simp]: "d_IN (lift f) (Inner (source \<Delta>)) = value_flow \<Delta> f + d_IN f (source \<Delta>)" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y. lift f (y, Inner (source \<Delta>)) * indicator {SOURCE} y) + (\<Sum>\<^sup>+ y\<in>range Inner. lift f (y, Inner (source \<Delta>)))"
    (is "_ = ?SOURCE + ?rest")
    unfolding d_IN_def
    apply(subst nn_integral_count_space_indicator, simp)
    apply(subst nn_integral_add[symmetric])
    apply(auto simp add: AE_count_space max_def not_Inner_conv split: split_indicator intro!: nn_integral_cong)
    done
  also have "?rest = d_IN f (source \<Delta>)" by(simp add: nn_integral_count_space_reindex d_IN_def)
  also have "?SOURCE = value_flow \<Delta> f"
    by(simp add: max_def one_ennreal_def[symmetric] )
  finally show ?thesis .
qed

private lemma flow_lift [simp]:
  assumes "flow \<Delta> f"
  shows "flow \<Delta>' (lift f)"
proof
  show "lift f e \<le> capacity \<Delta>' e" for e
    by(cases e rule: capacity'.cases)(auto intro: flowD_capacity[OF assms] simp add: \<alpha>_def intro: SUP_upper2 assms)

  fix x
  assume x: "x \<noteq> source \<Delta>'" "x \<noteq> sink \<Delta>'"
  then obtain x' where x': "x = Inner x'" by(cases x) auto
  then show "KIR (lift f) x" using x
    by(cases "x' = source \<Delta>")(auto simp add: flowD_source_IN[OF assms] dest: flowD_KIR[OF assms])
qed

private abbreviation (input) unlift :: "'v node flow \<Rightarrow> 'v flow"
where "unlift f \<equiv> (\<lambda>(x, y). f (Inner x, Inner y))"

private lemma flow_unlift [simp]:
  assumes f: "flow \<Delta>' f"
  shows "flow \<Delta> (unlift f)"
proof
  show "unlift f e \<le> capacity \<Delta> e" for e using flowD_capacity[OF f, of "map_prod Inner Inner e"]
    by(cases e)(simp)
next
  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT (unlift f) x = (\<Sum>\<^sup>+ y\<in>range Inner. f (Inner x, y))"
    by(simp add: nn_integral_count_space_reindex d_OUT_def)
  also have "\<dots> = d_OUT f (Inner x)" using flowD_capacity[OF f, of "(Inner x, SOURCE)"]
    by(auto simp add: nn_integral_count_space_indicator d_OUT_def not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = d_IN f (Inner x)" using x flowD_KIR[OF f, of "Inner x"] by(simp)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f (y, Inner x))"
    using x flowD_capacity[OF f, of "(SOURCE, Inner x)"]
    by(auto simp add: nn_integral_count_space_indicator d_IN_def not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = d_IN (unlift f) x" by(simp add: nn_integral_count_space_reindex d_IN_def)
  finally show "KIR (unlift f) x" .
qed

private lemma value_unlift:
  assumes f: "flow \<Delta>' f"
  shows "value_flow \<Delta> (unlift f) = value_flow \<Delta>' f"
proof -
  have "value_flow \<Delta> (unlift f) = (\<Sum>\<^sup>+ y\<in>range Inner. f (Inner (source \<Delta>), y))"
    by(simp add: nn_integral_count_space_reindex d_OUT_def)
  also have "\<dots> = d_OUT f (Inner (source \<Delta>))" using flowD_capacity[OF f, of "(Inner (source \<Delta>), SOURCE)"]
    by(auto simp add: nn_integral_count_space_indicator d_OUT_def not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = d_IN f (Inner (source \<Delta>))" using flowD_KIR[OF f, of "Inner (source \<Delta>)"] by(simp)
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (y, Inner (source \<Delta>)) * indicator {SOURCE} y)"
    unfolding d_IN_def using flowD_capacity[OF f, of "(x, Inner (source \<Delta>))" for x]
    by(intro nn_integral_cong)(auto intro!: antisym split: split_indicator if_split_asm elim: meta_allE)
  also have "\<dots> = f (SOURCE, Inner (source \<Delta>))" by simp
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (SOURCE, y) * indicator {Inner (source \<Delta>)} y)"
    by(simp add: one_ennreal_def[symmetric])
  also have "\<dots> = value_flow \<Delta>' f" unfolding d_OUT_def
    unfolding d_OUT_def using flowD_capacity[OF f, of "(SOURCE, Inner x)" for x] flowD_capacity[OF f, of "(SOURCE, SOURCE)"]
    apply(intro nn_integral_cong)
    apply(case_tac x)
    apply(auto intro!: antisym split: split_indicator if_split_asm elim: meta_allE)
    done
  finally show ?thesis .
qed

theorem ex_max_flow:
  "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<alpha> \<and> (\<forall>x. d_IN f x \<le> value_flow \<Delta> f)"
proof(cases "\<alpha>")
  case (real \<alpha>')
  hence \<alpha>: "\<alpha> \<noteq> \<top>" by simp
  then interpret \<Delta>': flow_attainability \<Delta>' by(rule \<Delta>'_flow_attainability)

  have source_out: "edge \<Delta>' (source \<Delta>') y \<longleftrightarrow> y = Inner (source \<Delta>)" for y by(auto)
  have nontrivial: "\<^bold>E\<^bsub>\<Delta>'\<^esub> \<noteq> {}" by(auto intro: edge'.intros)

  have eq: "(SUP g \<in> {g. flow \<Delta>' g}. value_flow \<Delta>' g) = (SUP g \<in> {g. flow \<Delta> g}. value_flow \<Delta> g)" (is "?lhs = ?rhs")
  proof(intro antisym SUP_least; unfold mem_Collect_eq)
    fix g
    assume g: "flow \<Delta>' g"
    hence "value_flow \<Delta>' g = value_flow \<Delta> (unlift g)" by(simp add: value_unlift)
    also { from g have "flow \<Delta> (unlift g)" by simp }
    then have "\<dots> \<le> ?rhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta>' g \<le> \<dots>" .
  next
    fix g
    assume g: "flow \<Delta> g"
    hence "value_flow \<Delta> g = value_flow \<Delta>' (lift g)" by simp
    also { from g have "flow \<Delta>' (lift g)" by simp }
    then have "\<dots> \<le> ?lhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta> g \<le> ?lhs" .
  qed
  also have "\<dots> = ennreal \<alpha>'" using real by(simp add: \<alpha>_def)
  finally obtain f where f: "flow \<Delta>' f"
    and value_f: "value_flow \<Delta>' f = (\<Squnion>g\<in>{g. flow \<Delta>' g}. value_flow \<Delta>' g)"
    and IN_f: "\<And>x. d_IN f x \<le> value_flow \<Delta>' f"
    using \<open>0 \<le> \<alpha>'\<close> by(blast dest: \<Delta>'.ex_max_flow''[OF source_out nontrivial])
  have "flow \<Delta> (unlift f)" using f by simp
  moreover have "value_flow \<Delta> (unlift f) = \<alpha>" using f eq value_f by(simp add: value_unlift \<alpha>_def)
  moreover {
    fix x
    have "d_IN (unlift f) x = (\<Sum>\<^sup>+ y\<in>range Inner. f (y, Inner x))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> \<le> d_IN f (Inner x)" unfolding d_IN_def
      by(auto intro!: nn_integral_mono simp add: nn_integral_count_space_indicator split: split_indicator)
    also have "\<dots> \<le> value_flow \<Delta> (unlift f)" using IN_f[of "Inner x"] f by(simp add: value_unlift)
    also note calculation }
  ultimately show ?thesis by blast
next
  case top
  show ?thesis
  proof(cases "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<top>")
    case True
    with top show ?thesis by auto
  next
    case False
    hence real: "\<forall>f. \<alpha> = \<top> \<longrightarrow> flow \<Delta> f \<longrightarrow> value_flow \<Delta> f < \<alpha>" using top by (auto simp: less_top)
    { fix i
      have "2 * 2 ^ i < \<alpha>" using top by (simp_all add: ennreal_mult_less_top power_less_top_ennreal)
      from flow_by_value[OF this real] have "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = 2 * 2 ^ i" by blast }
    then obtain f_i where f_i: "\<And>i. flow \<Delta> (f_i i)"
      and value_i: "\<And>i. value_flow \<Delta> (f_i i) = 2 * 2 ^ i" by metis
    define f where "f e = (\<Sum>\<^sup>+ i. f_i i e / (2 * 2 ^ i))" for e
    have "flow \<Delta> f"
    proof
      fix e
      have "f e \<le> (\<Sum>\<^sup>+ i. (SUP i. f_i i e) / (2 * 2 ^ i))" unfolding f_def
        by(rule nn_integral_mono)(auto intro!: divide_right_mono_ennreal SUP_upper)
      also have "\<dots> = (SUP i. f_i i e) / 2 * (\<Sum>\<^sup>+ i. 1 / 2 ^ i)"
        apply(subst nn_integral_cmult[symmetric])
        apply(auto intro!: nn_integral_cong intro: SUP_upper2
          simp: divide_ennreal_def ennreal_inverse_mult power_less_top_ennreal mult_ac)
        done
      also have "(\<Sum>\<^sup>+ i. 1 / 2 ^ i) = (\<Sum>i. ennreal ((1 / 2) ^ i))"
        by(simp add: nn_integral_count_space_nat power_divide divide_ennreal[symmetric] ennreal_power[symmetric])
      also have "\<dots> = ennreal (\<Sum>i. (1 / 2) ^ i)"
        by(intro suminf_ennreal2 complete_algebra_summable_geometric) simp_all
      also have "\<dots> = 2" by(subst suminf_geometric; simp)
      also have "(SUP i. f_i i e) / 2 * 2 = (SUP i. f_i i e)"
        by (simp add: ennreal_divide_times)
      also have "\<dots> \<le> capacity \<Delta> e" by(rule SUP_least)(rule flowD_capacity[OF f_i])
      finally show "f e \<le> capacity \<Delta> e" .

      fix x
      assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
      have "d_OUT f x = (\<Sum>\<^sup>+ i\<in>UNIV. \<Sum>\<^sup>+ y. f_i i (x, y) / (2 * 2 ^ i))"
        unfolding d_OUT_def f_def
        by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])
          (simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
      also have "\<dots> = (\<Sum>\<^sup>+ i. d_OUT (f_i i) x / (2 * 2 ^ i))" unfolding d_OUT_def
        by(simp add: nn_integral_divide)
      also have "\<dots> = (\<Sum>\<^sup>+ i. d_IN (f_i i) x / (2 * 2 ^ i))" by(simp add: flowD_KIR[OF f_i, OF x])
      also have "\<dots> = (\<Sum>\<^sup>+ i\<in>UNIV. \<Sum>\<^sup>+ y. f_i i (y, x) / (2 * 2 ^ i))"
        by(simp add: nn_integral_divide d_IN_def)
      also have "\<dots> = d_IN f x" unfolding d_IN_def f_def
        by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])
          (simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
      finally show "KIR f x" .
    qed
    moreover {
      have "value_flow \<Delta> f = (\<Sum>\<^sup>+ i. value_flow \<Delta> (f_i i) / (2 * 2 ^ i))"
        unfolding d_OUT_def f_def
        by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])
          (simp add: nn_integral_fst_count_space[where f="case_prod _", simplified] nn_integral_divide[symmetric])
      also have "\<dots> = \<top>"
        by(simp add: value_i ennreal_mult_less_top power_less_top_ennreal)
      finally have "value_flow \<Delta> f = \<top>" .
    }
    ultimately show ?thesis using top by auto
  qed
qed

end

end

end

end