theory MFMC_Network imports
  MFMC_Misc
begin

section \<open>Graphs\<close>

type_synonym 'v edge = "'v \<times> 'v"

record 'v graph =
  edge :: "'v \<Rightarrow> 'v \<Rightarrow> bool"

abbreviation edges :: "('v, 'more) graph_scheme \<Rightarrow> 'v edge set" ("\<^bold>E\<index>")
where "\<^bold>E\<^bsub>G\<^esub> \<equiv> {(x, y). edge G x y}"

definition outgoing :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> 'v set" ("\<^bold>O\<^bold>U\<^bold>T\<index>")
where "\<^bold>O\<^bold>U\<^bold>T\<^bsub>G\<^esub> x = {y. (x, y) \<in> \<^bold>E\<^bsub>G\<^esub>}"

definition incoming :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> 'v set" ("\<^bold>I\<^bold>N\<index>")
where "\<^bold>I\<^bold>N\<^bsub>G\<^esub> y = {x. (x, y) \<in> \<^bold>E\<^bsub>G\<^esub>}"

text \<open>
  Vertices are implicitly defined as the endpoints of edges, so we do not allow isolated vertices.
  For the purpose of flows, this does not matter as isolated vertices cannot contribute to a flow.
  The advantage is that we do not need any invariant on graphs that the endpoints of edges are a
  subset of the vertices. Conversely, this design choice makes a few proofs about reductions on webs
  harder, because we have to adjust other sets which are supposed to be part of the vertices.
\<close>

definition vertex :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> bool"
where "vertex G x \<longleftrightarrow> Domainp (edge G) x \<or> Rangep (edge G) x"

lemma vertexI:
  shows vertexI1: "edge \<Gamma> x y \<Longrightarrow> vertex \<Gamma> x"
  and vertexI2: "edge \<Gamma> x y \<Longrightarrow> vertex \<Gamma> y"
by(auto simp add: vertex_def)

abbreviation vertices :: "('v, 'more) graph_scheme \<Rightarrow> 'v set" ("\<^bold>V\<index>")
where "\<^bold>V\<^bsub>G\<^esub> \<equiv> Collect (vertex G)"

lemma "\<^bold>V_def": "\<^bold>V\<^bsub>G\<^esub> = fst ` \<^bold>E\<^bsub>G\<^esub> \<union> snd ` \<^bold>E\<^bsub>G\<^esub>"
by(auto 4 3 simp add: vertex_def intro: rev_image_eqI prod.expand)

type_synonym 'v path = "'v list"

abbreviation path :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> 'v path \<Rightarrow> 'v \<Rightarrow> bool"
where "path G \<equiv> rtrancl_path (edge G)"

inductive cycle :: "('v, 'more) graph_scheme \<Rightarrow> 'v path \<Rightarrow> bool"
  for G
where \<comment> \<open>Cycles must not pass through the same node multiple times. Otherwise, the cycle might
  enter a node via two different edges and leave it via just one edge. Thus, the clean-up lemma
  would not hold any more.\<close>
  cycle: "\<lbrakk> path G v p v; p \<noteq> []; distinct p \<rbrakk> \<Longrightarrow> cycle G p"

inductive_simps cycle_Nil [simp]: "cycle G Nil"

abbreviation cycles :: "('v, 'more) graph_scheme \<Rightarrow> 'v path set"
where "cycles G \<equiv> Collect (cycle G)"

lemma countable_cycles [simp]:
  assumes "countable (\<^bold>V\<^bsub>G\<^esub>)"
  shows "countable (cycles G)"
proof -
  have "cycles G \<subseteq> lists \<^bold>V\<^bsub>G\<^esub>"
    by(auto elim!: cycle.cases dest: rtrancl_path_Range_end rtrancl_path_Range simp add: vertex_def)
  thus ?thesis by(rule countable_subset)(simp add: assms)
qed

definition cycle_edges :: "'v path \<Rightarrow> 'v edge list"
where "cycle_edges p = zip p (rotate1 p)"

lemma cycle_edges_not_Nil: "cycle G p \<Longrightarrow> cycle_edges p \<noteq> []"
by(auto simp add: cycle_edges_def cycle.simps neq_Nil_conv zip_Cons1 split: list.split)

lemma distinct_cycle_edges:
  "cycle G p \<Longrightarrow> distinct (cycle_edges p)"
by(erule cycle.cases)(simp add: cycle_edges_def distinct_zipI2)

lemma cycle_enter_leave_same:
  assumes "cycle G p"
  shows "card (set [(x', y) \<leftarrow> cycle_edges p. x' = x]) = card (set [(x', y) \<leftarrow> cycle_edges p. y = x])"
  (is "?lhs = ?rhs")
using assms
proof cases
  case (cycle v)
  from distinct_cycle_edges[OF assms]
  have "?lhs = length [x' \<leftarrow> map fst (cycle_edges p). x' = x]"
    by(subst distinct_card; simp add: filter_map o_def split_def)
  also have "\<dots> = (if x \<in> set p then 1 else 0)" using cycle
    by(auto simp add: cycle_edges_def filter_empty_conv length_filter_conv_card card_eq_1_iff in_set_conv_nth dest: nth_eq_iff_index_eq)
  also have "\<dots> = length [y \<leftarrow> map snd (cycle_edges p). y = x]" using cycle
    apply(auto simp add: cycle_edges_def filter_empty_conv Suc_length_conv intro!: exI[where x=x])
    apply(drule split_list_first)
    apply(auto dest: split_list_first simp add: append_eq_Cons_conv rotate1_append filter_empty_conv split: if_split_asm dest: in_set_tlD)
    done
  also have "\<dots> = ?rhs" using distinct_cycle_edges[OF assms]
    by(subst distinct_card; simp add: filter_map o_def split_def)
  finally show ?thesis .
qed

lemma cycle_leave_ex_enter:
  assumes "cycle G p" and "(x, y) \<in> set (cycle_edges p)"
  shows "\<exists>z. (z, x) \<in> set (cycle_edges p)"
using assms
by(cases)(auto 4 3 simp add: cycle_edges_def cong: conj_cong split: if_split_asm intro: set_zip_rightI dest: set_zip_leftD)

lemma cycle_edges_edges:
  assumes "cycle G p"
  shows "set (cycle_edges p) \<subseteq> \<^bold>E\<^bsub>G\<^esub>"
proof
  fix x
  assume "x \<in> set (cycle_edges p)"
  then obtain i where x: "x = (p ! i, rotate1 p ! i)" and i: "i < length p"
    by(auto simp add: cycle_edges_def set_zip)
  from assms obtain v where p: "path G v p v" and "p \<noteq> []" and "distinct p" by cases
  let ?i = "Suc i mod length p"
  have "?i < length p" by (simp add: \<open>p \<noteq> []\<close>)
  note rtrancl_path_nth[OF p this]
  also have "(v # p) ! ?i = p ! i"
  proof(cases "Suc i < length p")
    case True thus ?thesis by simp
  next
    case False
    with i have "Suc i = length p" by simp
    moreover from p \<open>p \<noteq> []\<close> have "last p = v" by(rule rtrancl_path_last)
    ultimately show ?thesis using \<open>p \<noteq> []\<close> by(simp add: last_conv_nth)(metis diff_Suc_Suc diff_zero)
  qed
  also have "p ! ?i = rotate1 p ! i" using i by(simp add: nth_rotate1)
  finally show "x \<in> \<^bold>E\<^bsub>G\<^esub>" by(simp add: x)
qed


section \<open>Network and Flow\<close>

record 'v network = "'v graph" +
  capacity :: "'v edge \<Rightarrow> ennreal"
  source :: "'v"
  sink :: "'v"

type_synonym 'v flow = "'v edge \<Rightarrow> ennreal"

inductive_set support_flow :: "'v flow \<Rightarrow> 'v edge set"
  for f
where "f e > 0 \<Longrightarrow> e \<in> support_flow f"

lemma support_flow_conv: "support_flow f = {e. f e > 0}"
by(auto simp add: support_flow.simps)

lemma not_in_support_flowD: "x \<notin> support_flow f \<Longrightarrow> f x = 0"
by(simp add: support_flow_conv)

definition d_OUT :: "'v flow \<Rightarrow> 'v \<Rightarrow> ennreal"
where "d_OUT g x = (\<Sum>\<^sup>+ y. g (x, y))"

definition d_IN :: "'v flow \<Rightarrow> 'v \<Rightarrow> ennreal"
where "d_IN g y = (\<Sum>\<^sup>+ x. g (x, y))"

lemma d_OUT_mono: "(\<And>y. f (x, y) \<le> g (x, y)) \<Longrightarrow> d_OUT f x \<le> d_OUT g x"
by(auto simp add: d_OUT_def le_fun_def intro: nn_integral_mono)

lemma d_IN_mono: "(\<And>x. f (x, y) \<le> g (x, y)) \<Longrightarrow> d_IN f y \<le> d_IN g y"
by(auto simp add: d_IN_def le_fun_def intro: nn_integral_mono)

lemma d_OUT_0 [simp]: "d_OUT (\<lambda>_. 0) x = 0"
by(simp add: d_OUT_def)

lemma d_IN_0 [simp]: "d_IN (\<lambda>_. 0) x = 0"
by(simp add: d_IN_def)

lemma d_OUT_add: "d_OUT (\<lambda>e. f e + g e) x = d_OUT f x + d_OUT g x"
unfolding d_OUT_def by(simp add: nn_integral_add)

lemma d_IN_add: "d_IN (\<lambda>e. f e + g e) x = d_IN f x + d_IN g x"
unfolding d_IN_def by(simp add: nn_integral_add)

lemma d_OUT_cmult: "d_OUT (\<lambda>e. c * f e) x = c * d_OUT f x"
by(simp add: d_OUT_def nn_integral_cmult)

lemma d_IN_cmult: "d_IN (\<lambda>e. c * f e) x = c * d_IN f x"
by(simp add: d_IN_def nn_integral_cmult)

lemma d_OUT_ge_point: "f (x, y) \<le> d_OUT f x"
by(auto simp add: d_OUT_def intro!: nn_integral_ge_point)

lemma d_IN_ge_point: "f (y, x) \<le> d_IN f x"
by(auto simp add: d_IN_def intro!: nn_integral_ge_point)

lemma d_OUT_monotone_convergence_SUP:
  assumes "incseq (\<lambda>n y. f n (x, y))"
  shows "d_OUT (\<lambda>e. SUP n. f n e) x = (SUP n. d_OUT (f n) x)"
unfolding d_OUT_def by(rule nn_integral_monotone_convergence_SUP[OF assms]) simp

lemma d_IN_monotone_convergence_SUP:
  assumes "incseq (\<lambda>n x. f n (x, y))"
  shows "d_IN (\<lambda>e. SUP n. f n e) y = (SUP n. d_IN (f n) y)"
unfolding d_IN_def by(rule nn_integral_monotone_convergence_SUP[OF assms]) simp

lemma d_OUT_diff:
  assumes "\<And>y. g (x, y) \<le> f (x, y)" "d_OUT g x \<noteq> \<top>"
  shows "d_OUT (\<lambda>e. f e - g e) x = d_OUT f x - d_OUT g x"
using assms by(simp add: nn_integral_diff d_OUT_def)

lemma d_IN_diff:
  assumes "\<And>x. g (x, y) \<le> f (x, y)" "d_IN g y \<noteq> \<top>"
  shows "d_IN (\<lambda>e. f e - g e) y = d_IN f y - d_IN g y"
using assms by(simp add: nn_integral_diff d_IN_def)

lemma fixes G (structure)
  shows d_OUT_alt_def: "(\<And>y. (x, y) \<notin> \<^bold>E \<Longrightarrow> g (x, y) = 0) \<Longrightarrow> d_OUT g x = (\<Sum>\<^sup>+  y\<in>\<^bold>O\<^bold>U\<^bold>T x. g (x, y))"
  and d_IN_alt_def: "(\<And>x. (x, y) \<notin> \<^bold>E \<Longrightarrow> g (x, y) = 0) \<Longrightarrow> d_IN g y = (\<Sum>\<^sup>+ x\<in>\<^bold>I\<^bold>N y. g (x, y))"
unfolding d_OUT_def d_IN_def
by(fastforce simp add: max_def d_OUT_def d_IN_def nn_integral_count_space_indicator outgoing_def incoming_def intro!: nn_integral_cong split: split_indicator)+

lemma d_OUT_alt_def2: "d_OUT g x = (\<Sum>\<^sup>+ y\<in>{y. (x, y) \<in> support_flow g}. g (x, y))"
  and d_IN_alt_def2: "d_IN g y = (\<Sum>\<^sup>+ x\<in>{x. (x, y) \<in> support_flow g}. g (x, y))"
unfolding d_OUT_def d_IN_def
by(auto simp add: max_def d_OUT_def d_IN_def nn_integral_count_space_indicator outgoing_def incoming_def support_flow.simps intro!: nn_integral_cong split: split_indicator)+

definition d_diff :: "('v edge \<Rightarrow> ennreal) \<Rightarrow> 'v \<Rightarrow> ennreal"
where "d_diff g x = d_OUT g x - d_IN g x"

abbreviation KIR :: "('v edge \<Rightarrow> ennreal) \<Rightarrow> 'v \<Rightarrow> bool"
where "KIR f x \<equiv> d_OUT f x = d_IN f x"

inductive_set SINK :: "('v edge \<Rightarrow> ennreal) \<Rightarrow> 'v set"
  for f
where SINK: "d_OUT f x = 0 \<Longrightarrow> x \<in> SINK f"

lemma SINK_mono:
  assumes "\<And>e. f e \<le> g e"
  shows "SINK g \<subseteq> SINK f"
proof(rule subsetI; erule SINK.cases; hypsubst)
  fix x
  assume "d_OUT g x = 0"
  moreover have "d_OUT f x \<le> d_OUT g x" using assms by(rule d_OUT_mono)
  ultimately have "d_OUT f x = 0" by simp
  thus "x \<in> SINK f" ..
qed

lemma SINK_mono': "f \<le> g \<Longrightarrow> SINK g \<subseteq> SINK f"
by(rule SINK_mono)(rule le_funD)

lemma support_flow_Sup: "support_flow (Sup Y) = (\<Union>f\<in>Y. support_flow f)"
by(auto simp add: support_flow_conv less_SUP_iff)

lemma
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and countable: "countable (support_flow (Sup Y))"
  shows d_OUT_Sup: "d_OUT (Sup Y) x = (SUP f\<in>Y. d_OUT f x)" (is "?OUT x" is "?lhs1 x = ?rhs1 x")
  and d_IN_Sup: "d_IN (Sup Y) y = (SUP f\<in>Y. d_IN f y)" (is "?IN" is "?lhs2 = ?rhs2")
  and SINK_Sup: "SINK (Sup Y) = (\<Inter>f\<in>Y. SINK f)" (is "?SINK")
proof -
  have chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>f y. f (x, y)) ` Y)" for x using chain
    by(rule chain_imageI)(simp add: le_fun_def)
  have countable': "countable {y. (x, y) \<in> support_flow (Sup Y)}" for x
    using _ countable[THEN countable_image[where f=snd]]
    by(rule countable_subset)(auto intro: prod.expand rev_image_eqI)
  { fix x
    have "?lhs1 x = (\<Sum>\<^sup>+ y\<in>{y. (x, y) \<in> support_flow (Sup Y)}. SUP f\<in>Y. f (x, y))"
      by(subst d_OUT_alt_def2; simp)
    also have "\<dots> = (SUP f\<in>Y. \<Sum>\<^sup>+ y\<in>{y. (x, y) \<in> support_flow (Sup Y)}. f (x, y))" using Y
      by(rule nn_integral_monotone_convergence_SUP_countable)(auto simp add: chain' intro: countable')
    also have "\<dots> = ?rhs1 x" unfolding d_OUT_alt_def2
      by(auto 4 3 simp add: support_flow_Sup max_def nn_integral_count_space_indicator intro!: nn_integral_cong SUP_cong split: split_indicator dest: not_in_support_flowD)
    finally show "?OUT x" . }
  note out = this

  have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>f x. f (x, y)) ` Y)" for y using chain
    by(rule chain_imageI)(simp add: le_fun_def)
  have countable'': "countable {x. (x, y) \<in> support_flow (Sup Y)}" for y
    using _ countable[THEN countable_image[where f=fst]]
    by(rule countable_subset)(auto intro: prod.expand rev_image_eqI)
  have "?lhs2 = (\<Sum>\<^sup>+ x\<in>{x. (x, y) \<in> support_flow (Sup Y)}. SUP f\<in>Y. f (x, y))"
    by(subst d_IN_alt_def2; simp)
  also have "\<dots> = (SUP f\<in>Y. \<Sum>\<^sup>+ x\<in>{x. (x, y) \<in> support_flow (Sup Y)}. f (x, y))" using Y
    by(rule nn_integral_monotone_convergence_SUP_countable)(simp_all add: chain'' countable'')
  also have "\<dots> = ?rhs2" unfolding d_IN_alt_def2
    by(auto 4 3 simp add: support_flow_Sup max_def nn_integral_count_space_indicator intro!: nn_integral_cong SUP_cong split: split_indicator dest: not_in_support_flowD)
  finally show ?IN .

  show ?SINK by(rule set_eqI)(simp add: SINK.simps out Y bot_ennreal[symmetric])
qed

lemma
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and countable: "countable (support_flow f)"
  and bounded: "\<And>g e. g \<in> Y \<Longrightarrow> g e \<le> f e"
  shows d_OUT_Inf: "d_OUT f x \<noteq> top \<Longrightarrow> d_OUT (Inf Y) x = (INF g\<in>Y. d_OUT g x)" (is "_ \<Longrightarrow> ?OUT" is "_ \<Longrightarrow> ?lhs1 = ?rhs1")
  and d_IN_Inf: "d_IN f x \<noteq> top \<Longrightarrow> d_IN (Inf Y) x = (INF g\<in>Y. d_IN g x)" (is "_ \<Longrightarrow> ?IN" is "_ \<Longrightarrow> ?lhs2 = ?rhs2")
proof -
  text \<open>We take a detour here via suprema because we have more theorems about @{const nn_integral}
    with suprema than with infinma.\<close>

  from Y obtain g0 where g0: "g0 \<in> Y" by auto
  have g0_le_f: "g0 e \<le> f e" for e by(rule bounded[OF g0])

  have "support_flow (SUP g\<in>Y. (\<lambda>e. f e - g e)) \<subseteq> support_flow f"
    by(clarsimp simp add: support_flow.simps less_SUP_iff elim!: less_le_trans intro!: diff_le_self_ennreal)
  then have countable': "countable (support_flow (SUP g\<in>Y. (\<lambda>e. f e - g e)))" by(rule countable_subset)(rule countable)

  have "Complete_Partial_Order.chain (\<ge>) Y" using chain by(simp add: chain_dual)
  hence chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>g e. f e - g e) ` Y)"
    by(rule chain_imageI)(auto simp add: le_fun_def intro: ennreal_minus_mono)

  { assume finite: "d_OUT f x \<noteq> top"
    have finite' [simp]: "f (x, y) \<noteq> \<top>" for y using finite
      by(rule neq_top_trans) (rule d_OUT_ge_point)

    have finite'_g: "g (x, y) \<noteq> \<top>" if "g \<in> Y" for g y using finite'[of y]
      by(rule neq_top_trans)(rule bounded[OF that])

    have finite1: "(\<Sum>\<^sup>+ y. f (x, y) - (INF g\<in>Y. g (x, y))) \<noteq> top"
      using finite by(rule neq_top_trans)(auto simp add: d_OUT_def intro!: nn_integral_mono)
    have finite2: "d_OUT g x \<noteq> top" if "g \<in> Y" for g using finite
      by(rule neq_top_trans)(auto intro: d_OUT_mono bounded[OF that])

    have bounded1: "(\<Sqinter>g\<in>Y. d_OUT g x) \<le> d_OUT f x"
      using Y by (blast intro: INF_lower2 d_OUT_mono bounded)

    have "?lhs1 = (\<Sum>\<^sup>+ y. INF g\<in>Y. g (x, y))" by(simp add: d_OUT_def)
    also have "\<dots> = d_OUT f x - (\<Sum>\<^sup>+ y. f (x, y) - (INF g\<in>Y. g (x, y)))" unfolding d_OUT_def
      using finite1 g0_le_f
      apply(subst nn_integral_diff[symmetric])
      apply(auto simp add: AE_count_space intro!: diff_le_self_ennreal INF_lower2[OF g0] nn_integral_cong diff_diff_ennreal[symmetric])
      done
    also have "(\<Sum>\<^sup>+ y. f (x, y) - (INF g\<in>Y. g (x, y))) = d_OUT (\<lambda>e. SUP g\<in>Y. f e - g e) x"
      unfolding d_OUT_def by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "\<dots> = (SUP h\<in>(\<lambda>g e. f e - g e) ` Y. d_OUT h x)" using countable' chain' Y
      by(subst d_OUT_Sup[symmetric])(simp_all add: SUP_apply[abs_def])
    also have "\<dots> = (SUP g\<in>Y. d_OUT (\<lambda>e. f e - g e) x)" unfolding image_image ..
    also have "\<dots> = (SUP g\<in>Y. d_OUT f x - d_OUT g x)"
      by(rule SUP_cong[OF refl] d_OUT_diff)+(auto intro: bounded simp add: finite2)
    also have "\<dots> = d_OUT f x - ?rhs1" by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "d_OUT f x - \<dots> = ?rhs1"
      using Y by(subst diff_diff_ennreal)(simp_all add: bounded1 finite)
    finally show ?OUT .
  next
    assume finite: "d_IN f x \<noteq> top"
    have finite' [simp]: "f (y, x) \<noteq> \<top>" for y using finite
      by(rule neq_top_trans) (rule d_IN_ge_point)

    have finite'_g: "g (y, x) \<noteq> \<top>" if "g \<in> Y" for g y using finite'[of y]
      by(rule neq_top_trans)(rule bounded[OF that])

    have finite1: "(\<Sum>\<^sup>+ y. f (y, x) - (INF g\<in>Y. g (y, x))) \<noteq> top"
      using finite by(rule neq_top_trans)(auto simp add: d_IN_def diff_le_self_ennreal intro!: nn_integral_mono)
    have finite2: "d_IN g x \<noteq> top" if "g \<in> Y" for g using finite
      by(rule neq_top_trans)(auto intro: d_IN_mono bounded[OF that])

    have bounded1: "(\<Sqinter>g\<in>Y. d_IN g x) \<le> d_IN f x"
      using Y by (blast intro: INF_lower2 d_IN_mono bounded)

    have "?lhs2 = (\<Sum>\<^sup>+ y. INF g\<in>Y. g (y, x))" by(simp add: d_IN_def)
    also have "\<dots> = d_IN f x - (\<Sum>\<^sup>+ y. f (y, x) - (INF g\<in>Y. g (y, x)))" unfolding d_IN_def
      using finite1 g0_le_f
      apply(subst nn_integral_diff[symmetric])
      apply(auto simp add: AE_count_space intro!: diff_le_self_ennreal INF_lower2[OF g0] nn_integral_cong diff_diff_ennreal[symmetric])
      done
    also have "(\<Sum>\<^sup>+ y. f (y, x) - (INF g\<in>Y. g (y, x))) = d_IN (\<lambda>e. SUP g\<in>Y. f e - g e) x"
      unfolding d_IN_def by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "\<dots> = (SUP h\<in>(\<lambda>g e. f e - g e) ` Y. d_IN h x)" using countable' chain' Y
      by(subst d_IN_Sup[symmetric])(simp_all add: SUP_apply[abs_def])
    also have "\<dots> = (SUP g\<in>Y. d_IN (\<lambda>e. f e - g e) x)" unfolding image_image ..
    also have "\<dots> = (SUP g\<in>Y. d_IN f x - d_IN g x)"
      by(rule SUP_cong[OF refl] d_IN_diff)+(auto intro: bounded simp add: finite2)
    also have "\<dots> = d_IN f x - ?rhs2" by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "d_IN f x - \<dots> = ?rhs2"
      by(subst diff_diff_ennreal)(simp_all add: finite bounded1)
    finally show ?IN . }
qed

inductive flow :: "('v, 'more) network_scheme \<Rightarrow> 'v flow \<Rightarrow> bool"
  for \<Delta> (structure) and f
where
  flow: "\<lbrakk> \<And>e. f e \<le> capacity \<Delta> e;
     \<And>x. \<lbrakk> x \<noteq> source \<Delta>; x \<noteq> sink \<Delta> \<rbrakk> \<Longrightarrow> KIR f x \<rbrakk>
  \<Longrightarrow> flow \<Delta> f"

lemma flowD_capacity: "flow \<Delta> f \<Longrightarrow> f e \<le> capacity \<Delta> e"
by(cases e)(simp add: flow.simps)

lemma flowD_KIR: "\<lbrakk> flow \<Delta> f; x \<noteq> source \<Delta>; x \<noteq> sink \<Delta> \<rbrakk> \<Longrightarrow> KIR f x"
by(simp add: flow.simps)

lemma flowD_capacity_OUT: "flow \<Delta> f \<Longrightarrow> d_OUT f x \<le> d_OUT (capacity \<Delta>) x"
by(rule d_OUT_mono)(erule flowD_capacity)

lemma flowD_capacity_IN: "flow \<Delta> f \<Longrightarrow> d_IN f x \<le> d_IN (capacity \<Delta>) x"
by(rule d_IN_mono)(erule flowD_capacity)

abbreviation value_flow :: "('v, 'more) network_scheme \<Rightarrow> ('v edge \<Rightarrow> ennreal) \<Rightarrow> ennreal"
where "value_flow \<Delta> f \<equiv> d_OUT f (source \<Delta>)"

subsection \<open>Cut\<close>

type_synonym 'v cut = "'v set"

inductive cut :: "('v, 'more) network_scheme \<Rightarrow> 'v cut \<Rightarrow> bool"
  for \<Delta> and S
where cut: "\<lbrakk> source \<Delta> \<in> S; sink \<Delta> \<notin> S \<rbrakk> \<Longrightarrow> cut \<Delta> S"

inductive orthogonal :: "('v, 'more) network_scheme \<Rightarrow> 'v flow \<Rightarrow> 'v cut \<Rightarrow> bool"
  for \<Delta> f S
where
  "\<lbrakk> \<And>x y. \<lbrakk> edge \<Delta> x y; x \<in> S; y \<notin> S \<rbrakk> \<Longrightarrow> f (x, y) = capacity \<Delta> (x, y);
     \<And>x y. \<lbrakk> edge \<Delta> x y; x \<notin> S; y \<in> S \<rbrakk> \<Longrightarrow> f (x, y) = 0 \<rbrakk>
  \<Longrightarrow> orthogonal \<Delta> f S"

lemma orthogonalD_out:
  "\<lbrakk> orthogonal \<Delta> f S; edge \<Delta> x y; x \<in> S; y \<notin> S \<rbrakk> \<Longrightarrow> f (x, y) = capacity \<Delta> (x, y)"
by(simp add: orthogonal.simps)

lemma orthogonalD_in:
  "\<lbrakk> orthogonal \<Delta> f S; edge \<Delta> x y; x \<notin> S; y \<in> S \<rbrakk> \<Longrightarrow> f (x, y) = 0"
by(simp add: orthogonal.simps)



subsection \<open>Countable network\<close>

locale countable_network =
  fixes \<Delta> :: "('v, 'more) network_scheme" (structure)
  assumes countable_E [simp]: "countable \<^bold>E"
  and source_neq_sink [simp]: "source \<Delta> \<noteq> sink \<Delta>"
  and capacity_outside: "e \<notin> \<^bold>E \<Longrightarrow> capacity \<Delta> e = 0"
  and capacity_finite [simp]: "capacity \<Delta> e \<noteq> \<top>"
begin

lemma sink_neq_source [simp]: "sink \<Delta> \<noteq> source \<Delta>"
using source_neq_sink[symmetric] .

lemma countable_V [simp]: "countable \<^bold>V"
unfolding "\<^bold>V_def" using countable_E by auto

lemma flowD_outside:
  assumes g: "flow \<Delta> g"
  shows "e \<notin> \<^bold>E \<Longrightarrow> g e = 0"
using flowD_capacity[OF g, of e] capacity_outside[of e] by simp

lemma flowD_finite:
  assumes "flow \<Delta> g"
  shows "g e \<noteq> \<top>"
using flowD_capacity[OF assms, of e] by (auto simp: top_unique)

lemma zero_flow [simp]: "flow \<Delta> (\<lambda>_. 0)"
by(rule flow.intros) simp_all

end

subsection \<open>Reduction for avoiding antiparallel edges\<close>

locale antiparallel_edges = countable_network \<Delta>
  for \<Delta> :: "('v, 'more) network_scheme" (structure)
begin

text \<open>We eliminate the assumption of antiparallel edges by adding a vertex for every edge.
  Thus, antiparallel edges are split up into a cycle of 4 edges. This idea already appears in
  @{cite Aharoni1983EJC}.\<close>

datatype (plugins del: transfer size) 'v' vertex = Vertex 'v' | Edge 'v' 'v'

inductive edg :: "'v vertex \<Rightarrow> 'v vertex \<Rightarrow> bool"
where
  OUT: "edge \<Delta> x y \<Longrightarrow> edg (Vertex x) (Edge x y)"
| IN: "edge \<Delta> x y \<Longrightarrow> edg (Edge x y) (Vertex y)"

inductive_simps edg_simps [simp]:
  "edg (Vertex x) v"
  "edg (Edge x y) v"
  "edg v (Vertex x)"
  "edg v (Edge x y)"

fun split :: "'v flow \<Rightarrow> 'v vertex flow"
where
  "split f (Vertex x, Edge x' y) = (if x' = x then f (x, y) else 0)"
| "split f (Edge x y', Vertex y) = (if y' = y then f (x, y) else 0)"
| "split f _ = 0"

lemma split_Vertex1_eq_0I: "(\<And>z. y \<noteq> Edge x z) \<Longrightarrow> split f (Vertex x, y) = 0"
by(cases y) auto

lemma split_Vertex2_eq_0I: "(\<And>z. y \<noteq> Edge z x) \<Longrightarrow> split f (y, Vertex x) = 0"
by(cases y) simp_all

lemma split_Edge1_eq_0I: "(\<And>z. y \<noteq> Vertex x) \<Longrightarrow> split f (Edge z x, y) = 0"
by(cases y) simp_all

lemma split_Edge2_eq_0I: "(\<And>z. y \<noteq> Vertex x) \<Longrightarrow> split f (y, Edge x z) = 0"
by(cases y) simp_all

definition \<Delta>'' :: "'v vertex network"
where "\<Delta>'' = \<lparr>edge = edg, capacity = split (capacity \<Delta>), source = Vertex (source \<Delta>), sink = Vertex (sink \<Delta>)\<rparr>"

lemma \<Delta>''_sel [simp]:
  "edge \<Delta>'' = edg"
  "capacity \<Delta>'' = split (capacity \<Delta>)"
  "source \<Delta>'' = Vertex (source \<Delta>)"
  "sink \<Delta>'' = Vertex (sink \<Delta>)"
by(simp_all add: \<Delta>''_def)

lemma "\<^bold>E_\<Delta>''": "\<^bold>E\<^bsub>\<Delta>''\<^esub> = (\<lambda>(x, y). (Vertex x, Edge x y)) ` \<^bold>E \<union> (\<lambda>(x, y). (Edge x y, Vertex y)) ` \<^bold>E"
by(auto elim: edg.cases)

lemma "\<^bold>V_\<Delta>''": "\<^bold>V\<^bsub>\<Delta>''\<^esub> = Vertex ` \<^bold>V \<union> case_prod Edge ` \<^bold>E"
by(auto 4 4 simp add: vertex_def elim!: edg.cases)

lemma inj_on_Edge1 [simp]: "inj_on (\<lambda>x. Edge x y) A"
by(simp add: inj_on_def)

lemma inj_on_Edge2 [simp]: "inj_on (Edge x) A"
by(simp add: inj_on_def)

lemma d_IN_split_Vertex [simp]: "d_IN (split f) (Vertex x) = d_IN f x" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'\<in>range (\<lambda>y. Edge y x). split f (v', Vertex x))"
    by(auto intro!: nn_integral_cong split_Vertex2_eq_0I simp add: d_IN_def nn_integral_count_space_indicator split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_IN_def)
qed

lemma d_OUT_split_Vertex [simp]: "d_OUT (split f) (Vertex x) = d_OUT f x" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'\<in>range (Edge x). split f (Vertex x, v'))"
    by(auto intro!: nn_integral_cong split_Vertex1_eq_0I simp add: d_OUT_def nn_integral_count_space_indicator split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_OUT_def)
qed

lemma d_IN_split_Edge [simp]: "d_IN (split f) (Edge x y) = max 0 (f (x, y))" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'. split f (v', Edge x y) * indicator {Vertex x} v')"
    unfolding d_IN_def by(rule nn_integral_cong)(simp add: split_Edge2_eq_0I split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: max_def)
qed

lemma d_OUT_split_Edge [simp]: "d_OUT (split f) (Edge x y) = max 0 (f (x, y))" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'. split f (Edge x y, v') * indicator {Vertex y} v')"
    unfolding d_OUT_def by(rule nn_integral_cong)(simp add: split_Edge1_eq_0I split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: max_def)
qed

lemma \<Delta>''_countable_network: "countable_network \<Delta>''"
proof
  show "countable \<^bold>E\<^bsub>\<Delta>''\<^esub>" unfolding "\<^bold>E_\<Delta>''" by(simp)
  show "source \<Delta>'' \<noteq> sink \<Delta>''" by auto
  show "capacity \<Delta>'' e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Delta>''\<^esub>" for e using that
    by(cases "(capacity \<Delta>, e)" rule: split.cases)(auto simp add: capacity_outside)
  show "capacity \<Delta>'' e \<noteq> top" for e by(cases "(capacity \<Delta>, e)" rule: split.cases)(auto)
qed

interpretation \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)

lemma flow_split [simp]:
  assumes "flow \<Delta> f"
  shows "flow \<Delta>'' (split f)"
proof
  show "split f e \<le> capacity \<Delta>'' e" for e
    by(cases "(f, e)" rule: split.cases)(auto intro: flowD_capacity[OF assms] intro: SUP_upper2 assms)
  show "KIR (split f) x" if "x \<noteq> source \<Delta>''" "x \<noteq> sink \<Delta>''" for x
    using that by(cases "x")(auto dest: flowD_KIR[OF assms])
qed

abbreviation (input) collect :: "'v vertex flow \<Rightarrow> 'v flow"
where "collect f \<equiv> (\<lambda>(x, y). f (Edge x y, Vertex y))"

lemma d_OUT_collect:
  assumes f: "flow \<Delta>'' f"
  shows "d_OUT (collect f) x = d_OUT f (Vertex x)"
proof -
  have "d_OUT (collect f) x = (\<Sum>\<^sup>+ y. f (Edge x y, Vertex y))"
    by(simp add: nn_integral_count_space_reindex d_OUT_def)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range (Edge x). f (Vertex x, y))"
  proof(clarsimp simp add: nn_integral_count_space_reindex intro!: nn_integral_cong)
    fix y
    have "(\<Sum>\<^sup>+ z. f (Edge x y, z) * indicator {Vertex y} z) = d_OUT f (Edge x y)"
      unfolding d_OUT_def by(rule nn_integral_cong)(simp split: split_indicator add: \<Delta>''.flowD_outside[OF f])
    also have "\<dots> = d_IN f (Edge x y)" using f by(rule flowD_KIR) simp_all
    also have "\<dots> = (\<Sum>\<^sup>+ z. f (z, Edge x y) * indicator {Vertex x} z)"
      unfolding d_IN_def by(rule nn_integral_cong)(simp split: split_indicator add: \<Delta>''.flowD_outside[OF f])
    finally show "f (Edge x y, Vertex y) = f (Vertex x, Edge x y)"
      by(simp add: max_def)
  qed
  also have "\<dots> = d_OUT f (Vertex x)"
    by(auto intro!: nn_integral_cong \<Delta>''.flowD_outside[OF f] simp add: nn_integral_count_space_indicator d_OUT_def split: split_indicator)
  finally show ?thesis .
qed

lemma flow_collect [simp]:
  assumes f: "flow \<Delta>'' f"
  shows "flow \<Delta> (collect f)"
proof
  show "collect f e \<le> capacity \<Delta> e" for e using flowD_capacity[OF f, of "(case_prod Edge e, Vertex (snd e))"]
    by(cases e)(simp)

  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT (collect f) x = d_OUT f (Vertex x)" using f by(rule d_OUT_collect)
  also have "\<dots> = d_IN f (Vertex x)" using x flowD_KIR[OF f, of "Vertex x"] by(simp)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range (\<lambda>z. Edge z x). f (y, Vertex x))"
    by(auto intro!: nn_integral_cong \<Delta>''.flowD_outside[OF f] simp add: nn_integral_count_space_indicator d_IN_def split: split_indicator)
  also have "\<dots> = d_IN (collect f) x" by(simp add: nn_integral_count_space_reindex d_IN_def)
  finally show "KIR (collect f) x" .
qed

lemma value_collect: "flow \<Delta>'' f \<Longrightarrow> value_flow \<Delta> (collect f) = value_flow \<Delta>'' f"
by(simp add: d_OUT_collect)

end

end